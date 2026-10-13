#!/usr/bin/env bb
(require '[clojure.edn :as edn]
         '[clojure.java.io :as io]
         '[clojure.java.shell :as shell]
         '[clojure.set :as set]
         '[clojure.string :as str])

(def here (.getParentFile (.getAbsoluteFile (io/file *file*))))
(def path (or (first *command-line-args*) (str here "/worklist.edn")))
(def w (edn/read-string (slurp path)))
(defn die [& xs] (binding [*out* *err*] (apply println "topology-worklist:" xs)) (System/exit 1))
(when-not (= :topology/worklist-v1 (:schema w)) (die "unexpected schema" (:schema w)))
(doseq [k [:campaign :canonical-root :canonical-packages :statuses :edge-kinds :baseline :items]]
  (when-not (contains? w k) (die "ledger lacks" k)))
(def items (:items w))
(def ids (map :id items))
(def by-id (into {} (map (juxt :id identity) items)))
(defn owner-blocked? [dependency seen]
  (when-not (seen dependency)
    (let [item (by-id dependency)]
      ;; A :backlog lemma is never scheduled by itself; only a strategy
      ;; checkpoint elects a row for it. So a checkpoint waiting on work that
      ;; waits on one must run, exactly as for :needs-owner. On 2026-10-11
      ;; topo1 paused at 04:31 with 74 backlog lemmas: its checkpoint waited
      ;; on a row blocked on an unelected lemma.
      ;; A reviewed STOP (:stopped) delivered nothing, and nothing will
      ;; until a checkpoint elects the work it named, so it counts too; so
      ;; does a :superseded row, which will never finish (2026-10-12: topo3's
      ;; checkpoint waited on a superseded triangulation row and the loop
      ;; exited with nothing eligible).
      (or (#{:needs-owner :stopped :superseded} (:state item))
          (and (= :lemma (:kind item)) (= :backlog (:state item)))
          (and (= :blocked (:state item))
               (some #(owner-blocked? % (conj seen dependency))
                     (:depends-on item)))))))
(def root (:canonical-root w))
(def fixture-store (io/file here "fixture-store"))
(def lost-fixtures (atom []))
(defn sh [& args] (apply shell/sh (concat args [:dir root])))
(defn commit-exists? [sha]
  (and (string? sha)
       (zero? (:exit (sh "git" "cat-file" "-e" (str sha "^{commit}"))))))
(defn commit-paths [sha]
  (->> (str/split-lines (:out (sh "git" "show" "--pretty=" "--name-only" sha)))
       (remove str/blank?) set))
(defn file-sha [p]
  (let [candidate (io/file p)
        f (if (.isAbsolute candidate) candidate (io/file root p))]
    (when (.isFile f)
      (first (str/split (:out (shell/sh "sha256sum" (.getPath f))) #"\s+")))))
(defn committed-file-sha
  "sha256 of repo path p as it was at commit c; nil when absent there."
  [c p]
  (let [rel (str/replace (str p) (re-pattern (str "^" (java.util.regex.Pattern/quote (str root "/")))) "")
        r (shell/sh "sh" "-c" "git show \"$1:$2\" | sha256sum" "_" c rel :dir root)
        ok (zero? (:exit (sh "git" "cat-file" "-e" (str c ":" rel))))]
    (when ok (first (str/split (:out r) #"\s+")))))
(when-not (= (count ids) (count (set ids))) (die "duplicate item ids"))
(doseq [i items]
  (doseq [k [:id :kind :state :depends-on :consumer :acceptance]]
    (when-not (contains? i k) (die (:id i) "lacks" k)))
  ;; :backlog/:banked and :lemma belong to the lemma DAG, defined in code
  ;; (build_step.bb), so every ledger accepts them without a data migration.
  ;; :stopped (a reviewed STOP) is likewise defined in code.
  (when-not ((into (:statuses w) #{:backlog :banked :stopped}) (:state i)) (die (:id i) "unknown state" (:state i)))
  (when-not ((conj (:edge-kinds w) :lemma) (:kind i)) (die (:id i) "unknown kind" (:kind i)))
  (when-not (= (count (:depends-on i)) (count (set (:depends-on i))))
    (die (:id i) "contains duplicate dependencies"))
  (doseq [d (:depends-on i)] (when-not (by-id d) (die (:id i) "unknown dependency" d)))
  (let [ready? (every? #(let [state (:state (by-id %))]
                          (or (#{:done :banked} state)
                              (and (= :strategy-checkpoint (:kind i))
                                   (owner-blocked? % #{}))))
                       (:depends-on i))]
    (when (and (= :open (:state i)) (not ready?)) (die (:id i) "open with incomplete dependency"))
    (when (and (= :blocked (:state i)) ready?) (die (:id i) "blocked although dependencies are done")))
  (when (and (= :reusable-theorem (:kind i))
             (< (count (set (conj (set (:other-consumers i)) (:consumer i)))) 2)
             (not (:bounded-exception i)))
    (die (:id i) "reusable theorem lacks two consumers or bounded exception"))
  (when (= :representation-comparison (:kind i))
    ;; The row must name both representations and the orientation between
    ;; them. This asked for them as :source-representation,
    ;; :target-representation and :orientation -- names no row in this
    ;; worklist has ever carried. All 158 rows with representation data write
    ;; :representation {:source .. :target .. :direction ..}, so this branch
    ;; never executed until 2026-09-08 07:24, when the campaign's first
    ;; :representation-comparison row arrived correctly formed under the house
    ;; convention and stopped the loop. Read the house form; the flat names
    ;; still satisfy it, so a row written either way passes.
    (doseq [[label paths]
            [[:source-representation [[:representation :source]
                                      [:source-representation]]]
             [:target-representation [[:representation :target]
                                      [:target-representation]]]
             [:orientation [[:representation :direction] [:orientation]]]]]
      (when-not (some #(not (str/blank? (str (get-in i %)))) paths)
        (die (:id i) "representation comparison lacks" label))))
  ;; Lemma-DAG nodes (build_step.bb, "Lemma DAG"): never scheduled directly,
  ;; only :backlog until a reviewed row proves them, then :banked.
  (if (= :lemma (:kind i))
    (do (when-not (#{:backlog :banked} (:state i)) (die (:id i) "lemma node in state" (:state i)))
        (when (str/blank? (str (get-in i [:lemma :name]))) (die (:id i) "lemma node lacks :lemma :name"))
        (when (and (= :banked (:state i)) (not (get-in i [:lemma :banked-by])))
          (die (:id i) "banked lemma lacks :banked-by")))
    (when (#{:backlog :banked} (:state i)) (die (:id i) "only lemma nodes may be" (:state i))))
  (when-let [l (:implements-lemma i)]
    (when-not (= :lemma (:kind (by-id l))) (die (:id i) ":implements-lemma names no lemma node" l)))
  (when (= :strategy-checkpoint (:kind i))
    (when-not (and (= :strategy (:phase i)) (map? (:checkpoint i)))
      (die (:id i) "strategy checkpoint lacks :phase :strategy or checkpoint policy")))
  (when (#{:done-unreviewed :done} (:state i))
    (when-not (:evidence i) (die (:id i) "completed without evidence"))
    (let [e (:evidence i) commit (:commit e) fixture (:fixture e)
          ;; A row completed via REPAIR does its work across more than one
          ;; commit: the implementation writes the module and its .md, then the
          ;; repair touches only what it had to fix. On 2026-09-07
          ;; :critical-value-sard-projected-implicit-function-packaging-1
          ;; recorded its repair commit b0686676 (.lean only) against a
          ;; two-path scope and stopped the loop at row 60 of 70, even though
          ;; f6654435 + b0686676 cover that scope exactly and the .md was
          ;; correct as written.
          ;;
          ;; :commits records every commit belonging to the row and the scope
          ;; check runs over their union.  Scope is the row's write permission,
          ;; not a promise that every permitted file changes: program rows
          ;; routinely name their Main, status, closure, and blueprint while a
          ;; milestone changes only the files needed for that milestone.
          ;; :commit alone remains valid; 58 rows use it.
          commits (or (seq (:commits e)) (when commit [commit]))]
      (if (#{:stop :replan} (:outcome e))
        (when-not (and (:author e) (seq (:commands e)))
          (die (:id i) "reviewable scheduling result lacks author or commands"))
        (do
          (when-not (seq commits) (die (:id i) "completed without an evidence commit"))
          (doseq [c commits]
            (when-not (commit-exists? c) (die (:id i) "evidence commit absent" c)))
          (when-not (set/subset? (reduce into #{} (map commit-paths commits))
                                 (set (:scope i)))
            (die (:id i) "commit paths exceed scope"))
          (when-not (and (map? fixture) (:path fixture) (:sha256 fixture))
            (die (:id i) "completed without fixture path and hash"))
          ;; The fixture records the file as the row's evidence commit left
          ;; it. A later commit may legitimately change that file -- a closing
          ;; proof, or a graded statement repair (t96J07's rewrite, 2026-09-28,
          ;; failed two finished rows here) -- so accept the hash of the file
          ;; at one of the row's own commits as well as the current file.
          ;;
          ;; A fixture outside the repo (seats mostly write /tmp probes) does
          ;; not survive a reboot. build_step.bb keeps a content-addressed
          ;; copy in fixture-store/, which stands in for the recorded path
          ;; once that path is gone. Rows applied before the store existed
          ;; lost their /tmp fixtures when zone was rebuilt (2026-10-06);
          ;; for those, a PASS review that saw the file is the remaining
          ;; record, so an ABSENT out-of-repo fixture on a PASS row is
          ;; counted rather than fatal. A file that is present and differs
          ;; still fails.
          (let [p (:path fixture)
                sha (:sha256 fixture)
                out-of-repo? (and (.isAbsolute (io/file p))
                                  (not (str/starts-with? p (str root "/"))))
                current (file-sha p)]
            (cond
              (= sha current) nil
              (some #(= sha (committed-file-sha % p)) commits) nil
              ;; `/tmp` paths are reusable names, not stable identities.  A
              ;; later dependent probe may legitimately rewrite the same
              ;; pathname while the completed row's exact bytes remain in
              ;; the immutable, content-addressed fixture store.  Consult
              ;; that store regardless of whether the ephemeral path is now
              ;; absent or contains a newer fixture.
              (and out-of-repo? (= sha (file-sha (str fixture-store "/" sha)))) nil
              (and out-of-repo? (nil? current)
                   (= :pass (get-in i [:evidence :review :outcome])))
              (swap! lost-fixtures conj (:id i))
              :else (die (:id i) "fixture hash mismatch or file absent" p)))))
      (when (some #(not= (get % :expected-exit 0) (:exit %)) (:commands e))
        (die (:id i) "records an unexpected gate exit"))))
  (when (and (= :done (:state i)) (= :stop (get-in i [:evidence :outcome])))
    (die (:id i) "done although its receipt is a STOP (a reviewed STOP is :stopped)"))
  (when (= :stopped (:state i))
    (when-not (= :stop (get-in i [:evidence :outcome])) (die (:id i) "stopped without a STOP receipt"))
    (when-not (= :pass (get-in i [:evidence :review :outcome])) (die (:id i) "stopped without PASS review")))
  (when (= :done (:state i))
    (when-not (= :pass (get-in i [:evidence :review :outcome])) (die (:id i) "done without PASS review"))
    (when (= (get-in i [:evidence :author]) (get-in i [:evidence :review :seat]))
      (die (:id i) "author and reviewer are identical"))))

(defn visit [id visiting visited]
  (cond (visited id) visited
        (visiting id) (die "dependency cycle at" id)
        :else (reduce (fn [v d] (visit d (conj visiting id) v))
                      (conj visited id) (:depends-on (by-id id)))))
(reduce (fn [v id] (visit id #{} v)) #{} ids)

(let [active (filter #(#{:probing :implementing :repair} (:state %)) items)
      unreviewed (filter #(= :done-unreviewed (:state %)) items)
      pinned (filter #(= 0 (:campaign-priority %)) items)]
  (when (> (count active) 1) (die "more than one active writer" (map :id active)))
  (when (> (count unreviewed) 1) (die "more than one unreviewed row" (map :id unreviewed)))
  (when (> (count pinned) 1) (die "more than one campaign-priority 0 row" (map :id pinned))))

(let [package-path (io/file root ".lake/packages")
      canonical (.getCanonicalPath package-path)]
  (when-not (= canonical (:canonical-packages w))
    (die ".lake/packages resolves to" canonical "not" (:canonical-packages w)))
  (when (and (not= root "/home/joe/code/apm-lean")
             (not (java.nio.file.Files/isSymbolicLink (.toPath package-path))))
    (die "a non-canonical APM checkout must symlink .lake/packages"))
  (when-not (= "0" (str (:exit (shell/sh "git" "rev-parse" "--verify" (:git-sha (:baseline w)) :dir root))))
    (die "baseline commit absent" (:git-sha (:baseline w)))))
(println "topology-worklist:" (count items) "items OK;" (pr-str (frequencies (map :state items))))
(when (seq @lost-fixtures)
  (println "topology-worklist:" (count @lost-fixtures)
           "PASS rows whose out-of-repo fixture is gone; accepted on their review"))
