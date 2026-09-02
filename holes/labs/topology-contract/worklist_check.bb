#!/usr/bin/env bb
(require '[clojure.edn :as edn]
         '[clojure.java.io :as io]
         '[clojure.java.shell :as shell]
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
(def root (:canonical-root w))
(defn sh [& args] (apply shell/sh (concat args [:dir root])))
(defn commit-exists? [sha]
  (and (string? sha)
       (zero? (:exit (sh "git" "cat-file" "-e" (str sha "^{commit}"))))))
(defn commit-paths [sha]
  (->> (str/split-lines (:out (sh "git" "show" "--pretty=" "--name-only" sha)))
       (remove str/blank?) set))
(defn file-sha [p]
  (let [f (io/file root p)]
    (when (.isFile f)
      (first (str/split (:out (shell/sh "sha256sum" (.getPath f))) #"\s+")))))
(when-not (= (count ids) (count (set ids))) (die "duplicate item ids"))
(doseq [i items]
  (doseq [k [:id :kind :state :depends-on :consumer :acceptance]]
    (when-not (contains? i k) (die (:id i) "lacks" k)))
  (when-not ((:statuses w) (:state i)) (die (:id i) "unknown state" (:state i)))
  (when-not ((:edge-kinds w) (:kind i)) (die (:id i) "unknown kind" (:kind i)))
  (doseq [d (:depends-on i)] (when-not (by-id d) (die (:id i) "unknown dependency" d)))
  (let [ready? (every? #(= :done (:state (by-id %))) (:depends-on i))]
    (when (and (= :open (:state i)) (not ready?)) (die (:id i) "open with incomplete dependency"))
    (when (and (= :blocked (:state i)) ready?) (die (:id i) "blocked although dependencies are done")))
  (when (and (= :reusable-theorem (:kind i))
             (< (count (set (conj (set (:other-consumers i)) (:consumer i)))) 2)
             (not (:bounded-exception i)))
    (die (:id i) "reusable theorem lacks two consumers or bounded exception"))
  (when (= :representation-comparison (:kind i))
    (doseq [k [:source-representation :target-representation :orientation]]
      (when (str/blank? (str (get i k))) (die (:id i) "representation comparison lacks" k))))
  (when (= :strategy-checkpoint (:kind i))
    (when-not (and (= :strategy (:phase i)) (map? (:checkpoint i)))
      (die (:id i) "strategy checkpoint lacks :phase :strategy or checkpoint policy")))
  (when (#{:done-unreviewed :done} (:state i))
    (when-not (:evidence i) (die (:id i) "completed without evidence"))
    (let [e (:evidence i) commit (:commit e) fixture (:fixture e)]
      (if (#{:stop :replan} (:outcome e))
        (when-not (and (:author e) (seq (:commands e)))
          (die (:id i) "reviewable scheduling result lacks author or commands"))
        (do
          (when-not (commit-exists? commit) (die (:id i) "evidence commit absent" commit))
          (when-not (= (set (:scope i)) (commit-paths commit))
            (die (:id i) "commit paths differ from exact scope"))
          (when-not (and (map? fixture) (:path fixture) (:sha256 fixture))
            (die (:id i) "completed without fixture path and hash"))
          (when-not (= (:sha256 fixture) (file-sha (:path fixture)))
            (die (:id i) "fixture hash mismatch or file absent" (:path fixture)))))
      (when (some #(not= 0 (:exit %)) (:commands e))
        (die (:id i) "records a failed gate command"))))
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
