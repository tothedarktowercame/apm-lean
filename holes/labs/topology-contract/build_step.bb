#!/usr/bin/env bb
(require '[clojure.edn :as edn]
         '[clojure.string :as str]
         '[clojure.set :as set]
         '[clojure.java.shell :as shell]
         '[clojure.pprint :as pprint]
         '[clojure.walk :as walk]
         '[clojure.java.io :as io]
         '[cheshire.core :as json])

(def here (.getParent (.getAbsoluteFile (java.io.File. *file*))))
(def cmd (first *command-line-args*))
(def path (or (second *command-line-args*) (str here "/worklist.edn")))
(def original-text (slurp path))
(def data (edn/read-string original-text))
(def items (:items data))
(def ids (map :id items))
(def by-id (into {} (map (juxt :id identity) items)))
;; Closure first (Joe, 2026-10-10: "lemma work should lead to closures").
;; :consumer-closure ranked 4, below :reusable-theorem, so on 2026-10-11 the
;; t99J01 closure probe sat open behind a stream of polygon lemma rows after
;; its route was complete.
(def priority {:consumer-closure -1 :uptake 0 :final-adapter 1 :representation-comparison 2
               :reusable-theorem 3 :documentation 5})
(def max-stops (parse-long (or (System/getenv "TOPOLOGY_MAX_ROW_STOPS") "2")))
(def program-max-stops (parse-long (or (System/getenv "TOPOLOGY_PROGRAM_MAX_STOPS") "10")))
(def max-fails (parse-long (or (System/getenv "TOPOLOGY_MAX_ROW_FAILS") "4")))
(defn owner-blocked? [idx dependency seen]
  (when-not (seen dependency)
    (let [item (idx dependency)]
      ;; A :backlog lemma is never scheduled by itself; only a strategy
      ;; checkpoint elects a row for it. So a checkpoint waiting on work that
      ;; waits on one must run, exactly as for :needs-owner. On 2026-10-11
      ;; topo1 paused at 04:31 with 74 backlog lemmas: its checkpoint waited
      ;; on a row blocked on an unelected lemma.
      ;; A reviewed STOP (:stopped) delivered nothing, and nothing will
      ;; until a checkpoint elects the work it named, so it counts too.
      (or (#{:needs-owner :stopped} (:state item))
          (and (= :lemma (:kind item)) (= :backlog (:state item)))
          (and (= :blocked (:state item))
               (some #(owner-blocked? idx % (conj seen dependency))
                     (:depends-on item)))))))
(def satisfied-states
  "A dependency in one of these states no longer blocks its dependents: a
   reviewed row, or a lemma-DAG node someone has proved and banked."
  #{:done :banked})
(defn dependency-ready? [dependent dependency]
  (let [state (:state (by-id dependency))]
    (or (satisfied-states state)
        (and (= :strategy-checkpoint (:kind dependent))
             (owner-blocked? by-id dependency #{})))))
(defn eligible? [i]
  (and (#{:open :repair} (:state i))
       (every? #(dependency-ready? i %) (:depends-on i))))
(defn selected []
  (first (sort-by (juxt #(or (:campaign-priority %) 100)
                             #(get priority (:kind %) 99)
                             #(count (:scope %))
                             #(name (:id %)))
                  (filter eligible? items))))
(defn commit-exists? [root sha]
  (zero? (:exit (shell/sh "git" "cat-file" "-e" (str sha "^{commit}") :dir root))))
(defn replay! []
  (when-not (= :topology/replay-v1 (:schema data))
    (throw (ex-info "not a topology replay" {:path path})))
  (loop [done #{} xs items]
    (when-let [i (first xs)]
      (when-not (every? done (:depends-on i))
        (throw (ex-info "replay dependency not complete" {:id (:id i) :depends-on (:depends-on i)})))
      (doseq [sha (concat (when-let [x (:commit i)] [x]) (:commits i))]
        (when-not (commit-exists? "/home/joe/code/apm-lean" sha)
          (throw (ex-info "replay commit absent" {:id (:id i) :sha sha}))))
      (println (format "%-29s %-8s %s" (name (:id i)) (name (:result i))
                       (str/join "," (concat (when-let [x (:commit i)] [x]) (:commits i)))))
      (recur (conj done (:id i)) (next xs))))
  (println "replay: CLOSED" (name (:campaign data))
           (str (:baseline-placeholders data) "->" (:final-placeholders data))))
(defn rebase-onto
  "Apply this step's row changes (x relative to the ledger as read at startup)
  onto the ledger text now on disk. Another writer (a person adding a row, the
  other half of a split) may have changed the file while this step ran; a plain
  write of x would silently drop their rows (2026-09-29: a hand-added t99J04 row
  vanished under ffa2a465)."
  [x current-text]
  (if (= current-text original-text)
    x
    (let [cur (edn/read-string current-text)
          new-idx (into {} (map (juxt :id identity) (:items x)))
          changed (into {} (keep (fn [[id row]] (when (not= row (by-id id)) [id row])) new-idx))
          removed (set (remove new-idx ids))
          cur-ids (set (map :id (:items cur)))
          kept (->> (:items cur)
                    (remove #(removed (:id %)))
                    (mapv #(get changed (:id %) %)))
          added (->> (:items x) (filter #(and (changed (:id %)) (not (cur-ids (:id %))))))]
      (assoc x :items (into kept added)))))
(defn write-ledger! [x0]
  (loop [attempt 1]
  (let [seen (slurp path)
        x (rebase-onto x0 seen)
        tmp (io/file (str path ".tmp"))]
    (spit tmp (with-out-str (pprint/pprint x)))
    ;; Validate BEFORE the atomic move, so no receipt can ever write a ledger
    ;; that worklist_check refuses.
    ;;
    ;; The same invalid ledger has now been produced by two different receipt
    ;; types, each time on a :strategy-checkpoint row:
    ;;   2026-09-02  `applied fail`  -> :checkpoint-full-dag-refill-1
    ;;   2026-09-10  `applied go`    -> :oriented-checkpoint52-...-refill-1
    ;; Both left "strategy checkpoint lacks :phase :strategy or checkpoint
    ;; policy". The first was fixed by patching the :fail branch (2f41fd67);
    ;; :go then walked into the identical state because GO forces
    ;; :phase :implementation. Patching outcome by outcome only moves the hole.
    ;; The ledger's invariants live in worklist_check.bb, so the one place that
    ;; writes the ledger now asks it first.
    ;;
    ;; It also closes a worse gap: the loop commits the ledger BEFORE its own
    ;; validate() runs, so on 2026-09-10 the invalid state was committed to git
    ;; (3efbe0b9) and needed hand repair. A rejected receipt now leaves the
    ;; ledger untouched; the loop's invalid-receipt path clears the in-flight
    ;; pointer and the row is redispatched from its prior, valid state.
    (let [{:keys [exit err out]} (shell/sh "bb" (str here "/worklist_check.bb") (str tmp))]
      (when-not (zero? exit)
        (.delete tmp)
        (throw (ex-info (str "receipt would invalidate the ledger: "
                             (str/trim (str/replace (str err out) #"^topology-worklist:\s*" "")))
                        {}))))
    ;; Validation takes seconds; if the file changed meanwhile, rebase again.
    (if (and (not= seen (slurp path)) (< attempt 5))
      (do (.delete tmp) (recur (inc attempt)))
      (java.nio.file.Files/move (.toPath tmp) (.toPath (io/file path))
        (into-array java.nio.file.CopyOption
                    [java.nio.file.StandardCopyOption/REPLACE_EXISTING
                     java.nio.file.StandardCopyOption/ATOMIC_MOVE]))))))
(defn replace-item [xs id f]
  (mapv #(if (= id (:id %)) (f %) %) xs))
(defn normalize-prerequisite [asking-row prerequisite]
  ;; A prerequisite cannot depend on the row that is waiting for it. Agents
  ;; occasionally describe provenance by putting the asking probe in P's
  ;; :depends-on; after REVISE adds the reverse edge this becomes a cycle and
  ;; leaves an :open row with an incomplete dependency. Preserve the actual
  ;; scheduling constraint by splicing in the asking row's prior dependencies.
  (let [asking-id (:id asking-row)
        prior (:depends-on asking-row)]
    (update prerequisite :depends-on
            #(vec (distinct (mapcat (fn [dependency]
                                      (if (= asking-id dependency)
                                        prior
                                        [dependency]))
                                    (or % [])))))))
(defn unblock-ready [xs]
  (let [idx (into {} (map (juxt :id identity) xs))]
    (mapv #(if (and (= :blocked (:state %))
                    (every? (fn [d]
                              (let [state (:state (idx d))]
                                (or (satisfied-states state)
                                    (and (= :strategy-checkpoint (:kind %))
                                         (owner-blocked? idx d #{})))))
                            (:depends-on %)))
             (assoc % :state :open)
             %) xs)))
(defn normalize-receipt [receipt]
  ;; Implementation packets are asked to report the "next consumer residual",
  ;; and older receipts conventionally named the same datum :residual.  Keep
  ;; the producer's explicit field for audit, but present the canonical ledger
  ;; key to validation and downstream readers.
  (let [canonical-kind (fn [row]
                         (update row :kind
                                 #(get {:adapter :final-adapter
                                        :problem-adapter :final-adapter}
                                       % %)))]
    (cond-> receipt
      (and (= :done-unreviewed (:outcome receipt))
           (nil? (:residual receipt))
           (some? (:next-consumer-residual receipt)))
      (assoc :residual (:next-consumer-residual receipt))

      (= :replan (:outcome receipt))
      (update :replacement-items #(mapv canonical-kind %))

      (and (= :revise (:outcome receipt)) (:prerequisite receipt))
      (update :prerequisite canonical-kind))))

(def fixture-transition-preserve-schemas
  {:checkpoint60-primary
   {:path [:evidence :fixture :path]
    :preserve {:sha256 [:evidence :fixture :sha256]
    :supporting-path [:evidence :fixture :supporting-path]
    :supporting-sha256 [:evidence :fixture :supporting-sha256]
    :placeholder-count [:evidence :fixture :placeholder-count]
    :commit [:evidence :commit]
    :review-outcome [:evidence :review :outcome]}}
   :checkpoint66-supporting
   {:path [:evidence :fixture :supporting-path]
    :preserve {:fixture-path [:evidence :fixture :path]
    :sha256 [:evidence :fixture :sha256]
    :supporting-sha256 [:evidence :fixture :supporting-sha256]
    :placeholder-count [:evidence :fixture :placeholder-count]
    :commit [:evidence :commit]
    :review-outcome [:evidence :review :outcome]}}
   :checkpoint67-primary
   {:path [:evidence :fixture :path]
    :preserve {:sha256 [:evidence :fixture :sha256]
               :reviewed-source [:evidence :fixture :reviewed-source]
               :reviewed-source-sha256 [:evidence :fixture :reviewed-source-sha256]
               :predecessor-path [:evidence :fixture :predecessor-path]
               :predecessor-sha256 [:evidence :fixture :predecessor-sha256]
               :placeholder-count [:evidence :fixture :placeholder-count]
               :commit [:evidence :commit]
               :review-outcome [:evidence :review :outcome]
               :declarations [:acceptance :declarations]
               :statement-hashes [:evidence :statement-hashes]}}})

(def default-fixture-transition-schema
  {[:evidence :fixture :path] :checkpoint60-primary
   [:evidence :fixture :supporting-path] :checkpoint66-supporting})

(defn canonical-file [p]
  (let [f (io/file p)]
    (if (.isAbsolute f) f (io/file (:canonical-root data) p))))

(defn sha256-file [f]
  (when (.isFile f)
    (let [{:keys [exit out]} (shell/sh "sha256sum" (.getPath f))]
      (when (zero? exit) (first (str/split out #"\s+"))))))

;; Seats write most probe fixtures under /tmp, and worklist_check re-hashes
;; every completed row's fixture on each start. zone's 2026-10-06 disk loss
;; wiped /tmp, so 750 reviewed rows failed validation on 10-10 and neither loop
;; could restart. Keep a content-addressed copy, shared by both ledgers, at
;; apply time; worklist_check accepts it when the recorded path is gone.
(def fixture-store (io/file here "fixture-store"))

(defn stash-fixture! [{:keys [path sha256]}]
  (when (and path sha256)
    (let [f (canonical-file path)]
      (when (= sha256 (sha256-file f))
        (.mkdirs fixture-store)
        (let [dest (io/file fixture-store sha256)]
          (when-not (.isFile dest) (io/copy f dest)))))))

(defn apply-completion-transition [xs receipt outcome]
  (if-let [transition (:completion-transition receipt)]
    (do
      (when-not (= :done-unreviewed outcome)
        (throw (ex-info "completion transition requires done-unreviewed outcome" {})))
      (when-not (or (= #{:row :path :from :to :preserve} (set (keys transition)))
                    (= #{:row :path :from :to :preserve :preserve-schema}
                       (set (keys transition))))
        (throw (ex-info "completion transition has unsupported fields" {})))
      (let [schema-name (or (:preserve-schema transition)
                            (get default-fixture-transition-schema (:path transition)))
            schema (get fixture-transition-preserve-schemas schema-name)
            preserve-paths (:preserve schema)]
        (when-not schema
          (throw (ex-info "completion transition has unknown preserve schema" {})))
        (when-not (= (:path schema) (:path transition))
          (throw (ex-info "completion transition schema does not allow requested path" {})))
        (when-not (= (set (keys preserve-paths)) (set (keys (:preserve transition))))
          (throw (ex-info "completion transition must preserve every required value" {})))
        (let [matches (keep-indexed #(when (= (:row transition) (:id %2)) %1) xs)]
        (when-not (= 1 (count matches))
          (throw (ex-info "completion transition must identify exactly one row" {})))
        (let [index (first matches) row (nth xs index)
              fixture (get-in row [:evidence :fixture])
              target (canonical-file (:to transition))]
          (when-not (#{:done :done-unreviewed} (:state row))
            (throw (ex-info "completion transition target row is not completed" {})))
          (when-not (= (:from transition) (get-in row (:path transition)))
            (throw (ex-info "completion transition source path mismatch" {})))
          (doseq [[label path] preserve-paths]
            (when-not (= (get-in row path) (get-in transition [:preserve label]))
              (throw (ex-info "completion transition preserved value mismatch"
                              {:field label}))))
          (let [expected-hash (if (= [:evidence :fixture :path] (:path transition))
                                (:sha256 fixture) (:supporting-sha256 fixture))]
            (when-not (= expected-hash (sha256-file target))
              (throw (ex-info "completion transition target missing or hash mismatch" {}))))
          (assoc xs index (assoc-in row (:path transition) (:to transition)))))))
    xs))
(declare protected-path?)
(defn validate-inserted-row! [row allowed-ids]
  (when-let [p (seq (filter #(protected-path? (str %)) (:scope row)))]
    (throw (ex-info "inserted row scopes the statement registry, which loop rows may not write"
                    {:id (:id row) :paths (vec p)})))
  (doseq [dependency (:depends-on row)]
    (when-not (allowed-ids dependency)
      (throw (ex-info "inserted row has unknown dependency"
                      {:id (:id row) :dependency dependency}))))
  (when (= :representation-comparison (:kind row))
    (doseq [[label paths]
            [[:source-representation [[:representation :source]
                                      [:source-representation]]]
             [:target-representation [[:representation :target]
                                      [:target-representation]]]
             [:orientation [[:representation :direction] [:orientation]]]]]
      (when-not (some #(not (str/blank? (str (get-in row %)))) paths)
        (throw (ex-info "representation comparison row lacks required field"
                        {:id (:id row) :field label}))))))
;; Need-driven admission (Joe, 2026-09-10). A strategy checkpoint may elect
;; only work that an open frozen problem needs: every non-documentation row it
;; inserts must name a frozen problem that still has placeholders, and a
;; reusable theorem must name two. topo2 was seeded as an "independent
;; foundation campaign" and elected rows whose only consumers were labels such
;; as :circle-fundamental-class; the ledger validator accepted any consumer
;; name, so nothing tied that work to a problem. TOPOLOGY_PROBLEMS_ROOT lets
;; the tests use fixture problems whose state never changes.
(def problems-root
  (or (System/getenv "TOPOLOGY_PROBLEMS_ROOT")
      (str (or (:canonical-root data) (.getCanonicalPath (io/file here "../../.."))) "/problems")))
(def problem-dirs (delay (set (.list (io/file problems-root)))))
(defn problem-of
  "The frozen problem a consumer names: its own id, or the id prefix of a
   label such as :t02A05-moment-reduction. nil when it names no problem."
  [consumer]
  (let [s (str/replace (str consumer) #"^:" "")
        by-lower (into {} (map (juxt str/lower-case identity) @problem-dirs))]
    (or (@problem-dirs s)
        (some->> (re-find #"^[a-z]+\d\d[aj]\d\d" (str/lower-case s)) by-lower))))
(defn strip-lean [^String s]
  (let [n (count s) sb (StringBuilder.)]
    (loop [i 0]
      (if (>= i n)
        (str sb)
        (let [c (.charAt s i) nx (when (< (inc i) n) (.charAt s (inc i)))]
          (cond
            (and (= c \-) (= nx \-)) (recur (or (str/index-of s "\n" i) n))
            (and (= c \/) (= nx \-))
            (recur (loop [k (+ i 2) depth 1]
                     (cond (zero? depth) k
                           (>= k n) n
                           (str/starts-with? (subs s k (min n (+ k 2))) "/-") (recur (+ k 2) (inc depth))
                           (str/starts-with? (subs s k (min n (+ k 2))) "-/") (recur (+ k 2) (dec depth))
                           :else (recur (inc k) depth))))
            (and (= c \') (= nx \") (< (+ i 2) n) (= (.charAt s (+ i 2)) \')) (recur (+ i 3))
            (= c \") (recur (loop [k (inc i)]
                              (cond (>= k n) n
                                    (= (.charAt s k) \\) (recur (+ k 2))
                                    (= (.charAt s k) \") (inc k)
                                    :else (recur (inc k)))))
            :else (do (.append sb c) (recur (inc i)))))))))
(defn placeholder-count
  "sorry/admit/axiom outside comments and strings in the problem's Lean
   files; nil when the problem has no Lean file."
  [problem]
  (let [fs (->> (file-seq (io/file problems-root problem "lean"))
                (filter #(str/ends-with? (.getName %) ".lean")))]
    (when (seq fs)
      (reduce + (for [f fs :let [code (strip-lean (slurp f))]]
                  (+ (count (re-seq #"(?<![\w.])(?:sorry|admit)(?![\w.])" code))
                     (count (re-seq #"(?m)^[ \t]*(?:private[ \t]+|protected[ \t]+)?axiom[ \t]" code))))))))
(defn open-problems
  "Distinct frozen problems named by the row that still have placeholders."
  [row]
  (->> (cons (:consumer row) (:other-consumers row))
       (keep problem-of) distinct
       (filter #(some-> (placeholder-count %) pos?))
       set))
;; Approved statement registry (Joe, 2026-09-28). A problem is worth working
;; on only when its statement is one an outside grader approved: 18 of 62
;; problems this loop closed turned out to be proved against narrower, vacuous
;; or core-assuming statements. So only registered problems are electable
;; consumers, and no row may write the registry or its evidence. The per-
;; iteration `statement-registry.py check` in topology-build-loop.sh catches a
;; registered statement changed on master by anyone.
(def registered-problems
  (delay (let [f (io/file problems-root "STATEMENTS.json")]
           (if (.exists f)
             (set (keys (get (json/parse-string (slurp f)) "entries")))
             #{}))))
(def protected-path?
  (some-fn #{"problems/STATEMENTS.json" "scripts/statement-registry.py"}
           #(str/starts-with? % "holes/labs/statement-registry/")))
(defn need-violation
  "Why a strategy-elected work row is not needed to close an open problem, or nil."
  [row]
  (let [named-open (open-problems row)
        open (set (filter @registered-problems named-open))]
    (cond
      (and (empty? open) (seq named-open))
      {:id (:id row) :unregistered (vec named-open)
       :reason "names only open problems whose statement is not in the approved registry (problems/STATEMENTS.json); an unregistered statement needs a graded rewrite, not infrastructure"}
      (empty? open)
      {:id (:id row) :consumers (vec (cons (:consumer row) (:other-consumers row)))
       :reason "names no open frozen problem; infrastructure is elected only when an open problem needs it"}
      (and (= :reusable-theorem (:kind row)) (not (:bounded-exception row)) (< (count open) 2))
      {:id (:id row) :open-problems (vec open)
       :reason "reusable theorem needed by fewer than two open problems; elect it as that problem's adapter or record a :bounded-exception"})))
;; ---------------------------------------------------------------------------
;; Lemma DAG (Joe, 2026-10-10: "previous loops maintained a DAG so they could
;; keep track of the priority of lemmas"). TOPOLOGY-DEPENDENCY-DAG.md did this
;; by hand until 2026-09-28, when TOPOLOGY-ROUTES.md replaced it for elections
;; and nothing kept lemma dependencies any more. Lemmas now live in the ledger
;; as rows of kind :lemma, state :backlog or :banked, so they validate, commit
;; and rebase with every transition:
;;   - :depends-on      edges to the lemmas a lemma needs
;;   - :consumer/:other-consumers  the problems that need it directly
;;   - :lemma {:name :type :reported-by [...] :proved-in row}
;; Authors' :missing-theorems and strategy receipts' :lemmas add or update
;; nodes by name. A work row with :implements-lemma L, or a row whose author
;; reported L :status :proved, banks L when its review passes. `priorities`
;; ranks the backlog for strategy checkpoints.
(defn lemma-id [nm]
  (let [slug (-> (str nm) str/lower-case (str/replace #"[^a-z0-9]+" "-")
                 (str/replace #"^-+|-+$" ""))]
    (keyword (str "lemma-" (subs slug 0 (min 80 (count slug)))))))

(defn- lemma-collision-id [nm]
  (let [slug (-> (str nm) str/lower-case (str/replace #"[^a-z0-9]+" "-")
                 (str/replace #"^-+|-+$" ""))
        digest (.digest (java.security.MessageDigest/getInstance "SHA-256")
                        (.getBytes (str nm) java.nio.charset.StandardCharsets/UTF_8))
        suffix (subs (apply str (map #(format "%02x" (bit-and (int %) 0xff)) digest)) 0 12)]
    (keyword (str "lemma-" (subs slug 0 (min 60 (count slug))) "-" suffix))))

(defn- reaches?
  "Does `from` reach `to` along :depends-on in idx?"
  [idx from to]
  (loop [stack [from] seen #{}]
    (if-let [x (peek stack)]
      (cond (= x to) true
            (seen x) (recur (pop stack) seen)
            :else (recur (into (pop stack) (:depends-on (idx x))) (conj seen x)))
      false)))

(defn upsert-lemmas
  "Add or update lemma nodes from receipt entries {:id? :name :type :status
   :consumers :depends-on [names]}. An explicit id is used for a new node so
   same-receipt work rows can name it. Unknown dependency names become stub
   nodes; an edge that would close a cycle is dropped, not fatal."
  [items entries source-id]
  (let [entries (filter #(and (map? %) (not (str/blank? (str (:name %))))) entries)]
    (if (empty? entries)
      items
      (let [idx (atom (into {} (map (juxt :id identity) items)))
            order (atom (mapv :id items))
            ensure! (fn [nm consumers requested-id]
                      ;; Strategy receipts name newly elected rows' lemma node
                      ;; before that node exists in the ledger.  Preserve the
                      ;; explicit id they supplied; otherwise a qualified
                      ;; theorem name generates a different slug and leaves
                      ;; :implements-lemma dangling.  Existing nodes still win
                      ;; by theorem name, which keeps name-based upserts stable.
                      (let [existing-id (some (fn [[id row]]
                                                (when (and (= :lemma (:kind row))
                                                           (= (str nm) (get-in row [:lemma :name])))
                                                  id))
                                              @idx)
                            generated-id (lemma-id nm)
                            generated-row (@idx generated-id)
                            ;; Keep every existing stable id.  Only a newly
                            ;; generated id whose 80-character prefix is
                            ;; already occupied gets a content-derived suffix.
                            ;; Qualified theorem names commonly share prefixes
                            ;; much longer than 80 characters.
                            lid (or existing-id requested-id
                                    (if (and generated-row
                                             (= :lemma (:kind generated-row))
                                             (not= (str nm) (get-in generated-row [:lemma :name])))
                                      (lemma-collision-id nm)
                                      generated-id))
                            cur (@idx lid)]
                        (when (and cur (not= :lemma (:kind cur)))
                          (throw (ex-info "lemma id collides with a work row" {:id lid})))
                        (when (and cur (= :lemma (:kind cur))
                                   (not= (str nm) (get-in cur [:lemma :name])))
                          (throw (ex-info "lemma id names a different theorem"
                                          {:id lid :existing (get-in cur [:lemma :name])
                                           :requested (str nm)})))
                        (when-not cur
                          (swap! order conj lid)
                          (swap! idx assoc lid
                                 {:id lid :kind :lemma :state :backlog :phase :lemma
                                  :scope [] :depends-on []
                                  :consumer (or (first consumers) :portfolio)
                                  :other-consumers (vec (rest consumers))
                                  :acceptance {:lemma (str nm)}
                                  :lemma {:name (str nm) :reported-by []}}))
                        lid))]
        (doseq [{:keys [id name type status consumers depends-on area]} entries]
          (let [consumers (vec (distinct (keep #(when % (keyword (str/replace (str %) #"^:" ""))) consumers)))
                lid (ensure! name consumers id)]
            (swap! idx update lid
                   (fn [n]
                     (let [all (vec (distinct (remove #{:portfolio}
                                                      (concat [(:consumer n)] (:other-consumers n) consumers))))]
                       (cond-> (-> n
                                   (assoc :consumer (or (first all) :portfolio)
                                          :other-consumers (vec (rest all)))
                                   (update-in [:lemma :reported-by]
                                              #(vec (distinct (conj (or % []) source-id)))))
                         (and (not (str/blank? (str type))) (str/blank? (str (get-in n [:lemma :type]))))
                         (-> (assoc-in [:lemma :type] (str type))
                             (assoc-in [:acceptance :type] (str type)))
                         (and (not (str/blank? (str area))) (nil? (get-in n [:lemma :area])))
                         (assoc-in [:lemma :area] (str area))
                         (and (= :proved (keyword (str/replace (str status) #"^:" "")))
                              (= :backlog (:state n)))
                         (assoc-in [:lemma :proved-in] source-id)))))
            (doseq [dn depends-on :when (not (str/blank? (str dn)))]
              (let [did (ensure! dn [] nil)]
                (when-not (or (= did lid) (reaches? @idx did lid)
                              (some #{did} (:depends-on (@idx lid))))
                  (swap! idx update-in [lid :depends-on] conj did))))))
        (mapv @idx @order)))))

(defn reconcile-implements-lemmas
  "Resolve a replacement row's stale/synthesized lemma id from its exact
   declaration.  Strategy agents sometimes derive an id from the qualified
   theorem name even though that theorem already has a shorter stable ledger
   id.  Only an exact, unique theorem-name match is rewritten; ambiguity or a
   missing declaration remains invalid and is rejected by worklist_check."
  [items]
  (let [idx (into {} (map (juxt :id identity) items))
        ids-by-name (reduce (fn [m row]
                              (if (= :lemma (:kind row))
                                (update m (get-in row [:lemma :name]) (fnil conj []) (:id row))
                                m))
                            {} items)]
    (mapv (fn [row]
            (let [lid (:implements-lemma row)
                  declaration (get-in row [:acceptance :declaration])
                  matches (get ids-by-name declaration)]
              (if (and lid
                       (not= :lemma (:kind (idx lid)))
                       (= 1 (count matches)))
                (assoc row :implements-lemma (first matches))
                row)))
          items)))

;; Backlog lemmas whose declaration already exists. codex-71 found
;; (2026-10-11) the DAG listing rpSmoothAtlas and the smooth sphere descent
;; as missing although both were banked in RealProjectiveSmoothTarget.lean:
;; nodes are added from receipts' prose and nothing checks them against the
;; code. A :backlog lemma is banked here when its last name segment is
;; declared (theorem/lemma/def/instance/abbrev/structure) in a committed
;; ConstructionTargets/*.lean file that has no sorry/admit/axiom.
(defn- declared-in-targets [root]
  (let [{:keys [out]} (shell/sh "git" "grep" "-n" "-E"
                                "^[[:space:]]*(noncomputable[[:space:]]+)?(private[[:space:]]+|protected[[:space:]]+)?(theorem|lemma|def|instance|abbrev|structure)[[:space:]]+[^[:space:]:({]+"
                                "HEAD" "--" "ConstructionTargets/*.lean" :dir root)
        dirty (->> (:out (shell/sh "git" "grep" "-l" "-E" "(^|[^A-Za-z0-9_.])(sorry|admit)([^A-Za-z0-9_.]|$)|^[[:space:]]*axiom[[:space:]]"
                                   "HEAD" "--" "ConstructionTargets/*.lean" :dir root))
                   str/split-lines (map #(str/replace % #"^HEAD:" "")) set)]
    (reduce (fn [m line]
              (if-let [[_ f nm] (re-find #"^HEAD:([^:]+):\d+:.*?(?:theorem|lemma|def|instance|abbrev|structure)\s+([^\s:({]+)" line)]
                (if (dirty f) m (update m (last (str/split nm #"\.")) (fnil conj #{}) f))
                m))
            {} (str/split-lines out))))
(defn sync-banked [items]
  (let [decl (delay (declared-in-targets (:canonical-root data)))]
    (mapv #(if (and (= :lemma (:kind %)) (= :backlog (:state %)))
             ;; Qualified names (Mod.decl, ConstructionTargets.Mod.decl) must
             ;; be found in Mod.lean; an unqualified name must be declared in
             ;; exactly one file. A bare last-segment match banked
             ;; "normalization" from seven unrelated files.
             (let [segs (remove #{"ConstructionTargets"}
                                (str/split (str/trim (str (get-in % [:lemma :name]))) #"\."))
                   nm (last segs)
                   qual (when (< 1 (count segs)) (nth segs (- (count segs) 2)))
                   cands (when (re-matches #"[A-Za-z_][A-Za-z0-9_']*" (str nm)) (get @decl nm))
                   files (if qual
                           (filter (fn [f] (= (str qual ".lean") (last (str/split f #"/")))) cands)
                           (when (= 1 (count cands)) cands))]
               (if (seq files)
                 (-> % (assoc :state :banked)
                     (assoc-in [:lemma :banked-by] :declaration-found)
                     (assoc-in [:lemma :found-in] (vec (sort files))))
                 %))
             %)
          items)))

;; A row parked (:needs-owner) because it named a missing theorem is never
;; looked at again once someone else proves that theorem. On 2026-10-11
;; codex-71 found t99j01-path-component-cover-package-1 still parked on
;; IsCoveringMap.restrictPathComponent, which was banked hours earlier
;; (ConstructionTargets/RestrictPathComponent.lean). So: a :needs-owner row
;; named in a banked lemma's :reported-by goes back to :open with its stop
;; and fail counts reset.
(defn reopen-for-banked [items]
  (let [banked-reporters (set (mapcat #(get-in % [:lemma :reported-by])
                                      (filter #(and (= :lemma (:kind %)) (= :banked (:state %))) items)))]
    (mapv #(if (and (#{:needs-owner :stopped} (:state %)) (banked-reporters (:id %))
                    (not= :strategy-checkpoint (:kind %)))
             ;; :blocked, so unblock-ready opens it only once its own
             ;; dependencies are satisfied
             (assoc % :state :blocked :stop-count 0 :fail-count 0
                    :owner-reopen "reopened: a lemma this row reported missing is now banked")
             %)
          items)))

(defn bank-lemmas
  "On a PASS for row id: bank the lemma it implements and any lemma whose
   author reported it proved in this row."
  [items id]
  (let [row (some #(when (= id (:id %)) %) items)
        ;; a stopped row did not prove the lemma it was elected for
        target (when-not (= :stopped (:state row)) (:implements-lemma row))
        commit (or (get-in row [:evidence :commit]) (last (get-in row [:evidence :commits])))]
    (reopen-for-banked
     (mapv #(if (and (= :lemma (:kind %)) (= :backlog (:state %))
                     (or (= target (:id %)) (= id (get-in % [:lemma :proved-in]))))
              (-> % (assoc :state :banked)
                  (assoc-in [:lemma :banked-by] id)
                  (cond-> commit (assoc-in [:lemma :banked-commit] commit)))
              %)
           items))))

(defn priorities
  "Backlog lemmas ranked for election: ready ones (every dependency banked or
   done) first, then by how many open registered problems they unblock
   (directly, or through any row or lemma that depends on them), then by how
   few backlog lemmas those problems still wait on."
  [items]
  (let [idx (into {} (map (juxt :id identity) items))
        dependents (reduce (fn [m i] (reduce #(update %1 %2 (fnil conj #{}) (:id i)) m (:depends-on i)))
                           {} (remove #(#{:superseded} (:state %)) items))
        upward (fn [lid] (loop [stack [lid] seen #{}]
                           (if-let [x (peek stack)]
                             (if (seen x) (recur (pop stack) seen)
                                 (recur (into (pop stack) (dependents x)) (conj seen x)))
                             seen)))
        open-reg (fn [row] (set (filter @registered-problems (open-problems row))))
        backlog (filter #(and (= :lemma (:kind %)) (= :backlog (:state %))) items)
        unblocks (into {} (for [l backlog]
                            [(:id l) (set (mapcat #(open-reg (idx %)) (upward (:id l))))]))
        remaining (frequencies (mapcat val unblocks))
        ready? (fn [l] (every? #(satisfied-states (:state (idx %))) (:depends-on l)))]
    (->> backlog
         (map (fn [l] {:id (:id l) :name (get-in l [:lemma :name])
                       :ready (ready? l)
                       :unblocks (vec (sort (unblocks (:id l))))
                       :waits-on (vec (remove #(satisfied-states (:state (idx %))) (:depends-on l)))
                       :closest (or (some->> (seq (unblocks (:id l))) (map remaining) (apply min)) 0)}))
         (sort-by (juxt #(if (:ready %) 0 1) #(- (count (:unblocks %))) :closest :name)))))

;; Theory areas across problems (Joe, 2026-10-10: "the DAG should still
;; collect lemmas and theoretical areas (ConstructionTargets) of maximum impact
;; across problems"). Per-problem readiness finishes nearly-closed problems;
;; this view ranks AREAS by how many open registered problems they serve,
;; across both ledgers and the unassigned HEAVY list. An area is a shared tag
;; from TOPOLOGY-ROUTES.md's problem tables (or a lemma's own :area); its
;; modules are the ConstructionTargets files its banked lemmas committed.
(def routes-file (io/file (or (:canonical-root data) (.getCanonicalPath (io/file here "../../.."))) "TOPOLOGY-ROUTES.md"))
(defn route-tags
  "tag -> #{problem}, from every TOPOLOGY-ROUTES.md table row with an id
   column and a shared-tags column."
  []
  (if-not (.exists routes-file)
    {}
    (reduce
     (fn [m line]
       (let [cells (map str/trim (str/split (str/replace line #"^\||\|$" "") #"\|"))]
         (if (and (<= 3 (count cells)) (re-matches #"t[a-z0-9]{2}[AJ]\d\d|tunk\d\d" (first cells)))
           (reduce (fn [m piece]
                     (if-let [tag (re-find #"[a-z0-9]+(?:-[a-z0-9]+)+"
                                           (-> piece (str/replace "`" "") (str/replace #"\(.*?\)" "")))]
                       (update m tag (fnil conj #{}) (first cells))
                       m))
                   m (str/split (last cells) #","))
           m)))
     {} (str/split-lines (slurp routes-file)))))
(defn- commit-modules [sha]
  (when sha
    (->> (str/split-lines (:out (shell/sh "git" "show" "--pretty=" "--name-only" sha
                                          :dir (:canonical-root data))))
         (filter #(re-matches #"ConstructionTargets/.*\.lean" %)) set)))
(defn areas
  "Areas ranked by open registered problems served, over both ledgers."
  []
  (let [ledgers (distinct [path (str here "/worklist.edn") (str here "/worklist2.edn") (str here "/worklist3.edn")])
        lemmas (for [l ledgers :when (.exists (io/file l))
                     i (:items (edn/read-string (slurp l))) :when (= :lemma (:kind i))]
                 (assoc i ::ledger (.getName (io/file l))))
        tags (route-tags)
        open? (memoize (fn [p] (boolean (and (@registered-problems p) (some-> (placeholder-count p) pos?)))))
        lemma-area (fn [l] (or (get-in l [:lemma :area]) (some-> (get-in l [:lemma :banked-commit]) commit-modules sort first) "untagged"))
        grouped (group-by lemma-area lemmas)
        names (sort (set (concat (keys tags) (keys grouped))))]
    (->> (for [a names
               :let [ls (grouped a)
                     probs (set (concat (tags a) (keep problem-of (mapcat #(cons (:consumer %) (:other-consumers %)) ls))))
                     open (sort (filter open? probs))]
               :when (or (seq open) (seq ls))]
           {:area a :open-problems (count open) :problems (vec open)
            :banked (count (filter #(= :banked (:state %)) ls))
            :backlog (count (filter #(= :backlog (:state %)) ls))
            :ledgers (vec (sort (set (map ::ledger ls))))
            :modules (vec (sort (set (mapcat #(commit-modules (get-in % [:lemma :banked-commit])) ls))))})
         (sort-by (juxt #(- (:open-problems %)) #(- (:backlog %)) :area)))))

(defn apply-result! []
  (let [id (keyword (nth *command-line-args* 2 ""))
        receipt-path (nth *command-line-args* 3 "")
        receipt (normalize-receipt (edn/read-string (slurp receipt-path)))
        item (by-id id)
        outcome (:outcome receipt)]
    (when-not item (throw (ex-info "unknown result row" {:id id})))
    ;; Completed evidence must satisfy the same gate rule as worklist_check.
    ;; Reject before writing; a failed exploratory command is not a passing
    ;; gate merely because a later command succeeded.
    (when (#{:done-unreviewed :stop :replan :pass} outcome)
      ;; Review receipts also use command-description strings: their PASS
      ;; finding attests reproduction, unlike implementation gate records.
      ;; Preserve those descriptions without inventing exit codes. Structured
      ;; review gate records still must match their expected exits.
      (when-let [failed (seq (filter #(and (not (and (= :pass outcome) (string? %)))
                                          (not= (get % :expected-exit 0) (:exit %)))
                                    (:commands receipt)))]
        (throw (ex-info "receipt records an unexpected gate exit"
                        {:id id :commands failed}))))
    (case outcome
      :go (when-not (and (get-in receipt [:fixture :path])
                         (get-in receipt [:fixture :sha256])
                         (seq (:commands receipt))
                         (vector? (get-in receipt [:implementation :scope])))
            (throw (ex-info "GO receipt lacks fixture or commands" {:receipt receipt})))
      :revise nil
      :stop (when-not (:reason receipt)
              (throw (ex-info "STOP receipt lacks reason" {:receipt receipt})))
      :replan (let [rs (:replacement-items receipt)
                    work (butlast rs)
                    checkpoint (last rs)
                    work-ids (set (map :id work))
                    reusable-valid?
                    (fn [row]
                      (or (not= :reusable-theorem (:kind row))
                          (<= 2 (count (set (conj (set (:other-consumers row))
                                                  (:consumer row)))))
                          (:bounded-exception row)))]
                (when-not (and (:seat receipt) (seq (:commands receipt)) (:finding receipt)
                               (vector? rs) (<= 2 (count rs) 6)
                               (every? reusable-valid? work)
                               (= :strategy-checkpoint (:kind checkpoint))
                               (= :strategy (:phase checkpoint))
                               (set/subset? work-ids (set (:depends-on checkpoint))))
                  (throw (ex-info "REPLAN needs 1-5 work rows followed by their next checkpoint"
                                  {:receipt receipt})))
                (when-let [v (seq (keep need-violation
                                        (remove #(= :documentation (:kind %)) work)))]
                  (throw (ex-info "REPLAN elects work that no open frozen problem needs"
                                  {:violations (vec v)}))))
      :done-unreviewed
      (do
        (doseq [k [:author :commit :fixture :changed-paths :commands :residual]]
          (when-not (get receipt k)
            (throw (ex-info "implementation receipt lacks field" {:field k}))))
        ;; Refuse a completion before it can replace the row's evidence when
        ;; any commit writes outside the row's permitted scope. Include prior
        ;; commits for a genuine repair, matching worklist_check's union rule.
        (let [prior (concat (get-in item [:evidence :commits])
                            (when-let [c (get-in item [:evidence :commit])] [c]))
              commits (vec (distinct (remove nil?
                                             (concat prior
                                                     [(:commit receipt)]
                                                     (:commits receipt)))))]
          (doseq [c commits]
            (when-not (commit-exists? (:canonical-root data) c)
              (throw (ex-info "implementation evidence commit absent"
                              {:id id :commit c}))))
          (let [paths (reduce into #{}
                              (map #(->> (shell/sh "git" "show" "--pretty="
                                                     "--name-only" %
                                                     :dir (:canonical-root data))
                                         :out str/split-lines
                                         (remove str/blank?) set)
                                   commits))]
            (when-let [p (seq (filter protected-path? paths))]
              (throw (ex-info "implementation commit touches the statement registry, which loop rows may not write"
                              {:id id :paths (vec p)})))
            (when-not (set/subset? paths (set (:scope item)))
              (throw (ex-info "implementation commit paths exceed scope"
                              {:id id :scope (set (:scope item))
                               :commit-paths paths :commits commits})))))
        (stash-fixture! (:fixture receipt)))
      :pass (doseq [k [:seat :commands :finding]]
              (when-not (get receipt k)
                (throw (ex-info "PASS receipt lacks field" {:field k}))))
      :fail (doseq [k [:seat :finding]]
              (when-not (get receipt k)
                (throw (ex-info "FAIL receipt lacks field" {:field k}))))
      (throw (ex-info "unknown receipt outcome" {:outcome outcome})))
    (case outcome
      ;; Only validate a prerequisite that is actually being INSERTED. When it
      ;; already exists, the :revise branch below takes the `existing` path and
      ;; merges nothing from the receipt's copy -- it only adds the dependency
      ;; edge -- so validating that copy rejects a receipt over fields the
      ;; ledger will never read. On 2026-09-08 a re-dispatched probe returned a
      ;; second revise naming a prerequisite that had meanwhile been inserted
      ;; and given its orientation; the receipt still carried the older copy
      ;; without one, and the loop stopped over a row that was already correct.
      :revise (when-not (by-id (:id (:prerequisite receipt)))
                (validate-inserted-row!
                 (normalize-prerequisite (by-id id) (:prerequisite receipt))
                 (set ids)))
      :replan (let [rows (:replacement-items receipt)
                    allowed-ids (into (set ids) (map :id rows))]
                (doseq [row rows]
                  (validate-inserted-row! row allowed-ids)))
      nil)
    (let [items (apply-completion-transition items receipt outcome)
          new-items
          (case outcome
            ;; A row's :id is the ledger's referential integrity: other rows
            ;; name it in :depends-on. (merge % implementation) let a GO
            ;; receipt supply its own :id and so RENAME the row -- on
            ;; 2026-09-06 codex-1's GO renamed
            ;; critical-value-sard-local-rank-normal-form-probe-2 to
            ;; ...-implementation-2 and reset :depends-on to [], which left
            ;; critical-value-sard-rank-source-induction-probe-2 pointing at an
            ;; id that no longer existed. worklist_check.bb correctly refused
            ;; the ledger ("unknown dependency") and the supervisor stopped for
            ;; 13 hours. The implementation payload supplies scope and
            ;; acceptance; it does not get to re-identify the row it is
            ;; implementing.
            :go (replace-item items id
                              #(-> (merge % (dissoc (:implementation receipt)
                                                    :id :depends-on))
                                   (assoc :state :open :phase :implementation)
                                   (assoc-in [:evidence :probe] receipt)
                                   (cond-> (:id (:implementation receipt))
                                     (assoc-in [:evidence :requested-id]
                                               (:id (:implementation receipt))))))
            ;; REVISE means "I need prerequisite P before I can continue".
            ;; If P is ALREADY in the ledger that is a dependency, not a new
            ;; row: on 2026-09-07 a probe asked for
            ;; :critical-value-sard-implicit-function-residual-flatness-1,
            ;; which was already :done with a passing review, and this inserted
            ;; a second identical copy at :open. worklist_check refused the
            ;; ledger ("duplicate item ids") and the supervisor stopped. The
            ;; :replan branch below has always checked for exactly this; this
            ;; branch did not.
            ;;
            ;; A prerequisite that is already :done blocks nothing, so the
            ;; asking row stays runnable; one still in flight blocks it as
            ;; before. Either way the dependency is recorded once.
            :revise (let [p (normalize-prerequisite (by-id id)
                                                     (:prerequisite receipt))]
                      (when-not (and (map? p) (:id p))
                        (throw (ex-info "REVISE lacks prerequisite item" {:receipt receipt})))
                      (let [existing (by-id (:id p))
                            note (fn [row]
                                   (-> row
                                       (update :depends-on
                                               #(vec (distinct (conj (or % []) (:id p)))))
                                       (assoc-in [:evidence :probe] receipt)))]
                        (if existing
                          (vec (mapv #(if (= id (:id %))
                                        (let [already-depends?
                                              (some #{(:id p)} (:depends-on %))]
                                          (cond-> (note %)
                                            (not= :done (:state existing))
                                            (assoc :state :blocked)
                                            ;; A second REVISE naming the same
                                            ;; already-reviewed prerequisite is
                                            ;; contradictory: that dependency
                                            ;; is satisfied and cannot make a
                                            ;; fresh run produce a different
                                            ;; result.  Leaving the requester
                                            ;; :open made the supervisor run
                                            ;; the same probe forever (row 83,
                                            ;; 2026-10-11) until its unchanged-
                                            ;; ledger guard stopped the loop.
                                            ;; Park the stale route for a
                                            ;; strategy/owner rewrite instead.
                                            (and (= :done (:state existing))
                                                 already-depends?)
                                            (assoc :state :needs-owner
                                                   :review-finding
                                                   (str "REVISE repeated satisfied prerequisite "
                                                        (:id p)
                                                        "; route must name a new prerequisite or be rewritten"))))
                                        %)
                                     items))
                          (vec (mapcat #(if (= id (:id %))
                                          [(merge {:state :open :phase :probe :depends-on []}
                                                  p)
                                           (-> % (assoc :state :blocked) note)]
                                          [%]) items)))))
            ;; A second :stop on the same row goes to the owner, not back to
            ;; review. On 2026-09-30 both loops spent four hours on one row
            ;; each (about 70 rounds): the author stopped because the repair it
            ;; needed was a ledger edit outside its scope, the reviewer failed
            ;; the stop because there was no commit to review, and :fail sent
            ;; the row back to the same author.
            ;; Foundation programs (Joe, 2026-10-11: "let's do both"): a row
            ;; with :program true is a multi-job construction. Its STOPs are
            ;; checkpoints of progress, not reasons to park: it continues
            ;; from its last commit up to program-max-stops jobs.
            :stop (replace-item items id #(let [n (inc (or (:stop-count %) 0))]
                                            (-> % (assoc :stop-count n)
                                                (assoc :state (if (<= (if (:program %) program-max-stops max-stops) n)
                                                                :needs-owner
                                                                :done-unreviewed))
                                                (assoc :evidence (assoc receipt
                                                                  :author (:seat receipt)
                                                                  :disposition :stop)))))
            ;; program rows are the owner's; a checkpoint cannot supersede them
            :replan (let [supersede (set (remove #(:program (by-id %)) (:supersede receipt)))
                          replacement-ids (map :id (:replacement-items receipt))
                          conflicts (keep by-id replacement-ids)
                          _ (when (some #(not= :superseded (:state %)) conflicts)
                              (throw (ex-info "replacement id already exists"
                                              {:ids (map :id conflicts)})))
                          replacement-id-set (set replacement-ids)
                          prepared (->> items
                                        (remove #(replacement-id-set (:id %)))
                                        (mapv #(if (supersede (:id %))
                                                 (assoc % :state :superseded)
                                                 %)))
                          replacements (mapv #(-> %
                                                    ;; A strategy receipt may already name its
                                                    ;; checkpoint in :depends-on.  Append the
                                                    ;; completed checkpoint idempotently so the
                                                    ;; writer cannot create duplicate edges.
                                                    (update :depends-on
                                                            (fn [dependencies]
                                                              (vec (distinct
                                                                    (conj (or dependencies []) id)))))
                                                    (assoc :state :blocked))
                                              (:replacement-items receipt))]
                      (vec (mapcat #(if (= id (:id %))
                                      (into [(-> % (assoc :state :done-unreviewed)
                                                    (assoc :evidence (assoc receipt
                                                                      :author (:seat receipt)
                                                                      :disposition :replan)))]
                                            replacements)
                                      [%]) prepared)))
            ;; A REPAIRED row is completed more than once, and this used to
            ;; replace :evidence wholesale, so the repair's receipt discarded
            ;; the implementation's commit. worklist_check then compared one
            ;; commit's paths against the row's whole scope and the supervisor
            ;; stopped: on 2026-09-07
            ;; :critical-value-sard-projected-implicit-function-packaging-1
            ;; recorded only its repair b0686676 (.lean) against a two-path
            ;; scope, and the run halted at row 60 of 70 until a human recorded
            ;; f6654435 by hand.
            ;;
            ;; Accumulate instead. Prior commits carry forward into :commits,
            ;; which the checker unions against scope, so the ledger records
            ;; the row's whole history without anyone noticing in time. A row
            ;; completed once still carries :commit alone, which is what the
            ;; other rows use.
            :done-unreviewed
            (replace-item
             items id
             (fn [it]
               ;; History first, then the row's last recorded commit: the
               ;; union check does not care about order, but the ledger is read
               ;; by people and should run chronologically.
               (let [prior (concat (get-in it [:evidence :commits])
                                   (when-let [c (get-in it [:evidence :commit])] [c]))
                     all (vec (distinct (remove nil?
                                                (concat prior
                                                        (when-let [c (:commit receipt)] [c])
                                                        (:commits receipt)))))]
                 (-> it
                     (assoc :state :done-unreviewed)
                     (assoc :evidence (cond-> receipt
                                        (< 1 (count all)) (assoc :commits all)))))))
            :pass (replace-item items id #(-> %
                                                (assoc :state
                                                       (cond
                                                         (and (= :strategy-checkpoint (:kind %))
                                                              (= :stop (get-in % [:evidence :outcome])))
                                                         :needs-owner
                                                         ;; a reviewed program STOP continues
                                                         (and (:program %)
                                                              (= :stop (get-in % [:evidence :outcome])))
                                                         :open
                                                         ;; A PASS on a STOP says the stop was honest,
                                                         ;; not that the row delivered. As :done it
                                                         ;; unblocked dependents and banked the lemma it
                                                         ;; was meant to prove (2026-10-12: 190 rows, 8
                                                         ;; lemmas banked with no declaration anywhere;
                                                         ;; t00J07 waited on a hemisphere trivialization
                                                         ;; that was only ever a Prop). :stopped satisfies
                                                         ;; no dependency and banks nothing.
                                                         (= :stop (get-in % [:evidence :outcome]))
                                                         :stopped
                                                         :else :done))
                                                (cond-> (and (:program %) (= :stop (get-in % [:evidence :outcome])))
                                                  (-> (update :program-history (fnil conj [])
                                                              {:job (:stop-count %) :commit (get-in % [:evidence :commit])
                                                               :reason (get-in % [:evidence :reason])})
                                                      (assoc :continue-from (str "Continue this program from its last commit; earlier jobs: :program-history. Last stop: "
                                                                                 (get-in % [:evidence :reason])))))
                                                (assoc-in [:evidence :review] receipt)))
            :fail (if (= :strategy-checkpoint (:kind item))
                    (let [rejected-ids (set (map :id
                                                 (get-in item [:evidence :replacement-items])))]
                      (mapv #(cond
                               (= id (:id %))
                               (-> % (assoc :state :repair :phase :strategy)
                                     (assoc :review-finding (:finding receipt))
                                     (assoc-in [:evidence :review] receipt))

                               (rejected-ids (:id %))
                               (assoc % :state :superseded)

                               :else %)
                            items))
                    ;; Likewise a row whose review keeps failing: after
                    ;; max-fails failed reviews it waits for the owner.
                    (replace-item items id #(let [n (inc (or (:fail-count %) 0))]
                                              (-> % (assoc :fail-count n)
                                                  (assoc :state (if (<= max-fails n) :needs-owner :repair)
                                                         :phase :implementation)
                                                  (assoc :review-finding (:finding receipt))
                                                  (assoc-in [:evidence :review] receipt)))))
            (throw (ex-info "unknown receipt outcome" {:outcome outcome})))]
      (write-ledger! (assoc data :items
                            (unblock-ready
                             (cond-> (reconcile-implements-lemmas
                                      (upsert-lemmas new-items
                                                      (concat (:missing-theorems receipt) (:lemmas receipt))
                                                      id))
                               (= :pass outcome) (bank-lemmas id)
                               ;; after any PASS, also bank backlog lemmas
                               ;; whose declarations the commit just added
                               (= :pass outcome) (-> sync-banked reopen-for-banked)))))
      (println "applied" (name outcome) "to" (name id)))))

(defn repair-dependencies! []
  (let [id (keyword (nth *command-line-args* 2 ""))
        replacements (partition-all 2 (drop 3 *command-line-args*))
        item (by-id id)]
    (when-not item (throw (ex-info "unknown repair row" {:id id})))
    (when-not (and (seq replacements)
                   (every? #(= 2 (count %)) replacements))
      (throw (ex-info "dependency repair needs OLD NEW pairs" {:id id})))
    (let [pairs (mapv (fn [[old new]] [(keyword old) (keyword new)]) replacements)
          dependencies (set (:depends-on item))]
      (doseq [[old new] pairs]
        (when-not (dependencies old)
          (throw (ex-info "repair source dependency absent"
                          {:id id :dependency old})))
        (when-not (by-id new)
          (throw (ex-info "repair target dependency unknown"
                          {:id id :dependency new}))))
      (let [replacement-map (into {} pairs)
            repaired (update item :depends-on
                             #(mapv (fn [dependency]
                                      (get replacement-map dependency dependency)) %))]
        (write-ledger! (assoc data :items (replace-item items id (constantly repaired))))
        (println "repaired dependencies for" (name id))))))

(defn repair-fixture-hash! []
  (let [fixture-path (nth *command-line-args* 2 "")
        old-hash (nth *command-line-args* 3 "")
        new-hash (nth *command-line-args* 4 "")
        new-path (nth *command-line-args* 5 fixture-path)
        replacements (atom 0)
        repaired (walk/postwalk
                  (fn [x]
                    (if (and (map? x)
                             (= fixture-path (:path x))
                             (= old-hash (:sha256 x)))
                      (do (swap! replacements inc)
                          (assoc x :path new-path :sha256 new-hash))
                      x))
                  data)]
    (when-not (= 1 @replacements)
      (throw (ex-info "fixture hash repair needs exactly one matching fixture"
                      {:path fixture-path :old-hash old-hash
                       :matches @replacements})))
    (write-ledger! repaired)
    (println "repaired fixture evidence for" fixture-path "->" new-path)))

;; A refusal has to arrive as a sentence. build_step.bb's failures reach the
;; operator through topology-build-loop.sh's `die "invalid receipt ...: $out"`
;; and then through the supervisor's last_stop_reason, which keeps the FIRST
;; line -- and babashka's first line is "----- Error ----------". On
;; 2026-09-08 the real complaint ("representation comparison row lacks
;; required field", :field :orientation) sat twelve lines down inside a stack
;; trace, so the stop read "invalid receipt from <job>: ----- Error -----" and
;; three repair attempts were spent before anyone saw what was wrong.
(defn- die! [^Throwable t]
  (binding [*out* *err*]
    (let [data (ex-data t)]
      (println (str (.getMessage t)
                    (when (seq data) (str " " (pr-str data)))))))
  (System/exit 1))

(try
(case cmd
  "next-open" (println (or (some-> (selected) :id name) "NONE"))
  "unreviewed" (println (str/join " " (map (comp name :id)
                                               (filter #(= :done-unreviewed (:state %)) items))))
  "counts" (println (pr-str (frequencies (map :state items))))
  "row" (let [id (keyword (nth *command-line-args* 2 ""))]
          (if-let [i (by-id id)] (prn i) (System/exit 2)))
  "apply-result" (apply-result!)
  "repair-dependencies" (repair-dependencies!)
  "repair-fixture-hash" (repair-fixture-hash!)
  "replay" (replay!)
  ;; Closure readiness first (Joe, 2026-10-10: "lemma work should lead to
  ;; closures, it did historically"): per open registered problem, how many
  ;; lemmas it still waits on. A problem at 0 has a complete route, and its
  ;; closure adapter outranks every lemma (work-prompt.md rule 0/e).
  "priorities" (let [lem (filter #(= :lemma (:kind %)) items)
                     probs (sort (set (mapcat #(filter @registered-problems (open-problems %)) lem)))]
                 (doseq [p probs
                         :let [mine (filter #((set (map problem-of (cons (:consumer %) (:other-consumers %)))) p) lem)
                               waiting (count (filter #(= :backlog (:state %)) mine))
                               ;; A closure row that STOPped and passed review is
                               ;; :done, which reads like a closure. Name it, so a
                               ;; zero backlog is checked against what it said was
                               ;; missing (t96A07, 2026-10-11: its STOP named three
                               ;; packets that never entered the DAG).
                               stopped (->> items
                                            (filter #(and (= :stopped (:state %))
                                                          (= p (problem-of (:consumer %)))))
                                            (map :id) vec)]]
                   (prn {:problem p :placeholders (placeholder-count p)
                         :banked (count (filter #(= :banked (:state %)) mine))
                         :backlog waiting
                         :route (if (zero? waiting) :COMPLETE-elect-closure-adapter-now :open)
                         :closure-stopped stopped}))
                 ;; Within the ready lemmas, a lemma in a wider area ranks
                 ;; first: building it advances that area for every problem
                 ;; it serves, in either loop.
                 (let [as (areas)
                       impact (into {} (map (juxt :area :open-problems) as))
                       ls (into {} (map (juxt :id identity) (filter #(= :lemma (:kind %)) items)))]
                   (doseq [p (sort-by (juxt #(if (:ready %) 0 1) #(- (:area-open %)) #(- (count (:unblocks %))) :closest :name)
                                      (map #(let [a (get-in (ls (:id %)) [:lemma :area])]
                                              (assoc % :area (or a "UNTAGGED: give it an :area") :area-open (get impact a 0)))
                                           (priorities items)))]
                     (prn p))
                   (println ";; AREAS across both loops (open problems served, lemmas, modules):")
                   (doseq [a (take 25 as)] (prn a))))
  "areas" (doseq [a (areas)] (prn a))
  "sync-banked" (let [xs (reopen-for-banked (sync-banked items))
                      n (- (count (filter #(= :banked (:state %)) xs)) (count (filter #(= :banked (:state %)) items)))]
                  (write-ledger! (assoc data :items (unblock-ready xs)))
                  (println "sync-banked:" n "backlog lemmas found declared and banked"))
  ;; Owner edits to the lemma DAG go through the same upsert and validation as
  ;; receipts: `add-lemmas LEDGER FILE`, FILE holding a vector of entries.
  "add-lemmas" (let [entries (edn/read-string (slurp (nth *command-line-args* 2)))]
                 (write-ledger! (assoc data :items
                                       (unblock-ready
                                        (let [xs (upsert-lemmas items (map #(dissoc % :row) entries) :owner)
                                              ;; an entry carrying the :row that proved it
                                              ;; is linked to it (banked on its PASS), and banked at
                                              ;; once if that row already passed
                                              proved (for [{:keys [name row status]} entries
                                                           :when (and row (= :proved (keyword (str/replace (str status) #"^:" ""))))
                                                           :let [r (by-id (keyword (str/replace (str row) #"^:" "")))]
                                                           :when r]
                                                       [(lemma-id name) r])
                                              xs (mapv #(if-let [r (some (fn [[l r]] (when (= l (:id %)) r)) proved)]
                                                          (if (= :backlog (:state %)) (assoc-in % [:lemma :proved-in] (:id r)) %)
                                                          %) xs)]
                                          (reduce bank-lemmas xs (distinct (map :id (filter #(= :done (:state %)) (map second proved)))))))))
                 (println "lemma DAG:" (count (filter #(= :lemma (:kind %)) (:items (edn/read-string (slurp path))))) "nodes"))
  (do (binding [*out* *err*]
        (println "usage: build_step.bb next-open|unreviewed|counts|row|apply-result|repair-dependencies|repair-fixture-hash|replay [ledger] [args...]"))
      (System/exit 2)))
(catch clojure.lang.ExceptionInfo t (die! t)))
