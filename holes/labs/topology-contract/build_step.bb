#!/usr/bin/env bb
(require '[clojure.edn :as edn]
         '[clojure.string :as str]
         '[clojure.set :as set]
         '[clojure.java.shell :as shell]
         '[clojure.pprint :as pprint]
         '[clojure.java.io :as io])

(def here (.getParent (.getAbsoluteFile (java.io.File. *file*))))
(def cmd (first *command-line-args*))
(def path (or (second *command-line-args*) (str here "/worklist.edn")))
(def data (edn/read-string (slurp path)))
(def items (:items data))
(def ids (map :id items))
(def by-id (into {} (map (juxt :id identity) items)))
(def priority {:uptake 0 :final-adapter 1 :representation-comparison 2
               :reusable-theorem 3 :consumer-closure 4 :documentation 5})
(defn owner-blocked? [idx dependency seen]
  (when-not (seen dependency)
    (let [item (idx dependency)]
      (or (= :needs-owner (:state item))
          (and (= :blocked (:state item))
               (some #(owner-blocked? idx % (conj seen dependency))
                     (:depends-on item)))))))
(defn dependency-ready? [dependent dependency]
  (let [state (:state (by-id dependency))]
    (or (= :done state)
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
(defn write-ledger! [x]
  (let [tmp (io/file (str path ".tmp"))]
    (spit tmp (with-out-str (pprint/pprint x)))
    (java.nio.file.Files/move (.toPath tmp) (.toPath (io/file path))
      (into-array java.nio.file.CopyOption
                  [java.nio.file.StandardCopyOption/REPLACE_EXISTING
                   java.nio.file.StandardCopyOption/ATOMIC_MOVE]))))
(defn replace-item [xs id f]
  (mapv #(if (= id (:id %)) (f %) %) xs))
(defn unblock-ready [xs]
  (let [idx (into {} (map (juxt :id identity) xs))]
    (mapv #(if (and (= :blocked (:state %))
                    (every? (fn [d]
                              (let [state (:state (idx d))]
                                (or (= :done state)
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
  (cond-> receipt
    (and (= :done-unreviewed (:outcome receipt))
         (nil? (:residual receipt))
         (some? (:next-consumer-residual receipt)))
    (assoc :residual (:next-consumer-residual receipt))))
(defn validate-inserted-row! [row]
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
(defn apply-result! []
  (let [id (keyword (nth *command-line-args* 2 ""))
        receipt-path (nth *command-line-args* 3 "")
        receipt (normalize-receipt (edn/read-string (slurp receipt-path)))
        item (by-id id)
        outcome (:outcome receipt)]
    (when-not item (throw (ex-info "unknown result row" {:id id})))
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
                                  {:receipt receipt}))))
      :done-unreviewed (doseq [k [:author :commit :fixture :changed-paths :commands :residual]]
                         (when-not (get receipt k)
                           (throw (ex-info "implementation receipt lacks field" {:field k}))))
      :pass (doseq [k [:seat :commands :finding]]
              (when-not (get receipt k)
                (throw (ex-info "PASS receipt lacks field" {:field k}))))
      :fail (doseq [k [:seat :finding]]
              (when-not (get receipt k)
                (throw (ex-info "FAIL receipt lacks field" {:field k}))))
      (throw (ex-info "unknown receipt outcome" {:outcome outcome})))
    (case outcome
      :revise (validate-inserted-row! (:prerequisite receipt))
      :replan (doseq [row (:replacement-items receipt)]
                (validate-inserted-row! row))
      nil)
    (let [new-items
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
            :revise (let [p (:prerequisite receipt)]
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
                                        (cond-> (note %)
                                          (not= :done (:state existing))
                                          (assoc :state :blocked))
                                        %)
                                     items))
                          (vec (mapcat #(if (= id (:id %))
                                          [(merge {:state :open :phase :probe :depends-on []}
                                                  p)
                                           (-> % (assoc :state :blocked) note)]
                                          [%]) items)))))
            :stop (replace-item items id #(-> % (assoc :state :done-unreviewed)
                                                 (assoc :evidence (assoc receipt
                                                                   :author (:seat receipt)
                                                                   :disposition :stop))))
            :replan (let [supersede (set (:supersede receipt))
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
                                                    (update :depends-on (fnil conj []) id)
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
                                                       (if (and (= :strategy-checkpoint (:kind %))
                                                                (= :stop (get-in % [:evidence :outcome])))
                                                         :needs-owner
                                                         :done))
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
                    (replace-item items id #(-> % (assoc :state :repair :phase :implementation)
                                                  (assoc :review-finding (:finding receipt))
                                                  (assoc-in [:evidence :review] receipt))))
            (throw (ex-info "unknown receipt outcome" {:outcome outcome})))]
      (write-ledger! (assoc data :items (unblock-ready new-items)))
      (println "applied" (name outcome) "to" (name id)))))

(case cmd
  "next-open" (println (or (some-> (selected) :id name) "NONE"))
  "unreviewed" (println (str/join " " (map (comp name :id)
                                               (filter #(= :done-unreviewed (:state %)) items))))
  "counts" (println (pr-str (frequencies (map :state items))))
  "row" (let [id (keyword (nth *command-line-args* 2 ""))]
          (if-let [i (by-id id)] (prn i) (System/exit 2)))
  "apply-result" (apply-result!)
  "replay" (replay!)
  (do (binding [*out* *err*]
        (println "usage: build_step.bb next-open|unreviewed|counts|row|apply-result|replay [ledger] [row-id] [receipt]"))
      (System/exit 2)))
