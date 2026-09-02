#!/usr/bin/env bb
(require '[clojure.edn :as edn]
         '[clojure.string :as str]
         '[clojure.java.shell :as shell]
         '[clojure.pprint :as pprint]
         '[clojure.java.io :as io])

(def here (.getParent (.getAbsoluteFile (java.io.File. *file*))))
(def cmd (first *command-line-args*))
(def path (or (second *command-line-args*) (str here "/worklist.edn")))
(def data (edn/read-string (slurp path)))
(def items (:items data))
(def by-id (into {} (map (juxt :id identity) items)))
(def priority {:uptake 0 :final-adapter 1 :representation-comparison 2
               :reusable-theorem 3 :consumer-closure 4 :documentation 5})
(defn eligible? [i]
  (and (#{:open :repair} (:state i))
       (every? #(= :done (:state (by-id %))) (:depends-on i))))
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
                    (every? (fn [d] (= :done (:state (idx d)))) (:depends-on %)))
             (assoc % :state :open)
             %) xs)))
(defn apply-result! []
  (let [id (keyword (nth *command-line-args* 2 ""))
        receipt-path (nth *command-line-args* 3 "")
        receipt (edn/read-string (slurp receipt-path))
        item (by-id id)
        outcome (:outcome receipt)]
    (when-not item (throw (ex-info "unknown result row" {:id id})))
    (case outcome
      :go (when-not (and (get-in receipt [:fixture :path])
                         (get-in receipt [:fixture :sha256])
                         (seq (:commands receipt)))
            (throw (ex-info "GO receipt lacks fixture or commands" {:receipt receipt})))
      :revise nil
      :stop (when-not (:reason receipt)
              (throw (ex-info "STOP receipt lacks reason" {:receipt receipt})))
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
    (let [new-items
          (case outcome
            :go (replace-item items id #(-> % (assoc :state :open :phase :implementation)
                                                   (assoc-in [:evidence :probe] receipt)))
            :revise (let [p (:prerequisite receipt)]
                      (when-not (and (map? p) (:id p))
                        (throw (ex-info "REVISE lacks prerequisite item" {:receipt receipt})))
                      (vec (mapcat #(if (= id (:id %))
                                      [(merge {:state :open :phase :probe :depends-on []}
                                              p)
                                       (-> % (assoc :state :blocked)
                                             (update :depends-on (fnil conj []) (:id p))
                                             (assoc-in [:evidence :probe] receipt))]
                                      [%]) items)))
            :stop (replace-item items id #(-> % (assoc :state :needs-owner)
                                                 (assoc-in [:evidence :probe] receipt)))
            :done-unreviewed (replace-item items id #(-> % (assoc :state :done-unreviewed)
                                                            (assoc :evidence receipt)))
            :pass (replace-item items id #(-> % (assoc :state :done)
                                                (assoc-in [:evidence :review] receipt)))
            :fail (replace-item items id #(-> % (assoc :state :repair :phase :implementation)
                                                (assoc :review-finding (:finding receipt))
                                                (assoc-in [:evidence :review] receipt)))
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
