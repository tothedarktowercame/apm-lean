#!/usr/bin/env bb
;; Initialise proof state for APM prelim problems.
;;
;; Reads manifest.edn and .tex files, creates ProofState EDN files
;; compatible with futon3c's proof peripheral backend.
;;
;; Usage:
;;   bb init-proof-state.bb t01A01              # single problem
;;   bb init-proof-state.bb --canary            # four canary problems
;;   bb init-proof-state.bb --all               # all 489 problems
;;
;; Output: futon3c/data/proof-state/apm-<id>.edn per problem

(require '[clojure.string :as str]
         '[clojure.java.io :as io]
         '[clojure.edn :as edn])

(def script-dir (.getParentFile (io/file *file*)))
(def futon3c-dir (io/file (System/getProperty "user.home") "code/futon3c"))
(def state-dir (io/file futon3c-dir "data" "proof-state"))
(def canary-ids ["t01A01" "a96A03" "b03J02" "m96A04"])

;; --- Manifest loading ---

(defn load-manifest []
  (let [f (io/file script-dir "manifest.edn")]
    (edn/read-string (slurp f))))

(defn find-entry [manifest id]
  (first (filter #(= (:id %) id) manifest)))

;; --- Sub-part DAG construction ---
;; Per Excursion C, DERIVE decision 2:
;; - Each sub-part becomes a ledger item
;; - Sequential sub-parts get chain dependencies (b depends on a)
;; - A root item depends on all leaf sub-parts

(defn make-ledger-items
  "Create ledger items with DAG for a problem. If sub-parts exist,
   creates one item per part plus a root. Otherwise, creates a single
   root item for the whole problem."
  [problem-id subparts]
  (if (and subparts (seq subparts))
    (let [part-ids (mapv (fn [sp]
                           (str "part-" (second (re-find #"\((\w+)\)" (:label sp)))))
                         subparts)
          ;; Chain dependencies: part-b depends on part-a, etc.
          part-items (vec (map-indexed
                           (fn [i sp]
                             (let [pid (nth part-ids i)
                                   deps (if (pos? i)
                                          #{(nth part-ids (dec i))}
                                          #{})]
                               {:item/id pid
                                :item/label (str (:label sp) " " (subs (:body sp) 0 (min 60 (count (:body sp)))))
                                :item/status :open
                                :item/depends-on deps
                                :item/unlocks (if (< i (dec (count subparts)))
                                                #{(nth part-ids (inc i))}
                                                #{"root"})
                                :item/evidence-type :analytical}))
                           subparts))
          ;; Root depends on all parts (or just the last in a chain)
          root {:item/id "root"
                :item/label (str "Complete proof of " problem-id)
                :item/status :open
                :item/depends-on #{(last part-ids)}
                :item/unlocks #{}
                :item/evidence-type :analytical}]
      ;; Fix: root unlocks nothing, last part unlocks root
      (let [items (conj part-items root)]
        (into {} (map (fn [item] [(:item/id item) item]) items))))
    ;; No sub-parts: single root item
    {"root" {:item/id "root"
             :item/label (str "Prove " problem-id)
             :item/status :open
             :item/depends-on #{}
             :item/unlocks #{}
             :item/evidence-type :analytical}}))

;; --- SHA-256 ---

(defn sha256 [s]
  (let [md (java.security.MessageDigest/getInstance "SHA-256")
        bytes (.digest md (.getBytes s "UTF-8"))]
    (apply str (map #(format "%02x" %) bytes))))

;; --- ProofState creation ---

(defn make-proof-state
  "Create a ProofState EDN map for one problem."
  [entry]
  (let [problem-id (str "apm-" (:id entry))
        tex-file (io/file script-dir (:filename entry))
        raw-latex (slurp tex-file)
        now (str (java.time.Instant/now))
        statement raw-latex
        ledger (make-ledger-items (:id entry) (:subparts entry))]
    {:proof/problem-id problem-id
     :proof/version 0
     :proof/canonical {:statement statement
                       :closure-criterion "All parts proved analytically"
                       :statement-hash (sha256 statement)
                       :version-history [{:version 0
                                          :statement statement
                                          :hash (sha256 statement)
                                          :changed-at now
                                          :reason "Initial load from APM archive"}]}
     :proof/ledger ledger
     :proof/cycles []
     :proof/failed-routes []
     :proof/updated-at now
     ;; Per DERIVE decision 3: skip FALSIFY for APM
     :proof/current-mode :CONSTRUCT
     :proof/falsify-completed? true
     :proof/tryharder-log []
     :proof/active-license nil}))

;; --- Main ---

(let [args *command-line-args*
      manifest (load-manifest)
      ids (cond
            (some #{"--canary"} args) canary-ids
            (some #{"--all"} args) (mapv :id manifest)
            :else (filter #(not (str/starts-with? % "--")) args))]

  (.mkdirs state-dir)

  (doseq [id ids]
    (let [entry (find-entry manifest id)]
      (if entry
        (let [state (make-proof-state entry)
              problem-id (:proof/problem-id state)
              out-file (io/file state-dir (str problem-id ".edn"))]
          (spit out-file (with-out-str (clojure.pprint/pprint state)))
          (let [n-items (count (:proof/ledger state))
                subparts (:subpart-count entry)]
            (println (str "  " problem-id ": " n-items " ledger items"
                          (when (pos? subparts)
                            (str " (" subparts " sub-parts + root)"))
                          " → " (.getPath out-file)))))
        (println (str "  SKIP " id ": not found in manifest")))))

  (println (str "\n" (count ids) " proof states written to " (.getPath state-dir))))
