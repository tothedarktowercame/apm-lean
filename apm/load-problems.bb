#!/usr/bin/env bb
;; Problem loader for UT Austin math prelim archive.
;; Parses all .tex files in storage/apm/, extracts metadata and structure,
;; and writes manifest.edn.
;;
;; Usage: bb load-problems.bb
;;        bb load-problems.bb --canary   (just the four canary problems)

(require '[clojure.string :as str]
         '[clojure.java.io :as io]
         '[clojure.edn :as edn])

;; --- Filename parsing ---

(def subject-map
  {"a" :analysis
   "b" :algebra
   "m" :applied
   "t" :topology
   "aunk" :analysis    ;; unknown year/session
   "tunk" :topology})

(def session-map
  {"A" :spring
   "J" :fall})

(defn parse-filename
  "Parse a filename like a96A03.tex or tunk01.tex into metadata."
  [filename]
  (let [base (str/replace filename #"\.tex$" "")]
    (if-let [[_ prefix year-str session num-str]
             (re-matches #"([a-z])(\d{2})([AJ])(\d+)" base)]
      (let [year (+ 1900 (Integer/parseInt year-str))
            year (if (< year 1980) (+ year 100) year)]  ;; 00-03 → 2000-2003
        {:id base
         :filename filename
         :subject (subject-map prefix)
         :year year
         :session (session-map session)
         :number (Integer/parseInt num-str)})
      ;; Try "unk" pattern: aunk04.tex, tunk01.tex
      (if-let [[_ prefix num-str]
               (re-matches #"([a-z]+unk)(\d+)" base)]
        {:id base
         :filename filename
         :subject (subject-map prefix)
         :year nil
         :session nil
         :number (Integer/parseInt num-str)}
        ;; Unparseable
        {:id base
         :filename filename
         :subject nil
         :year nil
         :session nil
         :number nil
         :parse-error true}))))

;; --- LaTeX content parsing ---

(defn detect-subparts
  "Detect \\begin{alist} sub-parts, return vector of {:label :body} maps.
   If no alist, return nil."
  [text]
  (when (str/includes? text "\\begin{alist}")
    (let [;; Extract content between begin/end alist
          alist-match (re-find #"(?s)\\begin\{alist\}(.*?)\\end\{alist\}" text)
          alist-body (second alist-match)]
      (when alist-body
        (let [;; Split on \item, keeping content after each
              items (rest (str/split alist-body #"\\item\b"))
              labels (map char (range (int \a) (+ (int \a) (count items))))]
          (vec (map (fn [label body]
                      {:label (str "(" label ")")
                       :body (-> body
                                 (str/replace #"%-+\*?\s*" "")
                                 str/trim)})
                    labels items)))))))

(defn detect-inline-subparts
  "Detect inline sub-parts like 'Prove that (a) ... ; (b) ... ; and, (c) ...'."
  [text]
  (when (and (not (str/includes? text "\\begin{alist}"))
             (re-find #"\(a\)" text))
    (let [;; Find (a), (b), (c) etc. markers and split
          parts (re-seq #"\(([a-z])\)\s*([^(]*?)(?=\([a-z]\)|$)" text)]
      (when (>= (count parts) 2)
        (vec (map (fn [[_ label body]]
                    {:label (str "(" label ")")
                     :body (str/trim (str/replace body #"[;,]\s*(?:and,?\s*)?$" ""))})
                  parts))))))

(defn has-solution?
  "Check if the file contains a \\soln{} block."
  [text]
  (boolean (re-find #"\\soln\{" text)))

(defn has-hint?
  "Check if the file contains a hint."
  [text]
  (boolean (re-find #"(?i)\bhint[s]?\b" text)))

(defn parse-problem
  "Parse a single .tex file into a problem record."
  [file]
  (let [filename (.getName file)
        text (slurp file)
        meta (parse-filename filename)
        ;; Clean comment lines (%%% separators, %--- lines)
        clean-text (-> text
                       (str/replace #"(?m)^%.*$" "")
                       str/trim)
        subparts (or (detect-subparts text)
                     (detect-inline-subparts clean-text))]
    (merge meta
           {:raw-latex text
            :body clean-text
            :subparts subparts
            :subpart-count (count (or subparts []))
            :has-solution (has-solution? text)
            :has-hint (has-hint? text)})))

;; --- Canary set ---

(def canary-ids #{"t01A01" "a96A03" "b03J02" "m96A04"})

;; --- Main ---

(let [canary-only? (some #{"--canary"} *command-line-args*)
      apm-dir (io/file (str (System/getProperty "user.dir")))
      tex-files (->> (.listFiles apm-dir)
                     (filter #(str/ends-with? (.getName %) ".tex"))
                     (sort-by #(.getName %)))
      problems (map parse-problem tex-files)
      problems (if canary-only?
                 (filter #(canary-ids (:id %)) problems)
                 problems)
      ;; Summary stats
      by-subject (group-by :subject problems)
      with-subparts (filter #(pos? (:subpart-count %)) problems)
      parse-errors (filter :parse-error problems)
      ;; Manifest: metadata only (no raw-latex, for compactness)
      manifest (mapv #(dissoc % :raw-latex :body) problems)]

  ;; Print summary
  (println (str "Parsed " (count problems) " problems"
                (when canary-only? " (canary set only)")))
  (println)
  (println "By subject:")
  (doseq [[subj probs] (sort-by key by-subject)]
    (println (str "  " (name (or subj :unknown)) ": " (count probs))))
  (println)
  (println (str "With sub-parts: " (count with-subparts)))
  (println (str "With hints: " (count (filter :has-hint problems))))
  (println (str "With solutions: " (count (filter :has-solution problems))))
  (when (seq parse-errors)
    (println (str "\nParse errors: " (count parse-errors)))
    (doseq [p parse-errors]
      (println (str "  " (:filename p)))))

  ;; Show canaries
  (when canary-only?
    (println "\nCanary details:")
    (doseq [p (sort-by :id problems)]
      (println (str "\n--- " (:id p) " (" (name (:subject p)) ", "
                    (:year p) " " (when (:session p) (name (:session p)))
                    ", #" (:number p) ") ---"))
      (when (:subparts p)
        (println (str "  Sub-parts: " (count (:subparts p))))
        (doseq [sp (:subparts p)]
          (println (str "    " (:label sp) " "
                        (subs (:body sp) 0 (min 80 (count (:body sp)))) "..."))))
      (println (str "  Hint: " (:has-hint p)
                    "  Solution: " (:has-solution p)))))

  ;; Write manifest
  (let [manifest-file (io/file apm-dir "manifest.edn")]
    (spit manifest-file (with-out-str (clojure.pprint/pprint manifest)))
    (println (str "\nManifest written to " (.getPath manifest-file)))))
