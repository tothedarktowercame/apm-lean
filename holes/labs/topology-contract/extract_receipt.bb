#!/usr/bin/env bb
;; Read the receipt EDN FORM that follows PREFIX in RESULT, and emit it as one
;; canonical line.
;;
;; The protocol asks the agent for "exactly one unindented line", and the
;; extractor used to take it literally with awk. But a receipt embeds captured
;; command output, and on 2026-09-09 codex-6's receipt carried a literal newline
;; inside one :output string (a wrapped `sed | sha256sum` result). The line-based
;; read then returned a prefix ending mid-string, and build_step.bb died with
;; "EOF while reading string" -- stopping the loop at 259 of 268 rows on a
;; receipt whose content was entirely valid.
;;
;; A newline inside an EDN string is legal EDN. So read the FORM: take everything
;; after the prefix and let the reader find the end of the map. read-string stops
;; at the first complete form, so trailing agent chatter is ignored. Re-emitting
;; with pr-str escapes any embedded newline, so what lands on disk really is the
;; single line the rest of the pipeline expects.
(require '[clojure.string :as str] '[clojure.edn :as edn])
(let [[result prefix] *command-line-args*
      raw (slurp result)
      i (str/index-of raw prefix)]
  (when-not i
    (binding [*out* *err*] (println "receipt prefix not found")) (System/exit 1))
  (let [body (subs raw (+ i (count prefix)))]
    (try
      (println (pr-str (edn/read-string body)))
      (catch Exception e
        (binding [*out* *err*]
          (println (str "receipt is not readable EDN: " (.getMessage e))))
        (System/exit 1)))))
