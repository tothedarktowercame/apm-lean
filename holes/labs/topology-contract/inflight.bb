#!/usr/bin/env bb
(require '[clojure.edn :as edn])

(let [[op path & xs] *command-line-args*]
  (case op
    "write" (let [[row job seat token dispatched-at] xs
                  tmp (str path ".tmp")]
              (spit tmp (pr-str {:row row :job job :seat seat :token token
                                 :dispatched-at dispatched-at}))
              (.renameTo (java.io.File. tmp) (java.io.File. path)))
    "field" (let [[k] xs, m (edn/read-string (slurp path))]
              (println (or (get m (keyword k)) "")))
    "clear" (java.nio.file.Files/deleteIfExists
              (.toPath (java.io.File. path)))
    (throw (ex-info "usage: inflight.bb write|field|clear ..." {:op op}))))
