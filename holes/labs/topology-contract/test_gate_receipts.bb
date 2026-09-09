#!/usr/bin/env bb
(ns test-gate-receipts
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.test :refer [deftest is run-tests]]))

(def here (.getParent (io/file *file*)))
(deftest gate-receipts-are-checked-before-writing
  (doseq [outcome [:done-unreviewed :stop :replan :pass]]
    (let [ledger (java.io.File/createTempFile "gate-ledger" ".edn")
          receipt (java.io.File/createTempFile "gate-receipt" ".edn")
          fixture (if (= outcome :done-unreviewed) "done" (name outcome))
          original (slurp (io/file here "fixtures/transition-ledger.edn"))
          base (edn/read-string (slurp (io/file here "fixtures" (str fixture "-receipt.edn"))))]
      (try
        (spit ledger original)
        (spit receipt (pr-str (assoc base :commands [{:cmd "inspection query" :exit 1}])))
        (let [result (sh/sh "bb" (str here "/build_step.bb") "apply-result"
                            (str ledger) "edge" (str receipt))]
          (is (= 1 (:exit result)))
          (is (re-find #"unexpected gate exit" (:err result)))
          (is (= original (slurp ledger))))
        (finally (.delete ledger) (.delete receipt))))))

(deftest expected-exits-remain-accepted
  (doseq [command [{:cmd "successful gate" :exit 0}
                   {:cmd "negative search" :exit 1 :expected-exit 1}]]
    (let [ledger (java.io.File/createTempFile "gate-ledger" ".edn")
          receipt (java.io.File/createTempFile "gate-receipt" ".edn")]
      (try
        (spit ledger (slurp (io/file here "fixtures/transition-ledger.edn")))
        (spit receipt (pr-str {:outcome :stop :seat "test-author"
                              :reason "bounded stop" :commands [command]}))
        (is (zero? (:exit (sh/sh "bb" (str here "/build_step.bb") "apply-result"
                                (str ledger) "edge" (str receipt)))))
        (finally (.delete ledger) (.delete receipt))))))

(let [{:keys [fail error]} (run-tests)]
  (System/exit (if (zero? (+ fail error)) 0 1)))
