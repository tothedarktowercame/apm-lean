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

(deftest review-command-descriptions-are-not-exit-records
  (doseq [outcome [:pass :done-unreviewed :stop :replan]]
    (let [ledger (java.io.File/createTempFile "gate-ledger" ".edn")
          receipt (java.io.File/createTempFile "gate-receipt" ".edn")
          original (slurp (io/file here "fixtures/transition-ledger.edn"))
          fixture (if (= outcome :done-unreviewed) "done" (name outcome))
          base (edn/read-string (slurp (io/file here "fixtures" (str fixture "-receipt.edn"))))]
      (try
        (spit ledger
              (if (= outcome :pass)
                (let [w (edn/read-string original)
                      implementation (edn/read-string
                                      (slurp (io/file here "fixtures/done-receipt.edn")))]
                  (pr-str (-> w
                              (assoc-in [:items 0 :state] :done-unreviewed)
                              (assoc-in [:items 0 :evidence] implementation))))
                original))
        (spit receipt (pr-str (assoc base :commands ["lake env lean /tmp/Fixture.lean"])))
        (let [result (sh/sh "bb" (str here "/build_step.bb") "apply-result"
                            (str ledger) "edge" (str receipt))]
          (is (= (if (= outcome :pass) 0 1) (:exit result)))
          (if (= outcome :pass)
            (is (= ["lake env lean /tmp/Fixture.lean"]
                   (get-in (edn/read-string (slurp ledger))
                           [:items 0 :evidence :review :commands])))
            (is (= original (slurp ledger)))))
        (finally (.delete ledger) (.delete receipt))))))

(deftest corrected-diagnostics-remain-history-not-gates
  (let [ledger (java.io.File/createTempFile "gate-ledger" ".edn")
        receipt (java.io.File/createTempFile "gate-receipt" ".edn")
        original (slurp (io/file here "fixtures/transition-ledger.edn"))
        failed {:cmd "lake env lean /tmp/Boundary.lean" :exit 1
                :stage "Initial diagnostic: corrected before successful compilation."}
        passed {:cmd "lake env lean /tmp/Boundary.lean" :exit 0 :stage :final}
        base {:outcome :stop :seat "test-author" :reason "bounded stop"}]
    (try
      (spit ledger original)
      (spit receipt (pr-str (assoc base :commands [failed passed])))
      (let [result (sh/sh "bb" (str here "/build_step.bb") "apply-result"
                          (str ledger) "edge" (str receipt))]
        (is (= 1 (:exit result)))
        (is (re-find #"unexpected gate exit" (:err result)))
        (is (= original (slurp ledger))))
      (spit receipt (pr-str (assoc base :commands [passed] :diagnostic-history [failed])))
      (is (zero? (:exit (sh/sh "bb" (str here "/build_step.bb") "apply-result"
                              (str ledger) "edge" (str receipt)))))
      (is (= [failed] (get-in (edn/read-string (slurp ledger))
                             [:items 0 :evidence :diagnostic-history])))
      (finally (.delete ledger) (.delete receipt)))))

(def transition-preserve
  {:sha256 nil :supporting-path "support.lean" :supporting-sha256 "support-sha"
   :placeholder-count 0 :commit "fixture-commit" :review-outcome :pass})

(defn transition-ledger [hash]
  (let [base (edn/read-string (slurp (io/file here "fixtures/transition-ledger.edn")))
        historical {:id :historical :kind :reusable-theorem :state :done
                    :phase :implementation :depends-on [] :consumer :consumer-a
                    :other-consumers [:consumer-b] :scope [] :acceptance {}
                    :evidence {:outcome :stop :author "author" :commands [{:cmd "gate" :exit 0}]
                               :fixture {:path "mutable.lean" :sha256 hash
                                         :supporting-path "support.lean"
                                         :supporting-sha256 "support-sha" :placeholder-count 0}
                               :commit "fixture-commit"
                               :review {:outcome :pass :seat "reviewer"}}}]
    (update base :items #(vec (cons historical %)))))

(defn completion-transition [artifact hash]
  {:row :historical :path [:evidence :fixture :path]
   :from "mutable.lean" :to (.getAbsolutePath artifact)
   :preserve (assoc transition-preserve :sha256 hash)})

(deftest completion-fixture-path-transition-is-atomic-and-typed
  (let [artifact (java.io.File/createTempFile "immutable-fixture" ".lean")
        hash (:out (sh/sh "sha256sum" (.getAbsolutePath artifact)))
        hash (first (.split hash "\\s+"))
        original (transition-ledger hash)
        base (edn/read-string (slurp (io/file here "fixtures/done-receipt.edn")))
        cases (concat
               [{:label :success}
                {:label :unknown-row :change #(assoc % :row :absent)}
                {:label :non-completed :ledger #(assoc-in % [:items 0 :state] :open)}
                {:label :wrong-from :change #(assoc % :from "wrong.lean")}
                {:label :absent-target :change #(assoc % :to "/tmp/absent-fixture-transition")}
                {:label :wrong-path :change #(assoc % :path [:scope])}]
               (for [field (keys transition-preserve)]
                 {:label (keyword (str "wrong-" (name field)))
                  :change #(assoc-in % [:preserve field] ::wrong)}))]
    (try
      (doseq [{:keys [label change ledger]} cases]
        (let [ledger-file (java.io.File/createTempFile "transition-ledger" ".edn")
              receipt-file (java.io.File/createTempFile "transition-receipt" ".edn")
              input ((or ledger identity) original)
              transition ((or change identity) (completion-transition artifact hash))]
          (try
            (spit ledger-file (pr-str input))
            (spit receipt-file (pr-str (assoc base :completion-transition transition)))
            (let [result (sh/sh "bb" (str here "/build_step.bb") "apply-result"
                                (.getAbsolutePath ledger-file) "edge"
                                (.getAbsolutePath receipt-file))]
              (if (= :success label)
                (let [written (edn/read-string (slurp ledger-file))]
                  (is (zero? (:exit result)))
                  (is (= (.getAbsolutePath artifact)
                         (get-in written [:items 0 :evidence :fixture :path])))
                  (is (= (dissoc (first (:items input)) :evidence)
                         (dissoc (first (:items written)) :evidence)))
                  (is (= (dissoc (get-in input [:items 0 :evidence]) :fixture)
                         (dissoc (get-in written [:items 0 :evidence]) :fixture))))
                (do (is (= 1 (:exit result)) (name label))
                    (is (= (pr-str input) (slurp ledger-file)) (name label)))))
            (finally (.delete ledger-file) (.delete receipt-file)))))
      (finally (.delete artifact)))))

(deftest completion-transition-rejects-hash-mismatch-and-is-optional
  (let [artifact (java.io.File/createTempFile "immutable-fixture" ".lean")
        altered (java.io.File/createTempFile "altered-fixture" ".lean")
        actual (first (.split (:out (sh/sh "sha256sum" (.getAbsolutePath artifact))) "\\s+"))
        _ (spit altered "different bytes")]
    (try
      (doseq [[label ledger transition]
              [[:target-hash (transition-ledger actual)
                (assoc (completion-transition artifact actual)
                       :to (.getAbsolutePath altered))]
               [:no-transition (transition-ledger actual) nil]]]
        (let [ledger-file (java.io.File/createTempFile "transition-ledger" ".edn")
              receipt-file (java.io.File/createTempFile "transition-receipt" ".edn")
              base (edn/read-string (slurp (io/file here "fixtures/done-receipt.edn")))]
          (try
            (spit ledger-file (pr-str ledger))
            (spit receipt-file (pr-str (cond-> base transition
                                          (assoc :completion-transition transition))))
            (let [result (sh/sh "bb" (str here "/build_step.bb") "apply-result"
                                (.getAbsolutePath ledger-file) "edge"
                                (.getAbsolutePath receipt-file))]
              (is (= (if (= label :no-transition) 0 1) (:exit result))))
            (finally (.delete ledger-file) (.delete receipt-file)))))
      (finally (.delete artifact) (.delete altered)))))

(let [{:keys [fail error]} (run-tests)]
  (System/exit (if (zero? (+ fail error)) 0 1)))
