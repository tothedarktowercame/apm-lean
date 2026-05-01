# Proof Outline: a92J02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Given fₙ → f in measure on a finite-measure space, extract a subsequence converging to f almost everywhere."
 :terms [{:name "convergence in measure"
          :meaning "For every ε>0 the measure of {|fₙ-f|>ε} tends to zero"
          :needed-because "Defines the hypothesis and produces small-measure exceptional sets."}
         {:name "diagonal subsequence"
          :meaning "Choose n_k so that m{|f_{n_k}-f|>2^{-k}} ≤ 2^{-k}"
          :needed-because "Ensures the exceptional sets have a summable measure, enabling Borel–Cantelli."}
         {:name "Borel–Cantelli"
          :meaning "If ∑ m(E_k) < ∞ then almost every point belongs to only finitely many E_k"
          :needed-because "Converts the summable-measure exceptional sets into almost-everywhere convergence."}]
 :strategy [{:id :s1
             :formal-dependency "Convergence-in-measure hypothesis"
             :informal-dependency "Stage 1 construction of the subsequence"
             :why-this-now "Gives the `E_k` with rapidly shrinking measure."
             :lean-target "exists_fast_subseq"
             :mathlib-status "Standard diagonal extraction; relies on the convergence-in-measure definition."}
            {:id :s2
             :formal-dependency "Borel–Cantelli lemma for measurable sets"
             :informal-dependency "Stage 1 step turning ∑ μ(E_k)<∞ into an almost-everywhere statement"
             :why-this-now "Yields the pointwise limit along the chosen subsequence."
             :lean-target "ae_of_summable_measure"
             :mathlib-status "Mathlib already has a Borel–Cantelli lemma."}
            {:id :s3
             :formal-dependency "Measurability of {|f_{n_k}-f|>ε}"
             :informal-dependency "Stage 1 concluding argument that the subsequence converges a.e."
             :why-this-now "Completes the a.e. convergence proof."
             :lean-target "subseq_converges_ae"
             :mathlib-status "Should follow from existing `MeasureTheory` APIs once the previous steps are encoded."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a92J02'
  :frame-id 'apm-v2-a92J02-1775002223303'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the diagonal/Borel–Cantelli argument showing convergence in measure ⇒ a.e. convergence along a subsequence."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured the diagonal subsequence, summable-measure, and Borel–Cantelli dependencies in proof-plan.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Lean proof blocked: Mathlib has no `ConvergenceInMeasure` predicate (see `rg -n \"ConvergenceInMeasure\"`)."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  Convergence in measure only says the *measure* of the bad set is small, and the bad set itself depends on the tolerance. If you try to argue pointwise, you quickly run into the moving target “for every ε there exists an N.” The fix is to freeze the tolerances (εₖ = 2⁻ᵏ), diagonalize, and then invoke Borel–Cantelli.

***Key insight.***  For each k, pick nₖ so large that μ({|f_{nₖ}-f| > 2⁻ᵏ}) ≤ 2⁻ᵏ; this is possible because fₙ → f in measure. The sets Eₖ := {|f_{nₖ}-f| > 2⁻ᵏ} then have summable measures, so almost every point eventually avoids all of them.

***Complete proof.***  Define εₖ = 2⁻ᵏ and choose a strictly increasing sequence (nₖ) with μ(Eₖ) ≤ 2⁻ᵏ, where Eₖ = {|f_{nₖ}-f| > εₖ}. The geometric series shows ∑ μ(Eₖ) < ∞, so by Borel–Cantelli we have μ(limsup Eₖ) = 0. Hence for almost every x there exists K such that x ∉ Eₖ for k ≥ K, i.e. |f_{nₖ}(x) - f(x)| ≤ 2⁻ᵏ for k ≥ K. Therefore f_{nₖ}(x) → f(x) for almost every x.

***What connects.***  This is the canonical “subsequence + Borel–Cantelli” trick that also proves convergence in probability ⇒ almost sure convergence along a subsequence, shows that bounded L¹ sequences admit almost-everywhere convergent subsequences, etc.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Diagonal subsequence.*  Uses the convergence-in-measure hypothesis to choose (nₖ) with tiny exceptional sets.
- *Summable measures.*  Geometric bound ∑ 2⁻ᵏ < ∞.
- *Borel–Cantelli.*  Turns ∑ μ(Eₖ) < ∞ into “almost every x lies in only finitely many Eₖ,” giving the pointwise limit.

**Stage 3 — LEAN FORMALIZATION**

- *Target.*  `convergenceInMeasure.subseq_tendsto_ae` from `formal-alignment.edn`.
- *Status — blocked.*  Mathlib currently lacks a predicate for “convergence in measure”: `rg -n "ConvergenceInMeasure" -g"*.lean"` in `/home/joe/code/apm-lean` returns no hits. Without that definition, we cannot even state the theorem in Lean. The missing pieces are (a) a formal definition of convergence in measure and basic lemmas about it, and (b) the diagonally chosen subsequence tying into the existing Borel–Cantelli lemma. Until those APIs exist, Stage 3 remains open.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once convergence-in-measure is encoded, the Lean proof should line up perfectly with Stage 1: build the (nₖ), apply the existing Borel–Cantelli lemma (`MeasureTheory.BorelCantelli`), and unwrap the definitions to conclude almost-everywhere convergence of the subsequence.
