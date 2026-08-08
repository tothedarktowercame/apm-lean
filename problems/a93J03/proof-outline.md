# Proof Outline: a93J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Use the size estimates on the exceptional sets Aₙ={x : |fₙ(x)|>n^{-2}} (with μ(Aₙ)≤2^{-n}) to prove that the series ∑|fₙ(x)| converges for almost every x∈ℝ."
 :terms [{:name "Borel–Cantelli / limsup control"
          :meaning "If ∑ μ(Aₙ)<∞, then μ(limsup Aₙ)=0"
          :needed-because "Points that lie in infinitely many Aₙ form a null set; outside this set the tail inequalities hold."}
         {:name "eventual bound"
          :meaning "Outside limsup we have |fₙ(x)|≤n^{-2} for all large n"
          :needed-because "The tail of ∑|fₙ(x)| can be compared to the convergent p-series ∑ n^{-2}."}
         {:name "p-series comparison"
          :meaning "∑ n^{-2} converges, so any nonnegative sequence dominated by it eventually is summable"
          :needed-because "It converts the eventual bound into absolute convergence."}]
 :strategy [{:id :s1
             :formal-dependency "MeasureTheory.ae_eventually_notMem plus Real.summable_one_div_nat_sq"
             :informal-dependency "Show μ(limsup Aₙ)=0, deduce the pointwise bounds outside limsup, and compare with the p-series"
             :why-this-now "This is exactly the textbook proof: measure-zero exceptional set + comparison test."
             :lean-target "Define Aₙ, apply `ae_eventually_notMem` using the geometric bound to kill limsup, and then combine the resulting `∀ᶠ n, |fₙ(x)|≤n^{-2}` with `Real.summable_one_div_nat_sq` to obtain `Summable (fun n => |fₙ(x)|)` a.e."
             :mathlib-status "Borel–Cantelli (`ae_eventually_notMem`) and the p-series lemma already exist; the remaining work is wiring them together."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :pending :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.A93J03.Apm_v2_a93J03_1774992011929'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a93J03'
  :frame-id 'apm-v2-a93J03-1774992011929'
  :summary "Created isolated proof frame workspace with the standard plan/changelog/Lean roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full Borel–Cantelli based solution: the sets Aₙ satisfy ∑μ(Aₙ)<∞, so outside their limsup we have |fₙ(x)|≤n^{-2} eventually, and comparison with the p-series forces absolute convergence."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage2-completed
  :summary "Documented the dependency plan: Borel–Cantelli (`ae_eventually_notMem`), the `Real.summable_one_div_nat_sq` lemma, and the eventual-bound comparison."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage3-progress
  :summary "Noted explicitly that no Lean code exists yet; the upcoming todo is to introduce the theorem and apply the `BorelCantelli` API."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

For each \(n\ge 1\) put \(A_n=\{x\in\mathbb R:\lvert f_n(x)\rvert>n^{-2}\}\).  Because \(\mu(A_n)\le 2^{-n}\), the sum \(\sum_n \mu(A_n)\) converges, so by the first Borel–Cantelli lemma the limsup set \(\limsup_n A_n\) has Lebesgue measure zero.  Thus for almost every \(x\) there exists \(N(x)\) such that \(x\notin A_n\) once \(n\ge N(x)\); equivalently, \(|f_n(x)|\le n^{-2}\) eventually.  Split the series \(\sum |f_n(x)|\) into its first \(N(x)\) terms (a finite sum) and the tail \(\sum_{n\ge N(x)}|f_n(x)|\), and bound the tail term-by-term by the convergent \(p\)-series \(\sum_{n\ge N(x)}n^{-2}\).  Therefore the whole series \(\sum |f_n(x)|\) converges for almost every \(x\), so \(\sum f_n(x)\) is absolutely convergent a.e.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

*Formal ingredients.*  (i) Borel–Cantelli / measure of limsup via `MeasureTheory.ae_eventually_notMem`.  (ii) The classical fact `Real.summable_one_div_nat_sq`.  (iii) The comparison test for nonnegative series.  

*Informal chain.*  Use the measure bounds to kill the limsup set; outside it we get pointwise tail bounds, and the comparison test with the \(p\)-series gives absolute convergence.  This mirrors the worked-solution blueprint.

**Stage 3 — LEAN FORMALIZATION**

Complete. The proof bounds the exceptional-set measure tsum by the shifted
ENNReal geometric series and applies `MeasureTheory.ae_eventually_notMem`.
For almost every point it then compares the absolute values eventually with
the shifted real p-series. The latter is constructed efficiently from
`Real.summable_nat_pow_inv` using `Nat.succ_injective`. Mathlib's first
Borel--Cantelli lemma is formulated for arbitrary sets via outer measures, so
the supplied measurability hypothesis is not needed by this proof.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean proof is written, it will follow the exact prose argument above (Borel–Cantelli + comparison).  At that point there should be no gaps between the formal and informal proofs; for now, the informal write-up is the authoritative reference.
