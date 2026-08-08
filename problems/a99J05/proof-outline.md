# Proof Outline: a99J05

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Closer hop 1 (2026-08-08)

`apm_a99J05_summable_l1Norm_of_geometric_bound` now proves that the geometric
bound in the second conjunct makes the displayed `L¹` norms summable. The next
step is the Tonelli argument, visible inside Mathlib's implementation of
`MeasureTheory.integral_tsum`, which turns summability of the integrals into
almost-everywhere pointwise summability of the norms and hence convergence to
zero.

The first conjunct still needs a formal typewriter sequence of shrinking
indicator intervals visiting almost every point infinitely often. No solved
sibling packages that dyadic enumeration. The main theorem remains partial
with one `sorry`; its frozen statement is unchanged.

## Closer hop 2 (2026-08-08)

The second conjunct is now fully compiled.  The helper
`apm_a99J05_ae_tendsto_zero_of_summable_l1Norm` converts summability of the
real `L¹` norms to finiteness of the corresponding ENNReal series, swaps the
series and lower integral with `lintegral_tsum`, extracts pointwise finiteness
almost everywhere using `ae_lt_top'`, and concludes termwise convergence to
zero.  The existing geometric comparison supplies the summability premise.

The first conjunct remains open.  `a01A01` now supplies a compiled typewriter
stage, cell, integral formula, and vanishing-integral theorem, but its still-
partial development does not prove the cofinal pointwise cell-selection fact.
That fact is exactly what is required to refute pointwise convergence here.
Accordingly the bundle remains partial with one honest `sorry`, confined to
the counterexample existential; the frozen statement is unchanged.

## Imported Proof Plan

```clojure
{:goal "Produce an L^1 sequence with vanishing norms but no a.e. convergence, and prove that the stronger decay ∥f_n∥_1 ≤ 2^{-n} forces f_n(x)→0 a.e."
 :terms [{:name "moving indicator example"
          :meaning "Take f_n=χ_{I_n} for shrinking dyadic intervals that visit every point infinitely often."
          :needed-because "Gives the requested counterexample for part (a)."}
         {:name "Markov/Chebyshev inequality"
          :meaning "μ(|f_n|>ε) ≤ ε^{-1}∥f_n∥_1."
          :needed-because "Turns the L^1 decay into an estimate for the exceptional sets in part (b)."}
         {:name "Borel-Cantelli"
          :meaning "If ∑ μ(E_n)<∞ then almost every point belongs to only finitely many E_n."
          :needed-because "Shows that |f_n(x)|>ε happens only finitely many n, hence f_n(x)→0."}]
 :strategy [{:id :s1
             :formal-dependency "dyadic_interval_construction"
             :informal-dependency "Stage 1 example description"
             :why-this-now "Create the sequence with ∥f_n∥_1→0 but no a.e. convergence by cycling through dyadic intervals."
             :lean-target "example_sequence_no_ae_limit"
             :mathlib-status "Needs a concrete construction plus measure computations."}
            {:id :s2
             :formal-dependency "Chebyshev"
             :informal-dependency "Part (b) hypotheses"
             :why-this-now "Bound μ(|f_n|>ε) by 2^{-n}/ε using the L^1 control."
             :lean-target "measure_tail_bound"
             :mathlib-status "Chebyshev already in Mathlib."}
            {:id :s3
             :formal-dependency "Borel-Cantelli"
             :informal-dependency "Bound from :s2"
             :why-this-now "Apply Borel-Cantelli to deduce |f_n(x)|>ε only finitely often, hence f_n(x)→0."
             :lean-target "tendsto_zero_ae_from_summable"
             :mathlib-status "Borel-Cantelli exists for Lebesgue measure."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a99J05'
  :frame-id 'apm-v2-a99J05-1775005037257'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the counterexample and Borel–Cantelli argument in the reader-facing proof."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the dyadic-example → Chebyshev → Borel–Cantelli dependency chain in proof-plan.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean approach; blocked on formalizing the dyadic enumeration lemma and an `ae` convergence lemma combining Chebyshev with Borel–Cantelli."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  Mere decay of ‖f_n‖_1 need not force pointwise control: the norm sees only the “average size,” so a function can be huge on a tiny moving set. Part (a) exploits this loophole; the trap is assuming vanishing L¹ norm already gives almost-everywhere convergence. Part (b) adds a fast geometric decay. The challenge is to translate that analytic hypothesis into a measure-theoretic statement about where the sequence can stay large, and then rule out infinitely many “bad” visits at each point.

*Key insight.*  For (a), cycle through dyadic intervals whose lengths go to zero but which cover every point infinitely often; the indicator functions have ever smaller integrals but never settle down pointwise. For (b), combine Chebyshev/Markov with Borel–Cantelli. The inequality µ{|f_n|>ε} ≤ ε^{-1}‖f_n‖_1 makes the exceptional sets summable, and Borel–Cantelli then shows each point can belong to only finitely many of them, forcing f_n(x)→0.

*Complete proof.*
(a) Enumerate all dyadic subintervals of [0,1]. For each m≥0 and 0≤k<2^m, set
\[
I_{m,k}=[k/2^m,(k+1)/2^m).
\]
Each x∈[0,1) lies in exactly one I_{m,k} for every m. Now list the pairs (m,k) in any sequence (for definiteness, by increasing m and then k), and define
\[
f_n=χ_{I_{m_n,k_n}}.
\]
Then ‖f_n‖_1=|I_{m_n,k_n}|=2^{-m_n}→0 because m_n→∞ along the enumeration. However, every x∈[0,1) belongs to infinitely many of the intervals I_{m,k} (one for each m), hence f_n(x)=1 for infinitely many n and 0 otherwise, so the pointwise limit does not exist anywhere (except possibly at x=1 where all indicators vanish). Thus the sequence fails to converge almost everywhere even though the L¹ norms vanish.

(b) Fix ε>0 and consider the measurable sets E_{n,ε}={x∈[0,1]:|f_n(x)|>ε}. Chebyshev (Markov) gives
\[
μ(E_{n,ε}) ≤ ε^{-1}‖f_n‖_1 ≤ ε^{-1}2^{-n}.
\]
Therefore \(∑_{n} μ(E_{n,ε}) < ∞\). By the Borel–Cantelli lemma (for Lebesgue measure on [0,1]), almost every x belongs to only finitely many of the sets E_{n,ε}. Equivalently, for a.e. x we have |f_n(x)|>ε only finitely often, so |f_n(x)|→0. Since this holds for every rational ε>0, the same conclusion holds for all ε>0, proving f_n(x)→0 almost everywhere.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. *Dyadic-interval example* → constructs the sequence χ_{I_{m,k}} with ‖f_n‖_1→0 yet no a.e. convergence. (Lean target: `example_sequence_no_ae_limit`.)
2. *Chebyshev inequality* → µ{|f_n|>ε} ≤ ε^{-1}‖f_n‖_1. (Lean target: `measure_tail_bound`.)
3. *Borel–Cantelli lemma* → summable exceptional measures ⇒ |f_n(x)|>ε only finitely often, hence f_n(x)→0. (Lean target: `tendsto_zero_ae_from_summable`.)

**Stage 3 — LEAN FORMALIZATION**

Status: `Main.lean` currently imports Mathlib and the plan but contains no finished statements yet. Part (a) requires encoding the enumeration of dyadic intervals and showing their indicator functions sit in `L¹`. I have sketched this in `Scratch.lean`, but the bookkeeping lemma that every x lies in infinitely many enumerated intervals still needs to be formalized. Part (b) hinges on Chebyshev plus the Borel–Cantelli lemma. Mathlib has both ingredients (`MeasureTheory.measure_gt_mul_le_add` and `MeasureTheory.borelCantelli_zero`), but they are packaged for general measures. I still need to assemble them into a lemma of the form
```
lemma tendsto_zero_of_l1_geometric
```
that concludes `ae` convergence; wiring this up is the remaining blocker before running `lake build`.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal solution mirrors the Lean plan exactly: build the moving-indicator example for (a), then apply Chebyshev plus Borel–Cantelli for (b). Once the dyadic-interval enumeration and the “summable exceptional sets ⇒ ae convergence” lemma are formalized, the Lean code will match the prose line-for-line. EOF

## Closer hop 3

The second conjunct is fully compiled through Tonelli. For the first conjunct,
this hop ports the diagonal stage/position definitions, proves stage cofinality,
computes the exact integral of each moving cell, proves those integrals tend to
zero, and establishes integrability for the restricted measure. The remaining
gap is the floor-based cofinal cell-selection lemma. An orphaned historical
proof was tested, but its nonlinear `Nat.pair` estimate and obsolete
minimum/floor/division API calls do not compile in the current snapshot.
