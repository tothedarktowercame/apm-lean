# Proof Outline: a97A01

## Lean closure status

The file currently has one `sorry` in the main theorem. Five prerequisites now
compile:

- `apm_a97A01_abs_rademacher`: the frozen dyadic sign has absolute value one
  at every point.
- `apm_a97A01_rademacher_measurable`: the nested existential/interval
  definition is measurable.
- `apm_a97A01_integrable_mul_rademacher`: every frozen `L∞` pairing is
  integrable on the finite restricted interval.
- `apm_a97A01_norm_integral_mul_rademacher_le`: uniformly in `n`, pairing
  against an error `g` is bounded by `∫ |g|`.
- `apm_a97A01_rademacher_eq_one_of_mem_odd_cell`: an admissible odd-cell
  witness gives the positive sign after explicitly excluding `n = 1` and
  `t = 1`.

The remaining bridge begins with uniqueness/disjointness of the casted
half-open dyadic cells, which supplies the even-cell sign. It then requires
paired-interval cancellation and `L¹` approximation by dyadic step functions.
Once those are supplied, the compiled uniform `L¹` estimate closes the
approximation step directly.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that the Rademacher-like sequence f_n is weak-* null in L^∞: ∫ f f_n → 0 for every bounded measurable f."
 :terms [{:name "dyadic cancellation"
          :meaning "On each dyadic interval of length 2^{-n}, f_n alternates between ±1."
          :needed-because "Lets us pair subintervals to cancel the integral."
         }
         {:name "Lebesgue differentiation"
          :meaning "Average oscillation of f over small intervals tends to 0 for a.e. point."
          :needed-because "Controls the difference between f and its average on dyadic blocks."
         }
         {:name "L^∞ bound"
          :meaning "|∫_E f| ≤ ‖f‖_∞ m(E)."
          :needed-because "Bounds the part where differentiation fails or near the boundary."}]
 :strategy [{:id :s1
             :formal-dependency "Lebesgue differentiation theorem"
             :informal-dependency "Stage 1 small intervals"
             :why-this-now "Approximate f by its block averages on dyadic intervals."
             :lean-target "dyadic_average_convergence"
             :mathlib-status "LD theorem exists in Mathlib for a.e. points."}
            {:id :s2
             :formal-dependency "Pairing of adjacent dyadic intervals"
             :informal-dependency "Stage 1 dyadic cancellation"
             :why-this-now "Show that averages times f_n integrate to 0 on each block."
             :lean-target "paired_interval_cancellation"
             :mathlib-status "Simple algebraic identity; should be easy."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a97A01'
  :frame-id 'apm-v2-a97A01-1775003392734'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full informal solution (difficulty analysis, key insight, and detailed proof) plus contextual discussion in execute.md Stage 1."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured the lemma dependency narrative, Lean targets, and strategy links in Stage 2 of execute.md and proof-plan.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Began Lean planning but blocked pending a reusable Rademacher/dyadic infrastructure in Mathlib; documented the missing components in Stage 3."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The sequence \(f_n\) oscillates faster and faster; it’s tempting to think of it as converging weakly to 0, but you still have to justify the cancellation when \(f\) is only bounded and measurable. The trap is trying to use dominated convergence on \(f f_n\); there is no pointwise limit. Instead, approximate \(f\) by block averages where \(f_n\) sums to zero.

*Key insight.* Partition \([0,1]\) into dyadic intervals of length \(2^{-n}\). On each interval, \(f_n\) is \(+1\) on the left half and \(-1\) on the right half. Replace \(f\) by its average on each block: the integral of the average times \(f_n\) vanishes. The Lebesgue differentiation theorem says that, for large \(n\), the average is close to \(f\) on almost every point, so the remaining integral is small.

*Complete proof.* Let \(f∈L^∞([0,1])\) with essential supremum \(M\). For fixed \(n\), write the dyadic partition \(I_{k,n}=[(k-1)/2^n,k/2^n)\). Define the block-constant function
\[
A_n(t)=\frac{1}{|I_{k,n}|}∫_{I_{k,n}} f(s) ds \quad (t∈I_{k,n}).
\]
Then \(∫ f_n A_n = 0\) because \(A_n\) is constant on each \(I_{k,n}\) and the integral of \(f_n\) over each block splits into equal halves with opposite signs. Therefore
\[
∫ f f_n = ∫ (f-A_n) f_n.
\]
By Cauchy–Schwarz (here just Hölder with \(L^1\)-\(L^∞\)),
\[
|∫ (f-A_n) f_n| ≤ ‖f-A_n‖_1 · ‖f_n‖_∞ = ‖f-A_n‖_1,
\]
since \(|f_n|=1\) almost everywhere.

Lebesgue’s differentiation theorem says \(f(t)=\lim_n A_n(t)\) for almost every \(t\); hence \(‖f-A_n‖_1→0\). (One may justify this either directly from the theorem or using the density of step functions in \(L^1\).) Consequently \(∫ f f_n → 0\).

*What connects.* These \(f_n\) are the Rademacher functions. The argument above shows they converge to 0 in the weak-* topology of \(L^∞\); equivalently, they form an orthogonal system in \(L^2\). The “average-on-small-blocks then cancel” trick is the backbone of martingale convergence, Walsh/Fourier analysis, and the proof that step functions are dense in \(L^1\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Lebesgue differentiation:* block averages approximate \(f\) in \(L^1\). Needed to control \(‖f-A_n‖_1\). Lean target: `dyadic_average_convergence`.
- *Block cancellation:* integral of \(A_n f_n\) vanishes because \(f_n\) integrates to zero on each block. Lean target: `paired_interval_cancellation`.
- *Bound via Hölder:* \(|∫ (f-A_n) f_n| ≤ ‖f-A_n‖_1‖f_n‖_∞ = ‖f-A_n‖_1\). No new lemma needed; uses basic inequalities.

**Stage 3 — LEAN FORMALIZATION**

Plan: (1) formalize the dyadic partition and define block averages in `Main.lean`. (2) Use Mathlib’s Lebesgue differentiation theorem to show `‖f-A_n‖₁→0`. (3) Combine with the cancellation lemma to prove the limit. Stage 3 remains in progress; these lemmas are still to be encoded.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

After coding, note explicitly which version of Lebesgue differentiation was used and how the dyadic block averages were implemented so the written proof matches the formal one.
