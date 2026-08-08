# Proof Outline: a96J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Closer hop 1 (2026-08-08)

The formal reduction now contains two compiled, sorry-free helpers.  The lemma
`apm_a96J03_integral_abs_sub_translate` proves exact invariance of the `L¹`
error under `x ↦ x - t` using `integral_sub_right_eq_self`.
`apm_a96J03_exists_compact_continuous_approx` specializes
`Integrable.exists_hasCompactSupport_integral_sub_le` to produce a continuous,
compactly supported, integrable approximant in the theorem's absolute-value
metric.

The remaining formal bridge is translation continuity for a continuous
compactly supported real function.  The intended dominated-convergence proof
needs a fixed compact thickening of `tsupport g` for all `t` near zero and an
## Closer hop 2

`apm_a96J03_compact_core` now proves the complete compact-support translation
limit. It applies `continuousOn_integral_of_compact_support` to the jointly
continuous family `(t,x) ↦ |g (x-t)-g x|`. Over `t ∈ closedBall 0 1`, every
integrand is supported in the compact Minkowski sum
`tsupport g + closedBall 0 1`. The sole remaining task is the final
epsilon/triangle combination with the hop-1 approximation and Haar-invariance
lemmas.

integrable indicator bound on that thickening.  Mathlib's convolution
continuity results do not directly state continuity of this translation norm.
Consequently the main theorem remains partial with one `sorry`; its statement
was not changed.

## Imported Proof Plan

```clojure
{:goal "Prove translation continuity in L¹: ‖f(·-t)-f‖₁ → 0 as t→0."
 :terms [{:name "density of nice functions"
          :meaning "Smooth compactly-supported or simple functions are dense in L¹(ℝ)."
          :needed-because "Approximate f by a function whose translates are easily controlled."}
         {:name "uniform continuity on compact support"
          :meaning "A continuous compactly-supported g satisfies sup_{|t|<η}|g(x-t)-g(x)|→0."
          :needed-because "Gives the L¹ control for the approximant g."}
         {:name "triangle inequality split"
          :meaning "‖f(·-t)-f‖₁ ≤ ‖f-g‖₁ + ‖g(·-t)-g‖₁ + ‖g-f‖₁."
          :needed-because "Combines approximation and uniform continuity."}]
 :strategy [{:id :s1
             :formal-dependency "Density of C_c(ℝ) in L¹"
             :informal-dependency "Stage 1 approximation"
             :why-this-now "Choose g with ‖f-g‖₁ < ε/3 so that the error term is small."
             :lean-target "l1_dense_in_compacts"
             :mathlib-status "Mathlib has density of simple/SW functions; likely already available."}
            {:id :s2
             :formal-dependency "Uniform continuity of compactly-supported g"
             :informal-dependency "Stage 1 triangle inequality"
             :why-this-now "Show ‖g(·-t)-g‖₁ < ε/3 for |t| small by bounding integration over compact support."
             :lean-target "translation_continuity_compact"
             :mathlib-status "Need lemma about L¹ norm continuity for C_c functions; should follow from dominated convergence."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a96J03'
  :frame-id 'apm-v2-a96J03-1775003261538'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the translation-continuity proof (approximation + triangle inequality)."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured lemma dependencies: density, compact-support translation, triangle split."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined Lean strategy; waiting to implement lemmas in Main.lean."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The statement looks like a routine application of dominated convergence, but the integrand is 
\(|f(x-t)-f(x)|\): the two terms live at different points, so no single dominator is obvious. The key is to use the density of “nice” functions in \(L^1\) and handle those first.

*Key insight.* Approximate \(f\) by a continuous compactly supported function \(g\) with \(\|f-g\|_1\) tiny. Translations behave well on such a \(g\) because uniform continuity on a compact support makes \(|g(x-t)-g(x)|\) uniformly small, so its integral is small. Finally split the integral for \(f\) using the triangle inequality.

*Complete proof.* Fix \(ε>0\). Choose \(g\in C_c(\mathbb R)\) with \(\|f-g\|_1<ε/3\) (density of \(C_c\) in \(L^1\)). Because \(g\) is uniformly continuous on its compact support, there exists \(δ>0\) such that \(|g(x-t)-g(x)|<ε/(3 M)\) whenever \(|t|<δ\), with \(M=m(\mathrm{supp}\,g)+1\). Moreover \(|g(x-t)-g(x)|\le 2\|g\|_\infty\) and the integrand vanishes outside a fixed compact set, so the dominated convergence theorem yields \(\int |g(x-t)-g(x)|<ε/3\) for \(|t|<δ\). For such \(t\),
\[
\int |f(x-t)-f(x)| \le \int |f(x-t)-g(x-t)| + \int |g(x-t)-g(x)| + \int |g(x)-f(x)| < ε.
\]
Therefore \(\|f(·-t)-f\|_1\to 0\) as \(t\to 0\).

*What connects.* Translation continuity in \(L^1\) underlies convolution approximation, Fourier analysis, and the proof that smooth mollifiers approximate integrable functions. The “approximate by \(C_c\) + triangle inequality” trick is widely used whenever a linear operator behaves nicely on a dense subspace.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Density lemma:* \(C_c(\mathbb R)\) (or simple functions) is dense in \(L^1\). Needed to pick \(g\) close to \(f\). Lean target: `l1_dense_in_compacts`.
- *Translation continuity for \(C_c\):* uniform continuity on compact support + dominated convergence. Lean target: `translation_continuity_compact`.
- *Triangle inequality split:* combine approximation error and the \(g\)-translation bound to control \(f\).

**Stage 3 — LEAN FORMALIZATION**

Plan: (1) reuse Mathlib’s density of `C(ℝ,ℝ)` with compact support in `L¹`. (2) Prove `translation_continuity_compact` using uniform continuity and `tendsto_integral_of_dominated_convergence`. (3) Deduce `translation_continuity_L1` via the triangle inequality. Stage 3 remains in progress; these lemmas still need to be written in `Main.lean`, though the required Mathlib facts already exist.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

After finishing the Lean proof, document exactly which density and dominated-convergence lemmas were used so the prose mirrors the formal certificates.
