# Proof Outline: a00J02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'a00J02'
 :frame-id 'apm-v2-a00J02-1774989750574'
 :goal "Show that the renormalized limit lim_{x->0+} x^{-1/2} f(x) exists for any absolutely continuous f with f(0)=0 and f' in L^2([0,1]), and compute that limit."
 :terms ['absolute-continuity 'Cauchy-Schwarz 'L2-shrinking-integral]
 :strategy ["Use absolute continuity to represent f(x) as \\int_0^x f'(t) dt."
            "Apply Cauchy-Schwarz to bound |f(x)| by x^{1/2}(\\int_0^x |f'|^2)^{1/2}."
            "Exploit that \\int_0^x |f'|^2 -> 0 as x -> 0 because f' \\in L^2, concluding the limit is 0."]
 :checkpoints [{:stage 1 :status :completed :notes "Clean argument recorded in execute.md."}
               {:stage 2 :status :completed :notes "Dependency table (FTC + Cauchy–Schwarz + shrinking integral) documented."}
               {:stage 3 :status :completed :notes "Added Lean lemma `sqrt_mul_tendsto_zero` capturing the final limit step and built the project."}
               {:stage 4 :status :completed :notes "Noted that no additional prose changes were needed."}]
 :lean {:module-root 'ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774989750574'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a00J02'
  :frame-id 'apm-v2-a00J02-1774989750574'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."}
 {:kind :stage1-completed
  :problem-id 'a00J02'
  :frame-id 'apm-v2-a00J02-1774989750574'
  :summary "Wrote the full Cauchy–Schwarz argument showing |f(x)| ≤ √x ||f'||_{L²(0,x)} and deduced the zero limit."}
 {:kind :stage2-completed
  :problem-id 'a00J02'
  :frame-id 'apm-v2-a00J02-1774989750574'
  :summary "Recorded dependencies (FTC, Cauchy–Schwarz, shrinking L² integrals) and Lean targets in execute.md."}
 {:kind :stage3-completed
  :problem-id 'a00J02'
  :frame-id 'apm-v2-a00J02-1774989750574'
  :summary "Formalized the auxiliary lemma `sqrt_mul_tendsto_zero` and checked the Lean build."}
 {:kind :stage4-completed
  :problem-id 'a00J02'
  :frame-id 'apm-v2-a00J02-1774989750574'
  :summary "Confirmed the formal work matches the prose; no extra adjustments needed."}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

Let \(f\) be absolutely continuous on \([0,1]\) with \(f(0)=0\) and \(f'\in L^{2}([0,1])\).
Absolute continuity gives \(f(x)=\int_{0}^{x}f'(t)\,dt\) for every \(x\in[0,1]\).
Fix \(x\in(0,1]\).  Applying the Cauchy–Schwarz inequality to the functions
\(f'\cdot \mathbf{1}_{[0,x]}\) and \(\mathbf{1}_{[0,x]}\) yields
\[
|f(x)| = \left|\int_{0}^{x} f'(t)\,dt\right|
 \le \left(\int_{0}^{x} |f'(t)|^{2}\,dt\right)^{1/2}
      \left(\int_{0}^{x} 1^{2}\,dt\right)^{1/2}
 = x^{1/2} \left(\int_{0}^{x} |f'(t)|^{2}\,dt\right)^{1/2}.
\]
Divide by \(x^{1/2}\) to obtain
\[
0 \le \frac{|f(x)|}{x^{1/2}} \le \left(\int_{0}^{x} |f'(t)|^{2}\,dt\right)^{1/2}.
\tag{1}
\]
Because \(f'\in L^{2}([0,1])\), the map \(x\mapsto \int_{0}^{x}|f'(t)|^{2}\,dt\) is continuous,
nondecreasing, and tends to \(0\) as \(x\to 0^{+}\).
Taking the limit \(x\to 0^{+}\) in (1) forces
\[
\lim_{x\to 0^{+}} x^{-1/2} f(x) = 0.
\]
Thus the limit exists and equals \(0\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| Label | Statement / role | Dependencies | Why it's used now | Intended Lean target / search terms |
|-------|------------------|--------------|-------------------|--------------------------------------|
| L1 | \(f(x)=\int_{0}^{x} f'(t) dt\) for absolutely continuous \(f\) with \(f(0)=0\) | absolute continuity | expresses \(f(x)\) as an integral to which we can apply inequalities | `FundamentalTheoremCalculus`, `intervalIntegral` |
| L2 | Cauchy–Schwarz: \(|\int gh| \le \|g\|_2 \|h\|_2\) | inner-product structure on \(L^2\) | bounds \(f(x)\) by \(x^{1/2}\|f'\|_{L^{2}(0,x)}\) | `MeasureTheory.cauchySchwarz`, `Real.inner` |
| L3 | If \(g\in L^2\) then \(\int_{0}^{x} |g|^{2} \to 0\) as \(x\to 0^{+}\) | absolute continuity of the integral | converts the Cauchy–Schwarz bound into the desired limit | `tendsto_integral_Icc`, `MeasureTheory.integrableOn_subinterval` |

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a00J02/apm-v2-a00J02-1774989750574/proof-plan.edn

**Stage 3 — LEAN FORMALIZATION**

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A00J02/Apm_v2_a00J02_1774989750574/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A00J02/Apm_v2_a00J02_1774989750574/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

Goal: formalize the estimate
`|f x| ≤ Real.sqrt x * ‖f'‖_{L²(0,x)}` and conclude `x⁻¹⁄² * f x → 0`
using the fact that `∫₀ˣ |f'|² → 0`.  Mathlib already contains the
fundamental theorem of calculus for absolutely continuous functions and the
Hilbert-space Cauchy–Schwarz inequality.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

No additional adjustments were needed: the Lean proof follows the same single
inequality, and no unexpected side conditions appeared.  The textual proof
already reflects the exact estimates that the formal argument consumes.
