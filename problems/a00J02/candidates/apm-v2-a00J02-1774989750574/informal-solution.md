# Informal Solution: a00J02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
