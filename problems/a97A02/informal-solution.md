# Informal Solution: a97A02

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  The averaging operator \(f \mapsto f_h\) “should’’ smooth and bound \(f\), but \(f\) is only in \(L^p\), so neither pointwise values nor uniform continuity are available.  Two traps appear over and over: (1) trying to differentiate under the integral sign and use calculus even though \(f\) need not be differentiable; (2) believing that \(L^p\) functions have representative that is continuous a.e., which is false.  One has to argue purely with integral estimates.

*Key insight.*  View \(f_h(t)\) as the pairing \(\langle f, g_{t,h}\rangle\) where \(g_{t,h} = (2h)^{-1}\mathbf 1_{[t-h,t+h]}\).  Then Hölder’s inequality simultaneously provides the quantitative bound and controls differences \(g_{t,h}-g_{s,h}\) via the size of their symmetric difference.  The measure of that symmetric difference tends to \(0\) as \(t\to s\), so the Hölder pairing with a fixed \(f\in L^p\) is continuous.

*Proof.* Fix \(f\in L^p([0,1])\) with \(1\le p<\infty\) and \(h>0\).  Extend \(f\) by zero outside \([0,1]\), so the integral from \(t-h\) to \(t+h\) is taken over a function in \(L^p(\mathbb R)\) but still equals the desired average.  Let \(q\) be the Hölder conjugate of \(p\) (i.e. \(1/p+1/q=1\) with the convention \(q=\infty\) when \(p=1\)).  Define
\[
g_{t,h}(x) = \frac{1}{2h}\mathbf 1_{[t-h,t+h]}(x).
\]
Then \(f_h(t) = \int_{\mathbb R} f(x) g_{t,h}(x)\,dx\).  Hölder gives
\[
|f_h(t)| \le \|f\|_{L^p(\mathbb R)} \|g_{t,h}\|_{L^q(\mathbb R)}.
\]
Because \(g_{t,h}\) is constant \((2h)^{-1}\) on an interval of length \(2h\) and zero elsewhere, \(\|g_{t,h}\|_{L^q} = (2h)^{-1} (2h)^{1/q} = (2h)^{-1/p}\); when \(p=1\), interpret \(1/q=0\) so \(\|g_{t,h}\|_{L^\infty}=1\) and the same formula results.  Thus \(|f_h(t)| \le (2h)^{-1/p}\|f\|_p\) for all \(t\).

For continuity, take \(s,t\in[0,1]\).  The symmetric difference \(A_{s,t} = [s-h,s+h]\triangle[t-h,t+h]\) is the union of at most two intervals and has Lebesgue measure \(m(A_{s,t}) = 2|s-t|\).  Also
\[
f_h(t) - f_h(s) = \int f(x)\,\bigl(g_{t,h}(x)-g_{s,h}(x)\bigr)\,dx.
\]
By Hölder,
\[
|f_h(t)-f_h(s)| \le \|f\|_{L^p} \|g_{t,h}-g_{s,h}\|_{L^q}.
\]
The difference \(g_{t,h}-g_{s,h}\) is supported on \(A_{s,t}\) and has absolute value at most \((2h)^{-1}\), whence \(\|g_{t,h}-g_{s,h}\|_{L^q} \le (2h)^{-1} m(A_{s,t})^{1/q} = (2h)^{-1} (2|s-t|)^{1/q}\).  When \(p=1\) (so \(q=\infty\)), replace this with the direct inequality
\[
|f_h(t)-f_h(s)| \le \frac{1}{2h} \int_{A_{s,t}} |f(x)|\,dx,
\]
and the absolute continuity of the integral (because \(f\in L^1\)) shows the right-hand side tends to \(0\) as \(s\to t\).  For \(p>1\) the estimate above implies \(|f_h(t)-f_h(s)|\le C |t-s|^{1/q}\), so \(f_h\) is Hölder-continuous.  Either way, \(f_h\) is continuous on \([0,1]\).

*What connects.*  This is a baby instance of mollification/approximate identities: convolving any \(L^p\) function with an \(L^1\) kernel produces a continuous function bounded in terms of \(\|f\|_p\).  The exact same reasoning shows that Steklov averages converge to \(f\) in \(L^p\) as \(h\to0\), and (after replacing the box kernel with a smooth one) underlies every proof that \(C_c^\infty\) is dense in \(L^p\).  In PDE prelims this appears as “regularize \(f\) by convolution, estimate with Hölder, and pass to the limit.’’

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *averaging kernel in \(L^q\)* (Lean target `avg_kernel_bound`): formal dependency is Hölder’s inequality (`MeasureTheory.snorm_indicator`) and the computation \(\|g_{t,h}\|_{L^q}=(2h)^{-1/p}\).  Informally this certifies the norm bound.
- *kernel-continuity via symmetric difference* (Lean target `avg_kernel_continuous`): depends formally on Hölder plus bounds for indicator differences in \(L^q\); informally it is the argument that `f_h` is continuous.  The key search phrases were “indicator symmetric difference snorm tending to zero’’ and “integral over sliding window continuous’’.

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a97A02/apm-v2-a97A02-1775003733088/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a97A02/apm-v2-a97A02-1775003733088/formal-alignment.edn

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/a97A02/apm-v2-a97A02-1775003733088/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/a97A02/apm-v2-a97A02-1775003733088/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

*Status.*  Not completed.  I planned to define the kernel
\[
\mathrm{ker}_{t,h}(x) = (2h)^{-1} \mathbf 1_{[t-h,t+h]}(x)
\]
inside `Lp ℝ μ q` where `μ := volume.restrict (Set.Icc (0 : ℝ) 1)` and then declare `f_h(t)` to be the pairing `∫ f · ker`.  `Mathlib` already has Hölder’s inequality (`snorm_le_snorn_indicator_mul_snorm`), so the bound step is straightforward once the kernel is in `Lp`.  The genuine blocker is the continuity step: I need a lemma stating that the map
```
t ↦ Set.indicator (Set.Icc (t - h) (t + h)) (fun x => (2 * h)⁻¹ : ℝ)
```
is continuous as a function into `Lp ℝ μ q`.  After searching (`rg -n "indicator" Mathlib/MeasureTheory/Function` and `rg -n "symmetric difference" mathlib`) I found no ready-made lemma, and hand-rolling it requires a fair amount of measure-theoretic set gymnastics (proving that the symmetric difference of sliding intervals has snorm going to zero).  I stopped here to avoid an unreliable custom proof.  Once Mathlib provides (or I implement) a lemma controlling snorms of sliding indicators, wiring the Lean theorem is routine.  I have not run `lake build` because there is no new Lean code yet.

Frame-local Lean files:
- /home/joe/code/apm-lean/ApmCanaries/Frames/A97A02/Apm_v2_a97A02_1775003733088/Main.lean
- /home/joe/code/apm-lean/ApmCanaries/Frames/A97A02/Apm_v2_a97A02_1775003733088/Scratch.lean

Shared extension root for promoted lemmas:
- /home/joe/code/apm-lean/ApmCanaries/Local

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal proof already mirrors the desired Lean statement: everything hinges on Hölder and the symmetric-difference estimate.  The Lean blocker (lack of an `Lp`-continuity lemma for indicator kernels) is noted explicitly above, so readers know exactly which analytic fact must be supplied to make the formal argument go through.
