# Proof Outline: a97A02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Closer hop 1 (2026-08-08)

Two foundational facts now compile locally. First, the restricted
unit-interval measure is installed as finite and `MemLp.integrable` converts
the supplied `Lᵖ` representative to an integrable function. Second,
`apm_a97A02_measure_Icc_le` proves that every moving interval has restricted
measure at most `ENNReal.ofReal (2*h)`.

The remaining estimate requires specializing the finite-measure `Lᵖ ⊆ L¹`
bound to the moving restriction and normalizing the resulting ENNReal powers.
Continuity requires the atomless indefinite-integral theorem for the restricted
measure at the two moving endpoints. These conversions are not packaged in one
existing theorem, so the main result remains partial with one `sorry`; its
statement is unchanged.

## Closer hop 2 (2026-08-08)

The continuity conjunct is now completely proved by the local lemma
`apm_a97A02_continuousOn_average`.  For the atomless restricted Lebesgue
measure, an `Icc` integral is a difference of two `Iic` primitives; Mathlib's
continuity theorem for those primitives and composition with `t-h` and `t+h`
then give continuity of the quotient by the fixed nonzero denominator.

Only the pointwise norm estimate remains.  The repository contains useful
applications of `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, and that theorem
does give the needed ENNReal estimate on the moving restricted measure.  The
uncompleted portion is the exact chain from the Bochner integral norm to
`eLpNorm · 1`, followed by monotonicity in the interval measure and the
`ENNReal.rpow`/`toReal` normalization required by the frozen real-valued
right-hand side.  The main theorem therefore honestly retains one `sorry`.

## Imported Proof Plan

```clojure
{:goal "Prove that the local average f_h(t) = (2h)^{-1} ∫_{t-h}^{t+h} f(x) dx of any f ∈ L^p([0,1]) (1 ≤ p < ∞) is continuous in t and obeys the bound |f_h(t)| ≤ (2h)^{-1/p}‖f‖_p."
 :terms [{:name "averaging kernel"
          :meaning "g_{t,h} = (2h)^{-1} · 1_{[t-h,t+h]} viewed as an L^q function (q the Hölder conjugate)."
          :needed-because "Expresses f_h(t) as the L^p–L^q dual pairing ⟨f, g_{t,h}⟩ so we can apply Hölder and continuity of kernels."}
         {:name "Hölder inequality"
          :meaning "|∫ fg| ≤ ‖f‖_p ‖g‖_q for conjugate exponents."
          :needed-because "Gives both the claimed bound on f_h(t) and the Lipschitz control once g_{t,h} varies with t."}
         {:name "symmetric-difference estimate"
          :meaning "m([t-h,t+h] △ [s-h,s+h]) → 0 as t→s."
          :needed-because "Shows ‖g_{t,h} - g_{s,h}‖_q → 0, hence |f_h(t)-f_h(s)| → 0 via Hölder."}]
 :strategy [{:id :s1
             :formal-dependency "Hölder inequality and continuity of indicator kernels in L^q"
             :informal-dependency "Stage 1 symmetric-difference argument"
             :why-this-now "Bounding |f_h(t)-f_h(s)| by ‖f‖_p · ‖g_{t,h}-g_{s,h}‖_q gives continuity once the kernel difference shrinks."
             :lean-target "avg_kernel_continuous"
             :mathlib-status "Needs lemmas about measure of symmetric differences and Hölder, both in Mathlib."}
            {:id :s2
             :formal-dependency "Hölder inequality"
             :informal-dependency "Stage 1 computation of the norm bound"
             :why-this-now "Computing ‖g_{t,h}‖_q = (2h)^{(1/q)-1} yields |f_h(t)| ≤ (2h)^{-1/p}‖f‖_p."
             :lean-target "avg_kernel_bound"
             :mathlib-status "Direct algebra once g_{t,h} is in L^q."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a97A02'
  :frame-id 'apm-v2-a97A02-1775003733088'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full informal solution (why it’s hard, key insight, detailed proof, and context) inside execute.md Stage 1."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Documented the lemma dependency narrative and Lean targets in Stage 2 and updated proof-plan.edn/formal-alignment.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Could not finish the Lean proof because Mathlib currently lacks an L^q-continuity lemma for sliding indicator kernels; recorded the blocker in Stage 3."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

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

## Closer completion

Closer hop 2 avoided the indicator-kernel blocker by expressing the moving
integral as a difference of atomless `Iic` primitives, proving continuity.
Closer hop 3 completes the quantitative estimate. For the restricted measure
on the moving interval, `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` compares
the `L¹` and `Lᵖ` seminorms. Measure monotonicity and the interval-volume
bound replace the moving measure by `2h`; the Bochner integral norm is bounded
by the resulting `L¹` seminorm. Finally the proof transports the ENNReal
inequality through `toReal` and combines real powers to obtain exactly
`(2h)^(-1/p.toReal)`. The frozen theorem is fully closed.
