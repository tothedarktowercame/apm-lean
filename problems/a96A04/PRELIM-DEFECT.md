# PRELIM-DEFECT — a96A04

## The printed text

The source (`problem.tex`) opens "For $f\in L^2(\R)$", while the integral is over $\Rn$ and
clause (b) reads $\|u\|_{L^2(\Rn)}\leq\|f\|_{L^2(\Rn)}$.

## The defect

`L^2(\R)` is a typo for `L^2(\Rn)`. For $n\neq 1$, $f$ on $\R$ cannot be integrated over
$\Rn$, and clause (b) itself takes the norm of $f$ on $\Rn$. For $n=1$ the printed text is
well-typed and true. This is the only defect.

Two things that are not defects: $(x-y)^2$ is standard notation for $\|x-y\|^2$, and
`(1/4\pi t)^{n/2}` with its line break is the usual $(1/(4\pi t))^{n/2}$.

## Correction

Replace `L^2(\R)` by `L^2(\Rn)`. Nothing else changes.

## In Lean

`apm_a96a04` in `problems/a96A04/lean/Main.lean` takes `f : EuclideanSpace ℝ (Fin n) → ℂ`
with `MemLp f 2 volume`, kernel `(4πt)^(-(n:ℝ)/2) * exp(-‖x-y‖²/(4t))`, and states the three
clauses: `ContDiff ℝ ∞`, the `eLpNorm 2` contraction, and the `eLpNorm 2` limit along
`nhdsWithin 0 (Ioi 0)`.

It is proved with no `sorry`; `#print axioms apm_a96a04` gives `propext`,
`Classical.choice`, `Quot.sound`. Clause (a) uses a class of functions all of whose
derivatives have a fixed Gaussian majorant, closed under `fderiv`; the kernel is in the
class by `norm_iteratedFDeriv_comp_le`, and differentiation under the integral with
induction on the order gives `ContDiff ℝ ∞`. Clause (b) is Young's inequality. Clause (c)
is the approximate-identity limit by dilation and strong continuity of translations in `L²`.
