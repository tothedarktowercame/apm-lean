# Preliminary defect report: m98A05

## The false printed claim

Part (b) says that, for `H(x, ε) = F(x) + ε G(x)`, the assumptions
`H(x₀, ε₀) = 0` and invertibility of `DF(x₀)` imply that `H(x, ε) = 0`
has a solution for every `ε` sufficiently close to `ε₀`. This is false.
The derivative with respect to `x` at the base point is
`DₓH(x₀, ε₀) = DF(x₀) + ε₀ DG(x₀)`, not `DF(x₀)`.

## Complete counterexample

Take `X = Y = ℝ`, `F(x) = x² + x - 1`, `G(x) = 1 - x`, `x₀ = 0`, and
`ε₀ = 1`. Both functions are `C¹`, `DF(0) = 1` is invertible, and
`H(0,1) = F(0) + G(0) = 0`. On the other hand,
`H(x, ε) = x² + (1-ε)x + (ε-1)`, whose discriminant is
`(1-ε)² - 4(ε-1) = (ε-1)(ε-5)`. For every `ε` with `1 < ε < 5` this is
negative, so there is no real solution. Such `ε` occur in every neighbourhood
of `ε₀ = 1`. Here `DₓH(0,1) = DF(0) + DG(0) = 0`, exactly the derivative
that the printed hypothesis failed to control.

## Evident intent and smallest correction

Part (b) is the direct application of the implicit-function theorem to the
parameter-dependent equation. Its smallest correction is to replace
“`DF(x₀)` is invertible” by “`DF(x₀) + ε₀ DG(x₀)` is invertible”. No other
hypothesis or conclusion in (b) needs to change.

Part (c), literally read, is true but trivial: `w = 0` belongs to
`H²(0,π)`, satisfies both boundary conditions, and solves the equation for
every real `ε`. In the context of (a) and (b), the evident intended
application is the local branch through `(w,ε)=(0,0)`. A local
conclusion is that for sufficiently small `ε`, zero is the unique
sufficiently small `H²(0,π) ∩ H¹₀(0,π)` solution. There is no nonzero branch
through zero: the linearization `w ↦ w''-w` with Dirichlet boundary
conditions is invertible. Merely restating existence would preserve the
accidental `w=0` loophole rather than express the intended IFT application.
In fact the energy identity gives the sharper evident statement: for every
`ε`, any solution satisfying `|ε| sup_[0,π] |w| < 1` is zero. Consequently,
when `|ε| < 1`, zero is the unique solution in the open unit sup-norm ball.

Part (a) stands as printed. In part (b), the definition of `H`, the `C¹`
hypotheses, the base-point equation, and the local-existence conclusion stand
as printed; only the invertibility hypothesis changes. In part (c), the
equation, Sobolev space, boundary conditions, and small-parameter regime stand
as printed, while the intended conclusion must include local uniqueness of
the small solution.
