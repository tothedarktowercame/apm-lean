# Informal Solution: a98J04

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  A complex derivative is a limit in ℂ, but the question forces you to view everything as a real map ℝ²→ℝ². Students often forget how the real Jacobian encodes complex linearity. Merely computing a derivative of a sample function doesn’t explain why *every* complex-differentiable map has a highly symmetric Jacobian, nor why the two given maps fail.

*Key insight.*  Split any complex-valued function into real and imaginary parts, say `f(x+iy)=u(x,y)+i v(x,y)`. Complex differentiability is equivalent to the Cauchy–Riemann equations `u_x=v_y` and `u_y=-v_x`. Those two equalities force the Jacobian matrix
\[
J_f(x,y)=\begin{pmatrix}u_x & u_y\\ v_x & v_y\end{pmatrix}
\]
to equal
\[
\begin{pmatrix}a & -b\\ b & a\end{pmatrix}
\]
with `a=u_x=v_y` and `b=v_x=-u_y`. Such matrices commute with the 90° rotation matrix—exactly the signature of complex linear maps. The functions `g(x,y)=(x,-y)` and `h(x,y)=(x,2y)` have Jacobians `diag(1,-1)` and `diag(1,2)`, respectively, neither of which fits this pattern.

*Complete proof.*  Let `f=u+iv` be complex differentiable at `z0=x0+iy0`. Then (`u`,`v`) are real differentiable and satisfy the Cauchy–Riemann equations `u_x(x0,y0)=v_y(x0,y0)` and `u_y(x0,y0)=-v_x(x0,y0)`. Hence the real Jacobian matrix of `f` at `(x0,y0)` equals
\[
\begin{pmatrix}u_x & u_y\\ v_x & v_y\end{pmatrix}_{(x0,y0)}
=\begin{pmatrix} a & -b\\ b & a\end{pmatrix},
\]
where `a=u_x=v_y` and `b=v_x=-u_y` at the point. In other words, the derivative is represented by a complex-linear map `z↦a z + i b z = (a+ib)z` when expressed in the standard real basis.

Now examine the two given maps. For `g(x,y)=(x,-y)` we have constant Jacobian 
\[Dg=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\]
which would force `a=1` and `-b=0` from the top row and `b=0`, `a=-1` from the bottom row—an impossibility. Thus no complex-differentiable function can have this Jacobian. Likewise `h(x,y)=(x,2y)` has constant Jacobian
\[Dh=\begin{pmatrix}1&0\\0&2\end{pmatrix},\]
which would require simultaneously `a=1`, `-b=0`, `b=0`, and `a=2`; again impossible. Therefore neither `g` nor `h` satisfies the symmetry that every complex-differentiable map must have.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. *Split into real/imaginary parts* — express the real Jacobian via `u_x,u_y,v_x,v_y`. (Lean target: `jacobian_real_imag`.)
2. *Cauchy–Riemann ⇒ special matrix* — insert `u_x=v_y` and `u_y=-v_x` to deduce the `[[a,-b],[b,a]]` form. (Lean target: `jacobian_has_CR_form`.)
3. *Check g and h* — compute their constant Jacobians (`diag(1,-1)` and `diag(1,2)`) and note that these cannot equal `[[a,-b],[b,a]]`. (Lean target: `gh_fail_CR_form`.)

**Stage 3 — LEAN FORMALIZATION**

Files used: `ApmCanaries/Frames/A98J04/Apm_v2_a98J04_1775004924027/Main.lean` and `Scratch.lean`.

Plan: leverage Mathlib’s `Complex.differentiable_iff` which states that the real derivative of a complex-differentiable map is ℂ-linear. The ℂ-linear condition is equivalent to the commutation relation `L (I z) = I (L z)`, which in coordinates yields the CR matrix. The last step is to show that the linear maps induced by `g(x,y)=(x,-y)` (complex conjugation) and `h(x,y)=(x,2y)` do not satisfy this commutation, hence they cannot agree with the derivative of a complex-differentiable map.

Blocker: duplicating the CR matrix argument inside Lean still needs a helper lemma turning the abstract statement “`fderiv ℂ f z` is ℂ-linear” into the concrete `[[a,-b],[b,a]]` matrix. Mathlib has lemmas about `ComplexLinear` maps, but there is not yet a ready-made theorem producing the explicit `2×2` matrix on the real basis. Without that lemma the formal proof stops after proving the derivative is ℂ-linear, so `Main.lean` currently contains only the skeleton. Once a lemma such as
```
lemma complexLinear_matrix (L : ℂ →ₗ[ℂ] ℂ) :
  ∃ a b : ℝ, matrixReal L = ![[a, -b], [b, a]]
```
is available, the rest is straightforward matrix algebra, and `lake build` can be run.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The handwritten proof uses exactly the property that a complex derivative is ℂ-linear. The Lean strategy mirrors this, but needs the bridging lemma that translates ℂ-linearity into the explicit Jacobian matrix. After that lemma is implemented, both the textual and formal arguments consist of the same two steps: invoke Cauchy–Riemann, then check that `g` and `h` fail the symmetry.
