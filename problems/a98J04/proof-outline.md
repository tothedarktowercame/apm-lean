# Proof Outline: a98J04

## Closer hop 1 completion

The theorem is closed without changing its statement.  For a
complex-differentiable function, `DifferentiableAt.fderiv_restrictScalars`
identifies the real derivative with the scalar restriction of the
complex-linear derivative; `map_smul` then proves commutation with `I` for
every input.  Conjugation has derivative `Complex.conjCLE`.  The derivative of
`h` is assembled explicitly from `Complex.reCLM`, `Complex.imCLM`, and
`Complex.ofRealCLM`.  Evaluating the claimed symmetry at `1` reduces the two
counterexamples respectively to `-I = I` and `2 * I = I`.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Explain why the real Jacobian of a complex-differentiable map must be of the Cauchy-Riemann form, and why the matrices for g(x,y)=(x,-y) and h(x,y)=(x,2y) violate this."
 :terms [{:name "real and imaginary parts"
          :meaning "Write f = u + i v with u,v : Real^2 -> Real and express the Jacobian via their partial derivatives."
          :needed-because "Complex differentiability can be translated into conditions on the real Jacobian."}
         {:name "Cauchy-Riemann equations"
          :meaning "u_x = v_y and u_y = -v_x for complex differentiable maps."
          :needed-because "They force the Jacobian to have the special form [[a,-b],[b,a]]."}
         {:name "Jacobian matrices of g and h"
          :meaning "Compute Dg = diag(1,-1) and Dh = diag(1,2)."
          :needed-because "These matrices clearly fail the CR symmetry, so g,h cannot arise from a complex differentiable function."}]
 :strategy [{:id :s1
             :formal-dependency "Complex.differentiable_iff_CauchyRiemann"
             :informal-dependency "Stage 1 rewriting f=u+iv"
             :why-this-now "Translate complex differentiability into CR equations for u and v."
             :lean-target "jacobian_has_CR_form"
             :mathlib-status "Mathlib already provides Cauchy-Riemann expressed via real derivatives."}
            {:id :s2
             :formal-dependency "matrix_form_from_CR"
             :informal-dependency "Output of :s1"
             :why-this-now "Show the Jacobian equals [[u_x,-u_y],[u_y,u_x]] with u_x=v_y, etc."
             :lean-target "cr_matrix_block"
             :mathlib-status "Follows algebraically once CR equations hold."}
            {:id :s3
             :formal-dependency "matrix_comparison"
             :informal-dependency "Structure from :s2"
             :why-this-now "Compute Dg,Dh and note they do not equal [[a,-b],[b,a]]."
             :lean-target "g_h_fail_CR"
             :mathlib-status "Direct matrix arithmetic."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'a98J04'
  :frame-id 'apm-v2-a98J04-1775004924027'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Completed the reader-facing proof using Cauchy–Riemann equations to pin down the Jacobian form and rule out g,h."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Documented the lemma chain (split into u,v → CR equations → matrix comparison) for both the write-up and Lean plan."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Outlined the Lean approach; blocked on the missing lemma translating ℂ-linearity of fderiv into the explicit 2×2 CR matrix."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

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
