import Mathlib.Analysis.Complex.Liouville

/-!
# APM a94J05: Liouville's theorem and bounded real part

## Problem (from `a94J05.tex`)

State Cauchy's integral theorem expressing the value of an analytic function at
a point as a contour integral. Let `f` be entire. Prove:
**(a)** if `f` is bounded, then it is constant;
**(b)** if the real part of `f` is bounded below, then `f` is constant.

## Statement repair notes

1. The proposed Cauchy integral formula and Cauchy estimate lemmas are available
   in Mathlib (`Mathlib.Analysis.Complex.Liouville` provides
   `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` and Liouville's
   theorem directly). We use Mathlib's packaged Liouville instead.

2. The proposed statements for parts (a) and (b) are mathematically correct.

3. For part (b), the exponential trick `g = exp(-f)` converts a half-plane bound
   into a disk bound. Mathlib's `Differentiable.exists_const_forall_eq_of_bounded`
   then gives `g` constant. Differentiating this identity shows
   `exp(-f(z)) * (-f'(z)) = 0`; since the complex exponential never vanishes,
   `f'` is zero everywhere, so `f` is constant.

## Proof

**(a)** Direct application of Mathlib's Liouville:
`Differentiable.exists_const_forall_eq_of_bounded`.

**(b)** Define `g(z) = exp(-f(z))`. Then:
- `g` is entire (composition of `exp` with `-f`).
- `|g(z)| = exp(-Re f(z)) ≤ exp(C)` since `Re f(z) ≥ -C`.
- By Liouville (part a), `g` is constant: `g(z) = g(0)`.
- Differentiating the constant function `g` gives
  `exp(-f(z)) * (-f'(z)) = 0` for every `z`.
- Since `exp(-f(z)) ≠ 0`, it follows that `f'(z) = 0` everywhere.
- A differentiable function with zero derivative on `ℂ` is constant. ∎
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Bornology Set Topology

open scoped Real

namespace ApmCanaries.A94J05

/-- **Part (a): Liouville's theorem** — bounded entire ⟹ constant.

    Direct application of Mathlib's `Differentiable.exists_const_forall_eq_of_bounded`. -/
theorem liouville_bounded
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (M : ℝ) (hM : ∀ z, ‖f z‖ ≤ M) :
    ∃ c : ℂ, ∀ z, f z = c := by
  apply Differentiable.exists_const_forall_eq_of_bounded hf
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M, ?_⟩
  rintro y ⟨z, rfl⟩
  exact hM z

/-- **Part (b): Re f bounded below ⟹ f constant.**

    Uses the exponential trick: `g = exp(-f)` is bounded entire, hence constant
    by Liouville. Differentiating the resulting constant identity and using that
    the complex exponential never vanishes shows that `f' = 0`, hence `f` is
    constant. -/
theorem liouville_re_bounded_below
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C : ℝ) (hC : ∀ z, -C ≤ (f z).re) :
    ∃ c : ℂ, ∀ z, f z = c := by
  -- g(z) = exp(-f(z)) is bounded entire
  have hg : Differentiable ℂ (fun z => cexp (-f z)) :=
    Differentiable.cexp (Differentiable.neg hf)
  have hg_bdd : ∀ z, ‖cexp (-f z)‖ ≤ Real.exp C := by
    intro z
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    rw [neg_re]
    linarith [hC z]
  -- By Liouville, g is constant
  obtain ⟨c, hc⟩ := Differentiable.exists_const_forall_eq_of_bounded hg
    (by rw [isBounded_iff_forall_norm_le]
        refine ⟨Real.exp C, ?_⟩
        rintro y ⟨z, rfl⟩
        exact hg_bdd z)
  -- A constant function has zero derivative.
  have hg_deriv : ∀ z, deriv (fun w => cexp (-f w)) z = 0 := by
    intro z
    have hfun : (fun w => cexp (-f w)) = fun _ => c := funext hc
    rw [hfun]
    simp
  -- The chain rule and nonvanishing of exp force the derivative of f to vanish.
  have hf_deriv : ∀ z, deriv f z = 0 := by
    intro z
    have hchain := (hf z).hasDerivAt.neg.cexp.deriv
    have hzero : cexp (-f z) * -deriv f z = 0 := by
      change cexp ((-f) z) * -deriv f z = 0
      rw [← hchain]
      simpa only [Pi.neg_apply] using hg_deriv z
    exact neg_eq_zero.mp (mul_eq_zero.mp hzero |>.resolve_left (Complex.exp_ne_zero _))
  exact ⟨f 0, fun z => is_const_of_deriv_eq_zero hf hf_deriv z 0⟩

end ApmCanaries.A94J05
