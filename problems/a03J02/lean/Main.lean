import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# APM a03J02: Polynomial maps send null sets to null sets (Lusin's condition N)

**Problem.** Let `f : ℝⁿ → ℝⁿ` be a polynomial map (each component is a
polynomial in `ℝ[x₁,…,xₙ]`). Show that every set `E ⊂ ℝⁿ` with Lebesgue
measure zero has the property that `f(E)` has measure zero.

## Statement repair note

The informal proof proposes encoding the domain as `Fin n → ℝ` and building a
`IsPolynomialMap` predicate using `MvPolynomial`. Mathlib lacks calculus
infrastructure for `MvPolynomial.eval` (no `Differentiable` or `ContDiff`
lemmas), so proving polynomial ⟹ differentiable from `MvPolynomial` would
require substantial new analytic infrastructure.

**Structural repair:** The mathematical content is that *differentiable* maps
on finite-dimensional spaces send null sets to null sets — this is Mathlib's
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Gouëzel, in
the Jacobian/change-of-variables theory). The polynomial hypothesis is
stronger than needed: any `Differentiable` map satisfies Lusin's condition (N).

We state the main theorem at the `Differentiable` level (which Mathlib's
Jacobian theory directly proves), then separately state the polynomial version
with the polynomial ⟹ differentiable step marked at the genuine theory
boundary. No invariant is bypassed.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set

namespace ApmCanaries.A03J02

/-! ## Main theorem: differentiable maps send null sets to null sets -/

/-- **Lusin's condition (N) for differentiable maps.**

    A differentiable map `f : E → E` on a finite-dimensional real normed space
    maps Lebesgue-null sets to Lebesgue-null sets.

    This is a direct consequence of Mathlib's
    `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Gouëzel),
    which proves the result for `DifferentiableOn`. -/
theorem differentiable_image_null_of_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
    {f : E → E} (hf : Differentiable ℝ f)
    {s : Set E} (hs : μ s = 0) :
    μ (f '' s) = 0 := by
  apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hf.differentiableOn hs

/-! ## Polynomial maps -/

/-- A polynomial map `ℝⁿ → ℝⁿ`: each component is the evaluation of a
    multivariate polynomial. -/
def IsPolynomialMap {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ i : Fin n, ∃ p : MvPolynomial (Fin n) ℝ,
    ∀ x, f x i = MvPolynomial.eval x p

/-- The evaluation of a multivariate polynomial at `x : Fin n → ℝ` is differentiable
    as a function of `x`.

    This follows by expressing eval as a finite sum of monomial terms
    (`eval_eq'`), where each monomial is a product of coordinate powers,
    each of which is differentiable. -/
lemma MvPolynomial.eval_differentiable
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Differentiable ℝ (fun x : Fin n → ℝ => MvPolynomial.eval x p) := by
  rw [show (fun x => MvPolynomial.eval x p) =
        (fun x => ∑ d ∈ p.support, p.coeff d * ∏ i, x i ^ d i) by
        ext x; exact MvPolynomial.eval_eq' x p]
  fun_prop

/-- Polynomial maps are differentiable.

    Uses `MvPolynomial.eval_differentiable` for each component, then applies
    `differentiable_iff_pi` to combine into a `Differentiable` map. -/
lemma IsPolynomialMap.differentiable {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : IsPolynomialMap f) : Differentiable ℝ f := by
  rw [differentiable_pi]
  intro i x
  obtain ⟨p, hp⟩ := hf i
  rw [show (fun x => f x i) = (fun x => MvPolynomial.eval x p) by ext x; rw [hp]]
  exact (MvPolynomial.eval_differentiable p).differentiableAt

/-- **Main theorem: polynomial maps send null sets to null sets.**

    This is the problem statement. It follows from
    `differentiable_image_null_of_null` applied to
    `IsPolynomialMap.differentiable`. -/
theorem polynomial_map_image_null {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : IsPolynomialMap f)
    {E : Set (Fin n → ℝ)} (hE : volume E = 0) :
    volume (f '' E) = 0 := by
  exact differentiable_image_null_of_null (hf.differentiable) hE

end ApmCanaries.A03J02
