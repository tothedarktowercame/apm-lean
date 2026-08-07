import Mathlib

/-!
# APM m93A04: differentiability of a nonlinear integral operator

## Statement repairs

None. The problem explicitly asks the solver to choose sufficient hypotheses;
we choose joint continuity of `K` and its second partial derivative, followed
by the uniform smallness hypothesis `|∂₂K| ≤ c < 1` for invertibility.

## Encoding questions

None. `C[0,1]` is encoded as Mathlib's continuous-map Banach space on the
closed interval subtype, and the integrals are Bochner integrals over that
subtype with its restricted Lebesgue measure.
-/

noncomputable section

open MeasureTheory Set

abbrev apm_m93A04_I := Set.Icc (0 : ℝ) 1
abbrev apm_m93A04_C := C(apm_m93A04_I, ℝ)

/-- The abstract Neumann-series step needed for the derivative: once the
integral part has operator norm below one, its complement is bijective. -/
lemma apm_m93A04_bijective_one_sub_of_norm_lt_one
    (T : apm_m93A04_C →L[ℝ] apm_m93A04_C) (hT : ‖T‖ < 1) :
    Function.Bijective ((1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - T) := by
  have hu : IsUnit ((1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - T) :=
    isUnit_one_sub_of_norm_lt_one (x := T) hT
  rcases hu with ⟨u, hu⟩
  constructor
  · intro x y hxy
    have hxy' := congrArg (fun z ↦ (↑(u⁻¹) : apm_m93A04_C →L[ℝ] apm_m93A04_C) z) hxy
    simpa [← hu, ← ContinuousLinearMap.mul_apply] using hxy'
  · intro y
    refine ⟨(↑(u⁻¹) : apm_m93A04_C →L[ℝ] apm_m93A04_C) y, ?_⟩
    simp [← hu, ← ContinuousLinearMap.mul_apply]

theorem apm_m93a04
    (K K₂ : ℝ → ℝ → ℝ)
    (hK : Continuous (Function.uncurry K))
    (hK₂ : Continuous (Function.uncurry K₂))
    (hpartial : ∀ t u : ℝ, HasDerivAt (K t) (K₂ t u) u)
    (c : ℝ) (hc_nonneg : 0 ≤ c) (hc : c < 1)
    (hsmall : ∀ t u : ℝ, |K₂ t u| ≤ c)
    (F : apm_m93A04_C → apm_m93A04_C)
    (hF : ∀ (x : apm_m93A04_C) (t : apm_m93A04_I),
      F x t = x t - ∫ s : apm_m93A04_I, K t.1 (x s))
    (D : apm_m93A04_C →
      (apm_m93A04_C →L[ℝ] apm_m93A04_C))
    (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I),
      D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s) :
    (∀ x : apm_m93A04_C, HasFDerivAt F (D x) x) ∧
    ∀ x : apm_m93A04_C, Function.Bijective (D x) := by
  /-
  Boundary: proving the first conjunct requires upgrading `hpartial` to a
  uniform Frechet remainder estimate in the `ContinuousMap` sup norm and
  packaging the parameterized Bochner integral over the interval subtype.
  I searched the parametric-integral APIs
  `hasFDerivAt_integral_of_dominated_loc_of_lip` and
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`; they provide the relevant
  integral differentiation machinery, but applying them here still requires
  the missing uniformity, measurability, and domination setup.

  Closer hop 1 finds and proves the abstract inverse stage:
  `apm_m93A04_bijective_one_sub_of_norm_lt_one` applies Mathlib's
  `isUnit_one_sub_of_norm_lt_one` and explicitly transports the resulting unit
  inverse to `Function.Bijective`. Thus no local Neumann-series development is
  needed. `m94J06` confirms the same Banach-algebra inverse infrastructure.

  For bijectivity it remains to define the integral operator whose complement
  is `D x`, prove its operator norm is at most `c` (using
  `Measure.Subtype.volume_univ`/the unit-interval volume computation and the
  continuous-map sup norm), and rewrite `D x` as `1 - Tₓ`. Searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, prior operator artifacts, and git
  history found no packaged parameterized continuous-kernel operator with
  exactly these bounds. The frozen statement was left unchanged.
  -/
  sorry
