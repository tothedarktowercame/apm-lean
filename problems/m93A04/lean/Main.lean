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

/-- The concrete derivative formula itself determines the integral part and
bounds its operator norm by the uniform kernel bound. -/
lemma apm_m93A04_norm_one_sub_D_le
    (K₂ : ℝ → ℝ → ℝ) (hK₂ : Continuous (Function.uncurry K₂))
    (c : ℝ) (hc_nonneg : 0 ≤ c) (hsmall : ∀ t u : ℝ, |K₂ t u| ≤ c)
    (D : apm_m93A04_C → apm_m93A04_C →L[ℝ] apm_m93A04_C)
    (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I),
      D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s)
    (x : apm_m93A04_C) :
    ‖(1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - D x‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc_nonneg
  intro h
  apply (ContinuousMap.norm_le ((1 - D x) h)
    (mul_nonneg hc_nonneg (norm_nonneg h))).2
  intro t
  have hcont : Continuous (fun s : apm_m93A04_I => K₂ t.1 (x s) * h s) :=
    (hK₂.comp (continuous_const.prodMk x.continuous)).mul h.continuous
  have hint : Integrable (fun s : apm_m93A04_I => K₂ t.1 (x s) * h s) :=
    by simpa [MeasureTheory.IntegrableOn] using
      hcont.continuousOn.integrableOn_compact (μ := volume) isCompact_univ
  have hpoint : ∀ s : apm_m93A04_I,
      ‖K₂ t.1 (x s) * h s‖ ≤ c * ‖h‖ := by
    intro s
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hsmall _ _) (ContinuousMap.norm_coe_le_norm h s)
      (abs_nonneg _) hc_nonneg
  have hintegral : ‖∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s‖ ≤ c * ‖h‖ := by
    calc
      ‖∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s‖ ≤
          ∫ s : apm_m93A04_I, ‖K₂ t.1 (x s) * h s‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _s : apm_m93A04_I, c * ‖h‖ :=
        integral_mono hint.norm (integrable_const _) hpoint
      _ = c * ‖h‖ := by simp
  simpa [hD] using hintegral

/-- Under the uniform bound `c < 1`, every operator described by the frozen
derivative formula is bijective. -/
lemma apm_m93A04_bijective_D
    (K₂ : ℝ → ℝ → ℝ) (hK₂ : Continuous (Function.uncurry K₂))
    (c : ℝ) (hc_nonneg : 0 ≤ c) (hc : c < 1)
    (hsmall : ∀ t u : ℝ, |K₂ t u| ≤ c)
    (D : apm_m93A04_C → apm_m93A04_C →L[ℝ] apm_m93A04_C)
    (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I),
      D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s)
    (x : apm_m93A04_C) : Function.Bijective (D x) := by
  have hnorm : ‖(1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - D x‖ < 1 :=
    lt_of_le_of_lt (apm_m93A04_norm_one_sub_D_le K₂ hK₂ c hc_nonneg hsmall D hD x) hc
  simpa only [sub_sub_cancel] using
    apm_m93A04_bijective_one_sub_of_norm_lt_one
      ((1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - D x) hnorm

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

  Closer hop 2 routes around constructing a separate integral operator:
  `apm_m93A04_norm_one_sub_D_le` reads that operator directly as `1 - D x`
  from `hD`. Joint continuity supplies integrability on the compact interval;
  `norm_integral_le_integral_norm`, `ContinuousMap.norm_coe_le_norm`, and the
  probability-volume instance on the interval give `‖1 - D x‖ ≤ c`.
  `apm_m93A04_bijective_D` combines this with the hop-1 Neumann lemma and
  closes the second frozen conjunct in full.

  The only remaining bridge is the first conjunct. A renewed inspection of
  `hasFDerivAt_integral_of_dominated_loc_of_lip` and
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` confirms that their input
  is a Banach-valued integral with a fixed codomain. Applying them pointwise
  in `t` does not itself yield the required uniform `ContinuousMap`-norm
  remainder. One must derive a uniform remainder for `K t` on the compact
  image of `x` (uniformly also in `t`) from continuity of `K₂`, then pass that
  estimate through the subtype integral. No searched `LEMMA-INDEX.md`,
  `ConstructionTargets/`, sibling, Mathlib, or git-history result packages
  that uniform Nemytskii-to-sup-norm step. The frozen statement is unchanged.
  -/
  constructor
  · sorry
  · exact fun x ↦ apm_m93A04_bijective_D K₂ hK₂ c hc_nonneg hc hsmall D hD x
