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

/-- The proposed derivative is uniformly bounded in operator norm.  This is
the bounded-linear part of the remaining differentiability argument. -/
lemma apm_m93A04_norm_D_le
    (K₂ : ℝ → ℝ → ℝ) (hK₂ : Continuous (Function.uncurry K₂))
    (c : ℝ) (hc_nonneg : 0 ≤ c) (hsmall : ∀ t u : ℝ, |K₂ t u| ≤ c)
    (D : apm_m93A04_C → apm_m93A04_C →L[ℝ] apm_m93A04_C)
    (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I),
      D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s)
    (x : apm_m93A04_C) : ‖D x‖ ≤ 1 + c := by
  have hnorm :=
    apm_m93A04_norm_one_sub_D_le K₂ hK₂ c hc_nonneg hsmall D hD x
  calc
    ‖D x‖ = ‖(1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - (1 - D x)‖ := by
      congr 1
      abel
    _ ≤ ‖(1 : apm_m93A04_C →L[ℝ] apm_m93A04_C)‖ + ‖1 - D x‖ := by
      exact norm_sub_le (1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) (1 - D x)
    _ ≤ 1 + c := by simpa using add_le_add_left hnorm 1

/-- Why this unblocks `apm_m93a04`: this is the missing uniform
Nemytskii-to-`ContinuousMap` remainder theorem.  Joint continuity of the
scalar derivative on compact parameter/value ranges upgrades the pointwise
Taylor formula, after integration, to a Fréchet derivative in the sup norm. -/
theorem apm_m93A04_bridge_hasFDerivAt
    (K K₂ : ℝ → ℝ → ℝ)
    (hK : Continuous (Function.uncurry K))
    (hK₂ : Continuous (Function.uncurry K₂))
    (hpartial : ∀ t u : ℝ, HasDerivAt (K t) (K₂ t u) u)
    (F : apm_m93A04_C → apm_m93A04_C)
    (hF : ∀ (x : apm_m93A04_C) (t : apm_m93A04_I),
      F x t = x t - ∫ s : apm_m93A04_I, K t.1 (x s))
    (D : apm_m93A04_C →
      (apm_m93A04_C →L[ℝ] apm_m93A04_C))
    (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I),
      D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s)
    (x : apm_m93A04_C) :
    HasFDerivAt F (D x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let R : ℝ := ‖x‖ + 1
  have hR : 0 < R := add_pos_of_nonneg_of_pos (norm_nonneg x) zero_lt_one
  let Q : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc (-R) R
  have hQc : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn (Function.uncurry K₂) Q :=
    hQc.uniformContinuousOn_of_continuous hK₂.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.1 huc) ε hε
  have hr : 0 < min δ 1 := lt_min hδ zero_lt_one
  filter_upwards [Metric.ball_mem_nhds (0 : apm_m93A04_C) hr] with h hh
  have hhn : ‖h‖ < min δ 1 := by simpa [Metric.mem_ball, dist_zero_right] using hh
  have hhδ : ‖h‖ < δ := lt_of_lt_of_le hhn (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hhn (min_le_right _ _)
  have hpoint : ∀ (t s : apm_m93A04_I),
      ‖K t.1 (x s + h s) - K t.1 (x s) - K₂ t.1 (x s) * h s‖ ≤ ε * ‖h‖ := by
    intro t s
    let g : ℝ → ℝ := fun u ↦ K t.1 u - K₂ t.1 (x s) * u
    have hseg : ∀ u ∈ segment ℝ (x s) (x s + h s),
        |K₂ t.1 u - K₂ t.1 (x s)| < ε := by
      intro u hu
      have hu_dist : dist u (x s) ≤ ‖h s‖ := by
        have hz := segment_subset_closedBall_left (x s) (x s + h s) hu
        simpa [Metric.mem_closedBall, dist_comm, dist_eq_norm] using hz
      have htuQ : (t.1, u) ∈ Q := by
        refine ⟨t.2, ?_⟩
        have hxabs : |x s| ≤ ‖x‖ := by
          simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm x s
        have huabs : |u| < R := calc
          |u| = |x s + (u - x s)| := by ring_nf
          _ ≤ |x s| + |u - x s| := abs_add_le _ _
          _ ≤ ‖x‖ + ‖h s‖ := add_le_add hxabs (by simpa [Real.norm_eq_abs, dist_eq_norm] using hu_dist)
          _ ≤ ‖x‖ + ‖h‖ := by gcongr; exact ContinuousMap.norm_coe_le_norm h s
          _ < R := by simpa [R, add_comm] using add_lt_add_left hh1 ‖x‖
        exact ⟨le_of_lt (neg_lt_of_abs_lt huabs), le_of_lt (lt_of_abs_lt huabs)⟩
      have htxQ : (t.1, x s) ∈ Q := by
        refine ⟨t.2, ?_⟩
        have hxabs : |x s| ≤ ‖x‖ := by
          simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm x s
        have hlo := neg_le_of_abs_le hxabs
        have hhi := le_of_abs_le hxabs
        constructor <;> dsimp [R] <;> linarith
      apply hmod (t.1, u) htuQ (t.1, x s) htxQ
      simpa [Prod.dist_eq, dist_self, dist_eq_norm, max_lt_iff] using
        lt_of_le_of_lt hu_dist (lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm h s) hhδ)
    have hgder : ∀ u ∈ segment ℝ (x s) (x s + h s),
        HasDerivWithinAt g (K₂ t.1 u - K₂ t.1 (x s))
          (segment ℝ (x s) (x s + h s)) u := by
      intro u hu
      have hd : HasDerivAt g (K₂ t.1 u - K₂ t.1 (x s)) u := by
        simpa [g] using (hpartial t.1 u).sub ((hasDerivAt_id u).const_mul (K₂ t.1 (x s)))
      exact hd.hasDerivWithinAt
    have hm := (convex_segment (x s) (x s + h s)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hgder (fun u hu ↦ by simpa [Real.norm_eq_abs] using (le_of_lt (hseg u hu)))
      (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    calc
      ‖K t.1 (x s + h s) - K t.1 (x s) - K₂ t.1 (x s) * h s‖ =
          ‖g (x s + h s) - g (x s)‖ := by simp [g]; ring_nf
      _ ≤ ε * ‖(x s + h s) - x s‖ := hm
      _ ≤ ε * ‖h‖ := by simpa using mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm h s) hε.le
  apply (ContinuousMap.norm_le (F (x + h) - F x - D x h) (mul_nonneg hε.le (norm_nonneg h))).2
  intro t
  let A : apm_m93A04_I → ℝ := fun s ↦ K t.1 ((x + h) s)
  let B : apm_m93A04_I → ℝ := fun s ↦ K t.1 (x s)
  let C : apm_m93A04_I → ℝ := fun s ↦ K₂ t.1 (x s) * h s
  have hAc : Continuous A := hK.comp (continuous_const.prodMk (x + h).continuous)
  have hBc : Continuous B := hK.comp (continuous_const.prodMk x.continuous)
  have hCc : Continuous C :=
    (hK₂.comp (continuous_const.prodMk x.continuous)).mul h.continuous
  have hAi : Integrable A := by simpa [MeasureTheory.IntegrableOn] using
    hAc.continuousOn.integrableOn_compact (μ := volume) isCompact_univ
  have hBi : Integrable B := by simpa [MeasureTheory.IntegrableOn] using
    hBc.continuousOn.integrableOn_compact (μ := volume) isCompact_univ
  have hCi : Integrable C := by simpa [MeasureTheory.IntegrableOn] using
    hCc.continuousOn.integrableOn_compact (μ := volume) isCompact_univ
  have hintEq : (∫ s, (A s - B s - C s)) = (∫ s, A s) - (∫ s, B s) - (∫ s, C s) := by
    have hAB := integral_sub hAi hBi
    have hABC := integral_sub (hAi.sub hBi) hCi
    simpa only [Pi.sub_apply] using hABC.trans (congrArg (fun z : ℝ ↦ z - ∫ s, C s) hAB)
  have heq : (F (x + h) - F x - D x h) t = - ∫ s, (A s - B s - C s) := by
    rw [hintEq]
    simp only [ContinuousMap.sub_apply, hF, hD, ContinuousMap.add_apply]
    simp [A, B, C]
    ring
  rw [heq, norm_neg]
  calc
    ‖∫ s, (A s - B s - C s)‖ ≤ ∫ s, ‖A s - B s - C s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _s : apm_m93A04_I, ε * ‖h‖ := by
      apply integral_mono (hAi.sub hBi |>.sub hCi).norm (integrable_const _)
      intro s
      simpa [A, B, C] using hpoint t s
    _ = ε * ‖h‖ := by simp

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

  Closer hop 3 additionally proves `apm_m93A04_norm_D_le`, uniformly bounding
  the candidate derivative by `1 + c`.  A final search found only the scalar
  mean-value lemma `lipschitzWith_of_nnnorm_deriv_le` and the same fixed-
  codomain parametric-integral results; neither promotes the pointwise Taylor
  estimates to a `ContinuousMap`-valued Frechet remainder.  Thus boundedness
  of the derivative is now compiled, but the uniform remainder bridge remains
  open without introducing an unproved assertion.
  -/
  constructor
  · exact fun x ↦ apm_m93A04_bridge_hasFDerivAt K K₂ hK hK₂ hpartial F hF D hD x
  · exact fun x ↦ apm_m93A04_bijective_D K₂ hK₂ c hc_nonneg hc hsmall D hD x

#print axioms apm_m93a04
