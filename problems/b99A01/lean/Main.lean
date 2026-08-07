import Mathlib

/-! # APM b99A01: a half-plane maximum principle and valuation domains

The source file contains two independent problems.  Both are retained in the
single statement-bank theorem below.

## Statement repairs

* The boundary hypothesis binds `x : ℝ` but writes `|f(z)| ≤ M`.  This is the
  evident free-variable typo; it is encoded as `‖f (x : ℂ)‖ ≤ M`.
* Part (c) writes a degree-`n` expression with coefficients through
  `a_(n-1)`, so `n` is implicitly positive.  The formal statement makes
  `0 < n` explicit, excluding the syntactically meaningless degree-zero case.
-/

open Complex Set Polynomial

noncomputable section

/-- The upper half-plane maximum principle followed by all five valuation-domain
claims from the bundled source problem. -/
theorem apm_b99a01 :
    (∀ (f : ℂ → ℂ) (M : ℝ),
      Bornology.IsBounded (f '' {z : ℂ | 0 ≤ z.im}) →
      ContinuousOn f {z : ℂ | 0 ≤ z.im} →
      DifferentiableOn ℂ f {z : ℂ | 0 < z.im} →
      (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) →
      ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ M) ∧
    (∀ (V F : Type*) [CommRing V] [IsDomain V] [Field F] [Algebra V F]
      [IsFractionRing V F],
      (∀ α : F, α ≠ 0 →
        α ∈ Set.range (algebraMap V F) ∨
          α⁻¹ ∈ Set.range (algebraMap V F)) →
      (∀ I J : Ideal V, I ≤ J ∨ J ≤ I) ∧
      (∃! m : Ideal V, m.IsMaximal) ∧
      (∀ I : Ideal V, I.FG → I.IsPrincipal) ∧
      (∀ (α : F), α ≠ 0 → ∀ (n : ℕ), 0 < n → ∀ a : Fin n → V,
        α ^ n + ∑ i : Fin n, algebraMap V F (a i) * α ^ (i : ℕ)
            ∈ Set.range (algebraMap V F) →
        α ∈ Set.range (algebraMap V F)) ∧
      (∀ W : Subring F, Set.range (algebraMap V F) ⊆ W →
        (∀ α : F, α ≠ 0 → α ∈ W ∨ α⁻¹ ∈ W) ∧
        ∃ m : Ideal W, m.IsMaximal ∧
          (∀ n : Ideal W, n.IsMaximal → n = m) ∧
          (W : Set F) =
            {x | ∃ a s : V,
              algebraMap V F s ∉ ((↑) '' (m : Set W) : Set F) ∧
                x = algebraMap V F a / algebraMap V F s})) := by
  constructor
  · intro f M hbounded hcont hdiff hboundary z hz
    let g : ℂ → ℂ := fun w ↦ f (I * w)
    have hgdc : DiffContOnCl ℂ g {w : ℂ | 0 < w.re} := by
      constructor
      · apply hdiff.comp ((differentiable_const I).mul differentiable_id).differentiableOn
        intro w hw
        simpa [mul_im] using hw
      · apply hcont.comp (continuous_const_mul I).continuousOn
        intro w hw
        rw [closure_setOf_lt_re] at hw
        simpa [mul_im] using hw
    obtain ⟨C, hC⟩ := hbounded.exists_norm_le
    have hg_bound : ∀ w : ℂ, 0 ≤ w.re → ‖g w‖ ≤ C := by
      intro w hw
      apply hC
      exact ⟨I * w, by simpa [mul_im] using hw, rfl⟩
    have hgexp : ∃ c < (2 : ℝ), ∃ B,
        g =O[Bornology.cobounded ℂ ⊓ Filter.principal {w : ℂ | 0 < w.re}]
          fun w ↦ Real.exp (B * ‖w‖ ^ c) := by
      refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound C ?_⟩
      apply Filter.Eventually.filter_mono inf_le_right
      rw [Filter.eventually_principal]
      intro w hw
      simpa only [zero_mul, Real.exp_zero, Real.norm_eq_abs, abs_one, mul_one] using
        hg_bound w hw.le
    have hgreal : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop fun x : ℝ ↦ ‖g x‖ := by
      refine ⟨C, (Filter.eventually_ge_atTop 0).mono fun x hx ↦ ?_⟩
      exact hg_bound x (by simpa using hx)
    have hgimag : ∀ x : ℝ, ‖g (x * I)‖ ≤ M := by
      intro x
      have heq : I * ((x : ℂ) * I) = ((-x : ℝ) : ℂ) := calc
        I * ((x : ℂ) * I) = (x : ℂ) * (I * I) := by ring
        _ = (-x : ℝ) := by rw [I_mul_I]; norm_num
      simpa only [g, heq] using hboundary (-x)
    have hright : ‖g (-I * z)‖ ≤ M := by
      apply PhragmenLindelof.right_half_plane_of_bounded_on_real hgdc hgexp hgreal hgimag
      simpa [mul_re] using hz.le
    have heq : I * (-I * z) = z := calc
      I * (-I * z) = -(I * I) * z := by ring
      _ = z := by rw [I_mul_I]; simp
    simpa only [g, heq] using hright
  · intro V F _ _ _ _ _ hvaluation
    letI : ValuationRing V := (ValuationRing.iff_isInteger_or_isInteger V F).mpr fun α ↦ by
      by_cases hα : α = 0
      · left
        exact ⟨0, by simpa [hα]⟩
      · rcases hvaluation α hα with ⟨a, ha⟩ | ⟨a, ha⟩
        · exact Or.inl ⟨a, ha⟩
        · exact Or.inr ⟨a, ha⟩
    constructor
    · exact fun I J ↦
        ((ValuationRing.iff_ideal_total (R := V)).mp (inferInstance : ValuationRing V)).total I J
    constructor
    · exact IsLocalRing.maximal_ideal_unique V
    constructor
    · exact fun I hI ↦ IsBezout.isPrincipal_of_FG I hI
    constructor
    · -- Mathlib's valuation-ring instances provide `IsIntegrallyClosed V`.
      -- Package the displayed finite sum as a monic polynomial.
      haveI : IsIntegrallyClosed V := inferInstance
      intro α hα n hn a hβ
      obtain ⟨b, hb⟩ := hβ
      let p : V[X] := X ^ n + ∑ i : Fin n, C (a i) * X ^ (i : ℕ) - C b
      have hdeg : degree (∑ i : Fin n, C (a i) * X ^ (i : ℕ) - C b) < n := by
        apply (degree_sub_le _ _).trans_lt
        rw [max_lt_iff]
        constructor
        · exact degree_sum_fin_lt a
        · exact (degree_C_le : degree (C b : V[X]) ≤ 0).trans_lt
            (WithBot.coe_lt_coe.mpr hn)
      have hp : p.Monic := by
        simpa only [p, sub_eq_add_neg, add_assoc] using monic_X_pow_add hdeg
      have hroot : Polynomial.eval₂ (algebraMap V F) α p = 0 := by
        dsimp only [p]
        rw [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C]
        rw [eval₂_finset_sum]
        simp_rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
        rw [hb]
        ring
      have hint : IsIntegral V α := ⟨p, hp, hroot⟩
      exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
    · -- (Mathlib: RingTheory.Valuation.ValuationSubring)
      intro W hVW
      have hWval : ∀ α : F, α ≠ 0 → α ∈ W ∨ α⁻¹ ∈ W := by
        intro α hα
        exact (hvaluation α hα).imp (fun ⟨a, ha⟩ => hVW ⟨a, ha⟩)
          (fun ⟨a, ha⟩ => hVW ⟨a, ha⟩)
      refine ⟨hWval, ?_⟩
      let VW : ValuationSubring F :=
        ValuationSubring.ofSubring W fun x => by
          by_cases hx : x = 0
          · left
            simpa [hx] using W.zero_mem
          · exact hWval x hx
      letI : IsLocalRing W := VW.isLocalRing
      let m : Ideal W := IsLocalRing.maximalIdeal W
      refine ⟨m, IsLocalRing.maximalIdeal.isMaximal W,
        fun n hn => by simpa [m] using IsLocalRing.eq_maximalIdeal hn, ?_⟩
      ext x
      constructor
      · intro hx
        by_cases hx0 : x = 0
        · refine ⟨0, 1, ?_, by simp [hx0]⟩
          rintro ⟨w, hw, heq⟩
          have : IsUnit w := by
            have : w = 1 := Subtype.ext (by simpa using heq)
            simpa [this]
          change w ∈ IsLocalRing.maximalIdeal W at hw
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
          exact hw this
        · rcases hvaluation x hx0 with ⟨a, ha⟩ | ⟨s, hs⟩
          · refine ⟨a, 1, ?_, ?_⟩
            · rintro ⟨w, hw, heq⟩
              have : IsUnit w := by
                have : w = 1 := Subtype.ext (by simpa using heq)
                simpa [this]
              change w ∈ IsLocalRing.maximalIdeal W at hw
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
              exact hw this
            · simpa [ha]
          · refine ⟨1, s, ?_, ?_⟩
            · rintro ⟨w, hw, heq⟩
              change w ∈ IsLocalRing.maximalIdeal W at hw
              rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
              apply hw
              refine ⟨⟨w, ⟨x, hx⟩, ?_, ?_⟩, rfl⟩
              · apply Subtype.ext
                change (w : F) * x = 1
                rw [heq, hs]
                exact inv_mul_cancel₀ hx0
              · apply Subtype.ext
                change x * (w : F) = 1
                rw [heq, hs]
                exact mul_inv_cancel₀ hx0
            · rw [map_one, one_div, hs, inv_inv]
      · rintro ⟨a, s, hs, rfl⟩
        have hsW : algebraMap V F s ∈ W := hVW ⟨s, rfl⟩
        let sw : W := ⟨algebraMap V F s, hsW⟩
        have hsw : sw ∉ m := by
          intro h
          exact hs ⟨sw, h, rfl⟩
        have hunit : IsUnit sw := by
          change sw ∉ IsLocalRing.maximalIdeal W at hsw
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hsw
          exact Classical.not_not.mp hsw
        rw [div_eq_mul_inv]
        change algebraMap V F a * (algebraMap V F s)⁻¹ ∈ W
        apply W.mul_mem (hVW ⟨a, rfl⟩)
        have hinv_mem : (((↑(hunit.unit⁻¹) : W) : F)) ∈ W := Subtype.property _
        convert hinv_mem using 1
        symm
        calc
          ((↑(hunit.unit⁻¹) : W) : F) =
              ((↑hunit.unit : W) : F)⁻¹ :=
            by
              apply eq_inv_of_mul_eq_one_right
              exact congrArg ((↑) : W → F) hunit.unit.mul_inv
          _ = (sw : F)⁻¹ := congrArg Inv.inv (congrArg ((↑) : W → F) hunit.unit_spec)
          _ = (algebraMap V F s)⁻¹ := rfl
