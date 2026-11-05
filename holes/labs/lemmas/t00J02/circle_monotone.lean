import Mathlib

namespace t00J02_ModelProduct

open Set Filter
open scoped Topology

/-! The local real lift is the only circle-specific part of the argument. -/

/-- A locally injective circle map has, in a centered exponential chart, an injective
continuous real lift with a fixed monotonicity direction.  This follows by shrinking so
that both source and target avoid the negative-real-axis branch cut, taking `Complex.arg`,
and applying `ContinuousOn.strictMonoOn_of_injOn_Ioo`.  Estimated proof: 90--130 lines. -/
theorem circle_locally_monotone_aux_chart
    (ℓ : C(Circle, Circle)) (t₀ : Circle) (N : Set Circle)
    (hN : N ∈ 𝓝 t₀) (hinj : Set.InjOn ℓ N) :
    ∃ ε > 0, ∃ Φ : ℝ → ℝ,
      Φ 0 = 0 ∧
      ContinuousOn Φ (Ioo (-2 * ε) (2 * ε)) ∧
      (StrictMonoOn Φ (Ioo (-2 * ε) (2 * ε)) ∨
        StrictAntiOn Φ (Ioo (-2 * ε) (2 * ε))) ∧
      (∀ r ∈ Ioo (-2 * ε) (2 * ε),
        ℓ (t₀ * Circle.exp r) = ℓ t₀ * Circle.exp (Φ r)) ∧
      ∀ᶠ t in 𝓝 t₀, ∃ a ∈ Ioo (-ε) ε, t = t₀ * Circle.exp a := by
  sorry

theorem circle_locally_monotone (ℓ : C(Circle, Circle)) (t₀ : Circle) (N : Set Circle)
    (hN : N ∈ 𝓝 t₀) (hinj : Set.InjOn ℓ N) :
    ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ∀ᶠ t in 𝓝 t₀, ∃ δ > 0, ∃ ψ : ℝ → ℝ, ψ 0 = 0 ∧
      ContinuousOn ψ (Set.Ioo (-δ) δ) ∧
      ((m = 1 ∧ StrictMonoOn ψ (Set.Ioo (-δ) δ)) ∨ (m = -1 ∧ StrictAntiOn ψ (Set.Ioo (-δ) δ))) ∧
      ∀ r ∈ Set.Ioo (-δ) δ, ℓ (t * Circle.exp r) = ℓ t * Circle.exp (ψ r) := by
  obtain ⟨ε, hε, Φ, hΦ0, hΦcont, hdir, hΦeq, hchart⟩ :=
    circle_locally_monotone_aux_chart ℓ t₀ N hN hinj
  rcases hdir with hmono | hanti
  · refine ⟨1, Or.inl rfl, hchart.mono ?_⟩
    rintro t ⟨a, ha, rfl⟩
    let δ := ε
    have hδ : 0 < δ := hε
    let ψ : ℝ → ℝ := fun r => Φ (a + r) - Φ a
    refine ⟨δ, hδ, ψ, by simp [ψ], ?_, Or.inl ⟨rfl, ?_⟩, ?_⟩
    · exact (hΦcont.comp (continuous_const.add continuous_id).continuousOn
          (fun r hr => by
            constructor <;> dsimp [δ] at hr ⊢ <;> linarith [ha.1, ha.2, hr.1, hr.2])).sub continuousOn_const
    · intro x hx y hy hxy
      dsimp [ψ]
      simpa [add_comm] using sub_lt_sub_right
        (hmono (by constructor <;> dsimp [δ] at hx ⊢ <;> linarith [ha.1, ha.2, hx.1, hx.2])
          (by constructor <;> dsimp [δ] at hy ⊢ <;> linarith [ha.1, ha.2, hy.1, hy.2])
          (add_lt_add_right hxy a)) (Φ a)
    · intro r hr
      have ha2 : a ∈ Ioo (-2 * ε) (2 * ε) := by constructor <;> linarith [ha.1, ha.2]
      have har : a + r ∈ Ioo (-2 * ε) (2 * ε) := by
        constructor <;> dsimp [δ] at hr ⊢ <;> linarith [ha.1, ha.2, hr.1, hr.2]
      rw [mul_assoc, ← Circle.exp_add, hΦeq (a + r) har, hΦeq a ha2]
      simp only [ψ, Circle.exp_sub]
      simp only [div_eq_mul_inv, mul_assoc]
      congr 1
      rw [mul_comm (Circle.exp (Φ (a + r))) _, ← mul_assoc, mul_inv_cancel, one_mul]
  · refine ⟨-1, Or.inr rfl, hchart.mono ?_⟩
    rintro t ⟨a, ha, rfl⟩
    let δ := ε
    have hδ : 0 < δ := hε
    let ψ : ℝ → ℝ := fun r => Φ (a + r) - Φ a
    refine ⟨δ, hδ, ψ, by simp [ψ], ?_, Or.inr ⟨rfl, ?_⟩, ?_⟩
    · exact (hΦcont.comp (continuous_const.add continuous_id).continuousOn
          (fun r hr => by
            constructor <;> dsimp [δ] at hr ⊢ <;> linarith [ha.1, ha.2, hr.1, hr.2])).sub continuousOn_const
    · intro x hx y hy hxy
      dsimp [ψ]
      simpa [add_comm] using sub_lt_sub_right
        (hanti (by constructor <;> dsimp [δ] at hx ⊢ <;> linarith [ha.1, ha.2, hx.1, hx.2])
          (by constructor <;> dsimp [δ] at hy ⊢ <;> linarith [ha.1, ha.2, hy.1, hy.2])
          (add_lt_add_right hxy a)) (Φ a)
    · intro r hr
      have ha2 : a ∈ Ioo (-2 * ε) (2 * ε) := by constructor <;> linarith [ha.1, ha.2]
      have har : a + r ∈ Ioo (-2 * ε) (2 * ε) := by
        constructor <;> dsimp [δ] at hr ⊢ <;> linarith [ha.1, ha.2, hr.1, hr.2]
      rw [mul_assoc, ← Circle.exp_add, hΦeq (a + r) har, hΦeq a ha2]
      simp only [ψ, Circle.exp_sub]
      simp only [div_eq_mul_inv, mul_assoc]
      congr 1
      rw [mul_comm (Circle.exp (Φ (a + r))) _, ← mul_assoc, mul_inv_cancel, one_mul]

#print axioms circle_locally_monotone

end t00J02_ModelProduct
