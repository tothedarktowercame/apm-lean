import Mathlib

namespace t00J02_ModelProduct

open Set Filter
open scoped Topology

/-! The local real lift is the only circle-specific part of the argument. -/

/-- A continuous circle map admits a small exponential coordinate around the
image of any base point (copied from side_open.lean, codex-16). -/
lemma eventually_exists_small_exp_coordinate (ℓ : C(Circle, Circle)) (t₀ : Circle)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∃ r ∈ Set.Ioo (-ε) ε, ℓ t = ℓ t₀ * Circle.exp r := by
  let q : C(Circle, Circle) :=
    ⟨fun t => (ℓ t₀)⁻¹ * ℓ t, by fun_prop⟩
  let r : Circle → ℝ := fun t => Complex.arg (q t : ℂ)
  have hq0 : q t₀ = 1 := by simp [q]
  have hr0 : r t₀ = 0 := by simp [r, hq0]
  have hcont : ContinuousAt r t₀ := by
    apply (Complex.continuousAt_arg (by
      rw [hq0]
      exact Or.inl (by norm_num))).comp
    exact (continuous_subtype_val.comp q.continuous).continuousAt
  have hI : Set.Ioo (-ε) ε ∈ 𝓝 (r t₀) := by
    rw [hr0]
    exact Ioo_mem_nhds (neg_lt_zero.mpr hε) hε
  filter_upwards [hcont.eventually hI] with t ht
  refine ⟨r t, ht, ?_⟩
  have hexp : Circle.exp (r t) = q t := Circle.exp_arg (q t)
  rw [hexp]
  simp [q]

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
  let q : C(ℝ, Circle) := ⟨fun r => (ℓ t₀)⁻¹ * ℓ (t₀ * Circle.exp r), by fun_prop⟩
  have hq0 : q 0 = 1 := by simp [q]
  have hqc : Continuous fun r => ((q r : Circle) : ℂ) := continuous_subtype_val.comp q.continuous
  have hU : (fun r => ((q r : Circle) : ℂ)) ⁻¹' Complex.slitPlane ∩
      (fun r : ℝ => t₀ * Circle.exp r) ⁻¹' N ∈ 𝓝 (0 : ℝ) := by
    apply Filter.inter_mem
    · apply hqc.continuousAt.preimage_mem_nhds
      apply Complex.isOpen_slitPlane.mem_nhds
      rw [hq0]; exact Or.inl (by norm_num)
    · have hc : Continuous fun r : ℝ => t₀ * Circle.exp r := by fun_prop
      apply hc.continuousAt.preimage_mem_nhds
      simpa using hN
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hU
  set ε := min (ε₀ / 2) 1 with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hε2 : 2 * ε ≤ ε₀ := by have := min_le_left (ε₀ / 2) 1; linarith
  have hmem : ∀ r ∈ Ioo (-2 * ε) (2 * ε),
      ((q r : Circle) : ℂ) ∈ Complex.slitPlane ∧ t₀ * Circle.exp r ∈ N := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  let Φ : ℝ → ℝ := fun r => Complex.arg ((q r : Circle) : ℂ)
  have hΦexp : ∀ r, Circle.exp (Φ r) = q r := fun r => Circle.exp_arg (q r)
  have hΦeq : ∀ r ∈ Ioo (-2 * ε) (2 * ε), ℓ (t₀ * Circle.exp r) = ℓ t₀ * Circle.exp (Φ r) := by
    intro r _
    rw [hΦexp]
    simp [q]
  have hΦc : ContinuousOn Φ (Ioo (-2 * ε) (2 * ε)) := by
    intro r hr
    exact ((Complex.continuousAt_arg (hmem r hr).1).comp
      (f := fun r => ((q r : Circle) : ℂ)) hqc.continuousAt).continuousWithinAt
  have hΦi : InjOn Φ (Ioo (-2 * ε) (2 * ε)) := by
    intro r hr r' hr' h
    have h1 : q r = q r' := by rw [← hΦexp, ← hΦexp, h]
    have h2 : ℓ (t₀ * Circle.exp r) = ℓ (t₀ * Circle.exp r') := by
      have := congrArg (fun z => ℓ t₀ * z) h1
      simpa [q] using this
    have h3 := mul_left_cancel (hinj (hmem r hr).2 (hmem r' hr').2 h2)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h3
    have hm0 : m = 0 := by
      by_contra hm0
      have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
      have hpi := Real.pi_gt_three
      have heq : |r - r'| = |(m : ℝ)| * (2 * Real.pi) := by
        rw [hm, show r' + (m : ℝ) * (2 * Real.pi) - r' = (m : ℝ) * (2 * Real.pi) by ring, abs_mul,
          abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have hlt : |r - r'| < 4 := by
        rw [abs_lt]; constructor <;> linarith [hr.1, hr.2, hr'.1, hr'.2]
      nlinarith
    rw [hm0] at hm
    simpa using hm
  refine ⟨ε, hεpos, Φ, ?_, hΦc, hΦc.strictMonoOn_of_injOn_Ioo (by linarith) hΦi, hΦeq, ?_⟩
  · simp [Φ, hq0]
  · filter_upwards [eventually_exists_small_exp_coordinate (ContinuousMap.id Circle) t₀ hεpos]
      with t ⟨a, ha, heq⟩
    exact ⟨a, ha, heq⟩

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


/-- A continuous circle map injective near `t₀` maps every neighbourhood of `t₀` over a
nondegenerate open arc. -/
lemma locally_injective_circle_image_contains_arc
    (ℓ : C(Circle, Circle)) (t₀ : Circle) (N : Set Circle) (hN : N ∈ 𝓝 t₀)
    (hinj : Set.InjOn ℓ N) (N' : Set Circle) (hN' : N' ∈ 𝓝 t₀) :
    ∃ w : Circle, ∃ a b : ℝ, a < b ∧
      (fun r ↦ w * Circle.exp r) '' Set.Ioo a b ⊆ ℓ '' (N' ∩ N) := by
  obtain ⟨ε, hε, Φ, _, hΦc, hdir, hΦeq, _⟩ := circle_locally_monotone_aux_chart ℓ t₀ N hN hinj
  have hc : Continuous fun r : ℝ => t₀ * Circle.exp r := by fun_prop
  have hpre : (fun r : ℝ => t₀ * Circle.exp r) ⁻¹' (N' ∩ N) ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using Filter.inter_mem hN' hN)
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set u := min (ε₁ / 2) ε with hu
  have hupos : 0 < u := lt_min (by linarith) hε
  have hu1 : u ≤ ε₁ / 2 := min_le_left _ _
  have hu2 : u ≤ ε := min_le_right _ _
  have hIcc : Set.uIcc (-u) u ⊆ Set.Ioo (-2 * ε) (2 * ε) := by
    intro r hr
    rw [Set.uIcc_of_le (by linarith)] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hN'r : ∀ r ∈ Set.uIcc (-u) u, t₀ * Circle.exp r ∈ N' ∩ N := by
    intro r hr
    rw [Set.uIcc_of_le (by linarith)] at hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hm : -u ∈ Set.Ioo (-2 * ε) (2 * ε) := hIcc (Set.left_mem_uIcc)
  have hp : u ∈ Set.Ioo (-2 * ε) (2 * ε) := hIcc (Set.right_mem_uIcc)
  have hne : Φ (-u) ≠ Φ u := by
    rcases hdir with h | h
    · exact (h hm hp (by linarith)).ne
    · exact (h hm hp (by linarith)).ne'
  refine ⟨ℓ t₀, min (Φ (-u)) (Φ u), max (Φ (-u)) (Φ u),
    min_lt_max.mpr hne, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ Set.uIcc (Φ (-u)) (Φ u) := Set.Ioo_subset_Icc_self hy
  obtain ⟨r, hr, hry⟩ := intermediate_value_uIcc (hΦc.mono hIcc) hy'
  refine ⟨t₀ * Circle.exp r, hN'r r hr, ?_⟩
  simp only
  rw [hΦeq r (hIcc hr), hry]

#print axioms circle_locally_monotone

end t00J02_ModelProduct
