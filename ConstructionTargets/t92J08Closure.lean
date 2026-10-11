import Mathlib.Analysis.ODE.PicardLindelof

/-! # Uniform local flow input for t92J08 -/

open Set

noncomputable section

namespace t92J08Closure

open Classical

theorem exists_uniform_local_flow_in_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (x₀ : E) (hf : ContDiffAt ℝ 1 f x₀)
    (s : Set E) (hs : s ∈ nhds x₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℝ, 0 < r ∧ ∃ α : E → ℝ → E,
      ∀ x ∈ Metric.closedBall x₀ r,
        α x 0 = x ∧
        α x '' Ioo (-ε) ε ⊆ s ∧
        ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (f (α x t)) t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε₀, hε₀, a, r₀, L, K, hr₀, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one hf
  have hr₀a : r₀ ≤ a := by
    have hnonneg : (0 : ℝ) ≤ (L : ℝ) * ε₀ := mul_nonneg L.coe_nonneg hε₀.le
    have hbound : (L : ℝ) * ε₀ ≤ (a : ℝ) - (r₀ : ℝ) := by
      simpa using (hpl 0).mul_max_le
    exact_mod_cast (sub_nonneg.mp (hnonneg.trans hbound))
  let b : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a b
  have ha' : 0 < a' := by
    apply lt_min (lt_of_lt_of_le hr₀ hr₀a)
    exact_mod_cast (half_pos hδ)
  let r' : NNReal := a' / 2
  have hr'a' : r' < a' := by simpa [r'] using half_lt_self ha'
  obtain ⟨ε, hε, hpl'⟩ :=
    (hpl 0).exists_shrink_radius hε₀ (show a' ≤ a from min_le_left _ _) hr'a'
  have htarget : Metric.closedBall x₀ (a' : ℝ) ⊆ s := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    exact lt_of_le_of_lt (show (a' : ℝ) ≤ (b : ℝ) by exact_mod_cast min_le_right a b)
      (by simpa [b] using half_lt_self hδ)
  have hfixed (x : E) (hx : x ∈ Metric.closedBall x₀ (r' : ℝ)) :=
    ODE.FunSpace.exists_isFixedPt_next hpl' hx
  choose φ hφ using hfixed
  set α : E → ℝ → E := fun x ↦
    if hx : x ∈ Metric.closedBall x₀ (r' : ℝ) then (φ x hx).compProj else 0 with hα
  refine ⟨ε, hε, r', by exact_mod_cast (half_pos ha'), α, ?_⟩
  intro x hx
  have hα0 : α x 0 = x := by
    rw [hα]
    beta_reduce
    rw [dif_pos hx, ODE.FunSpace.compProj_apply,
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc (0 - ε) (0 + ε) by constructor <;> linarith),
      ← hφ, ODE.FunSpace.next_apply₀]
  refine ⟨hα0, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    apply htarget
    rw [hα]
    beta_reduce
    rw [dif_pos hx]
    exact (φ x hx).compProj_mem_closedBall hpl'.mul_max_le
  · intro t ht
    have ht' : t ∈ Ioo (0 - ε) (0 + ε) := by simpa using ht
    have hwithin : HasDerivWithinAt (α x) (f (α x t))
        (Icc (0 - ε) (0 + ε)) t := by
      rw [hα]
      beta_reduce
      rw [dif_pos hx, ODE.FunSpace.compProj_apply]
      apply ODE.hasDerivWithinAt_picard_Icc (t₀ := (0 : ℝ))
        (by simp [le_of_lt hε]) hpl'.continuousOn_uncurry
        (φ x hx).continuous_compProj.continuousOn
        (fun _ _ ↦ (φ x hx).compProj_mem_closedBall hpl'.mul_max_le) x
        (Ioo_subset_Icc_self ht') |>.congr_of_mem _ (Ioo_subset_Icc_self ht')
      intro t' ht'
      nth_rw 1 [← hφ]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    exact hwithin.hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

end t92J08Closure

#print axioms t92J08Closure.exists_uniform_local_flow_in_nhds
