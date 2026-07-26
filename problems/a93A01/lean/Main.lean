/-
! # APM a93A01: Uniform continuity ⟺ difference quotient condition

Let f : (0,1) → ℝ. Prove equivalence of:
(a) f is uniformly continuous on (0,1).
(b) ∀ ε > 0, ∃ N > 0, ∀ x,y ∈ (0,1) with x ≠ y,
    |(f(x)-f(y))/(x-y)| > N ⟹ |f(x)-f(y)| < ε.
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric Filter

noncomputable section

abbrev I01 : Set ℝ := Ioo (0 : ℝ) 1

/-- Condition (b). -/
def DiffQuotientCondition (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℝ, 0 < N ∧
      ∀ x ∈ I01, ∀ y ∈ I01, x ≠ y →
        N < |f x - f y| / |x - y| → |f x - f y| < ε

/-- Uniform continuity of f on (0,1). -/
def UnifContOn01 (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ I01, ∀ y ∈ I01,
        |x - y| < δ → |f x - f y| < ε

/-- Bridge: UnifContOn01 ⟹ UniformContinuousOn. -/
lemma unifContOn01_imp (f : ℝ → ℝ) (hf : UnifContOn01 f) :
    UniformContinuousOn f I01 := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hf ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx y hy hxy
  exact hδ x hx y hy (by simpa using hxy)

/-- UC on (0,1) implies f is bounded on (0,1).

    (0,1) is totally bounded ⟹ f's range on (0,1) is totally bounded
    (via restriction + TotallyBounded.image) ⟹ bounded. -/
lemma unifContOn01_bounded {f : ℝ → ℝ} (hf : UnifContOn01 f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ I01, |f x| ≤ B := by
  have h_uc : UniformContinuousOn f I01 := unifContOn01_imp f hf
  have h_uc_restrict : UniformContinuous (I01.restrict f) := h_uc.restrict
  -- (0,1) is totally bounded
  have h_tb_I01 : TotallyBounded (I01 : Set ℝ) := totallyBounded_Ioo 0 1
  -- Transfer to subtype: TotallyBounded (Set.univ : Set I01)
  have h_tb_univ : TotallyBounded (Set.univ : Set I01) := by
    have h_emb := isUniformEmbedding_subtype_val (p := fun x => x ∈ I01)
    have h_iff : TotallyBounded (Subtype.val '' (Set.univ : Set I01)) ↔
        TotallyBounded (Set.univ : Set I01) :=
      totallyBounded_image_iff h_emb.isUniformInducing
    -- h_iff : ∀ s, TotallyBounded (Subtype.val '' s) ↔ TotallyBounded s
    -- We need: TotallyBounded (Set.univ : Set I01)
    -- Subtype.val '' Set.univ = range Subtype.val = I01
    have h_img : Subtype.val '' (Set.univ : Set I01) = (I01 : Set ℝ) := by
      ext x
      constructor
      · rintro ⟨⟨x', hx'⟩, _, rfl⟩
        exact hx'
      · intro hx
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    rw [← h_img] at h_tb_I01
    exact h_iff.mp h_tb_I01
  -- Image of Set.univ under restrict f is totally bounded
  have h_tb_img : TotallyBounded ((I01.restrict f) '' Set.univ) :=
    h_tb_univ.image h_uc_restrict
  -- (I01.restrict f) '' Set.univ = f '' I01
  have h_eq : (I01.restrict f) '' Set.univ = f '' I01 := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  rw [h_eq] at h_tb_img
  -- Totally bounded ⟹ bounded
  have h_bdd : Bornology.IsBounded (f '' I01) := h_tb_img.isBounded
  -- Extract bound using isBounded_iff_subset_closedBall
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp h_bdd
  refine ⟨max r 0, le_max_right r 0, ?_⟩
  intro x hx
  have h_in : f x ∈ f '' I01 := ⟨x, hx, rfl⟩
  have h_sub : f x ∈ Metric.closedBall (0 : ℝ) r := hr h_in
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h_sub
  exact le_trans h_sub (le_max_left r 0)

/-- **(b) ⟹ (a)**. -/
theorem diffQuot_implies_unifCont {f : ℝ → ℝ} (hf : DiffQuotientCondition f) :
    UnifContOn01 f := by
  intro ε hε
  obtain ⟨N, hN_pos, hN⟩ := hf ε hε
  refine ⟨ε / N, by positivity, ?_⟩
  intro x hx y hy hxy_lt
  by_contra hcontra
  push_neg at hcontra
  have hxy_ne : x ≠ y := by
    intro heq
    rw [heq] at hcontra
    simp [sub_self, abs_zero] at hcontra
    linarith
  have hxy_pos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy_ne)
  have hquot : N < |f x - f y| / |x - y| := by
    rw [lt_div_iff₀ hxy_pos]
    have key : N * (ε / N) = ε := mul_div_cancel₀ ε hN_pos.ne'
    nlinarith [hxy_lt, hcontra, hN_pos, key]
  exact absurd (hN x hx y hy hxy_ne hquot) (not_lt_of_ge hcontra)

/-- **(a) ⟹ (b)**. -/
theorem unifCont_implies_diffQuot {f : ℝ → ℝ} (hf : UnifContOn01 f) :
    DiffQuotientCondition f := by
  intro ε hε
  obtain ⟨B, hB_nonneg, hB_bound⟩ := unifContOn01_bounded hf
  obtain ⟨δ, hδ_pos, hδ⟩ := hf ε hε
  -- B' = max B 1 ensures B' > 0
  set B' := max B 1
  have hB'_pos : 0 < B' := lt_max_iff.mpr (Or.inr (by norm_num))
  have hB'_bound : ∀ x ∈ I01, |f x| ≤ B' := fun x hx =>
    (hB_bound x hx).trans (le_max_left B 1)
  -- N = B' + B' / δ... actually just use 2*B'/δ to bound |f x - f y| ≤ 2*B'
  -- |f x - f y| ≤ |f x| + |f y| ≤ 2 * B'
  set N := (2 * B') / δ
  have hN_pos : 0 < N := div_pos (mul_pos (by norm_num) hB'_pos) hδ_pos
  refine ⟨N, hN_pos, ?_⟩
  intro x hx y hy hxy_ne hquot
  have hxy_pos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy_ne)
  -- From quotient > N: |x - y| < |f x - f y| / N ≤ 2*B' / N = 2*B' / (2*B'/δ) = δ
  have hxy_lt_δ : |x - y| < δ := by
    have h1 : |x - y| < |f x - f y| / N := by
      have h2 := (lt_div_iff₀ hxy_pos).mp hquot
      -- h2 : N * |x - y| < |f x - f y|
      rwa [lt_div_iff₀ hN_pos, mul_comm]
    have h_fdiff : |f x - f y| ≤ 2 * B' := by
      have hx' : |f x| ≤ B' := hB'_bound x hx
      have hy' : |f y| ≤ B' := hB'_bound y hy
      calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ B' + B' := by gcongr
        _ = 2 * B' := by ring
    calc |x - y| < |f x - f y| / N := h1
      _ ≤ (2 * B') / N := by gcongr
      _ = δ := by
        rw [div_div_eq_mul_div]
        field_simp
  exact hδ x hx y hy hxy_lt_δ

/-- **Main theorem**. -/
theorem unifCont_iff_diffQuot (f : ℝ → ℝ) :
    UnifContOn01 f ↔ DiffQuotientCondition f :=
  ⟨fun hf => unifCont_implies_diffQuot hf,
   fun hf => diffQuot_implies_unifCont hf⟩

end
