import Mathlib
import ApmCanaries.Frames.T94A02.Apm_v2_t94A02_1775009748581.Scratch

noncomputable section

open scoped Topology

namespace ApmCanaries.Frames.T94A02.Apm_v2_t94A02_1775009748581.Main

/-- Auxiliary distance-to-a-set function that is constant `1` on empty sets. -/
def distTo (S : Set ℝ) (x : ℝ) : ℝ :=
  if S = ∅ then 1 else Metric.infDist x S

lemma distTo_nonneg (S : Set ℝ) (x : ℝ) : 0 ≤ distTo S x := by
  classical
  by_cases h : S = ∅
  · simp [distTo, h]
  · simpa [distTo, h] using Metric.infDist_nonneg (x := x) (s := S)

lemma continuous_distTo (S : Set ℝ) : Continuous fun x : ℝ => distTo S x := by
  classical
  by_cases h : S = ∅
  · simpa [distTo, h] using continuous_const
  · simpa [distTo, h] using Metric.continuous_infDist_pt (s := S)

lemma distTo_eq_zero_iff {S : Set ℝ} (hS : IsClosed S) (x : ℝ) :
    distTo S x = 0 ↔ x ∈ S := by
  classical
  by_cases h : S = ∅
  · subst h
    simp [distTo]
  ·
    have hne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h
    simpa [distTo, h] using (hS.mem_iff_infDist_zero hne).symm

lemma distTo_add_pos {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) (x : ℝ) :
    0 < distTo A x + distTo B x := by
  classical
  by_cases hAemp : A = ∅
  ·
    have hBnonneg : 0 ≤ distTo B x := distTo_nonneg B x
    have : 0 < 1 + distTo B x :=
      add_pos_of_pos_of_nonneg zero_lt_one hBnonneg
    simpa [distTo, hAemp, add_comm] using this
  by_cases hBemp : B = ∅
  ·
    have hAnonneg : 0 ≤ distTo A x := distTo_nonneg A x
    have : 0 < distTo A x + 1 :=
      add_pos_of_nonneg_of_pos hAnonneg zero_lt_one
    simpa [distTo, hBemp, add_comm] using this
  have hA0 : distTo A x = 0 ↔ x ∈ A := distTo_eq_zero_iff hA x
  have hB0 : distTo B x = 0 ↔ x ∈ B := distTo_eq_zero_iff hB x
  have hApos := distTo_nonneg A x
  have hBpos := distTo_nonneg B x
  have hsum_ne : distTo A x + distTo B x ≠ 0 := by
    intro hzero
    have hALe : distTo A x ≤ 0 := by
      have := le_of_eq hzero
      have : distTo A x ≤ distTo A x + distTo B x :=
        le_add_of_nonneg_right hBpos
      exact this.trans_eq hzero
    have hAeq : distTo A x = 0 :=
      le_antisymm hALe hApos
    have hBLe : distTo B x ≤ 0 := by
      have : distTo B x ≤ distTo A x + distTo B x :=
        le_add_of_nonneg_left hApos
      exact this.trans_eq hzero
    have hBeq : distTo B x = 0 :=
      le_antisymm hBLe hBpos
    have hxA : x ∈ A := (hA0).1 hAeq
    have hxB : x ∈ B := (hB0).1 hBeq
    have hx : x ∈ A ∩ B := ⟨hxA, hxB⟩
    exact hdisj.le_bot hx
  have hsum_nonneg : 0 ≤ distTo A x + distTo B x :=
    add_nonneg hApos hBpos
  exact lt_of_le_of_ne' hsum_nonneg hsum_ne

/-- The normalized separator map. -/
def sepFun (A B : Set ℝ) (x : ℝ) : ℝ :=
  distTo A x / (distTo A x + distTo B x)

lemma sepFun_den_ne_zero {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) (x : ℝ) :
    distTo A x + distTo B x ≠ 0 :=
  (distTo_add_pos hA hB hdisj x).ne'

lemma sepFun_eq_zero_iff {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) (x : ℝ) :
    sepFun A B x = 0 ↔ x ∈ A := by
  classical
  have hden := sepFun_den_ne_zero hA hB hdisj x
  simp [sepFun, hden, distTo_eq_zero_iff hA x]

lemma sepFun_eq_one_iff {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) (x : ℝ) :
    sepFun A B x = 1 ↔ x ∈ B := by
  classical
  have hden := sepFun_den_ne_zero hA hB hdisj x
  constructor
  · intro h
    have h' :
        distTo A x = distTo A x + distTo B x :=
      (div_eq_one_iff_eq hden).1 h
    have hxBzero' : 0 = distTo B x := by
      have := congrArg (fun t => t - distTo A x) h'
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hxBzero : distTo B x = 0 := by simpa using hxBzero'.symm
    simpa [distTo_eq_zero_iff hB x] using hxBzero
  · intro hxB
    have hxB' : distTo B x = 0 := by
      simpa [distTo_eq_zero_iff hB x] using hxB
    have hnum :
        distTo A x = distTo A x + distTo B x := by
      simp [hxB']
    exact (div_eq_one_iff_eq hden).2 hnum

lemma sepFun_mem_Icc {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) (x : ℝ) :
    sepFun A B x ∈ Set.Icc (0 : ℝ) 1 := by
  have hdenpos := distTo_add_pos hA hB hdisj x
  have hAnonneg := distTo_nonneg A x
  have hBnonneg := distTo_nonneg B x
  refine ⟨?_, ?_⟩
  · exact div_nonneg hAnonneg hdenpos.le
  ·
    have hdenpos' : 0 < distTo A x + distTo B x := hdenpos
    have hle :
        distTo A x ≤ distTo A x + distTo B x :=
      le_add_of_nonneg_right hBnonneg
    exact (div_le_one hdenpos').2 hle

lemma continuous_sepFun {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)
    (hdisj : Disjoint A B) :
    Continuous fun x : ℝ => sepFun A B x := by
  classical
  apply Continuous.div (continuous_distTo A)
  · exact (continuous_distTo A).add (continuous_distTo B)
  · intro x
    exact sepFun_den_ne_zero hA hB hdisj x

/-- Main separation theorem specialized to ℝ. -/
theorem separate_closed_sets {A B : Set ℝ}
    (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      f '' Set.univ ⊆ Set.Icc (0 : ℝ) 1 ∧
      f ⁻¹' {0} = A ∧ f ⁻¹' {1} = B := by
  classical
  refine ⟨sepFun A B, ?_, ?_, ?_, ?_⟩
  · exact continuous_sepFun hA hB hdisj
  · intro y hy
    rcases hy with ⟨x, -, rfl⟩
    exact sepFun_mem_Icc hA hB hdisj x
  · ext x
    simp [sepFun_eq_zero_iff hA hB hdisj x]
  · ext x
    simp [sepFun_eq_one_iff hA hB hdisj x]

end ApmCanaries.Frames.T94A02.Apm_v2_t94A02_1775009748581.Main
