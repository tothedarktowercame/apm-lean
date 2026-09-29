import ConstructionTargets.T94A08ProjectiveQuotientOpen
import ConstructionTargets.ComplexProjectiveChartTargets

open Set Topology
open scoped LinearAlgebra.Projectivization
noncomputable section

namespace ConstructionTargets.T94A08ProjectiveConic

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ComplexProjectiveChartTargets

theorem continuous_chartInverse (i : Fin 3) :
    Continuous (chartInverse i) := by
  unfold chartInverse
  apply (continuous_quotientMap ℂ 2).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simp only [dif_pos]
    show Continuous (fun _ : AffineCoordinates i => (1 : ℂ))
    exact continuous_const
  · simpa only [dif_neg h] using
      (continuous_apply (⟨j, h⟩ : {k : Fin 3 // k ≠ i}) :
        Continuous fun z : AffineCoordinates i => z ⟨j, h⟩)

theorem coordinateLine_mem_affineSource (i : Fin 3) :
    Projectivization.rep (coordinateLine ℂ 2 i) i ≠ 0 := by
  intro h
  have hm := Projectivization.mk_rep (coordinateLine ℂ 2 i)
  rw [coordinateLine] at hm
  have he := (Projectivization.mk_eq_mk_iff ℂ _ _
    (Projectivization.rep_nonzero _) (by
      intro hz
      have hi := congrFun hz i
      simp at hi)).mp hm
  obtain ⟨a, ha⟩ := he
  have hi := congrFun ha i
  change Projectivization.rep
    (quotientMap ℂ 2 ⟨Pi.single i 1, by
      intro hz
      have hk := congrFun hz i
      simp at hk⟩) i = 0 at h
  rw [h] at hi
  apply Units.ne_zero a
  simpa only [Pi.smul_apply, Pi.single_eq_same, Units.smul_def, smul_eq_mul,
    mul_one] using hi

theorem coordinates_coordinateLine (i : Fin 3) :
    coordinates i (coordinateLine ℂ 2 i) = 0 := by
  funext j
  unfold coordinates
  have hi := coordinateLine_mem_affineSource i
  have hm := Projectivization.mk_rep (coordinateLine ℂ 2 i)
  rw [coordinateLine] at hm
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _
    (Projectivization.rep_nonzero _) (by
      intro hz
      have hk := congrFun hz i
      simp at hk)).mp hm
  have hj := congrFun ha j.1
  have hii := congrFun ha i
  simp [j.2] at hj
  simp at hii
  change Projectivization.rep
      (quotientMap ℂ 2 ⟨Pi.single i 1, by
        intro hz
        have hk := congrFun hz i
        simp at hk⟩) j.1 /
      Projectivization.rep
      (quotientMap ℂ 2 ⟨Pi.single i 1, by
        intro hz
        have hk := congrFun hz i
        simp at hk⟩) i = 0
  rw [← hj, ← hii]
  simp

theorem chartInverse_zero (i : Fin 3) :
    chartInverse i 0 = coordinateLine ℂ 2 i := by
  unfold chartInverse coordinateLine
  congr 1
  apply Subtype.ext
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

end ConstructionTargets.T94A08ProjectiveConic
