import ConstructionTargets.ProjectiveQuotientDescent
import ConstructionTargets.ComplexProjectiveChartTargets

open Set Topology
open scoped LinearAlgebra.Projectivization

noncomputable section
namespace ConstructionTargets.T99J05ArbitraryAffineChartContinuity

open ProjectiveSpaceTopology ProjectiveQuotientDescent
open ComplexProjectiveChartTargets

theorem t99J05_coordinates_continuousOn {n : ℕ} (i : Fin (n + 1)) :
    ContinuousOn (coordinates i)
      {x : CP n | Projectivization.rep x i ≠ 0} := by
  let s : Set (CP n) := {x | Projectivization.rep x i ≠ 0}
  let q : NonzeroVectors ℂ n → CP n := quotientMap ℂ n
  let qr := s.restrictPreimage q
  have hqr : IsOpenQuotientMap qr := by
    refine ⟨?_, continuous_quotientMap ℂ n |>.restrictPreimage, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ := surjective_quotientMap ℂ n x
      exact ⟨⟨v, hx⟩, rfl⟩
    · exact (projectiveQuotientMap_isOpen ℂ n).restrictPreimage s
  rw [continuousOn_iff_continuous_restrict]
  apply hqr.isQuotientMap.continuous_iff.mpr
  apply continuous_pi
  intro j
  have hnum : Continuous (fun v : q ⁻¹' s => v.1.1 j.1) :=
    (continuous_apply j.1).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hden : Continuous (fun v : q ⁻¹' s => v.1.1 i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hden0 : ∀ v : q ⁻¹' s, v.1.1 i ≠ 0 := by
    intro v
    have hv := v.2
    change quotientMap ℂ n v.1 ∈
      {x : CP n | Projectivization.rep x i ≠ 0} at hv
    have heq := Set.ext_iff.mp
      (ConstructionTargets.ComplexProjectiveChartTargets.affineSource_preimage i) v.1
    exact heq.mp hv
  convert hnum.div hden hden0 using 1
  funext v
  change Projectivization.rep (quotientMap ℂ n v.1) j.1 /
      Projectivization.rep (quotientMap ℂ n v.1) i = v.1.1 j.1 / v.1.1 i
  change (Projectivization.mk ℂ v.1.1 v.1.2).rep j.1 /
      (Projectivization.mk ℂ v.1.1 v.1.2).rep i = _
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1.1 v.1.2
  rw [← ha]
  change (a.1 * v.1.1 j.1) / (a.1 * v.1.1 i) = _
  field_simp

theorem t99J05_chartInverse_continuous {n : ℕ} (i : Fin (n + 1)) :
    Continuous (chartInverse i) := by
  apply (continuous_quotientMap ℂ n).comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases h : j = i
  · subst j
    simpa only [dif_pos] using
      (continuous_const : Continuous (fun _ : AffineCoordinates i => (1 : ℂ)))
  · simpa only [dif_neg h] using
      (continuous_apply (⟨j, h⟩ : {k : Fin (n + 1) // k ≠ i}) :
        Continuous (fun z : AffineCoordinates i => z ⟨j, h⟩))

theorem t99J05_affine_chart_continuity_package :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      ContinuousOn (coordinates i)
          {x : CP n | Projectivization.rep x i ≠ 0} ∧
        Continuous (chartInverse i) := by
  exact fun _ i => ⟨t99J05_coordinates_continuousOn i,
    t99J05_chartInverse_continuous i⟩

end ConstructionTargets.T99J05ArbitraryAffineChartContinuity
