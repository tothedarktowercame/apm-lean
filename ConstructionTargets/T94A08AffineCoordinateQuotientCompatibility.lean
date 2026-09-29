import ConstructionTargets.T94A08AffineChartInverseNormalization
import ConstructionTargets.T94A08AffineCoordinatePatchTopology

open Set Topology
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace ConstructionTargets.T94A08ProjectiveConic

open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.ProjectiveSpaceTopology

def AffineCoordinateQuotientCompatibility : Prop :=
  ∀ i : Fin 3,
    IsOpen {x : CP 2 | Projectivization.rep x i ≠ 0} ∧
    ContinuousOn (coordinates i)
      {x : CP 2 | Projectivization.rep x i ≠ 0} ∧
    (∀ z, Projectivization.rep (chartInverse i z) i ≠ 0) ∧
    (∀ x, x ∈ {x : CP 2 | Projectivization.rep x i ≠ 0} →
      chartInverse i (coordinates i x) = x) ∧
    (∀ z, coordinates i (chartInverse i z) = z)

theorem chartInverse_mem_affineSource (i : Fin 3)
    (z : AffineCoordinates i) :
    Projectivization.rep (chartInverse i z) i ≠ 0 := by
  unfold chartInverse
  let v : NonzeroVectors ℂ 2 := ⟨fun j => if h : j = i then 1 else z ⟨j, h⟩, by
    intro h
    have hi := congrFun h i
    simp at hi⟩
  change Projectivization.rep (quotientMap ℂ 2 v) i ≠ 0
  apply (quotientMap_rep_coord_ne_zero_iff i v).2
  simpa [v]

theorem coordinates_chartInverse (i : Fin 3)
    (z : AffineCoordinates i) :
    coordinates i (chartInverse i z) = z := by
  unfold chartInverse
  rw [coordinates_quotientMap_eq_vectorRatio i _ (by
    change (if h : i = i then (1 : ℂ) else z ⟨i, h⟩) ≠ 0
    simp)]
  funext j
  simp [j.2]

theorem chartInverse_coordinates (i : Fin 3) (x : CP 2)
    (hx : Projectivization.rep x i ≠ 0) :
    chartInverse i (coordinates i x) = x := by
  unfold chartInverse
  conv_rhs => rw [← Projectivization.mk_rep x]
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ (by
    intro h
    have hi := congrFun h i
    simp at hi) (Projectivization.rep_nonzero x)).2
  let a : ℂˣ := (Units.mk0 (Projectivization.rep x i) hx)⁻¹
  refine ⟨a, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    simpa [a, Units.smul_def, smul_eq_mul] using inv_mul_cancel₀ hx
  · simp only [dif_neg hji, Pi.smul_apply, Units.smul_def, smul_eq_mul]
    unfold coordinates
    change (Projectivization.rep x i)⁻¹ * Projectivization.rep x j =
      Projectivization.rep x j / Projectivization.rep x i
    rw [div_eq_mul_inv]
    ring

theorem affineCoordinateQuotientCompatibility :
    AffineCoordinateQuotientCompatibility := by
  intro i
  exact ⟨(affineCoordinatePatchTopology i).1,
    (affineCoordinatePatchTopology i).2,
    chartInverse_mem_affineSource i,
    chartInverse_coordinates i,
    coordinates_chartInverse i⟩

theorem affineChartConstruction_of_quotientCompatibility
    (h : AffineCoordinateQuotientCompatibility) :
    AffineChartConstruction 2 := by
  intro i
  rcases h i with ⟨hopen, hcont, hinvMem, hleft, hright⟩
  let e : OpenPartialHomeomorph (CP 2) (AffineCoordinates i) := {
    toPartialEquiv := {
      toFun := coordinates i
      invFun := chartInverse i
      source := {x : CP 2 | Projectivization.rep x i ≠ 0}
      target := Set.univ
      map_source' := fun _ _ => Set.mem_univ _
      map_target' := fun z _ => hinvMem z
      left_inv' := hleft
      right_inv' := fun z _ => hright z }
    open_source := hopen
    open_target := isOpen_univ
    continuousOn_toFun := hcont
    continuousOn_invFun := continuous_chartInverse i |>.continuousOn }
  refine ⟨e, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · exact coordinateLine_mem_affineSource i
  · exact coordinates_coordinateLine i
  · exact chartInverse_zero i

end ConstructionTargets.T94A08ProjectiveConic
