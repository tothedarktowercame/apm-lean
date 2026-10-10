import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology

/-! Explicit affine coordinates on complex projective space and the local
index of a nondegenerate fixed point in those coordinates. Existence of the
claimed open charts is a construction proposition, not an assumed inhabitant.
The ratio maps use the actual projectivization representatives; proving their
scale independence and continuity is part of realizing the open charts.
-/

noncomputable section
namespace ConstructionTargets.ComplexProjectiveChartTargets
open ProjectiveSpaceTopology

abbrev CP (n : ℕ) := Space ℂ n
abbrev AffineCoordinates {n : ℕ} (i : Fin (n + 1)) := {j : Fin (n + 1) // j ≠ i} → ℂ

def coordinates {n : ℕ} (i : Fin (n + 1)) (x : CP n) : AffineCoordinates i :=
  fun j => Projectivization.rep x j.val / Projectivization.rep x i

def chartInverse {n : ℕ} (i : Fin (n + 1)) (z : AffineCoordinates i) : CP n :=
  quotientMap ℂ n ⟨fun j => if h : j = i then 1 else z ⟨j,h⟩, by
    intro h
    have hi := congrFun h i
    simp at hi⟩

theorem affineSource_preimage {n : ℕ} (i : Fin (n + 1)) :
    quotientMap ℂ n ⁻¹' {x : CP n | Projectivization.rep x i ≠ 0} =
      {v : NonzeroVectors ℂ n | v.1 i ≠ 0} := by
  ext v
  change (Projectivization.mk ℂ v.1 v.2).rep i ≠ 0 ↔ v.1 i ≠ 0
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.1 v.2
  rw [← ha]
  change a.1 * v.1 i ≠ 0 ↔ v.1 i ≠ 0
  simp

theorem affineSource_isOpen {n : ℕ} (i : Fin (n + 1)) :
    IsOpen {x : CP n | Projectivization.rep x i ≠ 0} := by
  rw [isOpen_coinduced]
  rw [affineSource_preimage i]
  change IsOpen ((fun v : NonzeroVectors ℂ n => v.1 i) ⁻¹' ({0}ᶜ : Set ℂ))
  exact isOpen_compl_singleton.preimage
    ((continuous_apply i).comp continuous_subtype_val)

@[simp] theorem coordinates_chartInverse {n : ℕ} (i : Fin (n + 1))
    (z : AffineCoordinates i) :
    coordinates i (chartInverse i z) = z := by
  funext j
  let v : Fin (n + 1) → ℂ := fun k => if h : k = i then 1 else z ⟨k, h⟩
  have hv : v ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [v] at hi
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (Projectivization.mk ℂ v hv).rep j.1 /
      (Projectivization.mk ℂ v hv).rep i = z j
  rw [← ha]
  change (a.1 * v j.1) / (a.1 * v i) = z j
  simp [v, j.2]

theorem chartInverse_coordinates {n : ℕ} (i : Fin (n + 1))
    (x : CP n) (hx : Projectivization.rep x i ≠ 0) :
    chartInverse i (coordinates i x) = x := by
  rw [← Projectivization.mk_rep x]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(Projectivization.rep x i)⁻¹, ?_⟩
  funext k
  by_cases h : k = i
  · subst k
    simp [hx]
  · simp [coordinates, h, div_eq_inv_mul]

/-- These must be the actual affine charts of the already fixed quotient topology. -/
def AffineChartConstruction (n : ℕ) : Prop :=
  ∀ i : Fin (n + 1), ∃ e : OpenPartialHomeomorph (CP n) (AffineCoordinates i),
    e.source = {x : CP n | Projectivization.rep x i ≠ 0} ∧ e.target = Set.univ ∧
    (∀ x ∈ e.source, e x = coordinates i x) ∧ e.symm = chartInverse i ∧
    coordinateLine ℂ n i ∈ e.source ∧ e (coordinateLine ℂ n i) = 0 ∧
    e.symm 0 = coordinateLine ℂ n i

def localMap {n : ℕ} (f : CP n → CP n) (i : Fin (n + 1)) :
    AffineCoordinates i → AffineCoordinates i :=
  coordinates i ∘ f ∘ chartInverse i

/-- Real determinant of id-Df in the affine complex coordinates. -/
def fixedPointDeterminant {n : ℕ} (f : CP n → CP n) (i : Fin (n + 1)) : ℝ :=
  (ContinuousLinearMap.id ℝ (AffineCoordinates i) -
    fderiv ℝ (localMap f i) 0).toLinearMap.det

/-- Local Lefschetz index in the nondegenerate case; zero marks degeneracy. -/
def localIndex {n : ℕ} (f : CP n → CP n) (i : Fin (n + 1)) : ℤ :=
  let d := fixedPointDeterminant f i
  if 0 < d then 1 else if d < 0 then -1 else 0

end ConstructionTargets.ComplexProjectiveChartTargets
