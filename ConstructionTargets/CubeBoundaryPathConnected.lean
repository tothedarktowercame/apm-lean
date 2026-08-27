import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Subpath

/-! # Path connectedness of finite cube boundaries -/

open Set Function
open scoped Topology unitInterval
noncomputable section

namespace ConstructionTargets.CubeBoundaryPathConnected

/-- The coordinatewise straight path inside a cube. -/
def cubeSegment {N : Type*} (x y : I^N) : Path x y where
  toFun t i := Icc.convexCombo (x i) (y i) t
  continuous_toFun := by fun_prop
  source' := by ext i; simp [Icc.convexCombo]
  target' := by ext i; simp [Icc.convexCombo]

theorem cubeSegment_mem_boundary_of_coordinate_eq
    {N : Type*} (x y : I^N) (i : N) (e : I)
    (he : e = 0 ∨ e = 1) (hx : x i = e) (hy : y i = e) (t : I) :
    cubeSegment x y t ∈ Cube.boundary N := by
  refine ⟨i, ?_⟩
  rw [show cubeSegment x y t i = e by
    apply Subtype.ext
    simp [cubeSegment, hx, hy, Icc.convexCombo]
    ring]
  exact he

theorem joinedIn_boundary_of_shared_face
    {N : Type*} (x y : I^N) (i : N) (e : I)
    (he : e = 0 ∨ e = 1) (hx : x i = e) (hy : y i = e) :
    JoinedIn (Cube.boundary N) x y :=
  ⟨cubeSegment x y,
    cubeSegment_mem_boundary_of_coordinate_eq x y i e he hx hy⟩

/-- The boundary of an `n`-cube is path connected as soon as there is a spare
coordinate.  A point first moves within its witnessed face to a point on a
zero face, then moves within that zero face to the all-zero corner. -/
theorem cubeBoundary_isPathConnected (n : ℕ) (hn : 2 ≤ n) :
    IsPathConnected (Cube.boundary (Fin n)) := by
  let z : I^(Fin n) := fun _ => 0
  have hz : z ∈ Cube.boundary (Fin n) := by
    let i : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) hn⟩
    exact ⟨i, Or.inl rfl⟩
  refine ⟨z, hz, ?_⟩
  intro x hx
  obtain ⟨i, hi0 | hi1⟩ := hx
  · exact (joinedIn_boundary_of_shared_face x z i 0 (Or.inl rfl) hi0 rfl).symm
  · letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨j, hji⟩ := exists_ne i
    let y : I^(Fin n) := Function.update x j 0
    have hyi : y i = 1 := by simp [y, hji.symm, hi1]
    have hyj : y j = 0 := by simp [y]
    have hzj : z j = 0 := rfl
    exact ((joinedIn_boundary_of_shared_face x y i 1 (Or.inr rfl) hi1 hyi).trans
      (joinedIn_boundary_of_shared_face y z j 0 (Or.inl rfl) hyj hzj)).symm

theorem cubeBoundary_pathConnectedSpace (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace ↥(Cube.boundary (Fin n)) :=
  isPathConnected_iff_pathConnectedSpace.mp (cubeBoundary_isPathConnected n hn)

#print axioms cubeSegment_mem_boundary_of_coordinate_eq
#print axioms joinedIn_boundary_of_shared_face
#print axioms cubeBoundary_isPathConnected
#print axioms cubeBoundary_pathConnectedSpace

end ConstructionTargets.CubeBoundaryPathConnected
