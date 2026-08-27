import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence

/-!
# Euclidean adapter for a sphere with two antipodal points removed

This file specializes the coordinate-free radial equivalence to the standard
Euclidean spheres.  The only dimension-dependent step is the standard
orthonormal-basis equivalence from the orthogonal complement of a pole in
`Fin (n + 1)` coordinates to `Fin n` coordinates.
-/

noncomputable section

namespace ConstructionTargets.EuclideanSpherePoleOverlapAdapter

open ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
open scoped ContinuousMap

/-- The ambient Euclidean space for the concrete `n`-sphere. -/
abbrev EuclideanAmbient (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- The Euclidean coordinate space of the equatorial sphere. -/
abbrev EuclideanLower (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The concrete metric sphere convention used by the topology problems. -/
abbrev EuclideanSphere (n : ℕ) := UnitSphere (EuclideanAmbient n)

/-- A coordinate pole.  Index `0` exists in `Fin (n + 1)`, including when
`n = 0`. -/
def canonicalPoleVector (n : ℕ) : EuclideanAmbient n :=
  EuclideanSpace.single 0 1

@[simp]
theorem norm_canonicalPoleVector (n : ℕ) : ‖canonicalPoleVector n‖ = 1 := by
  simp [canonicalPoleVector]

/-- The coordinate pole as a point of the concrete sphere. -/
def canonicalPole (n : ℕ) : EuclideanSphere n :=
  polePoint (canonicalPoleVector n) (norm_canonicalPoleVector n)

/-- The orthogonal complement of the coordinate pole is linearly isometric
to the expected `n`-dimensional Euclidean space.  This statement is valid at
`n = 0`; both sides are then zero-dimensional. -/
def canonicalPoleOrthogonalLinearIsometryEquiv (n : ℕ) :
    ((ℝ ∙ canonicalPoleVector n)ᗮ) ≃ₗᵢ[ℝ] EuclideanLower n := by
  letI : Fact (Module.finrank ℝ (EuclideanAmbient n) = n + 1) := ⟨by simp⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (by
      intro h
      have := norm_canonicalPoleVector n
      rw [h, norm_zero] at this
      norm_num at this)).repr

/-- A linear isometry equivalence restricts to a homeomorphism of unit
spheres. -/
def unitSphereHomeomorphOfLinearIsometryEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) : UnitSphere E ≃ₜ UnitSphere F where
  toFun x := ⟨e x.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2⟩
  invFun y := ⟨e.symm y.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The unit sphere in the pole's orthogonal complement is the concrete
Euclidean `(n-1)`-sphere model (written with `Fin n` coordinates). -/
def canonicalOrthogonalSphereHomeomorph (n : ℕ) :
    UnitSphere ((ℝ ∙ canonicalPoleVector n)ᗮ) ≃ₜ UnitSphere (EuclideanLower n) :=
  unitSphereHomeomorphOfLinearIsometryEquiv
    (canonicalPoleOrthogonalLinearIsometryEquiv n)

/-- The concrete `n`-sphere with the coordinate pole and antipode removed. -/
abbrev EuclideanTwoPoleComplement (n : ℕ) :=
  TwoPoleComplement (canonicalPoleVector n) (norm_canonicalPoleVector n)

/-- Removing the two coordinate poles from the concrete Euclidean `n`-sphere
is homotopy equivalent to the unit sphere in `Fin n` coordinates. -/
def euclideanTwoPoleComplementHomotopyEquiv (n : ℕ) :
    EuclideanTwoPoleComplement n ≃ₕ UnitSphere (EuclideanLower n) :=
  (twoPoleComplementHomotopyEquivOrthogonalSphere
      (canonicalPoleVector n) (norm_canonicalPoleVector n)).trans
    (canonicalOrthogonalSphereHomeomorph n).toHomotopyEquiv

/-- Product transport of the concrete two-pole overlap equivalence. -/
def euclideanTwoPoleComplementProductHomotopyEquiv
    (n : ℕ) (Y : Type*) [TopologicalSpace Y] :
    (EuclideanTwoPoleComplement n × Y) ≃ₕ
      (UnitSphere (EuclideanLower n) × Y) :=
  (euclideanTwoPoleComplementHomotopyEquiv n).prodCongr
    (ContinuousMap.HomotopyEquiv.refl Y)

#print axioms norm_canonicalPoleVector
#print axioms canonicalPoleOrthogonalLinearIsometryEquiv
#print axioms unitSphereHomeomorphOfLinearIsometryEquiv
#print axioms canonicalOrthogonalSphereHomeomorph
#print axioms euclideanTwoPoleComplementHomotopyEquiv
#print axioms euclideanTwoPoleComplementProductHomotopyEquiv

end ConstructionTargets.EuclideanSpherePoleOverlapAdapter
