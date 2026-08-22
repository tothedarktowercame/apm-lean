import ConstructionTargets.SingularHomologyConcrete

/-!
# Sphere positive-homology vanishing from the shift and its degree-one endpoint

This isolates the endpoint not contained in `spherePositiveHomologyShift`:
`H₁(S^m) = 0` for `m > 1`.  Once that endpoint is supplied by the degree-one
part of the pair long exact sequence, every positive degree below the sphere
dimension follows formally from the shift.
-/

noncomputable section

namespace ConstructionTargets.T02A06SphereVanishingBridge

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete

abbrev EuclideanUnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

theorem spherePositiveHomology_isZero_of_lt_of_degreeOne
    (shift : ∀ (n k : ℕ), k ≠ 0 →
      (H (k + 1) (EuclideanUnitSphere (n + 1)) ≅
        H k (EuclideanUnitSphere n)))
    (degreeOne : ∀ m : ℕ, 1 < m → IsZero (H 1 (EuclideanUnitSphere m)))
    (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    IsZero (H k (EuclideanUnitSphere n)) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              exact degreeOne (n + 1) (by omega)
          | succ k =>
              have hkn' : k + 1 < n := by omega
              have hz : IsZero (H (k + 1) (EuclideanUnitSphere n)) :=
                ih (k + 1) (by omega) hkn'
              have e : H (k + 1 + 1) (EuclideanUnitSphere (n + 1)) ≅
                  H (k + 1) (EuclideanUnitSphere n) :=
                shift n (k + 1) (by omega)
              exact hz.of_iso e

#print axioms spherePositiveHomology_isZero_of_lt_of_degreeOne

end ConstructionTargets.T02A06SphereVanishingBridge
