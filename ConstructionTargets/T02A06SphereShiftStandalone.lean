import ConstructionTargets.SingularExcision

/-!
# Standalone boundary for the positive sphere-homology shift

The algebraic inputs to `spherePositiveHomologyShift` are available:

* `subcomplexUnionRelativeIso` identifies the two cokernels associated to a
  union of *simplicial subcomplexes*;
* `singularPairConnecting` and the three `singularPairHomology_exact_*`
  theorems provide the long exact sequence of a topological pair;
* `contractibleHigherHomology_isZero` supplies the required vanishing once a
  hemisphere has been identified as contractible.

What is not currently present is the geometric comparison joining these
pieces: there is no construction of hemisphere singular subcomplexes, no
proof that their union computes all sphere chains (using subdivision), and no
relative-homology excision isomorphism identifying the resulting quotient
with the pair used by `singularPairConnecting`.  Consequently the exact
statement below cannot yet be constructed from the axiom-clean public API.

This module deliberately contains no axiom, theorem placeholder, or `sorry`.
It fixes the exact target type and checks the public inputs at the boundary.
-/

noncomputable section

namespace ConstructionTargets.T02A06SphereShiftStandalone

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

abbrev EuclideanUnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

/-- The exact type of the missing construction, kept here without introducing
an axiom or an opaque placeholder. -/
abbrev SpherePositiveHomologyShiftType (n k : ℕ) :=
  H (k + 1) (EuclideanUnitSphere (n + 1)) ≅
    H k (EuclideanUnitSphere n)

#check subcomplexUnionRelativeIso
#check excisionCover_homologyMap_isIso_succ
#check singularPairConnecting
#check singularPairHomology_exact_subspace
#check singularPairHomology_exact_absolute
#check singularPairHomology_exact_relative
#check contractibleHigherHomology_isZero

end ConstructionTargets.T02A06SphereShiftStandalone
