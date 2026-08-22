import ConstructionTargets.SingularExcision

/-!
# The exact remaining comparison for `H₁(S¹)`

`SingularHomologyConcrete.intervalBoundaryRelativeH1IsoInt` computes
`H₁(I, ∂I)`.  To turn that computation into the singular homology of the
Euclidean unit circle, one still needs the geometric quotient comparison:
collapsing the two endpoints of the interval induces an isomorphism

`H₁(I, ∂I) ≅ H₁(S¹)`.

The free-chain reassembly theorem in `SingularExcision` does not itself supply
this statement: it compares cokernels attached to a union of *simplicial
subcomplexes*, rather than singular chains of a topological quotient.  This
file records the exact interface and proves that it is the sole missing input
for the scaffold's base computation.
-/

noncomputable section

namespace ConstructionTargets.SphereOneH1Concrete

open CategoryTheory
open ConstructionTargets.SingularHomologyConcrete

abbrev EuclideanUnitSphereOne :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

abbrev SphereOneH1 :=
  (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
    (AddCommGrpCat.of ℤ)).obj (TopCat.of EuclideanUnitSphereOne))

/-- Once the endpoint-collapse comparison is available, the already-proved
relative interval computation closes `H₁(S¹) ≅ ℤ` immediately. -/
noncomputable def sphereOneH1IsoIntOfRelativeIntervalComparison
    (quotientComparison :
      (RelativeSingularChains intervalBoundary).homology 1 ≅ SphereOneH1) :
    SphereOneH1 ≅ AddCommGrpCat.of ℤ :=
  quotientComparison.symm ≪≫ intervalBoundaryRelativeH1IsoInt

/-- The transported interval fundamental class witnesses non-vacuity. -/
noncomputable def sphereOneGeneratorOfRelativeIntervalComparison
    (quotientComparison :
      (RelativeSingularChains intervalBoundary).homology 1 ≅ SphereOneH1) :
    SphereOneH1 :=
  quotientComparison.hom intervalBoundaryRelativeH1Generator

@[simp] theorem sphereOneH1IsoIntOfRelativeIntervalComparison_generator
    (quotientComparison :
      (RelativeSingularChains intervalBoundary).homology 1 ≅ SphereOneH1) :
    (sphereOneH1IsoIntOfRelativeIntervalComparison quotientComparison).hom
        (sphereOneGeneratorOfRelativeIntervalComparison quotientComparison) = 1 := by
  simp [sphereOneH1IsoIntOfRelativeIntervalComparison,
    sphereOneGeneratorOfRelativeIntervalComparison]
  exact intervalBoundaryRelativeH1IsoInt_generator

theorem sphereOneGeneratorOfRelativeIntervalComparison_ne_zero
    (quotientComparison :
      (RelativeSingularChains intervalBoundary).homology 1 ≅ SphereOneH1) :
    sphereOneGeneratorOfRelativeIntervalComparison quotientComparison ≠ 0 := by
  intro h
  have hgen :=
    sphereOneH1IsoIntOfRelativeIntervalComparison_generator quotientComparison
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

#print axioms sphereOneH1IsoIntOfRelativeIntervalComparison
#print axioms sphereOneH1IsoIntOfRelativeIntervalComparison_generator
#print axioms sphereOneGeneratorOfRelativeIntervalComparison_ne_zero

end ConstructionTargets.SphereOneH1Concrete
