import ConstructionTargets.SphereHomology

/-!
# Integral singular homology of Mathlib's topological circle

This is the concrete comparison layer between Mathlib's `Circle`, represented
as the unit sphere in `ℂ`, and the Euclidean one-sphere computed by
`ConstructionTargets.SphereHomology`.
-/

noncomputable section

namespace ConstructionTargets.SingularHomologyConcrete

open CategoryTheory
open ConstructionTargets.SphereHomology

/-- The complex unit circle is homeomorphic to the Euclidean unit one-sphere. -/
noncomputable def circleHomeomorphSphereOne :
    Circle ≃ₜ Sphere 1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (fun z => by
    change z ∈ Metric.sphere 0 1 ↔ _
    simp only [Metric.mem_sphere, dist_zero_right]
    change ‖z‖ = 1 ↔ ‖Complex.orthonormalBasisOneI.repr z‖ = 1
    rw [Complex.orthonormalBasisOneI.repr.norm_map])

/-- Genuine integral singular first homology of Mathlib's topological circle. -/
noncomputable def circleSingularH1IsoInt :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle)) ≅ ModuleCat.of ℤ ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo circleHomeomorphSphereOne) ≪≫
    sphereModuleTopHomologyIsoInt 1 (by decide)

/-- The positively oriented circle class, normalized to map to `1 : ℤ`. -/
noncomputable def circleSingularH1Generator :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle)) :=
  circleSingularH1IsoInt.inv 1

@[simp] theorem circleSingularH1IsoInt_generator :
    circleSingularH1IsoInt.hom circleSingularH1Generator = 1 := by
  simp [circleSingularH1Generator]

theorem circleSingularH1Generator_ne_zero :
    circleSingularH1Generator ≠ 0 := by
  intro h
  have hgen := circleSingularH1IsoInt_generator
  rw [h, map_zero] at hgen
  exact zero_ne_one hgen

noncomputable instance circleSingularH1Nontrivial :
    Nontrivial
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle)) :=
  ⟨⟨circleSingularH1Generator, 0, circleSingularH1Generator_ne_zero⟩⟩

#print axioms circleHomeomorphSphereOne
#print axioms circleSingularH1IsoInt
#print axioms circleSingularH1IsoInt_generator
#print axioms circleSingularH1Generator_ne_zero
#print axioms circleSingularH1Nontrivial

end ConstructionTargets.SingularHomologyConcrete
