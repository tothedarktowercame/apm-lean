import ConstructionTargets.SphereHomology

/-!
# Integral singular homology of the complex unit circle

The sphere-homology library uses the Euclidean unit sphere in two real
coordinates, while Mathlib's `Circle` is the unit sphere in `ℂ`.  This file
provides the concrete homeomorphism between those presentations and transports
the production `ModuleCat ℤ` computation of first singular homology.
-/

noncomputable section

namespace ConstructionTargets.CircleHomology

open CategoryTheory

/-- The complex unit circle is homeomorphic to the Euclidean one-sphere. -/
noncomputable def circleHomeomorphSphereOne :
    Circle ≃ₜ ConstructionTargets.SphereHomology.Sphere 1 where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z, by
    rw [Metric.mem_sphere, dist_zero_right,
      Complex.orthonormalBasisOneI.repr.norm_map]
    exact Circle.norm_coe z⟩
  invFun x := ⟨Complex.orthonormalBasisOneI.repr.symm x, by
    change Complex.orthonormalBasisOneI.repr.symm x ∈
      Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
    rw [← mem_sphere_zero_iff_norm]
    exact x.property⟩
  left_inv z := by
    apply Subtype.ext
    exact Complex.orthonormalBasisOneI.repr.symm_apply_apply z
  right_inv x := by
    apply Subtype.ext
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply x
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The first integral singular homology of Mathlib's complex unit circle is
infinite cyclic, in the `ModuleCat ℤ` coefficient category. -/
noncomputable def circleH1IsoInt :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle)) ≅ ModuleCat.of ℤ ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo circleHomeomorphSphereOne) ≪≫
    ConstructionTargets.SphereHomology.sphereModuleTopHomologyIsoInt 1 one_pos

#print axioms circleHomeomorphSphereOne
#print axioms circleH1IsoInt

end ConstructionTargets.CircleHomology
