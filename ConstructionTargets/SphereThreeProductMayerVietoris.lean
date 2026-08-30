import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.SphereProductPoleCoverHomology

/-!
# Degree-two homology of `S³ × S³` from the pole cover

This file applies one production Mayer--Vietoris exact segment to the reviewed
open cover.  The two objects adjacent to the union's degree-two homology are
the reviewed zero objects.
-/

noncomputable section

namespace ConstructionTargets.SphereThreeProductMayerVietoris

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SphereProductPoleOpenCover
open ConstructionTargets.SphereProductPoleCoverHomology

/-- Integral singular `H₂(S³ × S³)` vanishes.  At degree parameter `1`, the
production union exact segment is

`H₂(U) ⊞ H₂(V) ⟶ H₂(X) ⟶ H₁(U ∩ V)`.

The reviewed homology-input file proves that both adjacent objects are zero.
-/
theorem sphereThreeProduct_singularH2_isZero :
    IsZero (SingularHomology 2 (TopCat.of X)) := by
  let hex := productionMayerVietoris_exact_union
    U V U_isOpen V_isOpen U_union_V 1
  apply hex.isZero_X₂
  · exact coverPieces_singularH2_biprod_isZero.eq_of_src _ _
  · exact intersection_singularH1_isZero.eq_of_tgt _ _

#print axioms productionMayerVietoris_exact_union
#print axioms sphereThreeProduct_singularH2_isZero

end ConstructionTargets.SphereThreeProductMayerVietoris
