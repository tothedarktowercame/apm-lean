import ConstructionTargets.CoefficientSubcomplexMayerVietoris
import ConstructionTargets.CoefficientCompactComplementGeometry

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementCoverSequence

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientSubcomplexMayerVietoris

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev ambientSSet (K L : Set X) := TopCat.toSSet.obj (TopCat.of (ambient K L))
abbrev leftRange (K L : Set X) : (ambientSSet K L).Subcomplex :=
  ambientSubspaceRange (left K L)
abbrev rightRange (K L : Set X) : (ambientSSet K L).Subcomplex :=
  ambientSubspaceRange (right K L)

noncomputable def shortComplex (K L : Set X) :=
  CoefficientSubcomplexMayerVietoris.shortComplex R (leftRange K L) (rightRange K L)

noncomputable def connecting (K L : Set X) (n : ℕ) :=
  CoefficientSubcomplexMayerVietoris.connecting R (leftRange K L) (rightRange K L) n

theorem exact_intersection (K L : Set X) (n : ℕ) :
    (ShortComplex.mk (connecting R K L n)
      (HomologicalComplex.homologyMap (shortComplex R K L).f n)
      ((CoefficientSubcomplexMayerVietoris.shortExact R (leftRange K L) (rightRange K L)).δ_comp (n + 1) n rfl)).Exact :=
  CoefficientSubcomplexMayerVietoris.exact_intersection R (leftRange K L) (rightRange K L) n

theorem exact_pieces (K L : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (shortComplex R K L).f n)
      (HomologicalComplex.homologyMap (shortComplex R K L).g n)
      (by rw [← HomologicalComplex.homologyMap_comp,
        (shortComplex R K L).zero, HomologicalComplex.homologyMap_zero])).Exact :=
  CoefficientSubcomplexMayerVietoris.exact_pieces R (leftRange K L) (rightRange K L) n

theorem exact_union (K L : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (shortComplex R K L).g (n + 1))
      (connecting R K L n)
      ((CoefficientSubcomplexMayerVietoris.shortExact R (leftRange K L) (rightRange K L)).comp_δ (n + 1) n rfl)).Exact :=
  CoefficientSubcomplexMayerVietoris.exact_union R (leftRange K L) (rightRange K L) n

#print axioms exact_intersection
#print axioms exact_pieces
#print axioms exact_union
end ConstructionTargets.CoefficientCompactComplementCoverSequence
