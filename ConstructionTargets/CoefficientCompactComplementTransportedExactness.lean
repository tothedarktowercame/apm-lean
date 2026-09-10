import ConstructionTargets.CoefficientCompactComplementUnionComparison
import ConstructionTargets.CoefficientCompactComplementPiecesComparison
import ConstructionTargets.ProductionOpenCoverMayerVietoris

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementTransportedExactness

open CategoryTheory Set
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementCoverSequence
open ConstructionTargets.CoefficientIntersectionRangeComparison
open ConstructionTargets.CoefficientCompactComplementPiecesComparison
open ConstructionTargets.CoefficientCompactComplementUnionComparison
open ConstructionTargets.ProductionOpenCoverMayerVietoris

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] [T2Space X]
variable (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)

noncomputable def intersectionSource (n : ℕ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (connecting R K L n)
    (HomologicalComplex.homologyMap (shortComplex R K L).f n)
    ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortExact R
      (leftRange K L) (rightRange K L)).δ_comp (n + 1) n rfl)

noncomputable def piecesSource (n : ℕ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (HomologicalComplex.homologyMap (shortComplex R K L).f n)
    (HomologicalComplex.homologyMap (shortComplex R K L).g n)
    (by rw [← HomologicalComplex.homologyMap_comp,
      (shortComplex R K L).zero, HomologicalComplex.homologyMap_zero])

noncomputable def unionSource (n : ℕ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (HomologicalComplex.homologyMap (shortComplex R K L).g (n + 1))
    (connecting R K L n)
    ((ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortExact R
      (leftRange K L) (rightRange K L)).comp_δ (n + 1) n rfl)

noncomputable def intersectionPresentation (n : ℕ) : ShortComplex (ModuleCat R) :=
  transportShortComplex (intersectionSource R K L n)
    (unionHomologyIso R K L hK hL (n + 1))
    (infimumToIntersectionHomologyIso R (left K L) (right K L) n)
    (piecesHomologyIso R K L n)

noncomputable def piecesPresentation (n : ℕ) : ShortComplex (ModuleCat R) :=
  transportShortComplex (piecesSource R K L n)
    (infimumToIntersectionHomologyIso R (left K L) (right K L) n)
    (piecesHomologyIso R K L n)
    (unionHomologyIso R K L hK hL n)

noncomputable def unionPresentation (n : ℕ) : ShortComplex (ModuleCat R) :=
  transportShortComplex (unionSource R K L n)
    (piecesHomologyIso R K L (n + 1))
    (unionHomologyIso R K L hK hL (n + 1))
    (infimumToIntersectionHomologyIso R (left K L) (right K L) n)

theorem intersectionPresentation_exact (n : ℕ) :
    (intersectionPresentation R K L hK hL n).Exact := by
  apply transportShortComplex_exact
  exact exact_intersection R K L n

theorem piecesPresentation_exact (n : ℕ) :
    (piecesPresentation R K L hK hL n).Exact := by
  apply transportShortComplex_exact
  exact exact_pieces R K L n

theorem unionPresentation_exact (n : ℕ) :
    (unionPresentation R K L hK hL n).Exact := by
  apply transportShortComplex_exact
  exact exact_union R K L n

#print axioms intersectionPresentation_exact
#print axioms piecesPresentation_exact
#print axioms unionPresentation_exact
end ConstructionTargets.CoefficientCompactComplementTransportedExactness
