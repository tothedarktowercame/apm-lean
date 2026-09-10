import ConstructionTargets.CoefficientCompactComplementTransportedExactness

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementTransportedArrows

open CategoryTheory Set
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementCoverSequence
open ConstructionTargets.CoefficientIntersectionRangeComparison
open ConstructionTargets.CoefficientCompactComplementPiecesComparison
open ConstructionTargets.CoefficientCompactComplementUnionComparison
open ConstructionTargets.CoefficientCompactComplementTransportedExactness

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] [T2Space X]
variable (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)

noncomputable def ambientConnecting (n : ℕ) :=
  (unionHomologyIso R K L hK hL (n + 1)).inv ≫
    connecting R K L n ≫
    (infimumToIntersectionHomologyIso R (left K L) (right K L) n).hom

noncomputable def overlapToPieces (n : ℕ) :=
  (infimumToIntersectionHomologyIso R (left K L) (right K L) n).inv ≫
    HomologicalComplex.homologyMap (shortComplex R K L).f n ≫
    (piecesHomologyIso R K L n).hom

noncomputable def piecesToAmbient (n : ℕ) :=
  (piecesHomologyIso R K L n).inv ≫
    HomologicalComplex.homologyMap (shortComplex R K L).g n ≫
    (unionHomologyIso R K L hK hL n).hom

theorem intersectionPresentation_f (n : ℕ) :
    (intersectionPresentation R K L hK hL n).f = ambientConnecting R K L hK hL n := rfl

theorem intersectionPresentation_g (n : ℕ) :
    (intersectionPresentation R K L hK hL n).g = overlapToPieces R K L n := rfl

theorem piecesPresentation_f (n : ℕ) :
    (piecesPresentation R K L hK hL n).f = overlapToPieces R K L n := rfl

theorem piecesPresentation_g (n : ℕ) :
    (piecesPresentation R K L hK hL n).g = piecesToAmbient R K L hK hL n := rfl

theorem unionPresentation_f (n : ℕ) :
    (unionPresentation R K L hK hL n).f = piecesToAmbient R K L hK hL (n + 1) := rfl

theorem unionPresentation_g (n : ℕ) :
    (unionPresentation R K L hK hL n).g = ambientConnecting R K L hK hL n := rfl

theorem exact_overlap (n : ℕ) :
    (ShortComplex.mk (ambientConnecting R K L hK hL n)
      (overlapToPieces R K L n)
      (by rw [← intersectionPresentation_f, ← intersectionPresentation_g]
          exact (intersectionPresentation R K L hK hL n).zero)).Exact := by
  simpa only [intersectionPresentation_f, intersectionPresentation_g] using
    intersectionPresentation_exact R K L hK hL n

theorem exact_pieces (n : ℕ) :
    (ShortComplex.mk (overlapToPieces R K L n)
      (piecesToAmbient R K L hK hL n)
      (by rw [← piecesPresentation_f, ← piecesPresentation_g]
          exact (piecesPresentation R K L hK hL n).zero)).Exact := by
  simpa only [piecesPresentation_f, piecesPresentation_g] using
    piecesPresentation_exact R K L hK hL n

theorem exact_ambient (n : ℕ) :
    (ShortComplex.mk (piecesToAmbient R K L hK hL (n + 1))
      (ambientConnecting R K L hK hL n)
      (by rw [← unionPresentation_f, ← unionPresentation_g]
          exact (unionPresentation R K L hK hL n).zero)).Exact := by
  simpa only [unionPresentation_f, unionPresentation_g] using
    unionPresentation_exact R K L hK hL n

#print axioms exact_overlap
#print axioms exact_pieces
#print axioms exact_ambient
end ConstructionTargets.CoefficientCompactComplementTransportedArrows
