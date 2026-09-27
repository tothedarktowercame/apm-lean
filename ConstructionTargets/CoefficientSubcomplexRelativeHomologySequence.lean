import ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact
import Mathlib.Algebra.Homology.HomologySequence

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex
open ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

/-- The connecting morphism produced by the genuine short exact sequence of
relative quotient chain complexes. -/
noncomputable def connecting (n : ℕ) :
    (cokernel (unionAmbient R P Q)).homology (n + 1) ⟶
      (cokernel (intersectionAmbient R P Q)).homology n :=
  (shortComplex_shortExact R P Q).δ (n + 1) n (by simp)

/-- Exactness at the middle relative homology object in degree `n + 1`. -/
theorem exact_intersection_pieces_union (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (intersectionToPiecesRelative R P Q) (n + 1))
      (HomologicalComplex.homologyMap
        (piecesToUnionRelative R P Q) (n + 1))
      (by rw [← HomologicalComplex.homologyMap_comp,
        relative_arrows_zero, HomologicalComplex.homologyMap_zero])).Exact :=
  (shortComplex_shortExact R P Q).homology_exact₂ (n + 1)

/-- Exactness at the union relative homology object before the connecting map. -/
theorem exact_pieces_union_connecting (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (piecesToUnionRelative R P Q) (n + 1))
      (connecting R P Q n)
      (by exact (shortComplex_shortExact R P Q).comp_δ (n + 1) n (by simp))).Exact :=
  (shortComplex_shortExact R P Q).homology_exact₃ (n + 1) n (by simp)

/-- Exactness after the connecting map at intersection relative homology. -/
theorem exact_union_connecting_intersection_pieces (n : ℕ) :
    (ShortComplex.mk
      (connecting R P Q n)
      (HomologicalComplex.homologyMap
        (intersectionToPiecesRelative R P Q) n)
      (by exact (shortComplex_shortExact R P Q).δ_comp (n + 1) n (by simp))).Exact :=
  (shortComplex_shortExact R P Q).homology_exact₁ (n + 1) n (by simp)

#print axioms connecting
#print axioms exact_intersection_pieces_union
#print axioms exact_pieces_union_connecting
#print axioms exact_union_connecting_intersection_pieces
end ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence
