import ConstructionTargets.CoefficientCompactComplementGeometry
import ConstructionTargets.CoefficientRelativeSmall

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementSmallComparison

open CategoryTheory Set
open ConstructionTargets.CoefficientCompactComplementGeometry

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] [T2Space X]
variable (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)

/-- The actual Boolean open cover of the complement of `K ∩ L`. -/
def cover (b : Bool) : Set (ambient K L) := if b then right K L else left K L

theorem cover_open (hK : IsCompact K) (hL : IsCompact L) (b : Bool) : IsOpen (cover K L b) := by
  cases b <;> simp [cover, left_open hK, right_open hL]

omit [TopologicalSpace X] [T2Space X] in
theorem cover_covers (K L : Set X) : univ ⊆ ⋃ b, cover K L b := by
  intro x hx
  have hu : x ∈ left K L ∪ right K L := by
    rw [left_union_right]
    exact mem_univ x
  rcases hu with hl | hr
  · exact mem_iUnion.mpr ⟨false, by simpa [cover] using hl⟩
  · exact mem_iUnion.mpr ⟨true, by simpa [cover] using hr⟩

/-- The overlap subspace, identified geometrically with the complement of `K ∪ L`. -/
def overlap : Set (ambient K L) := Subtype.val ⁻¹' (K ∪ L)ᶜ

omit [TopologicalSpace X] [T2Space X] in
theorem overlap_eq (K L : Set X) : overlap K L = left K L ∩ right K L := by
  rw [overlap, left_inter_right]

theorem ambientHomologyMap_isIso (hK : IsCompact K) (hL : IsCompact L) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (CoefficientSmallPath.coverSmallInclusion R (cover K L)) n) :=
  CoefficientSmallComparison.inclusion_isIso R (cover K L)
    (cover_open K L hK hL) (cover_covers K L) n

/-- Subdivision on the actual complement cover computes ambient coefficient homology. -/
noncomputable def ambientHomologyIso (n : ℕ) :
    (CoefficientSmallPath.coverSmallChains R (cover K L)).homology n ≅
      (CoefficientH0.SingularChains R (TopCat.of (ambient K L))).homology n :=
  CoefficientSmallComparison.homologyIso R (cover K L)
    (cover_open K L hK hL) (cover_covers K L) n

/-- The restricted cover computes the actual relative pair of the ambient
complement by the overlap corresponding to the complement of `K ∪ L`. -/
noncomputable def relativeHomologyIso (n : ℕ) :
    (CoefficientRelativeSmall.relativeSmall R (overlap K L) (cover K L)).homology n ≅
      (CoefficientRelativeSmall.relativeChains R (overlap K L)).homology n :=
  CoefficientRelativeSmall.comparisonIso R (overlap K L) (cover K L)
    (cover_open K L hK hL) (cover_covers K L) n

theorem relativeHomologyIso_hom (n : ℕ) :
    (relativeHomologyIso R K L hK hL n).hom =
      HomologicalComplex.homologyMap
        (CoefficientRelativeSmall.relativeMap R (overlap K L) (cover K L)) n := rfl

#print axioms cover_open
#print axioms cover_covers
#print axioms overlap_eq
#print axioms ambientHomologyMap_isIso
#print axioms relativeHomologyIso
#print axioms relativeHomologyIso_hom

end ConstructionTargets.CoefficientCompactComplementSmallComparison
