import ConstructionTargets.CoefficientEventualSmallness
noncomputable section
namespace ConstructionTargets.CoefficientIteratedHomotopy
open CategoryTheory
variable (R : Type) [CommRing R]
variable {X α : Type} [TopologicalSpace X] (U : α → Set X)

/-- All types are Type 0. No cover or nonemptiness hypothesis is needed. -/
def smallIterate (k : ℕ) :
    CoefficientSmallPath.coverSmallChains R U ⟶ CoefficientSmallPath.coverSmallChains R U :=
  Nat.rec (𝟙 _) (fun _ r => r ≫ CoefficientSmallPreservation.subdivision R U) k

def absoluteHomotopy (k : ℕ) : Homotopy
    (CoefficientEventualSmallness.subdivisionIterate R (X := X) k) (𝟙 _) := by
  induction k with
  | zero => exact Homotopy.refl _
  | succ k ih =>
    exact (CoefficientSingularPrism.subdivisionHomotopy R).compLeftId
      (CoefficientEventualSmallness.subdivisionIterate R k) |>.trans ih

def smallHomotopy (k : ℕ) : Homotopy (smallIterate R U k) (𝟙 _) := by
  induction k with
  | zero => exact Homotopy.refl _
  | succ k ih =>
    exact (CoefficientSmallPreservation.smallHomotopy R U).compLeftId
      (smallIterate R U k) |>.trans ih

theorem iterate_inclusion (k : ℕ) :
    smallIterate R U k ≫ CoefficientSmallPath.coverSmallInclusion R U =
      CoefficientSmallPath.coverSmallInclusion R U ≫
        CoefficientEventualSmallness.subdivisionIterate R k := by
  induction k with
  | zero => simp [smallIterate, CoefficientEventualSmallness.subdivisionIterate]
  | succ k ih =>
    change (smallIterate R U k ≫ CoefficientSmallPreservation.subdivision R U) ≫ _ =
      _ ≫ (CoefficientEventualSmallness.subdivisionIterate R k ≫ _)
    rw [Category.assoc, CoefficientSmallPreservation.subdivision_inclusion,
      ← Category.assoc, ih, Category.assoc]

theorem absolute_homology_identity (k n : ℕ) :
    HomologicalComplex.homologyMap (CoefficientEventualSmallness.subdivisionIterate R (X := X) k) n = 𝟙 _ := by
  rw [(absoluteHomotopy R (X := X) k).homologyMap_eq, HomologicalComplex.homologyMap_id]

theorem small_homology_identity (k n : ℕ) :
    HomologicalComplex.homologyMap (smallIterate R U k) n = 𝟙 _ := by
  rw [(smallHomotopy R U k).homologyMap_eq, HomologicalComplex.homologyMap_id]

theorem integral_interval (k n : ℕ) :
    HomologicalComplex.homologyMap (smallIterate ℤ CoefficientSmallPath.intervalCover k) n = 𝟙 _ :=
  small_homology_identity ℤ _ k n

theorem rational_interval (k n : ℕ) :
    HomologicalComplex.homologyMap (smallIterate ℚ CoefficientSmallPath.intervalCover k) n = 𝟙 _ :=
  small_homology_identity ℚ _ k n

#print axioms absoluteHomotopy
#print axioms smallHomotopy
#print axioms iterate_inclusion
#print axioms absolute_homology_identity
#print axioms small_homology_identity
end ConstructionTargets.CoefficientIteratedHomotopy
