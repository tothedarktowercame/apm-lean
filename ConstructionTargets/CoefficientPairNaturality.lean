import ConstructionTargets.CoefficientRadialPair
noncomputable section
namespace ConstructionTargets.CoefficientPairNaturality
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair CoefficientPairSequence
variable (R : Type) [CommRing R]
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def sequenceMap (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    sequence R A ⟶ sequence R B :=
  ShortComplex.homMk (subMap R A B f hf) (absoluteMap R f) (pairMap R A B f hf)
    (square R A B f hf).symm (CoefficientRadialPair.projection R A B f hf).symm

theorem component_sub (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    (sequenceMap R A B f hf).τ₁ = subMap R A B f hf := rfl
theorem component_absolute (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    (sequenceMap R A B f hf).τ₂ = absoluteMap R f := rfl
theorem component_relative (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    (sequenceMap R A B f hf).τ₃ = pairMap R A B f hf := rfl

theorem connecting_naturality (A : Set X) (B : Set Y) (f : C(X,Y))
    (hf : Set.MapsTo f A B) (n : ℕ) :
    connecting R A n ≫ HomologicalComplex.homologyMap (subMap R A B f hf) n =
      HomologicalComplex.homologyMap (pairMap R A B f hf) (n+1) ≫ connecting R B n :=
  HomologicalComplex.HomologySequence.δ_naturality (sequenceMap R A B f hf)
    (shortExact R A) (shortExact R B) (n+1) n rfl

theorem absolute_id : absoluteMap R (ContinuousMap.id X) = 𝟙 _ := by
  change (chains R).map (TopCat.toSSet.map (𝟙 (TopCat.of X))) = _
  simp only [CategoryTheory.Functor.map_id]

theorem absolute_comp (f : C(X,Y)) (g : C(Y,Z)) :
    absoluteMap R (g.comp f) = absoluteMap R f ≫ absoluteMap R g := by
  change (chains R).map (TopCat.toSSet.map (TopCat.ofHom f ≫ TopCat.ofHom g)) = _
  simp only [CategoryTheory.Functor.map_comp]
  rfl

theorem pair_id (A : Set X) : pairMap R A A (ContinuousMap.id X) (fun _ h => h) = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (CoefficientRelativeSmall.subspaceMap R A))).mp
  change cokernel.π _ ≫ _ = cokernel.π _ ≫ 𝟙 (cokernel (CoefficientRelativeSmall.subspaceMap R A))
  exact (CoefficientRadialPair.projection R A A (ContinuousMap.id X) (fun _ h => h)).trans
    ((congrArg (fun t => t ≫ cokernel.π (CoefficientRelativeSmall.subspaceMap R A))
      (absolute_id R (X := X))).trans (Category.id_comp _)) |>.trans (Category.comp_id _).symm

theorem pair_comp (A : Set X) (B : Set Y) (D : Set Z) (f : C(X,Y)) (g : C(Y,Z))
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D) :
    pairMap R A D (g.comp f) (hg.comp hf) = pairMap R A B f hf ≫ pairMap R B D g hg := by
  apply (cancel_epi (cokernel.π (CoefficientRelativeSmall.subspaceMap R A))).mp
  change cokernel.π _ ≫ _ = (cokernel.π _ ≫ pairMap R A B f hf) ≫ pairMap R B D g hg
  rw [CoefficientRadialPair.projection, CoefficientRadialPair.projection, absolute_comp]
  exact (Category.assoc _ _ _).trans (congrArg (fun t => absoluteMap R f ≫ t)
    (CoefficientRadialPair.projection R B D g hg).symm) |>.trans (Category.assoc _ _ _).symm

theorem homology_id (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (pairMap R A A (ContinuousMap.id X) (fun _ h => h)) n = 𝟙 _ := by
  rw [pair_id, HomologicalComplex.homologyMap_id]

theorem homology_comp (A : Set X) (B : Set Y) (D : Set Z) (f : C(X,Y)) (g : C(Y,Z))
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D) (n : ℕ) :
    HomologicalComplex.homologyMap (pairMap R A D (g.comp f) (hg.comp hf)) n =
      HomologicalComplex.homologyMap (pairMap R A B f hf) n ≫
        HomologicalComplex.homologyMap (pairMap R B D g hg) n := by
  rw [pair_comp, HomologicalComplex.homologyMap_comp]

theorem contractible_naturality [ContractibleSpace X] [ContractibleSpace Y]
    (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) (n : ℕ) (hn : n ≠ 0) :
    (CoefficientContractiblePair.contractibleConnectingIso R A n hn).hom ≫
      HomologicalComplex.homologyMap (subMap R A B f hf) n =
    HomologicalComplex.homologyMap (pairMap R A B f hf) (n+1) ≫
      (CoefficientContractiblePair.contractibleConnectingIso R B n hn).hom :=
  connecting_naturality R A B f hf n

def integral_empty (n : ℕ) := connecting_naturality ℤ (∅ : Set ℝ) ∅
  (ContinuousMap.id ℝ) (fun _ h => h) n

def rational_empty (n : ℕ) := connecting_naturality ℚ (∅ : Set ℝ) ∅
  (ContinuousMap.id ℝ) (fun _ h => h) n

theorem inclusion_square (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    (sequence R A).f ≫ (sequenceMap R A B f hf).τ₂ =
      (sequenceMap R A B f hf).τ₁ ≫ (sequence R B).f := square R A B f hf

theorem projection_square (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    (sequence R A).g ≫ (sequenceMap R A B f hf).τ₃ =
      (sequenceMap R A B f hf).τ₂ ≫ (sequence R B).g :=
  CoefficientRadialPair.projection R A B f hf

def integral_naturality (A : Set X) (B : Set Y) (f : C(X,Y))
    (hf : Set.MapsTo f A B) (n : ℕ) := connecting_naturality ℤ A B f hf n

def rational_naturality (A : Set X) (B : Set Y) (f : C(X,Y))
    (hf : Set.MapsTo f A B) (n : ℕ) := connecting_naturality ℚ A B f hf n

/- All spaces and coefficients have universe zero; subsets may be empty.
The contractible comparison requires positive target degree only. -/
#print axioms sequenceMap
#print axioms component_sub
#print axioms component_absolute
#print axioms component_relative
#print axioms inclusion_square
#print axioms projection_square
#print axioms connecting_naturality
#print axioms absolute_id
#print axioms absolute_comp
#print axioms pair_id
#print axioms pair_comp
#print axioms homology_id
#print axioms homology_comp
#print axioms contractible_naturality
#print axioms integral_empty
#print axioms rational_empty
#print axioms integral_naturality
#print axioms rational_naturality

end ConstructionTargets.CoefficientPairNaturality
