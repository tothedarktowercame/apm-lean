import ConstructionTargets.RelativeSingularCoefficients
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ConstructionTargets.RelativePairNaturality
open RelativeSingularCoefficients
variable (R : Type) [CommRing R]
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {A : Set X} {B : Set Y} {D : Set Z}
abbrev chains := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)

def submap (f : C(X,Y)) (h : Set.MapsTo f A B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun x => ⟨f x, h x.property⟩, f.continuous.comp continuous_subtype_val |>.subtype_mk _⟩

theorem inclusion_square (f : C(X,Y)) (h : Set.MapsTo f A B) :
    (chains R).map (submap f h) ≫ singularSubspaceMap R B =
      singularSubspaceMap R A ≫ (chains R).map (TopCat.ofHom f) := by
  rw [singularSubspaceMap, singularSubspaceMap, ← Functor.map_comp, ← Functor.map_comp]
  rfl

def arrowMap (f : C(X,Y)) (h : Set.MapsTo f A B) :
    Arrow.mk (singularSubspaceMap R A) ⟶ Arrow.mk (singularSubspaceMap R B) :=
  Arrow.homMk ((chains R).map (submap f h)) ((chains R).map (TopCat.ofHom f))
    (inclusion_square R f h)

def relativeMap (f : C(X,Y)) (h : Set.MapsTo f A B) :
    RelativeSingularChains R A ⟶ RelativeSingularChains R B :=
  cokernel.desc _ ((chains R).map (TopCat.ofHom f) ≫ relativeSingularProjection R B) (by
    change image.ι _ ≫ ((chains R).map (TopCat.ofHom f) ≫ cokernel.π (image.ι _)) = 0
    have hm := image.map_ι (arrowMap R f h)
    change image.map (arrowMap R f h) ≫ image.ι (singularSubspaceMap R B) =
      image.ι (singularSubspaceMap R A) ≫ (chains R).map (TopCat.ofHom f) at hm
    rw [← Category.assoc, ← hm]
    dsimp [arrowMap]
    simp only [Category.assoc, cokernel.condition, comp_zero])

@[reassoc] theorem projection_square (f : C(X,Y)) (h : Set.MapsTo f A B) :
    relativeSingularProjection R A ≫ relativeMap R f h =
      (chains R).map (TopCat.ofHom f) ≫ relativeSingularProjection R B :=
  cokernel.π_desc _ _ _

def pairMap (f : C(X,Y)) (h : Set.MapsTo f A B) :
    singularPairShortComplex R A ⟶ singularPairShortComplex R B where
  τ₁ := (chains R).map (submap f h)
  τ₂ := (chains R).map (TopCat.ofHom f)
  τ₃ := relativeMap R f h
  comm₁₂ := inclusion_square R f h
  comm₂₃ := (projection_square R f h).symm


theorem relativeMap_id : relativeMap R (ContinuousMap.id X) (Set.mapsTo_id A) =
    𝟙 (RelativeSingularChains R A) := by
  letI : Epi (relativeSingularProjection R A) := by
    exact (singularPairShortComplex_shortExact R A).epi_g
  apply (cancel_epi (relativeSingularProjection R A)).mp
  rw [projection_square]
  change (chains R).map (𝟙 (TopCat.of X)) ≫ _ = _
  simp

theorem relativeMap_comp (f : C(X,Y)) (h : Set.MapsTo f A B)
    (g : C(Y,Z)) (k : Set.MapsTo g B D) :
    relativeMap R (g.comp f) (k.comp h) = relativeMap R f h ≫ relativeMap R g k := by
  letI : Epi (relativeSingularProjection R A) := by
    exact (singularPairShortComplex_shortExact R A).epi_g
  apply (cancel_epi (relativeSingularProjection R A)).mp
  rw [projection_square, projection_square_assoc, projection_square]
  change (chains R).map (TopCat.ofHom f ≫ TopCat.ofHom g) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]

def connecting (A : Set X) (n : ℕ) :=
  (singularPairShortComplex_shortExact R A).δ (n+1) n rfl

theorem connecting_naturality (f : C(X,Y)) (h : Set.MapsTo f A B) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeMap R f h) (n+1) ≫ connecting R B n =
      connecting R A n ≫ HomologicalComplex.homologyMap ((chains R).map (submap f h)) n :=
  (HomologicalComplex.HomologySequence.δ_naturality (pairMap R f h)
    (singularPairShortComplex_shortExact R A) (singularPairShortComplex_shortExact R B)
    (n+1) n rfl).symm
/-- Exactness at the subspace-homology term in the long exact sequence of a
pair. -/
theorem singularPairHomology_exact_subspace
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (connecting R A n)
      (HomologicalComplex.homologyMap (singularSubspaceMap R A) n)
      ((singularPairShortComplex_shortExact R A).δ_comp (n + 1) n rfl)).Exact :=
  (singularPairShortComplex_shortExact R A).homology_exact₁ (n + 1) n rfl

/-- Exactness at the absolute-homology term in the long exact sequence of a
pair. -/
theorem singularPairHomology_exact_absolute
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (singularSubspaceMap R A) n)
      (HomologicalComplex.homologyMap (relativeSingularProjection R A) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        change HomologicalComplex.homologyMap ((singularPairShortComplex R A).f ≫
          (singularPairShortComplex R A).g) n = 0
        rw [(singularPairShortComplex R A).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (singularPairShortComplex_shortExact R A).homology_exact₂ n

/-- Exactness at the relative-homology term in the long exact sequence of a
pair. -/
theorem singularPairHomology_exact_relative
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (relativeSingularProjection R A) (n + 1))
      (connecting R A n)
      ((singularPairShortComplex_shortExact R A).comp_δ (n + 1) n rfl)).Exact :=
  (singularPairShortComplex_shortExact R A).homology_exact₃ (n + 1) n rfl


theorem integral_disk_identity :
    relativeMap ℤ (ContinuousMap.id Disk) (Set.mapsTo_id diskBoundary) = 𝟙 _ := relativeMap_id ℤ

theorem rational_disk_identity :
    relativeMap ℚ (ContinuousMap.id Disk) (Set.mapsTo_id diskBoundary) = 𝟙 _ := relativeMap_id ℚ

def diskNeg : C(Disk,Disk) :=
  ⟨fun x => ⟨-x.val, by simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using x.property⟩,
    by fun_prop⟩
theorem diskNeg_boundary : Set.MapsTo diskNeg diskBoundary diskBoundary := by
  intro x hx
  change ‖-x.val‖ = 1
  simpa only [norm_neg] using hx

theorem rational_disk_neg_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (relativeMap ℚ diskNeg diskNeg_boundary) (n+1) ≫
        connecting ℚ diskBoundary n =
      connecting ℚ diskBoundary n ≫
        HomologicalComplex.homologyMap ((chains ℚ).map (submap diskNeg diskNeg_boundary)) n :=
  connecting_naturality ℚ diskNeg diskNeg_boundary n

theorem diskNeg_ne_id : diskNeg ≠ ContinuousMap.id Disk := by
  intro h
  have he := congrArg (fun q : C(Disk,Disk) => (q ⟨1, by simp [Disk, Metric.mem_closedBall]⟩).val) h
  norm_num [diskNeg] at he

#print axioms diskNeg_ne_id
#print axioms pairMap
#print axioms relativeMap_id
#print axioms relativeMap_comp
#print axioms connecting_naturality
#print axioms singularPairHomology_exact_subspace
#print axioms singularPairHomology_exact_absolute
#print axioms singularPairHomology_exact_relative
#print axioms integral_disk_identity
#print axioms rational_disk_identity
#print axioms rational_disk_neg_naturality
end ConstructionTargets.RelativePairNaturality
