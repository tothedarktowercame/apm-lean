import ConstructionTargets.CoefficientChartTransitionUnit
noncomputable section
namespace ConstructionTargets.CoefficientTripleOverlap
open CategoryTheory
open CoefficientOverlapPair CoefficientOverlapNormalization CoefficientNeighborhoodLocal CoefficientChartPair CoefficientRadialPair
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
def common (a : Fin 3 → M) : Set M := ⋂ i, (chartAt (E m) (a i)).source
theorem common_open (a : Fin 3 → M) : IsOpen (common m a) :=
  isOpen_iInter_of_finite fun i => (chartAt (E m) (a i)).open_source
theorem common_sub (a : Fin 3 → M) (i : Fin 3) : common m a ⊆ (chartAt (E m) (a i)).source :=
  Set.iInter_subset _ i
def chart (a : Fin 3 → M) (x : M) (i : Fin 3) :=
  pointed m (a i) (common m a) (common_open m a) (common_sub m a i) x
def transition (a : Fin 3 → M) (x : M) (i j : Fin 3) := (chart m a x i).symm.trans (chart m a x j)
theorem transition_value (a : Fin 3 → M) (x : M) (i j : Fin 3)
    (z : image m (a i) (common m a) x) :
    (transition m a x i j z).val =
      chartAt (E m) (a j) ((chartAt (E m) (a i)).symm (z.val + chartAt (E m) (a i) x)) -
        chartAt (E m) (a j) x := rfl
theorem transition_comp (a : Fin 3 → M) (x : M) (i j k : Fin 3) :
    (transition m a x i j).trans (transition m a x j k) = transition m a x i k := by
  apply Homeomorph.ext
  intro z
  exact congrArg (chart m a x k) ((chart m a x j).symm_apply_apply _)
variable (R : Type) [CommRing R]
def chartPair (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i : Fin 3) :=
  CoefficientOverlapNormalization.chartPair R m (a i) (common m a) (common_open m a) (common_sub m a i) x hx

def pair (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j : Fin 3) :=
  (chartPair m R a x hx i).symm ≪≫ chartPair m R a x hx j

theorem mapsTo (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j : Fin 3) :
    Set.MapsTo (homeoMap (transition m a x i j))
      (localDeleted (image m (a i) (common m a) x) 0)
      (localDeleted (image m (a j) (common m a) x) 0) := by
  intro z hz
  apply (pointed_iff m (a j) (common m a) (common_open m a) (common_sub m a j) x hx _).mpr
  apply (pointed_iff m (a i) (common m a) (common_open m a) (common_sub m a i) x hx _).mp
  change chart m a x i ((chart m a x i).symm z) ∈ _
  simpa using hz

theorem pair_forward (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j : Fin 3) :
    (pair m R a x hx i j).hom = pairMap R _ _ (homeoMap (transition m a x i j)) (mapsTo m a x hx i j) := by
  unfold pair chartPair CoefficientOverlapNormalization.chartPair pairHomeo
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← CoefficientPairNaturality.pair_comp]
  rfl

theorem pair_comp (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j k : Fin 3) :
    (pair m R a x hx i j).hom ≫ (pair m R a x hx j k).hom = (pair m R a x hx i k).hom := by
  simp only [pair, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

theorem homology_comp (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j k : Fin 3) (n : ℕ) :
    HomologicalComplex.homologyMap (pair m R a x hx i j).hom n ≫
      HomologicalComplex.homologyMap (pair m R a x hx j k).hom n =
      HomologicalComplex.homologyMap (pair m R a x hx i k).hom n := by
  rw [← HomologicalComplex.homologyMap_comp, pair_comp]
theorem actual_relative_comp (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j k : Fin 3) :
    pairMap R _ _ (homeoMap (transition m a x i j)) (mapsTo m a x hx i j) ≫
      pairMap R _ _ (homeoMap (transition m a x j k)) (mapsTo m a x hx j k) =
      pairMap R _ _ (homeoMap (transition m a x i k)) (mapsTo m a x hx i k) := by
  rw [← pair_forward, ← pair_forward, ← pair_forward]
  exact pair_comp m R a x hx i j k
variable [T2Space M]
def model (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i : Fin 3) :=
  modelNormalization R m (image m (a i) (common m a) x) (image_open m (a i) _ x)
    ((pointed_zero m (a i) (common m a) (common_open m a) (common_sub m a i) x hx) ▸
      (chart m a x i ⟨x,hx⟩).property)

theorem restriction (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i : Fin 3) :
    normalization R m (a i) (common m a) (common_open m a) (common_sub m a i) x hx =
      CoefficientChartTransitionUnit.chartNormalization R m (a i) x (common_sub m a i hx) :=
  CoefficientChartRestriction.normalization_restriction R m (a i) (common m a) _
    (common_open m a) (chartAt (E m) (a i)).open_source (common_sub m a i) Set.Subset.rfl
      (common_sub m a i) x hx

theorem normalized_pair (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j : Fin 3) :
    (normalization R m (a i) (common m a) (common_open m a) (common_sub m a i) x hx).inv ≫
      (normalization R m (a j) (common m a) (common_open m a) (common_sub m a j) x hx).hom =
    (model m R a x hx i).inv ≫ HomologicalComplex.homologyMap (pair m R a x hx i j).hom (m+2) ≫
      (model m R a x hx j).hom := by
  unfold normalization ambientIso
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  unfold pair
  rw [Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMap_comp]
  rfl

theorem geometric_comparison (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j : Fin 3) :
    (CoefficientChartTransitionUnit.comparison R m (a i) (a j) x
      (common_sub m a i hx) (common_sub m a j hx)).hom =
    (model m R a x hx i).inv ≫ HomologicalComplex.homologyMap (pair m R a x hx i j).hom (m+2) ≫
      (model m R a x hx j).hom := by
  have h := normalized_pair m R a x hx i j
  rw [restriction, restriction] at h
  exact h

theorem geometric_unit (a : Fin 3 → M) (x : M) (hx : x ∈ common m a) (i j : Fin 3) :
    (CoefficientChartTransitionUnit.transitionUnit R m (a i) (a j) x
      (common_sub m a i hx) (common_sub m a j hx) : R) =
    ((model m R a x hx i).inv ≫ HomologicalComplex.homologyMap (pair m R a x hx i j).hom (m+2) ≫
      (model m R a x hx j).hom).hom (1 : R) :=
  congrArg (fun f => f.hom (1 : R)) (geometric_comparison m R a x hx i j)
#print axioms common_open
#print axioms transition_value
#print axioms actual_relative_comp
#print axioms restriction
#print axioms normalized_pair
#print axioms geometric_comparison
#print axioms geometric_unit
#print axioms CoefficientChartTransitionUnit.unit_cocycle
#print axioms transition_comp
#print axioms pair_forward
#print axioms homology_comp
end ConstructionTargets.CoefficientTripleOverlap
