import ConstructionTargets.CoefficientOverlapNormalization
noncomputable section
namespace ConstructionTargets.CoefficientChartRestriction
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair CoefficientNeighborhoodLocal CoefficientChartPair CoefficientOverlapPair
open CoefficientOverlapNormalization
theorem normalization_natural {C : Type*} [Category C] {A B D Z : C}
    (e : A ≅ Z) (f : B ≅ Z) (j : A ⟶ B) (g : A ⟶ D) (k : B ⟶ D)
    (hj : j ≫ f.hom = e.hom) (hg : j ≫ k = g) : e.inv ≫ g = f.inv ≫ k := by
  apply (cancel_epi e.hom).mp
  rw [Iso.hom_inv_id_assoc, ← hg, ← hj]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable (R : Type) [CommRing R]
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (a : M) (U V : Set M) (hU : IsOpen U) (hV : IsOpen V)
  (hUs : U ⊆ (chartAt (E m) a).source) (hVs : V ⊆ (chartAt (E m) a).source) (hUV : U ⊆ V) (x : M)
include hU hV hUs hVs hUV in
theorem image_subset : image m a U x ⊆ image m a V x := by
  intro z hz
  let y := (pointed m a U hU hUs x).symm ⟨z,hz⟩
  have he : (pointed m a V hV hVs x ⟨y.val,hUV y.property⟩).val = z := by
    change (pointed m a U hU hUs x y).val = z
    exact congrArg Subtype.val ((pointed m a U hU hUs x).apply_symm_apply ⟨z,hz⟩)
  exact he ▸ (pointed m a V hV hVs x ⟨y.val,hUV y.property⟩).property

def coordinateInclusion := nestedInclusion (image m a U x) (image m a V x) (image_subset m a U V hU hV hUs hVs hUV x)
theorem coordinate_square : (homeoMap (pointed m a V hV hVs x)).comp (nestedInclusion U V hUV) =
    (coordinateInclusion m a U V hU hV hUs hVs hUV x).comp (homeoMap (pointed m a U hU hUs x)) := by
  apply ContinuousMap.ext; intro y; rfl

theorem ambient_square : (ambient m a V hV hVs x).comp (coordinateInclusion m a U V hU hV hUs hVs hUV x) =
    ambient m a U hU hUs x := by
  apply ContinuousMap.ext; intro y; rfl

def imageMap := nestedMap R (image m a U x) (image m a V x) (image_subset m a U V hU hV hUs hVs hUV x) 0
variable (hx : x ∈ U)
theorem relative_square : imageMap R m a U V hU hV hUs hVs hUV x ≫
    ambientMap R m a V hV hVs x (hUV hx) = ambientMap R m a U hU hUs x hx := by
  unfold imageMap nestedMap ambientMap
  rw [← CoefficientPairNaturality.pair_comp]
  congr 1

theorem homology_square (n : ℕ) :
    HomologicalComplex.homologyMap (imageMap R m a U V hU hV hUs hVs hUV x) n ≫
      HomologicalComplex.homologyMap (ambientMap R m a V hV hVs x (hUV hx)) n =
    HomologicalComplex.homologyMap (ambientMap R m a U hU hUs x hx) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n) (relative_square R m a U V hU hV hUs hVs hUV x hx))

variable [T2Space M]
theorem normalization_restriction : normalization R m a U hU hUs x hx =
    normalization R m a V hV hVs x (hUV hx) := by
  apply Iso.ext
  let gU := (modelNormalization R m (image m a U x) (image_open m a U x)
    ((pointed_zero m a U hU hUs x hx) ▸ (pointed m a U hU hUs x ⟨x,hx⟩).property)).hom
  let gV := (modelNormalization R m (image m a V x) (image_open m a V x)
    ((pointed_zero m a V hV hVs x (hUV hx)) ▸ (pointed m a V hV hVs x ⟨x,hUV hx⟩).property)).hom
  have hg : HomologicalComplex.homologyMap (imageMap R m a U V hU hV hUs hVs hUV x) (m+2) ≫ gV = gU := by
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ (CoefficientModelLocal.localIso R m).hom)
      (nested_homology R (image m a U x) (image m a V x)
        (image_subset m a U V hU hV hUs hVs hUV x) 0 (m+2)))
  have hs := homology_square R m a U V hU hV hUs hVs hUV x hx (m+2)
  rw [← ambient_forward, ← ambient_forward] at hs
  exact normalization_natural (ambientIso R m a U hU hUs x hx (m+2))
    (ambientIso R m a V hV hVs x (hUV hx) (m+2)) _ gU gV hs hg

theorem generator_restriction : generator R m a U hU hUs x hx = generator R m a V hV hVs x (hUV hx) :=
  congrArg (fun e => e.inv.hom (1 : R)) (normalization_restriction R m a U V hU hV hUs hVs hUV x hx)

omit [T2Space M] in
theorem image_projection (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m a U x) 0))).f n ≫
      (imageMap R m a U V hU hV hUs hVs hUV x).f n =
    (absoluteMap R (coordinateInclusion m a U V hU hV hUs hVs hUV x)).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m a V x) 0))).f n :=
  CoefficientRadialPair.projection_degree R (localDeleted (image m a U x) 0)
    (localDeleted (image m a V x) 0) (coordinateInclusion m a U V hU hV hUs hVs hUV x) (fun _ hy => hy) n

def integral_restriction (m : ℕ) (a x : E m) (U V : Set (E m)) (hU : IsOpen U) (hV : IsOpen V)
    (hUs : U ⊆ (chartAt (E m) a).source) (hVs : V ⊆ (chartAt (E m) a).source) (hUV : U ⊆ V) (hx : x ∈ U) :=
  normalization_restriction ℤ m a U V hU hV hUs hVs hUV x hx
def rational_restriction (m : ℕ) (a x : E m) (U V : Set (E m)) (hU : IsOpen U) (hV : IsOpen V)
    (hUs : U ⊆ (chartAt (E m) a).source) (hVs : V ⊆ (chartAt (E m) a).source) (hUV : U ⊆ V) (hx : x ∈ U) :=
  normalization_restriction ℚ m a U V hU hV hUs hVs hUV x hx
#print axioms image_subset
#print axioms coordinate_square
#print axioms ambient_square
#print axioms relative_square
#print axioms homology_square
#print axioms normalization_restriction
#print axioms generator_restriction
#print axioms image_projection
#print axioms integral_restriction
#print axioms rational_restriction
end ConstructionTargets.CoefficientChartRestriction
