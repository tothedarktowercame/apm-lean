import ConstructionTargets.CoefficientFiniteModelChart
import ConstructionTargets.OneDimensionalChartLocalGenerator
noncomputable section
namespace ConstructionTargets.CoefficientManifoldLocalComparison
open CategoryTheory
open CoefficientNeighborhoodLocal CoefficientChartPair
variable (R : Type) [CommRing R]
variable {M : Type} [TopologicalSpace M] [T2Space M]
abbrev H (X : Type) [TopologicalSpace X] (x : X) (n : ℕ) :=
  (CoefficientRelativeSmall.relativeChains R (deleted x)).homology n
variable {d : ℕ}
def centered (a : EuclideanSpace ℝ (Fin d)) := Homeomorph.addRight (-a)
lemma centered_center (a : EuclideanSpace ℝ (Fin d)) : centered a a = 0 := by simp [centered]
def translationIso (a : EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    H R _ a n ≅ H R (EuclideanSpace ℝ (Fin d)) 0 n := by
  simpa only [centered_center] using homologyIso R (centered a) a n

def point (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) : e.source := ⟨x,hx⟩
omit [T2Space M] in
lemma source_deleted_eq (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) : deleted (point e x hx) = localDeleted e.source x := by
  ext y
  simp only [deleted, localDeleted, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, point]
omit [T2Space M] in
lemma target_deleted_eq (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) : deleted (e.toHomeomorphSourceTarget (point e x hx)) = localDeleted e.target (e x) := by
  ext y
  simp only [deleted, localDeleted, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff]
  rfl

def sourceIso (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) (n : ℕ) : H R e.source (point e x hx) n ≅ H R M x n := by
  simpa only [H, source_deleted_eq] using inclusionIso R e.source x e.open_source hx n

def targetIso (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) (n : ℕ) :
    H R e.target (e.toHomeomorphSourceTarget (point e x hx)) n ≅ H R _ (e x) n := by
  simpa only [H, target_deleted_eq] using inclusionIso R e.target (e x) e.open_target (e.map_source hx) n

def comparison (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) (n : ℕ) : H R M x n ≅ H R (EuclideanSpace ℝ (Fin d)) 0 n :=
  (sourceIso R e x hx n).symm ≪≫ homologyIso R e.toHomeomorphSourceTarget (point e x hx) n ≪≫
    targetIso R e x hx n ≪≫ translationIso R (e x) n

theorem forward (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) (n : ℕ) :
    (comparison R e x hx n).hom = (sourceIso R e x hx n).inv ≫
      HomologicalComplex.homologyMap (deletedMap R e.toHomeomorphSourceTarget (point e x hx)) n ≫
      (targetIso R e x hx n).hom ≫ (translationIso R (e x) n).hom := rfl

theorem inverse_left (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) (n : ℕ) :
    (comparison R e x hx n).inv ≫ (comparison R e x hx n).hom = 𝟙 _ :=
  (comparison R e x hx n).inv_hom_id

theorem inverse_right (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)))
    (x : M) (hx : x ∈ e.source) (n : ℕ) :
    (comparison R e x hx n).hom ≫ (comparison R e x hx n).inv = 𝟙 _ :=
  (comparison R e x hx n).hom_inv_id

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M]
def modelChart (hd : Module.finrank ℝ E = d) (x : M) :=
  CoefficientFiniteModelChart.converted hd (chartAt E x)
omit [T2Space M] in
lemma modelChart_center (hd : Module.finrank ℝ E = d) (x : M) : x ∈ (modelChart hd x).source := by
  rw [modelChart, CoefficientFiniteModelChart.converted_source]
  exact mem_chart_source E x

def lowComparison (hd : Module.finrank ℝ E = d) (_hlow : d ≤ 1) (x : M) (n : ℕ) :=
  comparison R (modelChart hd x) x (modelChart_center hd x) n

def allComparison (d : ℕ) (hd : Module.finrank ℝ E = d) (x : M) (n : ℕ) :
    H R M x n ≅ H R (EuclideanSpace ℝ (Fin d)) 0 n := by
  match d with
  | 0 => exact lowComparison R hd (by decide) x n
  | 1 => exact lowComparison R hd (by decide) x n
  | m+2 => exact CoefficientFiniteModelChart.comparison R m hd x n

theorem low_forward (hd : Module.finrank ℝ E = d) (hlow : d ≤ 1) (x : M) (n : ℕ) :
    (lowComparison R hd hlow x n).hom =
      (sourceIso R (modelChart hd x) x (modelChart_center hd x) n).inv ≫
      HomologicalComplex.homologyMap (deletedMap R (modelChart hd x).toHomeomorphSourceTarget
        (point (modelChart hd x) x (modelChart_center hd x))) n ≫
      (targetIso R (modelChart hd x) x (modelChart_center hd x) n).hom ≫
      (translationIso R (modelChart hd x x) n).hom := rfl

theorem zero_eq (hd : Module.finrank ℝ E = 0) (x : M) (n : ℕ) :
    allComparison R 0 hd x n = lowComparison R hd (by decide) x n := rfl

theorem one_eq (hd : Module.finrank ℝ E = 1) (x : M) (n : ℕ) :
    allComparison R 1 hd x n = lowComparison R hd (by decide) x n := rfl

theorem higher_eq (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) (n : ℕ) :
    allComparison R (m+2) hd x n = CoefficientFiniteModelChart.comparison R m hd x n := rfl

theorem all_inverse_left (hd : Module.finrank ℝ E = d) (x : M) (n : ℕ) :
    (allComparison R d hd x n).inv ≫ (allComparison R d hd x n).hom = 𝟙 _ :=
  (allComparison R d hd x n).inv_hom_id

theorem all_inverse_right (hd : Module.finrank ℝ E = d) (x : M) (n : ℕ) :
    (allComparison R d hd x n).hom ≫ (allComparison R d hd x n).inv = 𝟙 _ :=
  (allComparison R d hd x n).hom_inv_id

def normalization (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) :=
  allComparison R (m+2) hd x (m+2) ≪≫ CoefficientModelLocal.localIso R m

def generator (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) :=
  (normalization R m hd x).inv.hom (1 : R)
theorem generator_normalization (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) :
    (normalization R m hd x).hom.hom (generator R m hd x) = 1 :=
  congrArg (fun f => f.hom (1 : R)) (normalization R m hd x).inv_hom_id

theorem generator_image (m : ℕ) (hd : Module.finrank ℝ E = m+2) (x : M) :
    (allComparison R (m+2) hd x (m+2)).hom.hom (generator R m hd x) = CoefficientModelLocal.generator R m := by
  apply (ConcreteCategory.bijective_of_isIso (CoefficientModelLocal.localIso R m).hom).1
  exact (generator_normalization R m hd x).trans (CoefficientModelLocal.generator_normalization R m).symm

#print axioms comparison
#print axioms low_forward
#print axioms allComparison
#print axioms higher_eq
#print axioms zero_eq
#print axioms one_eq
#print axioms all_inverse_left
#print axioms all_inverse_right
#print axioms generator_normalization
#print axioms generator_image
#check OneDimensionalChartLocalGenerator.ambientLocalGenerator_generates
#print axioms OneDimensionalChartLocalGenerator.ambientLocalGenerator_generates
end ConstructionTargets.CoefficientManifoldLocalComparison
