import ConstructionTargets.LocalHomologyNeighborhoodExcision
import ConstructionTargets.CoefficientChartTransitionUnit
import ConstructionTargets.CoefficientTransitionLocalConstancy
import ConstructionTargets.CoefficientDistinguishedNormalization
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.HigherChartLocalGenerator

open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option autoImplicit false

namespace ConstructionTargets.ManifoldFundamentalClass

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.ChartPairRelativeHomologyTransport
open ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.CoefficientChartTransitionUnit
open ConstructionTargets.CoefficientNeighborhoodLocal
open ConstructionTargets.CoefficientOverlapPair
open ConstructionTargets.CoefficientTransitionLocalConstancy
open ConstructionTargets.IntegralSingularHomologyComparison

variable {X : Type} [TopologicalSpace X]

/-- Excision identifies the positive-degree local homology computed in any
open neighborhood of the distinguished point with the ambient local homology.
-/
theorem neighborhoodInclusion_Hsucc_isIso [T1Space X]
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U x) (deletedPoint x)
        (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)) (n + 1)) := by
  have hZ : Uᶜ ⊆ interior (deletedPoint x) := by
    have ho : IsOpen (deletedPoint x) := isClosed_singleton.isOpen_compl
    rw [ho.interior_eq]
    intro y hy hxy
    exact hy (hxy.symm ▸ hx)
  letI := relativeExcisionMap_homologyMap_isIso_succ
    (deletedPoint x) Uᶜ hU.isClosed_compl hZ n
  letI := relativeSingularMap_homeomorphPair_isIso
    (neighborhoodExcisionHomeomorph U)
    (neighborhoodDeletedPoint U x) (excisedSubspace (deletedPoint x) Uᶜ)
    (neighborhoodExcision_pair_iff U x) (n + 1)
  rw [neighborhoodInclusion_chain_eq, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Two normalized chart generators agree when their overlap transition acts
by the unit `1`.  The orientation argument establishing that hypothesis is a
separate downstream step. -/
theorem chartGenerator_eq_of_transitionUnit_eq_one
    (R : Type) [CommRing R] (m : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b x : M)
    (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source)
    (hori : transitionUnit R m a b x ha hb = 1) :
    chartGenerator R m a x ha = chartGenerator R m b x hb := by
  rw [generator_change R m a b x ha hb, hori]
  exact one_smul R _

/-- The transition unit restricted to the subtype of points in both chart
domains. -/
def overlapTransitionUnit (R : Type) [CommRing R] (m : ℕ)
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) (x : common m a b) : Rˣ :=
  transitionUnit R m a b x.1 x.2.1 x.2.2

theorem overlapTransitionUnit_isLocallyConstant
    (R : Type) [CommRing R] (m : ℕ)
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) : IsLocallyConstant (overlapTransitionUnit R m a b) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨V, hVopen, hxV, hVsub, heq⟩ := locally_constant R m a b x.1 x.2
  refine ⟨Subtype.val ⁻¹' V, hVopen.preimage continuous_subtype_val, hxV, ?_⟩
  intro y hy
  obtain ⟨hyCommon, hunit⟩ := heq y.1 hy
  simpa only [overlapTransitionUnit] using hunit

theorem overlapTransitionUnit_eq_of_isPreconnected
    (R : Type) [CommRing R] (m : ℕ)
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) (hconn : IsPreconnected (common m a b))
    (x y : common m a b) :
    overlapTransitionUnit R m a b x = overlapTransitionUnit R m a b y := by
  letI : PreconnectedSpace (common m a b) := Subtype.preconnectedSpace hconn
  exact (overlapTransitionUnit_isLocallyConstant R m a b).apply_eq_of_preconnectedSpace x y

theorem overlapTransitionUnit_eq_one_of_isPreconnected
    (R : Type) [CommRing R] (m : ℕ)
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) (hconn : IsPreconnected (common m a b))
    (x : common m a b) (hx : overlapTransitionUnit R m a b x = 1)
    (y : common m a b) : overlapTransitionUnit R m a b y = 1 := by
  exact (overlapTransitionUnit_eq_of_isPreconnected R m a b hconn x y).symm.trans hx

theorem chartGenerator_eq_on_preconnected_overlap_of_baseUnit_eq_one
    (R : Type) [CommRing R] (m : ℕ)
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) (hconn : IsPreconnected (common m a b))
    (x : common m a b) (hx : overlapTransitionUnit R m a b x = 1)
    (y : common m a b) :
    chartGenerator R m a y.1 y.2.1 = chartGenerator R m b y.1 y.2.2 := by
  apply chartGenerator_eq_of_transitionUnit_eq_one R m a b y.1 y.2.1 y.2.2
  exact overlapTransitionUnit_eq_one_of_isPreconnected R m a b hconn x hx y

theorem integralOverlapTransitionUnit_eq_one_or_neg_one
    (m : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) (x : common m a b) :
    overlapTransitionUnit ℤ m a b x = 1 ∨
      overlapTransitionUnit ℤ m a b x = -1 := by
  let u := overlapTransitionUnit ℤ m a b x
  have huv : (u : ℤ) * (u⁻¹ : ℤˣ) = 1 := u.val_inv
  rcases Int.eq_one_or_neg_one_of_mul_eq_one huv with hu | hu
  · left
    apply Units.ext
    exact hu
  · right
    apply Units.ext
    exact hu

theorem integralOverlapTransitionUnit_eq_one_of_ne_neg_one
    (m : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) (x : common m a b)
    (hneg : overlapTransitionUnit ℤ m a b x ≠ -1) :
    overlapTransitionUnit ℤ m a b x = 1 := by
  rcases integralOverlapTransitionUnit_eq_one_or_neg_one m a b x with h | h
  · exact h
  · exact (hneg h).elim

theorem integralChartGenerator_eq_on_preconnected_overlap_of_ne_neg_one
    (m : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (a b : M) (hconn : IsPreconnected (common m a b))
    (x : common m a b) (hneg : overlapTransitionUnit ℤ m a b x ≠ -1)
    (y : common m a b) :
    chartGenerator ℤ m a y.1 y.2.1 = chartGenerator ℤ m b y.1 y.2.2 := by
  apply chartGenerator_eq_on_preconnected_overlap_of_baseUnit_eq_one
    ℤ m a b hconn x
  exact integralOverlapTransitionUnit_eq_one_of_ne_neg_one m a b x hneg

def globalGenerator (R : Type) [CommRing R] (G : ModuleCat R)
    (e : G ≅ ModuleCat.of R R) : G :=
  e.inv.hom 1

theorem globalGenerator_generates (R : Type) [CommRing R] (G : ModuleCat R)
    (e : G ≅ ModuleCat.of R R) :
    ∀ z : G, ∃ r : R, r • globalGenerator R G e = z := by
  intro z
  refine ⟨e.hom.hom z, ?_⟩
  unfold globalGenerator
  rw [← e.inv.hom.map_smul]
  change e.inv.hom (e.hom.hom z • (1 : R)) = z
  rw [smul_eq_mul, mul_one]
  exact ConcreteCategory.congr_hom e.hom_inv_id z

theorem mapGlobalGenerator_generates_of_isIso
    (R : Type) [CommRing R] (G H : ModuleCat R)
    (e : G ≅ ModuleCat.of R R) (f : G ⟶ H) [IsIso f] :
    ∀ z : H, ∃ r : R, r • f.hom (globalGenerator R G e) = z := by
  intro z
  obtain ⟨r, hr⟩ := globalGenerator_generates R G e ((asIso f).inv.hom z)
  refine ⟨r, ?_⟩
  rw [← f.hom.map_smul, hr]
  exact ConcreteCategory.congr_hom (asIso f).inv_hom_id z

theorem isIso_of_map_globalGenerator_eq_globalGenerator
    (R : Type) [CommRing R] (G H : ModuleCat R)
    (eG : G ≅ ModuleCat.of R R) (eH : H ≅ ModuleCat.of R R)
    (f : G ⟶ H)
    (hgen : f.hom (globalGenerator R G eG) = globalGenerator R H eH) :
    IsIso f := by
  have hf : f = eG.hom ≫ eH.inv := by
    ext z
    obtain ⟨r, rfl⟩ := globalGenerator_generates R G eG z
    rw [map_smul, hgen]
    change r • eH.inv.hom 1 = eH.inv.hom (eG.hom.hom (r • eG.inv.hom 1))
    rw [map_smul, map_smul]
    have hone : eG.hom.hom (eG.inv.hom (1 : R)) = 1 :=
      ConcreteCategory.congr_hom eG.inv_hom_id 1
    rw [hone]
  rw [hf]
  infer_instance

def absoluteSingularMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : SingularChains (TopCat.of X) ⟶ SingularChains (TopCat.of Y) :=
  ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)

def localizationMap {X : Type} [TopologicalSpace X] (x : X) (n : ℕ) :
    (SingularChains (TopCat.of X)).homology n ⟶
      (RelativeSingularChains (deletedPoint x)).homology n :=
  HomologicalComplex.homologyMap (relativeSingularProjection (deletedPoint x)) n

theorem localizationMap_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y)
    (h : Set.MapsTo f (deletedPoint x) (deletedPoint y)) (n : ℕ) :
    HomologicalComplex.homologyMap (absoluteSingularMap f) n ≫ localizationMap y n =
      localizationMap x n ≫
        HomologicalComplex.homologyMap
          (relativeSingularMap (deletedPoint x) (deletedPoint y) f h) n := by
  have hchain := relativeSingularMap_projection_naturality
    (deletedPoint x) (deletedPoint y) f h
  have hhom := congrArg (fun q => HomologicalComplex.homologyMap q n) hchain
  simpa only [HomologicalComplex.homologyMap_comp, localizationMap,
    absoluteSingularMap] using hhom

theorem localizationMap_apply_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y)
    (h : Set.MapsTo f (deletedPoint x) (deletedPoint y)) (n : ℕ)
    (c : (SingularChains (TopCat.of X)).homology n) :
    localizationMap y n
        (HomologicalComplex.homologyMap (absoluteSingularMap f) n c) =
      HomologicalComplex.homologyMap
          (relativeSingularMap (deletedPoint x) (deletedPoint y) f h) n
        (localizationMap x n c) := by
  exact ConcreteCategory.congr_hom (localizationMap_naturality f x y h n) c

private abbrev moduleSingularHomology (X : TopCat) (n : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj X)

private abbrev moduleSingularHomologyMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map f)

def groupGlobalGenerator (X : TopCat) (n : ℕ)
    (e : moduleSingularHomology X n ≅ ModuleCat.of ℤ ℤ) :
    (SingularChains X).homology n :=
  (singularHomologyComparison X n).hom.hom
    (globalGenerator ℤ (moduleSingularHomology X n) e)

theorem groupGlobalGenerator_generates (X : TopCat) (n : ℕ)
    (e : moduleSingularHomology X n ≅ ModuleCat.of ℤ ℤ)
    (z : (SingularChains X).homology n) :
    ∃ r : ℤ, r • groupGlobalGenerator X n e = z := by
  let c := (singularHomologyComparison X n).inv.hom z
  obtain ⟨r, hr⟩ := globalGenerator_generates ℤ (moduleSingularHomology X n) e c
  have hrz : r • globalGenerator ℤ (moduleSingularHomology X n) e = c := by
    rw [← int_smul_eq_zsmul]
    exact hr
  refine ⟨r, ?_⟩
  rw [groupGlobalGenerator]
  calc
    r • (singularHomologyComparison X n).hom.hom
          (globalGenerator ℤ (moduleSingularHomology X n) e) =
        (singularHomologyComparison X n).hom.hom
          (r • globalGenerator ℤ (moduleSingularHomology X n) e) := by
            exact ((singularHomologyComparison X n).hom.hom.map_zsmul _ _).symm
    _ = (singularHomologyComparison X n).hom.hom c := congrArg _ hrz
    _ = z := ConcreteCategory.congr_hom
      (singularHomologyComparison X n).inv_hom_id z

theorem absoluteSingularMap_groupGlobalGenerator_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ)
    (eX : moduleSingularHomology (TopCat.of X) n ≅ ModuleCat.of ℤ ℤ)
    (eY : moduleSingularHomology (TopCat.of Y) n ≅ ModuleCat.of ℤ ℤ)
    (hmodule : (moduleSingularHomologyMap (TopCat.ofHom f) n).hom
        (globalGenerator ℤ (moduleSingularHomology (TopCat.of X) n) eX) =
      globalGenerator ℤ (moduleSingularHomology (TopCat.of Y) n) eY) :
    HomologicalComplex.homologyMap (absoluteSingularMap f) n
        (groupGlobalGenerator (TopCat.of X) n eX) =
      groupGlobalGenerator (TopCat.of Y) n eY := by
  have hmodule' :
      (forgetIntModules.map (moduleSingularHomologyMap (TopCat.ofHom f) n)).hom
          (globalGenerator ℤ (moduleSingularHomology (TopCat.of X) n) eX) =
        globalGenerator ℤ (moduleSingularHomology (TopCat.of Y) n) eY := hmodule
  have hn := ConcreteCategory.congr_hom
    (singularHomologyComparison_naturality (TopCat.ofHom f) n)
    (globalGenerator ℤ (moduleSingularHomology (TopCat.of X) n) eX)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hmodule'] at hn
  simpa only [groupGlobalGenerator, absoluteSingularMap] using hn.symm

theorem localizationMap_groupGlobalGenerator_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y)
    (h : Set.MapsTo f (deletedPoint x) (deletedPoint y)) (n : ℕ)
    (eX : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) ≅ ModuleCat.of ℤ ℤ)
    (eY : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)) ≅ ModuleCat.of ℤ ℤ)
    (gx : (RelativeSingularChains (deletedPoint x)).homology n)
    (gy : (RelativeSingularChains (deletedPoint y)).homology n)
    (hmodule : ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))).hom
        (globalGenerator ℤ
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
            (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) eX) =
      globalGenerator ℤ
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)) eY)
    (hx : localizationMap x n (groupGlobalGenerator (TopCat.of X) n eX) = gx)
    (hlocal : HomologicalComplex.homologyMap
        (relativeSingularMap (deletedPoint x) (deletedPoint y) f h) n gx = gy) :
    localizationMap y n (groupGlobalGenerator (TopCat.of Y) n eY) = gy := by
  rw [← absoluteSingularMap_groupGlobalGenerator_naturality f n eX eY hmodule]
  rw [localizationMap_apply_naturality f x y h n]
  rw [hx, hlocal]

theorem localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M]
    (e : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) (k + 2)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of M)) ≅ ModuleCat.of ℤ ℤ)
    (x : M) :
    ∃ r : ℤ, r • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x =
      localizationMap x (k + 2) (groupGlobalGenerator (TopCat.of M) (k + 2) e) := by
  exact HigherChartLocalGenerator.ambientLocalGenerator_generates (k := k) x
    (localizationMap x (k + 2) (groupGlobalGenerator (TopCat.of M) (k + 2) e))

theorem ambientLocalGenerator_zsmul_injective
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    Function.Injective (fun r : ℤ =>
      r • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x) := by
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap (HigherChartLocalGenerator.P k) (deletedPoint x)
      (HigherChartLocalGenerator.ambientChartMap (k := k) x)
      (HigherChartLocalGenerator.ambientChartMap_mapsTo (k := k) x)) (k + 2)
  letI := HigherChartLocalGenerator.ambientChartMap_Hn_isIso (k := k) x
  intro r s hrs
  have hrs' := congrArg
    (fun z => (ConstructionTargets.HigherModelLocalHomology.localIsoInt k).hom
      ((asIso f).inv.hom z)) hrs
  change (ConstructionTargets.HigherModelLocalHomology.localIsoInt k).hom
      ((asIso f).inv.hom
        (r • f (ConstructionTargets.HigherModelLocalHomology.generator k))) =
    (ConstructionTargets.HigherModelLocalHomology.localIsoInt k).hom
      ((asIso f).inv.hom
        (s • f (ConstructionTargets.HigherModelLocalHomology.generator k))) at hrs'
  simp only [map_zsmul] at hrs'
  have hinv : (asIso f).inv.hom
      (f.hom (ConstructionTargets.HigherModelLocalHomology.generator k)) =
      ConstructionTargets.HigherModelLocalHomology.generator k :=
    ConcreteCategory.congr_hom (asIso f).hom_inv_id _
  rw [hinv,
    ConstructionTargets.HigherModelLocalHomology.normalization,
    smul_eq_mul, mul_one, smul_eq_mul, mul_one] at hrs'
  exact hrs'

theorem localizationCoefficient_eq_one_of_normalized
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M]
    (e : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) (k + 2)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of M)) ≅ ModuleCat.of ℤ ℤ)
    (x : M) (r : ℤ)
    (hr : r • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x =
      localizationMap x (k + 2) (groupGlobalGenerator (TopCat.of M) (k + 2) e))
    (hnormalized : localizationMap x (k + 2)
        (groupGlobalGenerator (TopCat.of M) (k + 2) e) =
      HigherChartLocalGenerator.ambientLocalGenerator (k := k) x) :
    r = 1 := by
  apply ambientLocalGenerator_zsmul_injective k x
  change r • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x =
    1 • HigherChartLocalGenerator.ambientLocalGenerator (k := k) x
  simpa only [one_zsmul] using hr.trans hnormalized

theorem distinguishedChartGenerator_eq_coefficientGenerator
    (R : Type) [CommRing R] (m : ℕ)
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) :
    CoefficientChartTransitionUnit.chartGenerator R m x x (mem_chart_source _ x) =
      CoefficientChartLocal.generator R m x := by
  unfold CoefficientChartTransitionUnit.chartGenerator
    CoefficientChartTransitionUnit.chartNormalization
    CoefficientChartLocal.generator
  rw [CoefficientDistinguishedNormalization.distinguished R m x]
  rfl

def integralSubtypeInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem integralSingularChainsComparison_subtype_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (integralSubtypeInclusion A))) ≫
        (singularChainsComparison (TopCat.of X)).hom =
      (singularChainsComparison (TopCat.of A)).hom ≫
        (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (integralSubtypeInclusion A)) := by
  exact singularChainsComparison_naturality (integralSubtypeInclusion A)

/-- The coefficient-relative subtype map is exactly the module-valued
topological singular-chain map used by the integral comparison. -/
theorem coefficientSubspaceMap_eq_integralSubtypeChainMap
    {X : Type} [TopologicalSpace X] (A : Set X) :
    CoefficientRelativeSmall.subspaceMap ℤ A =
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (integralSubtypeInclusion A)) := by
  rfl

private abbrev moduleSubtypeChainMap {X : Type} [TopologicalSpace X]
    (A : Set X) :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (integralSubtypeInclusion A))

private abbrev groupSubtypeChainMap {X : Type} [TopologicalSpace X]
    (A : Set X) :=
  (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (integralSubtypeInclusion A))

/-- The absolute integral chain comparison induces the canonical comparison
between the direct relative cokernels of the same subtype inclusion. -/
noncomputable def integralMappedRelativeCokernelComparison
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel ((forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map (moduleSubtypeChainMap A)) ≅
      cokernel (groupSubtypeChainMap A) :=
  cokernel.mapIso
    ((forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map (moduleSubtypeChainMap A))
    (groupSubtypeChainMap A)
    (singularChainsComparison (TopCat.of A))
    (singularChainsComparison (TopCat.of X))
    (integralSingularChainsComparison_subtype_naturality A)

/-- Forgetting the integer-module structure commutes canonically with the
relative-chain cokernel of a subtype inclusion. -/
noncomputable def forgetIntegralRelativeCokernelComparison
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CoefficientRelativeSmall.relativeChains ℤ A) ≅
      cokernel ((forgetIntModules.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (CoefficientRelativeSmall.subspaceMap ℤ A)) := by
  letI : (forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).IsEquivalence := by
    change ((forgetIntModules.asEquivalence.mapHomologicalComplex
      (ComplexShape.down ℕ)).functor).IsEquivalence
    infer_instance
  exact
    PreservesCokernel.iso
      (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ))
      (CoefficientRelativeSmall.subspaceMap ℤ A)

/-- The canonical chain-complex comparison from integral coefficient-relative
chains, after forgetting module structure, to production relative singular
chains. -/
noncomputable def integralRelativeChainsComparison
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CoefficientRelativeSmall.relativeChains ℤ A) ≅
      RelativeSingularChains A :=
  forgetIntegralRelativeCokernelComparison A ≪≫
    integralMappedRelativeCokernelComparison A ≪≫
    (relativeSingularChainsIsoCokernelSubspaceMap A).symm

/-- The relative-chain comparison induces the canonical comparison from
forgotten integral coefficient-relative homology to production relative
singular homology. -/
noncomputable def integralRelativeHomologyComparison
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    forgetIntModules.obj
        ((CoefficientRelativeSmall.relativeChains ℤ A).homology n) ≅
      (RelativeSingularChains A).homology n := by
  let K := CoefficientRelativeSmall.relativeChains ℤ A
  exact ((K.sc n).mapHomologyIso forgetIntModules).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat
      (ComplexShape.down ℕ) n).mapIso (integralRelativeChainsComparison A)

/-- Normalize production ambient local homology by pulling back through the
actual ambient chart map and then applying the concrete model normalization. -/
noncomputable def ambientLocalNormalization
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (RelativeSingularChains (deletedPoint x)).homology (k + 2) ≅
      AddCommGrpCat.of ℤ := by
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap (HigherChartLocalGenerator.P k) (deletedPoint x)
      (HigherChartLocalGenerator.ambientChartMap (k := k) x)
      (HigherChartLocalGenerator.ambientChartMap_mapsTo (k := k) x)) (k + 2)
  letI := HigherChartLocalGenerator.ambientChartMap_Hn_isIso (k := k) x
  exact (asIso f).symm ≪≫ HigherModelLocalHomology.localIsoInt k

theorem ambientLocalNormalization_generator
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (ambientLocalNormalization k x).hom.hom
        (HigherChartLocalGenerator.ambientLocalGenerator (k := k) x) = 1 := by
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap (HigherChartLocalGenerator.P k) (deletedPoint x)
      (HigherChartLocalGenerator.ambientChartMap (k := k) x)
      (HigherChartLocalGenerator.ambientChartMap_mapsTo (k := k) x)) (k + 2)
  letI := HigherChartLocalGenerator.ambientChartMap_Hn_isIso (k := k) x
  change (HigherModelLocalHomology.localIsoInt k).hom.hom
    ((asIso f).inv.hom (f (HigherModelLocalHomology.generator k))) = 1
  have h := ConcreteCategory.congr_hom (asIso f).hom_inv_id
    (HigherModelLocalHomology.generator k)
  change (asIso f).inv.hom (f (HigherModelLocalHomology.generator k)) =
    HigherModelLocalHomology.generator k at h
  rw [h]
  exact HigherModelLocalHomology.normalization k

/-- The concrete coefficient-to-production normalization square forces exact
transport of the two normalized chart generators. -/
theorem integralRelativeHomologyComparison_generator_of_normalization
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hcompat :
      (integralRelativeHomologyComparison (deletedPoint x) (k + 2)).hom ≫
          (ambientLocalNormalization k x).hom =
        forgetIntModules.map (CoefficientChartLocal.localIso ℤ k x).hom) :
    (integralRelativeHomologyComparison (deletedPoint x) (k + 2)).hom.hom
        (CoefficientChartLocal.generator ℤ k x) =
      HigherChartLocalGenerator.ambientLocalGenerator (k := k) x := by
  apply (ConcreteCategory.bijective_of_isIso
    (ambientLocalNormalization k x).hom).1
  have h := ConcreteCategory.congr_hom hcompat
    (CoefficientChartLocal.generator ℤ k x)
  change (ambientLocalNormalization k x).hom.hom
      ((integralRelativeHomologyComparison (deletedPoint x) (k + 2)).hom.hom
        (CoefficientChartLocal.generator ℤ k x)) =
    (CoefficientChartLocal.localIso ℤ k x).hom.hom
      (CoefficientChartLocal.generator ℤ k x) at h
  rw [h, CoefficientChartLocal.generator_normalization,
    ambientLocalNormalization_generator]

/-- The canonical integral direct-cokernel comparison intertwines the two
absolute-to-relative cokernel projections. -/
theorem integralDirectCokernelComparison_projection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel.π
        ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (integralSubtypeInclusion A))) ≫
      (integralMappedRelativeCokernelComparison A).hom =
    (singularChainsComparison (TopCat.of X)).hom ≫
      cokernel.π (singularSubspaceMap A) := by
  unfold integralMappedRelativeCokernelComparison
  rw [cokernel.mapIso_hom]
  unfold cokernel.map
  rw [cokernel.π_desc]
  rfl

/-- The canonical preservation isomorphism carries the forgotten coefficient
relative projection to the cokernel projection formed after forgetting. -/
theorem forgetIntegralRelativeCokernelComparison_projection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
      (forgetIntegralRelativeCokernelComparison A).hom =
    cokernel.π
      ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (CoefficientRelativeSmall.subspaceMap ℤ A)) := by
  unfold forgetIntegralRelativeCokernelComparison
  rw [PreservesCokernel.π_iso_hom]

private abbrev forgottenCoefficientSubtypeMap
    {X : Type} [TopologicalSpace X] (A : Set X) :=
  (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (CoefficientRelativeSmall.subspaceMap ℤ A)

private abbrev forgottenIntegralSubtypeMap
    {X : Type} [TopologicalSpace X] (A : Set X) :=
  (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (integralSubtypeInclusion A))

/-- Canonical transport between the two equal presentations of the forgotten
integral subtype map at the level of direct cokernels. -/
noncomputable def coefficientIntegralCokernelTransport
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (CoefficientRelativeSmall.subspaceMap ℤ A)) ≅
    cokernel ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (integralSubtypeInclusion A))) :=
  cokernel.mapIso
    (forgottenCoefficientSubtypeMap A)
    (forgottenIntegralSubtypeMap A)
    (Iso.refl _)
    (Iso.refl _)
    (by
      change forgottenCoefficientSubtypeMap A = forgottenIntegralSubtypeMap A
      exact congrArg
        (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (coefficientSubspaceMap_eq_integralSubtypeChainMap A))

theorem coefficientIntegralCokernelTransport_projection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel.π ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
      (coefficientIntegralCokernelTransport A).hom =
    cokernel.π ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (integralSubtypeInclusion A))) := by
  unfold coefficientIntegralCokernelTransport
  rw [cokernel.mapIso_hom]
  unfold cokernel.map
  rw [cokernel.π_desc]
  simp

/-- The three canonical integral cokernel comparisons intertwine the complete
forgotten coefficient projection with the production direct-cokernel projection. -/
theorem integralCompositeCokernelComparison_projection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
      (forgetIntegralRelativeCokernelComparison A).hom ≫
      (coefficientIntegralCokernelTransport A).hom ≫
      (integralMappedRelativeCokernelComparison A).hom =
    (singularChainsComparison (TopCat.of X)).hom ≫
      cokernel.π (singularSubspaceMap A) := by
  rw [← Category.assoc,
    forgetIntegralRelativeCokernelComparison_projection]
  rw [← Category.assoc, coefficientIntegralCokernelTransport_projection]
  exact integralDirectCokernelComparison_projection A

/-- The direct production cokernel projection followed by the inverse
presentation isomorphism is the actual relative singular-chain projection. -/
theorem cokernelProjection_comp_relativeSingularChainsIso_inv
    {X : Type} [TopologicalSpace X] (A : Set X) :
    cokernel.π (singularSubspaceMap A) ≫
      (relativeSingularChainsIsoCokernelSubspaceMap A).inv =
    relativeSingularProjection A := by
  rw [← relativeProjection_comp_cokernelIso_hom]
  simp

/-- The complete integral comparison carries the forgotten coefficient
projection to the production relative singular-chain projection. -/
theorem integralCompositeRelativeProjection_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
      (forgetIntegralRelativeCokernelComparison A).hom ≫
      (coefficientIntegralCokernelTransport A).hom ≫
      (integralMappedRelativeCokernelComparison A).hom ≫
      (relativeSingularChainsIsoCokernelSubspaceMap A).inv =
    (singularChainsComparison (TopCat.of X)).hom ≫
      relativeSingularProjection A := by
  slice_lhs 1 4 => rw [integralCompositeCokernelComparison_projection]
  simpa only [Category.assoc] using congrArg
    (fun k => (singularChainsComparison (TopCat.of X)).hom ≫ k)
    (cokernelProjection_comp_relativeSingularChainsIso_inv A)

/-- The corrected integral relative-chain comparison includes the canonical
transport between the coefficient and explicit integral subtype-map cokernels. -/
noncomputable def integralRelativeChainsComparisonWithTransport
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CoefficientRelativeSmall.relativeChains ℤ A) ≅
      RelativeSingularChains A :=
  forgetIntegralRelativeCokernelComparison A ≪≫
    coefficientIntegralCokernelTransport A ≪≫
    integralMappedRelativeCokernelComparison A ≪≫
    (relativeSingularChainsIsoCokernelSubspaceMap A).symm

theorem integralRelativeChainsComparisonWithTransport_projection
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
      (integralRelativeChainsComparisonWithTransport A).hom =
    (singularChainsComparison (TopCat.of X)).hom ≫
      relativeSingularProjection A := by
  exact integralCompositeRelativeProjection_naturality A

/-- Pass the transport-explicit integral relative-chain comparison canonically
to homology after forgetting the integer module structure. -/
noncomputable def integralRelativeHomologyComparisonWithTransport
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    forgetIntModules.obj
        ((CoefficientRelativeSmall.relativeChains ℤ A).homology n) ≅
      (RelativeSingularChains A).homology n := by
  let K := CoefficientRelativeSmall.relativeChains ℤ A
  exact ((K.sc n).mapHomologyIso forgetIntModules).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat
      (ComplexShape.down ℕ) n).mapIso
        (integralRelativeChainsComparisonWithTransport A)

/-- Applying homology to the corrected relative-chain projection square gives
the corresponding equality of homology morphisms. -/
theorem integralRelativeChainsComparisonWithTransport_homology_projection
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A))) n ≫
      HomologicalComplex.homologyMap
        (integralRelativeChainsComparisonWithTransport A).hom n =
    HomologicalComplex.homologyMap
        (singularChainsComparison (TopCat.of X)).hom n ≫
      HomologicalComplex.homologyMap (relativeSingularProjection A) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using congrArg
    (fun f => HomologicalComplex.homologyMap f n)
    (integralRelativeChainsComparisonWithTransport_projection A)

/-- Expand the hom of the corrected relative-homology comparison into the
inverse preservation morphism followed by homology of the chain comparison. -/
theorem integralRelativeHomologyComparisonWithTransport_hom
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (integralRelativeHomologyComparisonWithTransport A n).hom =
      (((CoefficientRelativeSmall.relativeChains ℤ A).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        (integralRelativeChainsComparisonWithTransport A).hom n := by
  unfold integralRelativeHomologyComparisonWithTransport
  rfl

/-- Inverse homology preservation is natural for the coefficient
absolute-to-relative projection. -/
theorem coefficientRelativeProjection_mapHomologyIso_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    forgetIntModules.map
        (HomologicalComplex.homologyMap
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) n) ≫
      (((CoefficientRelativeSmall.relativeChains ℤ A).sc n).mapHomologyIso
        forgetIntModules).inv =
    (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A))) n := by
  let φ := cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
    (ComplexShape.down ℕ) n).map φ
  have hpres := ShortComplex.mapHomologyIso_inv_naturality ψ forgetIntModules
  change forgetIntModules.map (ShortComplex.homologyMap ψ) ≫
      (((CoefficientRelativeSmall.relativeChains ℤ A).sc n).mapHomologyIso
        forgetIntModules).inv =
    (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n
  exact hpres

/-- Inverse homology preservation is natural for the coefficient subspace
inclusion. -/
theorem coefficientPairInclusion_mapHomologyIso_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    forgetIntModules.map
        (HomologicalComplex.homologyMap
          (CoefficientRelativeSmall.subspaceMap ℤ A) n) ≫
      (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapHomologyIso
        forgetIntModules).inv =
    (((CoefficientH0.SingularChains ℤ (TopCat.of A)).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (CoefficientRelativeSmall.subspaceMap ℤ A)) n := by
  let φ := CoefficientRelativeSmall.subspaceMap ℤ A
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
    (ComplexShape.down ℕ) n).map φ
  have hpres := ShortComplex.mapHomologyIso_inv_naturality ψ forgetIntModules
  change forgetIntModules.map (ShortComplex.homologyMap ψ) ≫
      (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapHomologyIso
        forgetIntModules).inv =
    (((CoefficientH0.SingularChains ℤ (TopCat.of A)).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        ((forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n
  exact hpres

/-- Inverse cycles preservation is natural for the coefficient subspace
inclusion. -/
theorem coefficientPairInclusion_mapCyclesIso_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    let φ := CoefficientRelativeSmall.subspaceMap ℤ A
    let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) n).map φ
    forgetIntModules.map (ShortComplex.cyclesMap ψ) ≫
        (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapCyclesIso
          forgetIntModules).inv =
      (((CoefficientH0.SingularChains ℤ (TopCat.of A)).sc n).mapCyclesIso
          forgetIntModules).inv ≫
        ShortComplex.cyclesMap
          (forgetIntModules.mapShortComplex.map ψ) := by
  dsimp only
  exact ShortComplex.mapCyclesIso_inv_naturality _ _

/-- Inverse opcycles preservation is natural for the coefficient subspace
inclusion. -/
theorem coefficientPairInclusion_mapOpcyclesIso_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    let φ := CoefficientRelativeSmall.subspaceMap ℤ A
    let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) n).map φ
    forgetIntModules.map (ShortComplex.opcyclesMap ψ) ≫
        (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapOpcyclesIso
          forgetIntModules).inv =
      (((CoefficientH0.SingularChains ℤ (TopCat.of A)).sc n).mapOpcyclesIso
          forgetIntModules).inv ≫
        ShortComplex.opcyclesMap
          (forgetIntModules.mapShortComplex.map ψ) := by
  dsimp only
  exact ShortComplex.mapOpcyclesIso_inv_naturality _ _

/-- Inverse left-homology preservation is natural for the coefficient
subspace inclusion. -/
theorem coefficientPairInclusion_mapLeftHomologyIso_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    let φ := CoefficientRelativeSmall.subspaceMap ℤ A
    let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) n).map φ
    forgetIntModules.map (ShortComplex.leftHomologyMap ψ) ≫
        (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapLeftHomologyIso
          forgetIntModules).inv =
      (((CoefficientH0.SingularChains ℤ (TopCat.of A)).sc n).mapLeftHomologyIso
          forgetIntModules).inv ≫
        ShortComplex.leftHomologyMap
          (forgetIntModules.mapShortComplex.map ψ) := by
  dsimp only
  exact ShortComplex.mapLeftHomologyIso_inv_naturality _ _

/-- Inverse right-homology preservation is natural for the coefficient
subspace inclusion. -/
theorem coefficientPairInclusion_mapRightHomologyIso_naturality
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    let φ := CoefficientRelativeSmall.subspaceMap ℤ A
    let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
      (ComplexShape.down ℕ) n).map φ
    forgetIntModules.map (ShortComplex.rightHomologyMap ψ) ≫
        (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapRightHomologyIso
          forgetIntModules).inv =
      (((CoefficientH0.SingularChains ℤ (TopCat.of A)).sc n).mapRightHomologyIso
          forgetIntModules).inv ≫
        ShortComplex.rightHomologyMap
          (forgetIntModules.mapShortComplex.map ψ) := by
  dsimp only
  exact ShortComplex.mapRightHomologyIso_inv_naturality _ _

/-- Forgetting the integer-module structure preserves short exact
sequences. -/
theorem forgetIntModules_shortExact
    {S : ShortComplex (ModuleCat ℤ)} (hS : S.ShortExact) :
    (S.map forgetIntModules).ShortExact := by
  exact hS.map_of_exact forgetIntModules

/-- Forgetting coefficients preserves the two zero composites in a snake
input, component by component. -/
theorem forgetIntModulesSnakeInput_zero_squares
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    forgetIntModules.mapShortComplex.map S.v₀₁ ≫
        forgetIntModules.mapShortComplex.map S.v₁₂ = 0 ∧
      forgetIntModules.mapShortComplex.map S.v₁₂ ≫
        forgetIntModules.mapShortComplex.map S.v₂₃ = 0 := by
  constructor
  · apply ShortComplex.Hom.ext
    · change forgetIntModules.map S.v₀₁.τ₁ ≫ forgetIntModules.map S.v₁₂.τ₁ = 0
      rw [← forgetIntModules.map_comp, S.w₀₂_τ₁, forgetIntModules.map_zero]
    · change forgetIntModules.map S.v₀₁.τ₂ ≫ forgetIntModules.map S.v₁₂.τ₂ = 0
      rw [← forgetIntModules.map_comp, S.w₀₂_τ₂, forgetIntModules.map_zero]
    · change forgetIntModules.map S.v₀₁.τ₃ ≫ forgetIntModules.map S.v₁₂.τ₃ = 0
      rw [← forgetIntModules.map_comp, S.w₀₂_τ₃, forgetIntModules.map_zero]
  · apply ShortComplex.Hom.ext
    · change forgetIntModules.map S.v₁₂.τ₁ ≫ forgetIntModules.map S.v₂₃.τ₁ = 0
      rw [← forgetIntModules.map_comp, S.w₁₃_τ₁, forgetIntModules.map_zero]
    · change forgetIntModules.map S.v₁₂.τ₂ ≫ forgetIntModules.map S.v₂₃.τ₂ = 0
      rw [← forgetIntModules.map_comp, S.w₁₃_τ₂, forgetIntModules.map_zero]
    · change forgetIntModules.map S.v₁₂.τ₃ ≫ forgetIntModules.map S.v₂₃.τ₃ = 0
      rw [← forgetIntModules.map_comp, S.w₁₃_τ₃, forgetIntModules.map_zero]

/-- Forgetting the integer-module structure preserves limits of parallel
pairs. -/
theorem forgetIntModules_preservesParallelPairLimits :
    PreservesLimitsOfShape WalkingParallelPair forgetIntModules := by
  change PreservesLimitsOfShape WalkingParallelPair
    forgetIntModules.asEquivalence.functor
  infer_instance

/-- Forgetting the integer-module structure preserves colimits of parallel
pairs. -/
theorem forgetIntModules_preservesParallelPairColimits :
    PreservesColimitsOfShape WalkingParallelPair forgetIntModules := by
  change PreservesColimitsOfShape WalkingParallelPair
    forgetIntModules.asEquivalence.functor
  infer_instance

/-- The image of the first component kernel fork of a snake input remains a
limit cone after forgetting the integer-module structure. -/
noncomputable def forgetIntModulesSnakeInput_preservedKernelτ₁
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    IsLimit (forgetIntModules.mapCone
      (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁)) := by
  letI := forgetIntModules_preservesParallelPairLimits
  exact isLimitOfPreserves forgetIntModules S.h₀τ₁

/-- The parallel-pair diagram formed before forgetting integer-module
structure agrees with the parallel-pair diagram formed afterwards. -/
noncomputable def forgetIntModulesParallelPairZeroIso
    {X Y : ModuleCat ℤ} (f : X ⟶ Y) :
    parallelPair f 0 ⋙ forgetIntModules ≅
      parallelPair (forgetIntModules.map f) 0 :=
  NatIso.ofComponents (fun j ↦ match j with
    | WalkingParallelPair.zero => Iso.refl _
    | WalkingParallelPair.one => Iso.refl _) (by
    intro i j g
    rcases i <;> rcases j <;> rcases g
    · simpa only [Functor.comp_obj, Functor.comp_map, parallelPair_obj_zero,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
        using forgetIntModules.map_id X
    · simp
    · simpa only [Functor.comp_obj, Functor.comp_map, parallelPair_obj_zero,
        parallelPair_obj_one, parallelPair_map_right, Iso.refl_hom,
        Category.comp_id, Category.id_comp]
        using forgetIntModules.map_zero X Y
    · simpa only [Functor.comp_obj, Functor.comp_map, parallelPair_obj_one,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
        using forgetIntModules.map_id Y)

/-- Transport the preserved first component kernel cone to the parallel-pair
diagram formed after forgetting the integer-module structure. -/
noncomputable def forgetIntModulesSnakeInput_transportedKernelτ₁
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    IsLimit ((Cone.postcompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₁).hom).obj
        (forgetIntModules.mapCone
          (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁))) :=
  (IsLimit.postcomposeHomEquiv
    (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₁)
    (forgetIntModules.mapCone
      (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁))).symm
        (forgetIntModulesSnakeInput_preservedKernelτ₁ S)

/-- The transported first component kernel cone agrees with the first
component of the kernel fork formed after forgetting coefficients. -/
noncomputable def forgetIntModulesSnakeInput_kernelτ₁ConeIso
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    (Cone.postcompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₁).hom).obj
        (forgetIntModules.mapCone
          (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁)) ≅
      (KernelFork.ofι
        (forgetIntModules.mapShortComplex.map S.v₀₁)
        (forgetIntModulesSnakeInput_zero_squares S).1).map ShortComplex.π₁ :=
  Cone.ext (Iso.refl _) (by
    intro j
    rcases j with (_ | _) <;> rfl)

/-- The first component of the kernel fork formed after forgetting
coefficients is a limit cone. -/
noncomputable def forgetIntModulesSnakeInput_kernelτ₁IsLimit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    IsLimit ((KernelFork.ofι
      (forgetIntModules.mapShortComplex.map S.v₀₁)
      (forgetIntModulesSnakeInput_zero_squares S).1).map ShortComplex.π₁) :=
  (IsLimit.equivIsoLimit
    (forgetIntModulesSnakeInput_kernelτ₁ConeIso S)).toFun
      (forgetIntModulesSnakeInput_transportedKernelτ₁ S)

abbrev ForgottenSnakeKernelτ₂Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
    IsLimit ((KernelFork.ofι (forgetIntModules.mapShortComplex.map S.v₀₁)
      (forgetIntModulesSnakeInput_zero_squares S).1).map ShortComplex.π₂)

/-- The second component of the kernel fork formed after forgetting
coefficients is a limit cone. -/
noncomputable def forgetSnakeKernelτ₂Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeKernelτ₂Limit S := by
  letI := forgetIntModules_preservesParallelPairLimits
  let hp : IsLimit (forgetIntModules.mapCone
      (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂)) :=
    isLimitOfPreserves forgetIntModules S.h₀τ₂
  let ht : IsLimit ((Cone.postcompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₂).hom).obj
        (forgetIntModules.mapCone
          (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂))) :=
    (IsLimit.postcomposeHomEquiv
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₂)
      (forgetIntModules.mapCone
        (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂))).symm hp
  let e : (Cone.postcompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₂).hom).obj
        (forgetIntModules.mapCone
          (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂)) ≅
      (KernelFork.ofι (forgetIntModules.mapShortComplex.map S.v₀₁)
        (forgetIntModulesSnakeInput_zero_squares S).1).map ShortComplex.π₂ :=
    Cone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
  exact (IsLimit.equivIsoLimit e).toFun ht

abbrev ForgottenSnakeKernelτ₃Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
  IsLimit ((KernelFork.ofι (forgetIntModules.mapShortComplex.map S.v₀₁)
    (forgetIntModulesSnakeInput_zero_squares S).1).map ShortComplex.π₃)

/-- The third component of the kernel fork formed after forgetting
coefficients is a limit cone. -/
noncomputable def forgetSnakeKernelτ₃Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeKernelτ₃Limit S := by
  letI := forgetIntModules_preservesParallelPairLimits
  let hp : IsLimit (forgetIntModules.mapCone
      (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃)) :=
    isLimitOfPreserves forgetIntModules S.h₀τ₃
  let ht : IsLimit ((Cone.postcompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₃).hom).obj
        (forgetIntModules.mapCone
          (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃))) :=
    (IsLimit.postcomposeHomEquiv
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₃)
      (forgetIntModules.mapCone
        (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃))).symm hp
  let e : (Cone.postcompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₃).hom).obj
        (forgetIntModules.mapCone
          (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃)) ≅
      (KernelFork.ofι (forgetIntModules.mapShortComplex.map S.v₀₁)
        (forgetIntModulesSnakeInput_zero_squares S).1).map ShortComplex.π₃ :=
    Cone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
  exact (IsLimit.equivIsoLimit e).toFun ht

abbrev ParallelPairZeroπ₁Comparison
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : ShortComplex C} (f : X ⟶ Y) :
    Type _ := parallelPair f 0 ⋙ ShortComplex.π₁ ≅ parallelPair f.τ₁ 0

/-- Evaluating a parallel-pair diagram of short-complex morphisms at its
first object agrees with forming the componentwise parallel pair. -/
noncomputable def scPairZeroπ₁Iso
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : ShortComplex C} (f : X ⟶ Y) :
    ParallelPairZeroπ₁Comparison f :=
  NatIso.ofComponents (fun j ↦ match j with
    | WalkingParallelPair.zero => Iso.refl _
    | WalkingParallelPair.one => Iso.refl _) (by
    intro i j g
    rcases i <;> rcases j <;> rcases g
    · simpa using ShortComplex.π₁.map_id X
    · simp
    · simpa using ShortComplex.π₁.map_zero X Y
    · simpa using ShortComplex.π₁.map_id Y)

abbrev ParallelPairZeroπ₂Comparison
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : ShortComplex C} (f : X ⟶ Y) :
    Type _ := parallelPair f 0 ⋙ ShortComplex.π₂ ≅ parallelPair f.τ₂ 0

/-- Evaluating a parallel-pair diagram of short-complex morphisms at its
second object agrees with forming the componentwise parallel pair. -/
noncomputable def scPairZeroπ₂Iso
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : ShortComplex C} (f : X ⟶ Y) :
    ParallelPairZeroπ₂Comparison f :=
  NatIso.ofComponents (fun j ↦ match j with
    | WalkingParallelPair.zero => Iso.refl _
    | WalkingParallelPair.one => Iso.refl _) (by
    intro i j g
    rcases i <;> rcases j <;> rcases g
    · simpa using ShortComplex.π₂.map_id X
    · simp
    · simpa using ShortComplex.π₂.map_zero X Y
    · simpa using ShortComplex.π₂.map_id Y)

abbrev ParallelPairZeroπ₃Comparison
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : ShortComplex C} (f : X ⟶ Y) :
    Type _ := parallelPair f 0 ⋙ ShortComplex.π₃ ≅ parallelPair f.τ₃ 0

/-- Evaluating a parallel-pair diagram of short-complex morphisms at its
third object agrees with forming the componentwise parallel pair. -/
noncomputable def scPairZeroπ₃Iso
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : ShortComplex C} (f : X ⟶ Y) :
    ParallelPairZeroπ₃Comparison f :=
  NatIso.ofComponents (fun j ↦ match j with
    | WalkingParallelPair.zero => Iso.refl _
    | WalkingParallelPair.one => Iso.refl _) (by
    intro i j g
    rcases i <;> rcases j <;> rcases g
    · simpa using ShortComplex.π₃.map_id X
    · simp
    · simpa using ShortComplex.π₃.map_zero X Y
    · simpa using ShortComplex.π₃.map_id Y)

abbrev ForgottenSnakeKernelLimit (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
  IsLimit (KernelFork.ofι (forgetIntModules.mapShortComplex.map S.v₀₁)
    (forgetIntModulesSnakeInput_zero_squares S).1)

/-- The kernel fork of the first mapped snake-input morphism is a limit. -/
noncomputable def forgetSnakeKernelLimit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeKernelLimit S := by
  let c := KernelFork.ofι (forgetIntModules.mapShortComplex.map S.v₀₁)
    (forgetIntModulesSnakeInput_zero_squares S).1
  apply ShortComplex.isLimitOfIsLimitπ
  · let k := c.map ShortComplex.π₁
    let ht : IsLimit ((Cone.postcompose
        (scPairZeroπ₁Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).inv).obj k) :=
      (IsLimit.postcomposeHomEquiv
        (scPairZeroπ₁Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).symm k).symm
          (forgetIntModulesSnakeInput_kernelτ₁IsLimit S)
    let e : (Cone.postcompose
        (scPairZeroπ₁Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).inv).obj k ≅
        ShortComplex.π₁.mapCone c :=
      Cone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
    exact (IsLimit.equivIsoLimit e).toFun ht

  · let k := c.map ShortComplex.π₂
    let ht : IsLimit ((Cone.postcompose
        (scPairZeroπ₂Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).inv).obj k) :=
      (IsLimit.postcomposeHomEquiv
        (scPairZeroπ₂Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).symm k).symm
          (forgetSnakeKernelτ₂Limit S)
    let e : (Cone.postcompose
        (scPairZeroπ₂Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).inv).obj k ≅
        ShortComplex.π₂.mapCone c :=
      Cone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
    exact (IsLimit.equivIsoLimit e).toFun ht

  · let k := c.map ShortComplex.π₃
    let ht : IsLimit ((Cone.postcompose
        (scPairZeroπ₃Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).inv).obj k) :=
      (IsLimit.postcomposeHomEquiv
        (scPairZeroπ₃Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).symm k).symm
          (forgetSnakeKernelτ₃Limit S)
    let e : (Cone.postcompose
        (scPairZeroπ₃Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).inv).obj k ≅
        ShortComplex.π₃.mapCone c :=
      Cone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
    exact (IsLimit.equivIsoLimit e).toFun ht

abbrev ForgottenSnakeCokernelτ₁Preserved
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
  IsColimit (forgetIntModules.mapCocone
    (CokernelCofork.ofπ S.v₂₃.τ₁ S.w₁₃_τ₁))

/-- The image of the first component cokernel cofork remains a colimit after
forgetting the integer-module structure. -/
noncomputable def forgetSnakeCokernelτ₁Preserved
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeCokernelτ₁Preserved S := by
  letI := forgetIntModules_preservesParallelPairColimits
  exact isColimitOfPreserves forgetIntModules S.h₃τ₁

abbrev ForgottenSnakeCokernelτ₁Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
  IsColimit ((CokernelCofork.ofπ
    (forgetIntModules.mapShortComplex.map S.v₂₃)
    (forgetIntModulesSnakeInput_zero_squares S).2).map ShortComplex.π₁)

/-- The first component cokernel of the forgotten snake input is a colimit. -/
noncomputable def forgetSnakeCokernelτ₁Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeCokernelτ₁Limit S := by
  let c := forgetIntModules.mapCocone
    (CokernelCofork.ofπ S.v₂₃.τ₁ S.w₁₃_τ₁)
  let ht : IsColimit ((Cocone.precompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₁).inv).obj c) :=
    (IsColimit.precomposeInvEquiv
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₁) c).symm
        (forgetSnakeCokernelτ₁Preserved S)
  let e : ((Cocone.precompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₁).inv).obj c) ≅
      (CokernelCofork.ofπ
        (forgetIntModules.mapShortComplex.map S.v₂₃)
        (forgetIntModulesSnakeInput_zero_squares S).2).map ShortComplex.π₁ :=
    Cocone.ext (Iso.refl _) (by
      intro j
      rcases j with (_ | _) <;> rfl)
  exact (IsColimit.equivIsoColimit e).toFun ht

abbrev ForgottenSnakeCokernelτ₂Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
  IsColimit ((CokernelCofork.ofπ
    (forgetIntModules.mapShortComplex.map S.v₂₃)
    (forgetIntModulesSnakeInput_zero_squares S).2).map ShortComplex.π₂)

/-- The second component cokernel of the forgotten snake input is a colimit. -/
noncomputable def forgetSnakeCokernelτ₂Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeCokernelτ₂Limit S := by
  letI := forgetIntModules_preservesParallelPairColimits
  let c := forgetIntModules.mapCocone
    (CokernelCofork.ofπ S.v₂₃.τ₂ S.w₁₃_τ₂)
  let hp : IsColimit c := isColimitOfPreserves forgetIntModules S.h₃τ₂
  let ht : IsColimit ((Cocone.precompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₂).inv).obj c) :=
    (IsColimit.precomposeInvEquiv
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₂) c).symm hp
  let e : ((Cocone.precompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₂).inv).obj c) ≅
      (CokernelCofork.ofπ
        (forgetIntModules.mapShortComplex.map S.v₂₃)
        (forgetIntModulesSnakeInput_zero_squares S).2).map ShortComplex.π₂ :=
    Cocone.ext (Iso.refl _) (by
      intro j
      rcases j with (_ | _) <;> rfl)
  exact (IsColimit.equivIsoColimit e).toFun ht

abbrev ForgottenSnakeCokernelτ₃Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
  IsColimit ((CokernelCofork.ofπ
    (forgetIntModules.mapShortComplex.map S.v₂₃)
    (forgetIntModulesSnakeInput_zero_squares S).2).map ShortComplex.π₃)

/-- The third component cokernel of the forgotten snake input is a colimit. -/
noncomputable def forgetSnakeCokernelτ₃Limit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeCokernelτ₃Limit S := by
  letI := forgetIntModules_preservesParallelPairColimits
  let c := forgetIntModules.mapCocone
    (CokernelCofork.ofπ S.v₂₃.τ₃ S.w₁₃_τ₃)
  let hp : IsColimit c := isColimitOfPreserves forgetIntModules S.h₃τ₃
  let ht : IsColimit ((Cocone.precompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₃).inv).obj c) :=
    (IsColimit.precomposeInvEquiv
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₃) c).symm hp
  let e : ((Cocone.precompose
      (forgetIntModulesParallelPairZeroIso S.v₁₂.τ₃).inv).obj c) ≅
      (CokernelCofork.ofπ
        (forgetIntModules.mapShortComplex.map S.v₂₃)
        (forgetIntModulesSnakeInput_zero_squares S).2).map ShortComplex.π₃ :=
    Cocone.ext (Iso.refl _) (by
      intro j
      rcases j with (_ | _) <;> rfl)
  exact (IsColimit.equivIsoColimit e).toFun ht

abbrev ForgottenSnakeCokernelLimit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :=
  IsColimit (CokernelCofork.ofπ
    (forgetIntModules.mapShortComplex.map S.v₂₃)
    (forgetIntModulesSnakeInput_zero_squares S).2)

/-- The cokernel cofork of the forgotten snake input is a colimit. -/
noncomputable def forgetSnakeCokernelLimit
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ForgottenSnakeCokernelLimit S := by
  let c := CokernelCofork.ofπ
    (forgetIntModules.mapShortComplex.map S.v₂₃)
    (forgetIntModulesSnakeInput_zero_squares S).2
  apply ShortComplex.isColimitOfIsColimitπ c
  · let k := c.map ShortComplex.π₁
    let ht : IsColimit ((Cocone.precompose
        (scPairZeroπ₁Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).hom).obj k) :=
      (IsColimit.precomposeHomEquiv
        (scPairZeroπ₁Iso (forgetIntModules.mapShortComplex.map S.v₁₂)) k).symm
          (forgetSnakeCokernelτ₁Limit S)
    let e : (Cocone.precompose
        (scPairZeroπ₁Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).hom).obj k ≅
        ShortComplex.π₁.mapCocone c :=
      Cocone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
    exact (IsColimit.equivIsoColimit e).toFun ht

  · let k := c.map ShortComplex.π₂
    let ht : IsColimit ((Cocone.precompose
        (scPairZeroπ₂Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).hom).obj k) :=
      (IsColimit.precomposeHomEquiv
        (scPairZeroπ₂Iso (forgetIntModules.mapShortComplex.map S.v₁₂)) k).symm
          (forgetSnakeCokernelτ₂Limit S)
    let e : (Cocone.precompose
        (scPairZeroπ₂Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).hom).obj k ≅
        ShortComplex.π₂.mapCocone c :=
      Cocone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
    exact (IsColimit.equivIsoColimit e).toFun ht
  · let k := c.map ShortComplex.π₃
    let ht : IsColimit ((Cocone.precompose
        (scPairZeroπ₃Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).hom).obj k) :=
      (IsColimit.precomposeHomEquiv
        (scPairZeroπ₃Iso (forgetIntModules.mapShortComplex.map S.v₁₂)) k).symm
          (forgetSnakeCokernelτ₃Limit S)
    let e : (Cocone.precompose
        (scPairZeroπ₃Iso (forgetIntModules.mapShortComplex.map S.v₁₂)).hom).obj k ≅
        ShortComplex.π₃.mapCocone c :=
      Cocone.ext (Iso.refl _) (by intro j; rcases j with (_ | _) <;> rfl)
    exact (IsColimit.equivIsoColimit e).toFun ht

/-- Forgetting the integer-module structure on every component of a snake
input produces a snake input in additive commutative groups. -/
noncomputable def forgetSnakeInput
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    ShortComplex.SnakeInput AddCommGrpCat where
  L₀ := S.L₀.map forgetIntModules
  L₁ := S.L₁.map forgetIntModules
  L₂ := S.L₂.map forgetIntModules
  L₃ := S.L₃.map forgetIntModules
  v₀₁ := forgetIntModules.mapShortComplex.map S.v₀₁
  v₁₂ := forgetIntModules.mapShortComplex.map S.v₁₂
  v₂₃ := forgetIntModules.mapShortComplex.map S.v₂₃
  w₀₂ := (forgetIntModulesSnakeInput_zero_squares S).1
  w₁₃ := (forgetIntModulesSnakeInput_zero_squares S).2
  h₀ := forgetSnakeKernelLimit S
  h₃ := forgetSnakeCokernelLimit S
  L₁_exact := S.L₁_exact.map forgetIntModules
  epi_L₁_g := by
    apply ConcreteCategory.epi_of_surjective
    exact (ModuleCat.epi_iff_surjective S.L₁.g).mp inferInstance
  L₂_exact := S.L₂_exact.map forgetIntModules
  mono_L₂_f := by
    apply ConcreteCategory.mono_of_injective
    exact (ModuleCat.mono_iff_injective S.L₂.f).mp inferInstance

/-- Naturality of the comparison from forgotten coefficient homology to the
homology of the forgotten complex. -/
theorem forgetHomologyMap_naturality
    {ι : Type} {c : ComplexShape ι}
    {K₁ K₂ : HomologicalComplex (ModuleCat ℤ) c} (f : K₁ ⟶ K₂) (i : ι) :
    ((K₁.sc i).mapHomologyIso forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          ((forgetIntModules.mapHomologicalComplex c).map f) i =
      forgetIntModules.map (HomologicalComplex.homologyMap f i) ≫
        ((K₂.sc i).mapHomologyIso forgetIntModules).inv :=
  (ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) c i).map f)
      forgetIntModules).symm

abbrev ForgottenHomologyRowHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c)) (i : ι) :
    Type _ :=
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) c i).mapShortComplex.obj K).map
        forgetIntModules ⟶
      (HomologicalComplex.homologyFunctor AddCommGrpCat c i).mapShortComplex.obj
        (K.map (forgetIntModules.mapHomologicalComplex c))

/-- The three component homology comparisons form a morphism of rows. -/
noncomputable def forgetHomologyRowHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c)) (i : ι) :
    ForgottenHomologyRowHom K i :=
  { τ₁ := ((K.X₁.sc i).mapHomologyIso forgetIntModules).inv
    τ₂ := ((K.X₂.sc i).mapHomologyIso forgetIntModules).inv
    τ₃ := ((K.X₃.sc i).mapHomologyIso forgetIntModules).inv
    comm₁₂ := forgetHomologyMap_naturality K.f i
    comm₂₃ := forgetHomologyMap_naturality K.g i }

/-- Naturality of the comparison from forgotten coefficient opcycles to the
opcycles of the forgotten complex. -/
theorem forgetOpcyclesMap_naturality
    {ι : Type} {c : ComplexShape ι}
    {K₁ K₂ : HomologicalComplex (ModuleCat ℤ) c} (f : K₁ ⟶ K₂) (i : ι) :
    ((K₁.sc i).mapOpcyclesIso forgetIntModules).inv ≫
        HomologicalComplex.opcyclesMap
          ((forgetIntModules.mapHomologicalComplex c).map f) i =
      forgetIntModules.map (HomologicalComplex.opcyclesMap f i) ≫
        ((K₂.sc i).mapOpcyclesIso forgetIntModules).inv :=
  (ShortComplex.mapOpcyclesIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) c i).map f)
      forgetIntModules).symm

abbrev ForgottenOpcyclesRowHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c)) (i : ι) : Type _ :=
    ((HomologicalComplex.opcyclesFunctor (ModuleCat ℤ) c i).mapShortComplex.obj K).map
        forgetIntModules ⟶
      (HomologicalComplex.opcyclesFunctor AddCommGrpCat c i).mapShortComplex.obj
        (K.map (forgetIntModules.mapHomologicalComplex c))

/-- The three component opcycles comparisons form a morphism of rows. -/
noncomputable def forgetOpcyclesRowHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c)) (i : ι) :
    ForgottenOpcyclesRowHom K i :=
  { τ₁ := ((K.X₁.sc i).mapOpcyclesIso forgetIntModules).inv
    τ₂ := ((K.X₂.sc i).mapOpcyclesIso forgetIntModules).inv
    τ₃ := ((K.X₃.sc i).mapOpcyclesIso forgetIntModules).inv
    comm₁₂ := forgetOpcyclesMap_naturality K.f i
    comm₂₃ := forgetOpcyclesMap_naturality K.g i }

/-- Naturality of the comparison from forgotten coefficient cycles to the
cycles of the forgotten complex. -/
theorem forgetCyclesMap_naturality
    {ι : Type} {c : ComplexShape ι}
    {K₁ K₂ : HomologicalComplex (ModuleCat ℤ) c} (f : K₁ ⟶ K₂) (i : ι) :
    ((K₁.sc i).mapCyclesIso forgetIntModules).inv ≫
        HomologicalComplex.cyclesMap
          ((forgetIntModules.mapHomologicalComplex c).map f) i =
      forgetIntModules.map (HomologicalComplex.cyclesMap f i) ≫
        ((K₂.sc i).mapCyclesIso forgetIntModules).inv :=
  (ShortComplex.mapCyclesIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) c i).map f)
      forgetIntModules).symm

abbrev ForgottenCyclesRowHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c)) (i : ι) : Type _ :=
    ((HomologicalComplex.cyclesFunctor (ModuleCat ℤ) c i).mapShortComplex.obj K).map
        forgetIntModules ⟶
      (HomologicalComplex.cyclesFunctor AddCommGrpCat c i).mapShortComplex.obj
        (K.map (forgetIntModules.mapHomologicalComplex c))

/-- The three component cycles comparisons form a morphism of rows. -/
noncomputable def forgetCyclesRowHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c)) (i : ι) :
    ForgottenCyclesRowHom K i :=
  { τ₁ := ((K.X₁.sc i).mapCyclesIso forgetIntModules).inv
    τ₂ := ((K.X₂.sc i).mapCyclesIso forgetIntModules).inv
    τ₃ := ((K.X₃.sc i).mapCyclesIso forgetIntModules).inv
    comm₁₂ := forgetCyclesMap_naturality K.f i
    comm₂₃ := forgetCyclesMap_naturality K.g i }

/-- The terminal homology-row comparison is the previously constructed
homology-row morphism at the terminal degree. -/
noncomputable def forgetTerminalHomologyRowHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c)) (j : ι) :
    ForgottenHomologyRowHom K j :=
  forgetHomologyRowHom K j

/-- The right-derived homology comparison agrees with the standard mapped
homology comparison for the coefficient-forgetting functor. -/
theorem forgetMapHomologyIsoRight_eq
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i : ι) :
    (K.sc i).mapHomologyIso' forgetIntModules =
      (K.sc i).mapHomologyIso forgetIntModules :=
  (K.sc i).mapHomologyIso'_eq_mapHomologyIso forgetIntModules

abbrev ForgottenHomologyιNaturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i : ι) : Prop :=
    ((K.sc i).mapHomologyIso forgetIntModules).inv ≫
        ((forgetIntModules.mapHomologicalComplex c).obj K).homologyι i =
      forgetIntModules.map (K.homologyι i) ≫
        ((K.sc i).mapOpcyclesIso forgetIntModules).inv

/-- The homology-to-opcycles map commutes with forgetting coefficients. -/
theorem forgetHomologyι_naturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i : ι) :
    ForgottenHomologyιNaturality K i := by
  change ((K.sc i).mapHomologyIso forgetIntModules).inv ≫
      ((K.sc i).map forgetIntModules).homologyι =
    forgetIntModules.map ((K.sc i).homologyι) ≫
      ((K.sc i).mapOpcyclesIso forgetIntModules).inv
  rw [← forgetMapHomologyIsoRight_eq K i]
  rw [(K.sc i).rightHomologyData.mapHomologyIso'_eq forgetIntModules]
  rw [(K.sc i).rightHomologyData.mapOpcyclesIso_eq forgetIntModules]
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso]
  simp only [Category.assoc,
    ShortComplex.RightHomologyData.homologyIso_inv_comp_homologyι,
    ShortComplex.RightHomologyData.map_ι]
  calc
    _ = forgetIntModules.map
          ((K.sc i).rightHomologyData.homologyIso.hom ≫
            (K.sc i).rightHomologyData.ι) ≫
          ((K.sc i).rightHomologyData.map forgetIntModules).opcyclesIso.inv := by
        rw [forgetIntModules.map_comp]
        simp only [Category.assoc]
        rfl
    _ = forgetIntModules.map
          ((K.sc i).homologyι ≫
            (K.sc i).rightHomologyData.opcyclesIso.hom) ≫
          ((K.sc i).rightHomologyData.map forgetIntModules).opcyclesIso.inv := by
        rw [(K.sc i).rightHomologyData.homologyIso_hom_comp_ι]
    _ = _ := by
      rw [forgetIntModules.map_comp]
      simp only [Category.assoc]
      rfl

abbrev ForgottenPOpcyclesNaturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i : ι) : Prop :=
  forgetIntModules.map (K.pOpcycles i) ≫
      ((K.sc i).mapOpcyclesIso forgetIntModules).inv =
    ((forgetIntModules.mapHomologicalComplex c).obj K).pOpcycles i

/-- The projection to opcycles commutes with forgetting coefficients. -/
theorem forgetPOpcycles_naturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i : ι) :
    ForgottenPOpcyclesNaturality K i := by
  dsimp [ForgottenPOpcyclesNaturality]
  rw [(K.sc i).rightHomologyData.mapOpcyclesIso_eq forgetIntModules]
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso]
  calc
    _ = forgetIntModules.map
          ((K.sc i).pOpcycles ≫ (K.sc i).rightHomologyData.opcyclesIso.hom) ≫
          ((K.sc i).rightHomologyData.map forgetIntModules).opcyclesIso.inv := by
        rw [forgetIntModules.map_comp]
        simp only [Category.assoc]
        rfl
    _ = forgetIntModules.map (K.sc i).rightHomologyData.p ≫
          ((K.sc i).rightHomologyData.map forgetIntModules).opcyclesIso.inv := by
        rw [(K.sc i).rightHomologyData.pOpcycles_comp_opcyclesIso_hom]
    _ = ((K.sc i).rightHomologyData.map forgetIntModules).p ≫
          ((K.sc i).rightHomologyData.map forgetIntModules).opcyclesIso.inv := by
        rfl
    _ = _ := (K.sc i).rightHomologyData.map forgetIntModules |>.p_comp_opcyclesIso_inv

abbrev ForgottenICyclesNaturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i : ι) : Prop :=
  ((K.sc i).mapCyclesIso forgetIntModules).inv ≫
      ((forgetIntModules.mapHomologicalComplex c).obj K).iCycles i =
    forgetIntModules.map (K.iCycles i)

/-- The inclusion of cycles commutes with forgetting coefficients. -/
theorem forgetICycles_naturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i : ι) :
    ForgottenICyclesNaturality K i := by
  dsimp [ForgottenICyclesNaturality]
  apply (cancel_epi ((K.sc i).mapCyclesIso forgetIntModules).hom).1
  simp only [Iso.hom_inv_id_assoc]
  exact ((K.sc i).mapCyclesIso_hom_iCycles forgetIntModules).symm

abbrev ForgottenToCyclesNaturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i j : ι) : Prop :=
  ((forgetIntModules.mapHomologicalComplex c).obj K).toCycles i j =
    forgetIntModules.map (K.toCycles i j) ≫
      ((K.sc j).mapCyclesIso forgetIntModules).inv

/-- The differential factorization through cycles commutes with forgetting
coefficients. -/
theorem forgetToCycles_naturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i j : ι) :
    ForgottenToCyclesNaturality K i j := by
  dsimp [ForgottenToCyclesNaturality]
  letI : Mono (((forgetIntModules.mapHomologicalComplex c).obj K).iCycles j) := by
    infer_instance
  letI : ((forgetIntModules.mapHomologicalComplex c).obj K).HasHomology j := by infer_instance
  apply (cancel_mono (((forgetIntModules.mapHomologicalComplex c).obj K).iCycles j)).1
  refine Eq.trans (Eq.trans ?_ (congrArg (fun q =>
    forgetIntModules.map (K.toCycles i j) ≫ q)
      (forgetICycles_naturality K j)).symm) (Category.assoc _ _ _).symm
  calc
    _ = ((forgetIntModules.mapHomologicalComplex c).obj K).d i j :=
      ((forgetIntModules.mapHomologicalComplex c).obj K).toCycles_i i j
    _ = forgetIntModules.map (K.d i j) := rfl
    _ = forgetIntModules.map (K.toCycles i j ≫ K.iCycles j) :=
      congrArg forgetIntModules.map (K.toCycles_i i j).symm
    _ = _ := forgetIntModules.map_comp _ _

abbrev ForgottenOpcyclesToCyclesNaturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i j : ι) : Prop :=
  ((K.sc i).mapOpcyclesIso forgetIntModules).inv ≫
      ((forgetIntModules.mapHomologicalComplex c).obj K).opcyclesToCycles i j =
    forgetIntModules.map (K.opcyclesToCycles i j) ≫
      ((K.sc j).mapCyclesIso forgetIntModules).inv

theorem forgetOpcyclesToCycles_naturality
    {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (i j : ι) :
    ForgottenOpcyclesToCyclesNaturality K i j := by
  letI : ((forgetIntModules.mapHomologicalComplex c).obj K).HasHomology i := by infer_instance
  letI : ((forgetIntModules.mapHomologicalComplex c).obj K).HasHomology j := by infer_instance
  dsimp [ForgottenOpcyclesToCyclesNaturality]
  apply (cancel_epi (forgetIntModules.map (K.pOpcycles i))).1
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  rw [forgetPOpcycles_naturality]
  refine Eq.trans (((forgetIntModules.mapHomologicalComplex c).obj K).pOpcycles_opcyclesToCycles i j) ?_
  refine Eq.trans (forgetToCycles_naturality K i j) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  apply congrArg (fun q => q ≫ ((K.sc j).mapCyclesIso forgetIntModules).inv)
  calc
    forgetIntModules.map (K.toCycles i j) =
        forgetIntModules.map (K.pOpcycles i ≫ K.opcyclesToCycles i j) :=
      congrArg forgetIntModules.map (K.pOpcycles_opcyclesToCycles i j).symm
    _ = _ := forgetIntModules.map_comp _ _

abbrev ForgottenHomologyπNaturality {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (j : ι) : Prop :=
  ((K.sc j).mapCyclesIso forgetIntModules).inv ≫
      ((forgetIntModules.mapHomologicalComplex c).obj K).homologyπ j =
    forgetIntModules.map (K.homologyπ j) ≫
      ((K.sc j).mapHomologyIso forgetIntModules).inv

theorem forgetHomologyπ_naturality {ι : Type} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat ℤ) c) (j : ι) :
    ForgottenHomologyπNaturality K j := by
  letI : ((forgetIntModules.mapHomologicalComplex c).obj K).HasHomology j := by infer_instance
  dsimp [ForgottenHomologyπNaturality]
  change ((K.sc j).mapCyclesIso forgetIntModules).inv ≫
      ((K.sc j).map forgetIntModules).homologyπ = _
  rw [ShortComplex.LeftHomologyData.mapCyclesIso_eq
    (hl := (K.sc j).homologyData.left)]
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq
    (hl := (K.sc j).homologyData.left)]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  rw [← ShortComplex.LeftHomologyData.π_comp_homologyIso_inv
    (h := (K.sc j).homologyData.left.map forgetIntModules)]
  have hcore :
      forgetIntModules.map (K.sc j).homologyData.left.cyclesIso.hom ≫
          ((K.sc j).homologyData.left.map forgetIntModules).π =
        forgetIntModules.map ((K.sc j).homologyπ) ≫
          forgetIntModules.map (K.sc j).homologyData.left.homologyIso.hom := by
    change forgetIntModules.map (K.sc j).homologyData.left.cyclesIso.hom ≫
        forgetIntModules.map (K.sc j).homologyData.left.π = _
    rw [← forgetIntModules.map_comp, ← forgetIntModules.map_comp]
    rw [← ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ ((K.sc j).homologyData.left.map forgetIntModules).homologyIso.inv) hcore

abbrev ForgottenHomologySequenceSnakeInputHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c))
    (hK : K.ShortExact)
    (hKF : (K.map (forgetIntModules.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :=
  ShortComplex.SnakeInput.Hom
    (forgetSnakeInput (HomologicalComplex.HomologySequence.snakeInput hK i j hij))
    (HomologicalComplex.HomologySequence.snakeInput hKF i j hij)

noncomputable def forgetHomologySequenceSnakeInputHom
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c))
    (hK : K.ShortExact)
    (hKF : (K.map (forgetIntModules.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    ForgottenHomologySequenceSnakeInputHom K hK hKF i j hij where
  f₀ := forgetHomologyRowHom K i
  f₁ := forgetOpcyclesRowHom K i
  f₂ := forgetCyclesRowHom K j
  f₃ := forgetTerminalHomologyRowHom K j
  comm₀₁ := by
    apply ShortComplex.hom_ext
    · exact forgetHomologyι_naturality K.X₁ i
    · exact forgetHomologyι_naturality K.X₂ i
    · exact forgetHomologyι_naturality K.X₃ i
  comm₁₂ := by
    apply ShortComplex.hom_ext
    · exact forgetOpcyclesToCycles_naturality K.X₁ i j
    · exact forgetOpcyclesToCycles_naturality K.X₂ i j
    · exact forgetOpcyclesToCycles_naturality K.X₃ i j
  comm₂₃ := by
    apply ShortComplex.hom_ext
    · exact forgetHomologyπ_naturality K.X₁ j
    · exact forgetHomologyπ_naturality K.X₂ j
    · exact forgetHomologyπ_naturality K.X₃ j

abbrev ForgottenHomologySequenceDeltaNaturality
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c))
    (hK : K.ShortExact)
    (hKF : (K.map (forgetIntModules.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j) : Prop :=
  (forgetSnakeInput
      (HomologicalComplex.HomologySequence.snakeInput hK i j hij)).δ ≫
      ((K.X₁.sc j).mapHomologyIso forgetIntModules).inv =
    ((K.X₃.sc i).mapHomologyIso forgetIntModules).inv ≫
      (HomologicalComplex.HomologySequence.snakeInput hKF i j hij).δ

theorem forgetHomologySequence_delta_naturality
    {ι : Type} {c : ComplexShape ι}
    (K : ShortComplex (HomologicalComplex (ModuleCat ℤ) c))
    (hK : K.ShortExact)
    (hKF : (K.map (forgetIntModules.mapHomologicalComplex c)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    ForgottenHomologySequenceDeltaNaturality K hK hKF i j hij := by
  exact ShortComplex.SnakeInput.naturality_δ
    (forgetHomologySequenceSnakeInputHom K hK hKF i j hij)

theorem forgetSnakeDelta_map_apply_of_witness
    (S : ShortComplex.SnakeInput (ModuleCat ℤ))
    (x₃ : S.L₀.X₃) (x₂ : S.L₁.X₂) (x₁ : S.L₂.X₁)
    (h₂ : S.L₁.g x₂ = S.v₀₁.τ₃ x₃)
    (h₁ : S.L₂.f x₁ = S.v₁₂.τ₂ x₂) :
    (forgetIntModules.map S.δ) x₃ =
      (forgetIntModules.map S.v₂₃.τ₁) x₁ := by
  exact ShortComplex.SnakeInput.δ_apply' S x₃ x₂ x₁ h₂ h₁

theorem forgetSnakeInput_delta_map
    (S : ShortComplex.SnakeInput (ModuleCat ℤ)) :
    (forgetSnakeInput S).δ = forgetIntModules.map S.δ := by
  ext x₃
  obtain ⟨x₂, h₂⟩ :=
    (ModuleCat.epi_iff_surjective S.L₁.g).mp inferInstance (S.v₀₁.τ₃ x₃)
  have hz : S.L₂.g (S.v₁₂.τ₂ x₂) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.v₁₂.comm₂₃]
    rw [ConcreteCategory.comp_apply, h₂]
    rw [← ConcreteCategory.comp_apply, S.w₀₂_τ₃]
    rfl
  obtain ⟨x₁, h₁⟩ :=
    (S.L₂.moduleCat_exact_iff.mp S.L₂_exact) (S.v₁₂.τ₂ x₂) hz
  have ht : (forgetSnakeInput S).δ x₃ =
      (forgetSnakeInput S).v₂₃.τ₁ x₁ := by
    let D := forgetSnakeInput S
    have eq := CategoryTheory.congr_fun (D.snd_δ)
      (Limits.Concrete.pullbackMk D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂)
    have eq₁ := Concrete.pullbackMk_fst D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
    have eq₂ := Concrete.pullbackMk_snd D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂
    simp only [ConcreteCategory.comp_apply] at eq
    rw [eq₂] at eq
    refine eq.trans (CategoryTheory.congr_arg (D.v₂₃.τ₁) ?_)
    apply (AddCommGrpCat.mono_iff_injective D.L₂.f).1 inferInstance
    change (D.φ₁ ≫ D.L₂.f) (Limits.Concrete.pullbackMk
      D.L₁.g D.v₀₁.τ₃ x₂ x₃ h₂) = D.L₂.f x₁
    rw [ShortComplex.SnakeInput.φ₁_L₂_f]
    dsimp [ShortComplex.SnakeInput.φ₂]
    exact (CategoryTheory.congr_arg D.v₁₂.τ₂ eq₁).trans h₁.symm
  exact ht.trans
    (forgetSnakeDelta_map_apply_of_witness S x₃ x₂ x₁ h₂ h₁).symm

/-- The corrected relative-homology comparison intertwines the coefficient
absolute-to-relative map with the production relative projection. -/
theorem integralRelativeHomologyComparisonWithTransport_projection
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    forgetIntModules.map
        (HomologicalComplex.homologyMap
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) n) ≫
      (integralRelativeHomologyComparisonWithTransport A n).hom =
    (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        (singularChainsComparison (TopCat.of X)).hom n ≫
      HomologicalComplex.homologyMap (relativeSingularProjection A) n := by
  rw [integralRelativeHomologyComparisonWithTransport_hom]
  calc
    _ = (_ ≫ _) ≫ _ := (Category.assoc _ _ _).symm
    _ = (_ ≫ _) ≫ _ := congrArg (fun f => f ≫ _)
      (coefficientRelativeProjection_mapHomologyIso_naturality A n)
    _ = _ ≫ (_ ≫ _) := Category.assoc _ _ _
    _ = _ ≫ (_ ≫ _) := congrArg (fun f => _ ≫ f)
      (integralRelativeChainsComparisonWithTransport_homology_projection A n)
    _ = (_ ≫ _) ≫ _ := (Category.assoc _ _ _).symm

/-- A supplied normalization square sends the coefficient generator through
the corrected relative-homology comparison to the ambient local generator. -/
theorem integralRelativeHomologyComparisonWithTransport_generator_of_normalization
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hcompat :
      (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom ≫
          (ambientLocalNormalization k x).hom =
        forgetIntModules.map (CoefficientChartLocal.localIso ℤ k x).hom) :
    (integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom.hom
        (CoefficientChartLocal.generator ℤ k x) =
      HigherChartLocalGenerator.ambientLocalGenerator (k := k) x := by
  apply (ConcreteCategory.bijective_of_isIso
    (ambientLocalNormalization k x).hom).1
  have h := ConcreteCategory.congr_hom hcompat
    (CoefficientChartLocal.generator ℤ k x)
  change (ambientLocalNormalization k x).hom.hom
      ((integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom.hom
        (CoefficientChartLocal.generator ℤ k x)) =
    (CoefficientChartLocal.localIso ℤ k x).hom.hom
      (CoefficientChartLocal.generator ℤ k x) at h
  rw [h, CoefficientChartLocal.generator_normalization,
    ambientLocalNormalization_generator]

/-- The image of the normalized coefficient generator determines the full
normalization square for the corrected relative-homology comparison. -/
theorem integralRelativeHomologyComparisonWithTransport_normalization_of_generator
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hgen :
      (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom.hom
          (CoefficientChartLocal.generator ℤ k x) =
        HigherChartLocalGenerator.ambientLocalGenerator (k := k) x) :
    (integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom ≫
        (ambientLocalNormalization k x).hom =
      forgetIntModules.map (CoefficientChartLocal.localIso ℤ k x).hom := by
  ext z
  let r : ℤ := (CoefficientChartLocal.localIso ℤ k x).hom.hom z
  have hz : z = r • CoefficientChartLocal.generator ℤ k x := by
    apply (ConcreteCategory.bijective_of_isIso
      (CoefficientChartLocal.localIso ℤ k x).hom).1
    simp [r, CoefficientChartLocal.generator]
  rw [hz]
  change (ambientLocalNormalization k x).hom.hom
      ((integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom.hom
          (r • CoefficientChartLocal.generator ℤ k x)) =
    (CoefficientChartLocal.localIso ℤ k x).hom.hom
      (r • CoefficientChartLocal.generator ℤ k x)
  have hc := map_zsmul
    (integralRelativeHomologyComparisonWithTransport
    (deletedPoint x) (k + 2)).hom.hom
    r (CoefficientChartLocal.generator ℤ k x)
  calc
    _ = (ambientLocalNormalization k x).hom.hom
        (r • (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom.hom
            (CoefficientChartLocal.generator ℤ k x)) :=
      congrArg (ambientLocalNormalization k x).hom.hom hc
    _ = _ := by
      rw [hgen, map_zsmul, ambientLocalNormalization_generator,
        map_zsmul, CoefficientChartLocal.generator_normalization]

/-- The ambient normalization coordinate of the corrected comparison's image
of the coefficient local generator. -/
noncomputable def correctedLocalGeneratorCoefficient
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) : ℤ :=
  (ambientLocalNormalization k x).hom.hom
    ((integralRelativeHomologyComparisonWithTransport
      (deletedPoint x) (k + 2)).hom.hom
        (CoefficientChartLocal.generator ℤ k x))

/-- The corrected image of the coefficient generator is its normalization
coordinate times the ambient local generator. -/
theorem integralRelativeHomologyComparisonWithTransport_generator_eq_zsmul
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom.hom
        (CoefficientChartLocal.generator ℤ k x) =
      correctedLocalGeneratorCoefficient k x •
        HigherChartLocalGenerator.ambientLocalGenerator (k := k) x := by
  apply (ConcreteCategory.bijective_of_isIso
    (ambientLocalNormalization k x).hom).1
  unfold correctedLocalGeneratorCoefficient
  rw [map_zsmul, ambientLocalNormalization_generator, smul_eq_mul, mul_one]

/-- The corrected comparison conjugated by the coefficient and ambient
normalizations, as an automorphism of the additive group of integers. -/
noncomputable def correctedLocalNormalizationAutomorphism
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    AddCommGrpCat.of ℤ ≅ AddCommGrpCat.of ℤ :=
  (forgetIntModules.mapIso (CoefficientChartLocal.localIso ℤ k x)).symm ≪≫
    integralRelativeHomologyComparisonWithTransport (deletedPoint x) (k + 2) ≪≫
    ambientLocalNormalization k x

/-- The integer unit canonically induced by the corrected local normalization
automorphism. -/
noncomputable def correctedLocalGeneratorUnit
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) : ℤˣ :=
  CoefficientChartTransitionUnit.isoUnit ℤ
    (moduleIsoOfUnderlyingIso (correctedLocalNormalizationAutomorphism k x))

/-- The corrected local-generator coefficient is the integer underlying the
unit of its normalization-conjugated automorphism. -/
theorem correctedLocalGeneratorCoefficient_eq_unit
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    correctedLocalGeneratorCoefficient k x =
      (correctedLocalGeneratorUnit k x : ℤ) := by
  unfold correctedLocalGeneratorUnit
  let e := correctedLocalNormalizationAutomorphism k x
  let em : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ ℤ := moduleIsoOfUnderlyingIso e
  have hmap : forgetIntModules.map em.hom = e.hom := by
    dsimp [em, moduleIsoOfUnderlyingIso]
    exact forgetIntModules.map_preimage
      (X := ModuleCat.of ℤ ℤ) (Y := ModuleCat.of ℤ ℤ) e.hom
  have happ := ConcreteCategory.congr_hom hmap (1 : ℤ)
  calc
    correctedLocalGeneratorCoefficient k x = e.hom.hom 1 := by
      unfold correctedLocalGeneratorCoefficient
        CoefficientChartLocal.generator
      dsimp [e, correctedLocalNormalizationAutomorphism]
      rfl
    _ = em.hom.hom 1 := happ.symm
    _ = (CoefficientChartTransitionUnit.isoUnit ℤ
        em : ℤ) * 1 :=
      CoefficientChartTransitionUnit.isoUnit_action ℤ _ 1
    _ = _ := mul_one _

/-- The corrected local-generator coefficient is one of the two integer
units; no orientation sign is selected here. -/
theorem correctedLocalGeneratorCoefficient_eq_one_or_neg_one
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    correctedLocalGeneratorCoefficient k x = 1 ∨
      correctedLocalGeneratorCoefficient k x = -1 := by
  rw [correctedLocalGeneratorCoefficient_eq_unit]
  exact Int.isUnit_eq_one_or (correctedLocalGeneratorUnit k x).isUnit

/-- Nonnegativity selects the positive value of the corrected local-generator
coefficient. -/
theorem correctedLocalGeneratorCoefficient_eq_one_of_nonneg
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hnonneg : 0 ≤ correctedLocalGeneratorCoefficient k x) :
    correctedLocalGeneratorCoefficient k x = 1 := by
  rcases correctedLocalGeneratorCoefficient_eq_one_or_neg_one k x with h | h
  · exact h
  · omega

/-- A compatible corrected normalization sends the corrected local-generator
coefficient to one. -/
theorem correctedLocalGeneratorCoefficient_eq_one_of_normalization
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hcompat :
      (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom ≫
          (ambientLocalNormalization k x).hom =
        forgetIntModules.map (CoefficientChartLocal.localIso ℤ k x).hom) :
    correctedLocalGeneratorCoefficient k x = 1 := by
  unfold correctedLocalGeneratorCoefficient
  rw [integralRelativeHomologyComparisonWithTransport_generator_of_normalization
    k x hcompat, ambientLocalNormalization_generator]

/-- Coefficient one turns the corrected comparison's scalar generator formula
into exact generator transport. -/
theorem integralRelativeHomologyComparisonWithTransport_generator_of_coefficient_one
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hcoeff : correctedLocalGeneratorCoefficient k x = 1) :
    (integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom.hom
        (CoefficientChartLocal.generator ℤ k x) =
      HigherChartLocalGenerator.ambientLocalGenerator (k := k) x := by
  rw [integralRelativeHomologyComparisonWithTransport_generator_eq_zsmul,
    hcoeff, one_zsmul]

/-- Coefficient one supplies the corrected comparison's complete normalization
square. -/
theorem integralRelativeHomologyComparisonWithTransport_normalization_of_coefficient_one
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hcoeff : correctedLocalGeneratorCoefficient k x = 1) :
    (integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom ≫
        (ambientLocalNormalization k x).hom =
      forgetIntModules.map (CoefficientChartLocal.localIso ℤ k x).hom := by
  apply integralRelativeHomologyComparisonWithTransport_normalization_of_generator
  exact integralRelativeHomologyComparisonWithTransport_generator_of_coefficient_one
    k x hcoeff

/-- Nonnegativity of the corrected local coefficient supplies the corrected
comparison's complete normalization square. -/
theorem integralRelativeHomologyComparisonWithTransport_normalization_of_nonnegative
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hnonneg : 0 ≤ correctedLocalGeneratorCoefficient k x) :
    (integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom ≫
        (ambientLocalNormalization k x).hom =
      forgetIntModules.map (CoefficientChartLocal.localIso ℤ k x).hom := by
  apply integralRelativeHomologyComparisonWithTransport_normalization_of_coefficient_one
  exact correctedLocalGeneratorCoefficient_eq_one_of_nonneg k x hnonneg

/-- Excluding the negative unit selects coefficient one for the corrected
local generator. -/
theorem correctedLocalGeneratorCoefficient_eq_one_of_ne_neg_one
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M)
    (hne : correctedLocalGeneratorCoefficient k x ≠ -1) :
    correctedLocalGeneratorCoefficient k x = 1 := by
  rcases correctedLocalGeneratorCoefficient_eq_one_or_neg_one k x with h | h
  · exact h
  · exact (hne h).elim

/-- The corrected local-generator coefficient is definitionally the value at
one of the normalization-conjugated automorphism. -/
theorem correctedLocalGeneratorCoefficient_eq_automorphism_one
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    correctedLocalGeneratorCoefficient k x =
      (correctedLocalNormalizationAutomorphism k x).hom.hom 1 := by
  unfold correctedLocalGeneratorCoefficient
    correctedLocalNormalizationAutomorphism CoefficientChartLocal.generator
  rfl

/-- The corrected normalization automorphism is negation exactly when its
extracted local-generator coefficient is negative one. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_iff
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ ↔
      correctedLocalGeneratorCoefficient k x = -1 := by
  constructor
  · intro h
    rw [correctedLocalGeneratorCoefficient_eq_automorphism_one, h]
    rfl
  · intro h
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext_int
    change (correctedLocalNormalizationAutomorphism k x).hom.hom 1 =
      ((-𝟙 _ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ)).hom 1
    rw [← correctedLocalGeneratorCoefficient_eq_automorphism_one]
    exact h

/-- The hom of the corrected normalization automorphism is its defining
three-factor normalization composite. -/
theorem correctedLocalNormalizationAutomorphism_hom
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom =
      (forgetIntModules.mapIso
        (CoefficientChartLocal.localIso ℤ k x)).inv ≫
      (integralRelativeHomologyComparisonWithTransport
        (deletedPoint x) (k + 2)).hom ≫
      (ambientLocalNormalization k x).hom := by
  rfl

/-- The ambient chart map induces the isomorphism on local homology used by
the production normalization. -/
noncomputable def ambientChartHomologyIso
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) := by
  letI := HigherChartLocalGenerator.ambientChartMap_Hn_isIso (k := k) x
  exact asIso (HomologicalComplex.homologyMap
        (relativeSingularMap (HigherChartLocalGenerator.P k) (deletedPoint x)
          (HigherChartLocalGenerator.ambientChartMap (k := k) x)
          (HigherChartLocalGenerator.ambientChartMap_mapsTo (k := k) x))
        (k + 2))

/-- The hom of the ambient local normalization is chart pullback followed by
the concrete model normalization. -/
theorem ambientLocalNormalization_hom
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (ambientLocalNormalization k x).hom =
      (ambientChartHomologyIso k x).inv ≫
      (HigherModelLocalHomology.localIsoInt k).hom := by
  rfl

/-- Cancelling the inverse coefficient normalization exposes the forward
coefficient normalization in the negative-automorphism equation. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_after_coefficient
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ ↔
      (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom ≫
          (ambientLocalNormalization k x).hom =
        (forgetIntModules.mapIso
          (CoefficientChartLocal.localIso ℤ k x)).hom ≫ (-𝟙 _) := by
  rw [correctedLocalNormalizationAutomorphism_hom]
  let e := forgetIntModules.mapIso (CoefficientChartLocal.localIso ℤ k x)
  change
    e.inv ≫
          (integralRelativeHomologyComparisonWithTransport
            (deletedPoint x) (k + 2)).hom ≫
          (ambientLocalNormalization k x).hom = -𝟙 _ ↔
      (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom ≫
          (ambientLocalNormalization k x).hom = e.hom ≫ (-𝟙 _)
  constructor
  · intro h
    have hh := congrArg (fun f => e.hom ≫ f) h
    simpa only [Category.assoc, e.hom_inv_id_assoc] using hh
  · intro h
    have hh := congrArg (fun f => e.inv ≫ f) h
    simpa only [Category.assoc, e.inv_hom_id_assoc] using hh

/-- The negative-automorphism equation with both endpoint normalizations
exposed as their chart and model factors. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_endpoint_factors
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ ↔
      (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom ≫
          (ambientChartHomologyIso k x).inv ≫
          (HigherModelLocalHomology.localIsoInt k).hom =
        forgetIntModules.map
            (CoefficientChartLocal.localIso ℤ k x).hom ≫ (-𝟙 _) := by
  rw [correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_after_coefficient]
  rw [ambientLocalNormalization_hom]
  simp only [Functor.mapIso_hom]

/-- The concrete forward composite underlying the coefficient-chart local
normalization. -/
noncomputable def coefficientLocalForwardComposite
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (CoefficientChartLocal.E k) M] (x : M) :=
  (CoefficientNeighborhoodLocal.inclusionIso ℤ
      (chartAt (CoefficientChartLocal.E k) x).source x
      (chartAt (CoefficientChartLocal.E k) x).open_source
      (CoefficientChartPair.source_member (k + 2) x) (k + 2)).inv ≫
  (CoefficientChartLocal.sourceTransport ℤ k x (k + 2)).inv ≫
  HomologicalComplex.homologyMap
    (CoefficientChartPair.deletedMap ℤ
      (CoefficientChartLocal.pointedChart k x)
      (CoefficientChartPair.sourcePoint (k + 2) x)) (k + 2) ≫
  (CoefficientChartLocal.targetTransport ℤ k x (k + 2)).hom ≫
  HomologicalComplex.homologyMap
    (CoefficientNeighborhoodLocal.inclusionMap ℤ
      (CoefficientChartLocal.pointedTarget k x) 0) (k + 2) ≫
  (CoefficientModelLocal.localIso ℤ k).hom

/-- The coefficient projection followed by the concrete coefficient-chart
normalization, exposed as its ordered seven factors. -/
noncomputable def coefficientProjectedForwardComposite
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (CoefficientChartLocal.E k) M] (x : M) :=
  forgetIntModules.map
      (HomologicalComplex.homologyMap
        (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ (deletedPoint x)))
        (k + 2)) ≫
  forgetIntModules.map
      (CoefficientNeighborhoodLocal.inclusionIso ℤ
        (chartAt (CoefficientChartLocal.E k) x).source x
        (chartAt (CoefficientChartLocal.E k) x).open_source
        (CoefficientChartPair.source_member (k + 2) x) (k + 2)).inv ≫
  forgetIntModules.map
      (CoefficientChartLocal.sourceTransport ℤ k x (k + 2)).inv ≫
  forgetIntModules.map
      (HomologicalComplex.homologyMap
        (CoefficientChartPair.deletedMap ℤ
          (CoefficientChartLocal.pointedChart k x)
          (CoefficientChartPair.sourcePoint (k + 2) x)) (k + 2)) ≫
  forgetIntModules.map
      (CoefficientChartLocal.targetTransport ℤ k x (k + 2)).hom ≫
  forgetIntModules.map
      (HomologicalComplex.homologyMap
        (CoefficientNeighborhoodLocal.inclusionMap ℤ
          (CoefficientChartLocal.pointedTarget k x) 0) (k + 2)) ≫
  forgetIntModules.map (CoefficientModelLocal.localIso ℤ k).hom

theorem coefficientProjection_comp_coefficientLocalForwardComposite
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (CoefficientChartLocal.E k) M] (x : M) :
    forgetIntModules.map
        (HomologicalComplex.homologyMap
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ (deletedPoint x)))
          (k + 2)) ≫
      forgetIntModules.map (coefficientLocalForwardComposite k x) =
    coefficientProjectedForwardComposite k x := by
  unfold coefficientProjectedForwardComposite coefficientLocalForwardComposite
  rfl

/-- The coefficient-chart local isomorphism has the concrete forward
factorization used by the normalization comparison. -/
theorem coefficientLocalIso_hom_eq_forwardComposite
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (CoefficientChartLocal.E k) M] (x : M) :
    (CoefficientChartLocal.localIso ℤ k x).hom =
      coefficientLocalForwardComposite k x := by
  exact CoefficientChartLocal.forward_composite ℤ k x

/-- The negative-automorphism equation with its coefficient endpoint replaced
by the concrete forward factorization. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_coefficient_factors
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ ↔
      (integralRelativeHomologyComparisonWithTransport
          (deletedPoint x) (k + 2)).hom ≫
          (ambientChartHomologyIso k x).inv ≫
          (HigherModelLocalHomology.localIsoInt k).hom =
        forgetIntModules.map (coefficientLocalForwardComposite k x) ≫ (-𝟙 _) := by
  rw [correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_endpoint_factors]
  rw [coefficientLocalIso_hom_eq_forwardComposite]
  rfl

/-- The negative-automorphism equation with the corrected relative-homology
comparison exposed as homology preservation followed by the chain comparison. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_corrected_comparison_factors
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ ↔
      (((CoefficientRelativeSmall.relativeChains ℤ (deletedPoint x)).sc (k + 2)).mapHomologyIso
          forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          (integralRelativeChainsComparisonWithTransport (deletedPoint x)).hom (k + 2) ≫
        (ambientChartHomologyIso k x).inv ≫
        (HigherModelLocalHomology.localIsoInt k).hom =
      forgetIntModules.map (coefficientLocalForwardComposite k x) ≫ (-𝟙 _) := by
  rw [correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_coefficient_factors]
  rw [integralRelativeHomologyComparisonWithTransport_hom]
  constructor <;> intro h <;> simpa only [← Category.assoc] using h

/-- The hom of the transported integral relative-chain comparison is its
defining four-isomorphism composite. -/
theorem integralRelativeChainsComparisonWithTransport_hom
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (integralRelativeChainsComparisonWithTransport A).hom =
      (forgetIntegralRelativeCokernelComparison A).hom ≫
      (coefficientIntegralCokernelTransport A).hom ≫
      (integralMappedRelativeCokernelComparison A).hom ≫
      (relativeSingularChainsIsoCokernelSubspaceMap A).inv := by
  rfl

/-- Homology of the transported integral relative-chain comparison factors as
the ordered composite of the homology maps of its four defining factors. -/
theorem integralRelativeChainsComparisonWithTransport_homologyMap
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (integralRelativeChainsComparisonWithTransport A).hom n =
      HomologicalComplex.homologyMap
          (forgetIntegralRelativeCokernelComparison A).hom n ≫
      HomologicalComplex.homologyMap
          (coefficientIntegralCokernelTransport A).hom n ≫
      HomologicalComplex.homologyMap
          (integralMappedRelativeCokernelComparison A).hom n ≫
      HomologicalComplex.homologyMap
          (relativeSingularChainsIsoCokernelSubspaceMap A).inv n := by
  rw [integralRelativeChainsComparisonWithTransport_hom]
  simp only [HomologicalComplex.homologyMap_comp]
  rfl

/-- The four homology factors of the transported integral relative-chain
comparison, packaged as a single composite. -/
noncomputable def integralTransportHomologyComposite
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :=
  HomologicalComplex.homologyMap
      (forgetIntegralRelativeCokernelComparison A).hom n ≫
  HomologicalComplex.homologyMap
      (coefficientIntegralCokernelTransport A).hom n ≫
  HomologicalComplex.homologyMap
      (integralMappedRelativeCokernelComparison A).hom n ≫
  HomologicalComplex.homologyMap
      (relativeSingularChainsIsoCokernelSubspaceMap A).inv n

theorem integralRelativeChainsComparisonWithTransport_homologyMap_eq_composite
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (integralRelativeChainsComparisonWithTransport A).hom n =
      integralTransportHomologyComposite A n := by
  exact integralRelativeChainsComparisonWithTransport_homologyMap A n

/-- The negative-automorphism equation with the transported comparison's four
homology factors represented by `integralTransportHomologyComposite`. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_transport_homology_factors
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ ↔
      (((CoefficientRelativeSmall.relativeChains ℤ (deletedPoint x)).sc (k + 2)).mapHomologyIso
          forgetIntModules).inv ≫
        integralTransportHomologyComposite (deletedPoint x) (k + 2) ≫
        (ambientChartHomologyIso k x).inv ≫
        (HigherModelLocalHomology.localIsoInt k).hom =
      forgetIntModules.map (coefficientLocalForwardComposite k x) ≫ (-𝟙 _) := by
  rw [correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_corrected_comparison_factors]
  rw [integralRelativeChainsComparisonWithTransport_homologyMap_eq_composite]

/-- The coefficient relative projection cancels the preservation prefix of the
explicit transported-comparison homology composite. -/
theorem coefficientProjection_comp_integralTransportHomologyComposite
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    forgetIntModules.map
        (HomologicalComplex.homologyMap
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) n) ≫
      (((CoefficientRelativeSmall.relativeChains ℤ A).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      integralTransportHomologyComposite A n =
    (((CoefficientH0.SingularChains ℤ (TopCat.of X)).sc n).mapHomologyIso
        forgetIntModules).inv ≫
      HomologicalComplex.homologyMap
        (singularChainsComparison (TopCat.of X)).hom n ≫
      HomologicalComplex.homologyMap (relativeSingularProjection A) n := by
  rw [← integralRelativeChainsComparisonWithTransport_homologyMap_eq_composite]
  simpa only [← Category.assoc] using
    integralRelativeHomologyComparisonWithTransport_projection A n

/-- Precomposing the forbidden negative-sign equation by the coefficient
absolute-to-relative projection exposes the production projection factors. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_projected_factors
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ →
      (((CoefficientH0.SingularChains ℤ (TopCat.of M)).sc (k + 2)).mapHomologyIso
          forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          (singularChainsComparison (TopCat.of M)).hom (k + 2) ≫
        HomologicalComplex.homologyMap
          (relativeSingularProjection (deletedPoint x)) (k + 2) ≫
        (ambientChartHomologyIso k x).inv ≫
        (HigherModelLocalHomology.localIsoInt k).hom =
      forgetIntModules.map
          (HomologicalComplex.homologyMap
            (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ (deletedPoint x)))
            (k + 2)) ≫
        forgetIntModules.map (coefficientLocalForwardComposite k x) ≫
        (-𝟙 _) := by
  intro hneg
  have h :=
    (correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_transport_homology_factors
      k x).mp hneg
  let q := forgetIntModules.map
    (HomologicalComplex.homologyMap
      (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ (deletedPoint x)))
      (k + 2))
  have hq := congrArg (fun f => q ≫ f) h
  dsimp [q] at hq
  have halign := coefficientProjection_comp_integralTransportHomologyComposite
    (deletedPoint x) (k + 2)
  have halignTail := congrArg
    (fun f => f ≫ (ambientChartHomologyIso k x).inv ≫
      (HigherModelLocalHomology.localIsoInt k).hom) halign
  calc
    _ = q ≫
        (((CoefficientRelativeSmall.relativeChains ℤ (deletedPoint x)).sc
          (k + 2)).mapHomologyIso forgetIntModules).inv ≫
        integralTransportHomologyComposite (deletedPoint x) (k + 2) ≫
        (ambientChartHomologyIso k x).inv ≫
        (HigherModelLocalHomology.localIsoInt k).hom := by
          simpa only [Category.assoc] using halignTail.symm
    _ = _ := hq

/-- The projected forbidden-sign equation with its coefficient endpoint
replaced by the concrete seven-factor composite. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_concrete_endpoints
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ →
      (((CoefficientH0.SingularChains ℤ (TopCat.of M)).sc (k + 2)).mapHomologyIso
          forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          (singularChainsComparison (TopCat.of M)).hom (k + 2) ≫
        HomologicalComplex.homologyMap
          (relativeSingularProjection (deletedPoint x)) (k + 2) ≫
        (ambientChartHomologyIso k x).inv ≫
        (HigherModelLocalHomology.localIsoInt k).hom =
      coefficientProjectedForwardComposite k x ≫ (-𝟙 _) := by
  intro hneg
  have h :=
    correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_projected_factors
      k x hneg
  have he := coefficientProjection_comp_coefficientLocalForwardComposite k x
  have heneg := congrArg (fun f => f ≫ (-𝟙 _)) he
  exact h.trans (by simpa only [Category.assoc] using heneg)

/-- The production-side chart factors preceding higher-model normalization. -/
noncomputable def productionProjectedChartPrefix
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :=
  (((CoefficientH0.SingularChains ℤ (TopCat.of M)).sc (k + 2)).mapHomologyIso
      forgetIntModules).inv ≫
  HomologicalComplex.homologyMap
      (singularChainsComparison (TopCat.of M)).hom (k + 2) ≫
  HomologicalComplex.homologyMap
      (relativeSingularProjection (deletedPoint x)) (k + 2) ≫
  (ambientChartHomologyIso k x).inv

/-- The coefficient-side projection and chart factors preceding coefficient
model normalization. -/
noncomputable def coefficientProjectedChartPrefix
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (CoefficientChartLocal.E k) M] (x : M) :=
  forgetIntModules.map
      (HomologicalComplex.homologyMap
        (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ (deletedPoint x)))
        (k + 2)) ≫
  forgetIntModules.map
      (CoefficientNeighborhoodLocal.inclusionIso ℤ
        (chartAt (CoefficientChartLocal.E k) x).source x
        (chartAt (CoefficientChartLocal.E k) x).open_source
        (CoefficientChartPair.source_member (k + 2) x) (k + 2)).inv ≫
  forgetIntModules.map
      (CoefficientChartLocal.sourceTransport ℤ k x (k + 2)).inv ≫
  forgetIntModules.map
      (HomologicalComplex.homologyMap
        (CoefficientChartPair.deletedMap ℤ
          (CoefficientChartLocal.pointedChart k x)
          (CoefficientChartPair.sourcePoint (k + 2) x)) (k + 2)) ≫
  forgetIntModules.map
      (CoefficientChartLocal.targetTransport ℤ k x (k + 2)).hom ≫
  forgetIntModules.map
      (HomologicalComplex.homologyMap
        (CoefficientNeighborhoodLocal.inclusionMap ℤ
          (CoefficientChartLocal.pointedTarget k x) 0) (k + 2))

/-- The forbidden-sign endpoint equality separated into its chart prefixes
and final model normalizations. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_prefix_model_equality
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ →
      productionProjectedChartPrefix k x ≫
          (HigherModelLocalHomology.localIsoInt k).hom =
        coefficientProjectedChartPrefix k x ≫
          forgetIntModules.map (CoefficientModelLocal.localIso ℤ k).hom ≫
          (-𝟙 _) := by
  intro hneg
  have h :=
    correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_concrete_endpoints
      k x hneg
  simpa only [productionProjectedChartPrefix, coefficientProjectedChartPrefix,
    coefficientProjectedForwardComposite, Category.assoc] using h

/-- The coefficient model normalization exposed as its connecting, radial,
and sphere-normalization factors after forgetting coefficients. -/
noncomputable def coefficientModelNormalizationComposite (k : ℕ) :=
  forgetIntModules.map
      (CoefficientPairSequence.connecting ℤ
        (CoefficientModelLocal.puncture (k + 2)) (k + 1)) ≫
  forgetIntModules.map
      ((CoefficientRadialPair.F ℤ (k + 1)).map
        (TopCat.ofHom
          (PuncturedNormedSpaceRadialEquivalence.radialNormalize
            (CoefficientModelLocal.E (k + 2))))) ≫
  forgetIntModules.map (CoefficientSphereAntipodal.normalization ℤ k).hom

theorem coefficientModelLocalIso_forget_hom
    (k : ℕ) :
    forgetIntModules.map (CoefficientModelLocal.localIso ℤ k).hom =
      coefficientModelNormalizationComposite k := by
  unfold coefficientModelNormalizationComposite CoefficientModelLocal.localIso
    CoefficientModelLocal.radialIso
  rfl

/-- The forbidden-sign prefix equality with both model normalizations exposed
as connecting, radial, and sphere factors. -/
theorem correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_model_factors
    (k : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (HigherChartLocalGenerator.E k) M] (x : M) :
    (correctedLocalNormalizationAutomorphism k x).hom = -𝟙 _ →
      productionProjectedChartPrefix k x ≫
          singularPairConnecting
            (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1) ≫
          ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat (k + 1)).obj
            (AddCommGrpCat.of ℤ)).map
              (TopCat.ofHom (T02A06DiskRadialComparison.radialNormalizeMap (k + 2))) ≫
          (SphereHomology.sphereTopHomologyIsoInt (k + 1) (by omega)).hom =
        coefficientProjectedChartPrefix k x ≫
          coefficientModelNormalizationComposite k ≫ (-𝟙 _) := by
  intro hneg
  have h :=
    correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_prefix_model_equality
      k x hneg
  rw [HigherModelLocalHomology.comparison] at h
  have he := coefficientModelLocalIso_forget_hom k
  have heq := congrArg
    (fun f => coefficientProjectedChartPrefix k x ≫ f ≫ (-𝟙 _)) he
  exact h.trans (by simpa only [Category.assoc] using heq)

/-- The coefficient normalization based in the unit open disk, exposed as
the disk-to-Euclidean local-homology map followed by the model normalization. -/
theorem coefficientIntegralBall_forget_hom (k : ℕ) :
    forgetIntModules.map
        (CoefficientNeighborhoodLocal.integral_ball k).hom =
      forgetIntModules.map
          (HomologicalComplex.homologyMap
            (CoefficientNeighborhoodLocal.inclusionMap ℤ
              (Metric.ball (0 : CoefficientModelLocal.E (k + 2)) 1) 0)
            (k + 2)) ≫
        forgetIntModules.map (CoefficientModelLocal.localIso ℤ k).hom := by
  unfold CoefficientNeighborhoodLocal.integral_ball
    CoefficientNeighborhoodLocal.modelNormalization
  exact forgetIntModules.map_comp _ _

/-- The forgotten coefficient normalization from the unit open disk, with
the terminal Euclidean model normalization exposed into its three factors. -/
theorem coefficientIntegralBall_forget_hom_eq_model_factors (k : ℕ) :
    forgetIntModules.map
        (CoefficientNeighborhoodLocal.integral_ball k).hom =
      forgetIntModules.map
          (HomologicalComplex.homologyMap
            (CoefficientNeighborhoodLocal.inclusionMap ℤ
              (Metric.ball (0 : CoefficientModelLocal.E (k + 2)) 1) 0)
            (k + 2)) ≫
        coefficientModelNormalizationComposite k := by
  rw [coefficientIntegralBall_forget_hom]
  exact congrArg
    (fun f =>
      forgetIntModules.map
          (HomologicalComplex.homologyMap
            (CoefficientNeighborhoodLocal.inclusionMap ℤ
              (Metric.ball (0 : CoefficientModelLocal.E (k + 2)) 1) 0)
            (k + 2)) ≫ f)
    (coefficientModelLocalIso_forget_hom k)

/-- The canonical integral coefficient-to-production comparison for the
unit open disk relative to its puncture. -/
noncomputable def integralOpenDiskRelativeHomologyComparison (k : ℕ) :
    IntegralSingularHomologyComparison.forgetIntModules.obj
        ((CoefficientRelativeSmall.relativeChains ℤ
          (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))).homology
            (k + 2)) ≅
      (RelativeSingularChains
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))).homology
          (k + 2) :=
  integralRelativeHomologyComparisonWithTransport
    (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 2)

theorem integralOpenDiskRelativeHomologyComparison_hom (k : ℕ) :
    (integralOpenDiskRelativeHomologyComparison k).hom =
      (integralRelativeHomologyComparisonWithTransport
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))
        (k + 2)).hom := rfl

/-- The canonical integral comparison on the punctured unit disk in the
degree targeted by the pair connecting morphism. -/
noncomputable def integralOpenDiskPunctureHomologyComparison (k : ℕ) :=
  singularHomologyComparison
    (TopCat.of
      (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))) (k + 1)

theorem integralOpenDiskPunctureHomologyComparison_hom (k : ℕ) :
    (integralOpenDiskPunctureHomologyComparison k).hom =
      (singularHomologyComparison
        (TopCat.of
          (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)))
        (k + 1)).hom := rfl

/-- The chain-level comparison of the coefficient and production short exact
sequences for the punctured unit disk. -/
noncomputable def integralOpenDiskPairShortComplexComparison (k : ℕ) :
    (CoefficientPairSequence.sequence ℤ
      (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))).map
        (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)) ⟶
      singularPairShortComplex
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) where
  τ₁ := (singularChainsComparison
    (TopCat.of (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)))).hom
  τ₂ := (singularChainsComparison
    (TopCat.of (T02A06HemisphereExcision.euclideanOpenDisk (k + 2)))).hom
  τ₃ := (integralRelativeChainsComparisonWithTransport
    (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))).hom
  comm₁₂ := by
    simpa only [CoefficientPairSequence.sequence,
      CoefficientCokernelComparison.cokernelShortComplex,
      CoefficientPairSequence.inclusion,
      coefficientSubspaceMap_eq_integralSubtypeChainMap] using
      (integralSingularChainsComparison_subtype_naturality
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))).symm
  comm₂₃ := by
    simpa only [CoefficientPairSequence.sequence,
      CoefficientCokernelComparison.cokernelShortComplex] using
      (integralRelativeChainsComparisonWithTransport_projection
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))).symm

/-- Forgetting the integer-module structure preserves the coefficient pair
short exact sequence for the punctured unit disk. -/
theorem integralOpenDiskCoefficientPairShortExact (k : ℕ) :
    ((CoefficientPairSequence.sequence ℤ
      (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))).map
        (forgetIntModules.mapHomologicalComplex
          (ComplexShape.down ℕ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let h := CoefficientPairSequence.shortExact ℤ
    (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))
  letI := h.mono_f
  letI := h.epi_g
  exact (h.map
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) i)).map_of_exact
      forgetIntModules

/-- The snake-lemma input defining the coefficient connecting morphism for
the punctured open disk. -/
noncomputable def coefficientOpenDiskSnakeInput (k : ℕ) :=
  HomologicalComplex.HomologySequence.snakeInput
    (CoefficientPairSequence.shortExact ℤ
      (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)))
    (k + 2) (k + 1) rfl

/-- The snake-lemma input defining the connecting morphism after forgetting
the integer-module structure. -/
noncomputable def forgottenCoefficientOpenDiskSnakeInput (k : ℕ) :=
  HomologicalComplex.HomologySequence.snakeInput
    (integralOpenDiskCoefficientPairShortExact k)
    (k + 2) (k + 1) rfl

/-- The two named snake inputs expose exactly the original and forgotten
coefficient connecting morphisms. -/
theorem openDiskSnakeInputs_delta (k : ℕ) :
    (coefficientOpenDiskSnakeInput k).δ =
      CoefficientPairSequence.connecting ℤ
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1) ∧
    (forgottenCoefficientOpenDiskSnakeInput k).δ =
      (integralOpenDiskCoefficientPairShortExact k).δ
        (k + 2) (k + 1) rfl := by
  constructor <;> rfl

/-- Connecting-map naturality for the chain-level integral comparison of the
punctured unit-disk pair, before rewriting the source connecting map through
homology preservation. -/
theorem integralOpenDiskConnecting_naturality_raw (k : ℕ) :
    (integralOpenDiskCoefficientPairShortExact k).δ
        (k + 2) (k + 1) rfl ≫
      HomologicalComplex.homologyMap
        (integralOpenDiskPairShortComplexComparison k).τ₁ (k + 1) =
    HomologicalComplex.homologyMap
        (integralOpenDiskPairShortComplexComparison k).τ₃ (k + 2) ≫
      singularPairConnecting
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1) := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (integralOpenDiskPairShortComplexComparison k)
    (integralOpenDiskCoefficientPairShortExact k)
    (singularPairShortComplex_shortExact
      (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)))
    (k + 2) (k + 1) rfl

theorem integralOpenDiskComparison_component_homology_maps (k : ℕ) :
    (integralOpenDiskPunctureHomologyComparison k).hom =
      (((ConstructionTargets.CoefficientH0.SingularChains ℤ
          (TopCat.of (ConstructionTargets.T02A06HemisphereExcision.puncturedOpenDiskSet
            (k + 2)))).sc (k + 1)).mapHomologyIso
          forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          (integralOpenDiskPairShortComplexComparison k).τ₁ (k + 1) ∧
    (integralOpenDiskRelativeHomologyComparison k).hom =
      (((ConstructionTargets.CoefficientRelativeSmall.relativeChains ℤ
          (ConstructionTargets.T02A06HemisphereExcision.puncturedOpenDiskSet
            (k + 2))).sc (k + 2)).mapHomologyIso
          forgetIntModules).inv ≫
        HomologicalComplex.homologyMap
          (integralOpenDiskPairShortComplexComparison k).τ₃ (k + 2) := by
  constructor <;> rfl

/-- The coefficient connecting map with its target moved to homology of the
forgotten puncture chain complex. -/
noncomputable def coefficientOpenDiskConnectingTransport (k : ℕ) :=
  forgetIntModules.map
      (CoefficientPairSequence.connecting ℤ
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
    (((CoefficientH0.SingularChains ℤ
        (TopCat.of (T02A06HemisphereExcision.puncturedOpenDiskSet
          (k + 2)))).sc (k + 1)).mapHomologyIso forgetIntModules).inv

theorem coefficientOpenDiskConnectingTransport_eq (k : ℕ) :
    coefficientOpenDiskConnectingTransport k =
      forgetIntModules.map
          (CoefficientPairSequence.connecting ℤ
            (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
        (((CoefficientH0.SingularChains ℤ
            (TopCat.of (T02A06HemisphereExcision.puncturedOpenDiskSet
              (k + 2)))).sc (k + 1)).mapHomologyIso forgetIntModules).inv := rfl

theorem coefficientOpenDiskConnecting_forgotten_naturality (k : ℕ) :
    forgetIntModules.map
        (CoefficientPairSequence.connecting ℤ
          (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
      (((CoefficientH0.SingularChains ℤ
        (TopCat.of (T02A06HemisphereExcision.puncturedOpenDiskSet
          (k + 2)))).sc (k + 1)).mapHomologyIso forgetIntModules).inv =
    (((CoefficientRelativeSmall.relativeChains ℤ
        (T02A06HemisphereExcision.puncturedOpenDiskSet
          (k + 2))).sc (k + 2)).mapHomologyIso forgetIntModules).inv ≫
      (integralOpenDiskCoefficientPairShortExact k).δ
        (k + 2) (k + 1) rfl := by
  rw [← (openDiskSnakeInputs_delta k).1]
  let S := coefficientOpenDiskSnakeInput k
  let e := (((CoefficientH0.SingularChains ℤ
    (TopCat.of (T02A06HemisphereExcision.puncturedOpenDiskSet
      (k + 2)))).sc (k + 1)).mapHomologyIso forgetIntModules).inv
  calc
    forgetIntModules.map S.δ ≫ e = (forgetSnakeInput S).δ ≫ e :=
      congrArg (fun q => q ≫ e) (forgetSnakeInput_delta_map S).symm
    _ = _ := by
      simpa only [S, e, coefficientOpenDiskSnakeInput] using
        (forgetHomologySequence_delta_naturality
          (CoefficientPairSequence.sequence ℤ
            (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)))
          (CoefficientPairSequence.shortExact ℤ
            (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)))
          (integralOpenDiskCoefficientPairShortExact k)
          (k + 2) (k + 1) rfl)

theorem coefficientOpenDiskConnecting_comparison (k : ℕ) :
    forgetIntModules.map
        (CoefficientPairSequence.connecting ℤ
          (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
      (integralOpenDiskPunctureHomologyComparison k).hom =
    (integralOpenDiskRelativeHomologyComparison k).hom ≫
      singularPairConnecting
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1) := by
  rw [(integralOpenDiskComparison_component_homology_maps k).1,
    (integralOpenDiskComparison_component_homology_maps k).2]
  let f := forgetIntModules.map
    (CoefficientPairSequence.connecting ℤ
      (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1))
  let g := (((CoefficientH0.SingularChains ℤ
    (TopCat.of (T02A06HemisphereExcision.puncturedOpenDiskSet
      (k + 2)))).sc (k + 1)).mapHomologyIso forgetIntModules).inv
  let h := HomologicalComplex.homologyMap
    (integralOpenDiskPairShortComplexComparison k).τ₁ (k + 1)
  let r := (((CoefficientRelativeSmall.relativeChains ℤ
    (T02A06HemisphereExcision.puncturedOpenDiskSet
      (k + 2))).sc (k + 2)).mapHomologyIso forgetIntModules).inv
  let d := (integralOpenDiskCoefficientPairShortExact k).δ
    (k + 2) (k + 1) rfl
  let m := HomologicalComplex.homologyMap
    (integralOpenDiskPairShortComplexComparison k).τ₃ (k + 2)
  let q := singularPairConnecting
    (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)
  have hd : d ≫ h = m ≫ q := by
    simpa only [d, h, m, q] using integralOpenDiskConnecting_naturality_raw k
  change f ≫ (g ≫ h) = (r ≫ m) ≫ q
  rw [← Category.assoc f g h]
  rw [show f ≫ g = r ≫ d by
    simpa only [f, g, r, d] using
      coefficientOpenDiskConnecting_forgotten_naturality k]
  exact (Category.assoc r d h).trans
    ((congrArg (fun z => r ≫ z) hd).trans (Category.assoc r m q).symm)

def coefficientOpenDiskAmbientInclusion (d : ℕ) :
    C(T02A06HemisphereExcision.euclideanOpenDisk d,
      CoefficientModelLocal.E d) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

theorem coefficientOpenDiskAmbientInclusion_mapsTo (d : ℕ) :
    Set.MapsTo (coefficientOpenDiskAmbientInclusion d)
      (T02A06HemisphereExcision.puncturedOpenDiskSet d)
      (CoefficientModelLocal.puncture d) := by
  intro x hx
  change x.1 ≠ 0 at hx ⊢
  exact hx

theorem coefficientOpenDiskConnecting_model_naturality (k : ℕ) :
    CoefficientPairSequence.connecting ℤ
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1) ≫
      HomologicalComplex.homologyMap
        (CoefficientRadialPair.subMap ℤ
          (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))
          (CoefficientModelLocal.puncture (k + 2))
          (coefficientOpenDiskAmbientInclusion (k + 2))
          (coefficientOpenDiskAmbientInclusion_mapsTo (k + 2))) (k + 1) =
    HomologicalComplex.homologyMap
        (CoefficientRadialPair.pairMap ℤ
          (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))
          (CoefficientModelLocal.puncture (k + 2))
          (coefficientOpenDiskAmbientInclusion (k + 2))
          (coefficientOpenDiskAmbientInclusion_mapsTo (k + 2))) (k + 2) ≫
      CoefficientPairSequence.connecting ℤ
        (CoefficientModelLocal.puncture (k + 2)) (k + 1) := by
  exact CoefficientPairNaturality.connecting_naturality ℤ
    (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))
    (CoefficientModelLocal.puncture (k + 2))
    (coefficientOpenDiskAmbientInclusion (k + 2))
    (coefficientOpenDiskAmbientInclusion_mapsTo (k + 2)) (k + 1)

def coefficientOpenDiskPunctureInclusion (d : ℕ) :
    C(T02A06HemisphereExcision.puncturedOpenDisk d,
      PuncturedNormedSpaceRadialEquivalence.PuncturedSpace
        (CoefficientModelLocal.E d)) where
  toFun x := ⟨x.1.1, x.2⟩
  continuous_toFun := by fun_prop

theorem coefficientOpenDisk_subspaceMap_eq (d : ℕ) :
    SingularExcision.subspaceMap
        (T02A06HemisphereExcision.puncturedOpenDiskSet d)
        (CoefficientModelLocal.puncture d)
        (coefficientOpenDiskAmbientInclusion d)
        (coefficientOpenDiskAmbientInclusion_mapsTo d) =
      TopCat.ofHom (coefficientOpenDiskPunctureInclusion d) := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem coefficientOpenDisk_radial_factorization (d : ℕ) :
    (PuncturedNormedSpaceRadialEquivalence.radialNormalize
      (CoefficientModelLocal.E d)).comp
        (coefficientOpenDiskPunctureInclusion d) =
      T02A06DiskRadialComparison.radialNormalizeMap d := by
  ext x : 1
  rfl

theorem coefficientOpenDiskRadial_homology_factorization (d n : ℕ) :
    HomologicalComplex.homologyMap
        (CoefficientRadialPair.subMap ℤ
          (T02A06HemisphereExcision.puncturedOpenDiskSet d)
          (CoefficientModelLocal.puncture d)
          (coefficientOpenDiskAmbientInclusion d)
          (coefficientOpenDiskAmbientInclusion_mapsTo d)) n ≫
      (CoefficientRadialPair.F ℤ n).map (TopCat.ofHom
        (PuncturedNormedSpaceRadialEquivalence.radialNormalize
          (CoefficientModelLocal.E d))) =
    (CoefficientRadialPair.F ℤ n).map (TopCat.ofHom
      (T02A06DiskRadialComparison.radialNormalizeMap d)) := by
  change (CoefficientRadialPair.F ℤ n).map
    (SingularExcision.subspaceMap _ _ _ _) ≫ _ = _
  rw [coefficientOpenDisk_subspaceMap_eq]
  rw [← (CoefficientRadialPair.F ℤ n).map_comp]
  exact congrArg
    (fun f => (CoefficientRadialPair.F ℤ n).map (TopCat.ofHom f))
    (coefficientOpenDisk_radial_factorization d)

noncomputable def coefficientSphereNormalizationComparisonAutomorphism (k : ℕ) :
    AddCommGrpCat.of ℤ ≅ AddCommGrpCat.of ℤ :=
  (forgetIntModules.mapIso
      (CoefficientSphereAntipodal.normalization ℤ k)).symm ≪≫
    IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (T02A06.euclideanUnitSphere (k + 2))) (k + 1) ≪≫
    SphereHomology.sphereTopHomologyIsoInt (k + 1) (by omega)

theorem coefficientSphereNormalization_comparison (k : ℕ) :
    forgetIntModules.map (CoefficientSphereAntipodal.normalization ℤ k).hom ≫
        (coefficientSphereNormalizationComparisonAutomorphism k).hom =
      (IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (T02A06.euclideanUnitSphere (k + 2))) (k + 1)).hom ≫
        (SphereHomology.sphereTopHomologyIsoInt (k + 1) (by omega)).hom := by
  rw [coefficientSphereNormalizationComparisonAutomorphism]
  simp only [Iso.trans_hom, Iso.symm_hom]
  simpa only [Category.assoc] using
    (forgetIntModules.mapIso
      (CoefficientSphereAntipodal.normalization ℤ k)).hom_inv_id_assoc
        ((IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of (T02A06.euclideanUnitSphere (k + 2))) (k + 1)).hom ≫
          (SphereHomology.sphereTopHomologyIsoInt
            (k + 1) (by omega)).hom)

noncomputable def coefficientSphereNormalizationComparisonUnit (k : ℕ) : ℤˣ :=
  CoefficientChartTransitionUnit.isoUnit ℤ
    (moduleIsoOfUnderlyingIso
      (coefficientSphereNormalizationComparisonAutomorphism k))

theorem coefficientSphereNormalizationComparisonAutomorphism_apply_one (k : ℕ) :
    (coefficientSphereNormalizationComparisonAutomorphism k).hom.hom 1 =
      (coefficientSphereNormalizationComparisonUnit k : ℤ) := by
  let e := coefficientSphereNormalizationComparisonAutomorphism k
  let em : ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ ℤ := moduleIsoOfUnderlyingIso e
  have hmap : forgetIntModules.map em.hom = e.hom := by
    dsimp [em, moduleIsoOfUnderlyingIso]
    exact forgetIntModules.map_preimage
      (X := ModuleCat.of ℤ ℤ) (Y := ModuleCat.of ℤ ℤ) e.hom
  have happ := ConcreteCategory.congr_hom hmap (1 : ℤ)
  calc
    e.hom.hom 1 = em.hom.hom 1 := happ.symm
    _ = (CoefficientChartTransitionUnit.isoUnit ℤ em : ℤ) * 1 :=
      CoefficientChartTransitionUnit.isoUnit_action ℤ _ 1
    _ = _ := by
      simp [coefficientSphereNormalizationComparisonUnit, e, em]

theorem coefficientSphereNormalizationComparisonAutomorphism_hom_eq_id_or_neg
    (k : ℕ) :
    (coefficientSphereNormalizationComparisonAutomorphism k).hom = 𝟙 _ ∨
      (coefficientSphereNormalizationComparisonAutomorphism k).hom = -𝟙 _ := by
  have hu : (coefficientSphereNormalizationComparisonUnit k : ℤ) = 1 ∨
      (coefficientSphereNormalizationComparisonUnit k : ℤ) = -1 :=
    Int.isUnit_eq_one_or (coefficientSphereNormalizationComparisonUnit k).isUnit
  rcases hu with hu | hu
  · left
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext_int
    change (coefficientSphereNormalizationComparisonAutomorphism k).hom.hom 1 = 1
    rw [coefficientSphereNormalizationComparisonAutomorphism_apply_one, hu]
  · right
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext_int
    change (coefficientSphereNormalizationComparisonAutomorphism k).hom.hom 1 = -1
    rw [coefficientSphereNormalizationComparisonAutomorphism_apply_one, hu]

theorem coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_endpoints
    (k : ℕ)
    (hneg :
      (coefficientSphereNormalizationComparisonAutomorphism k).hom = -𝟙 _) :
    (IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of (T02A06.euclideanUnitSphere (k + 2))) (k + 1)).hom ≫
        (SphereHomology.sphereTopHomologyIsoInt
          (k + 1) (by omega)).hom =
      (forgetIntModules.mapIso
          (CoefficientSphereAntipodal.normalization ℤ k)).hom ≫ (-𝟙 _) := by
  let e := forgetIntModules.mapIso
    (CoefficientSphereAntipodal.normalization ℤ k)
  let p := IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (T02A06.euclideanUnitSphere (k + 2))) (k + 1) ≪≫
    SphereHomology.sphereTopHomologyIsoInt (k + 1) (by omega)
  change p.hom = e.hom ≫ (-𝟙 _)
  change e.inv ≫ p.hom = -𝟙 _ at hneg
  have hh := congrArg (fun f => e.hom ≫ f) hneg
  simpa only [Category.assoc, e.hom_inv_id_assoc] using hh

theorem coefficientOpenDiskRadial_forgotten_naturality (k : ℕ) :
    forgetIntModules.map
        ((CoefficientRadialPair.F ℤ (k + 1)).map
          (TopCat.ofHom
            (T02A06DiskRadialComparison.radialNormalizeMap (k + 2)))) ≫
      (singularHomologyComparison
        (TopCat.of (T02A06.euclideanUnitSphere (k + 2))) (k + 1)).hom =
    (integralOpenDiskPunctureHomologyComparison k).hom ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat (k + 1)).obj
        (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom
            (T02A06DiskRadialComparison.radialNormalizeMap (k + 2))) := by
  simpa only [integralOpenDiskPunctureHomologyComparison_hom] using
    singularHomologyComparison_naturality
      (TopCat.ofHom
        (T02A06DiskRadialComparison.radialNormalizeMap (k + 2))) (k + 1)

noncomputable def coefficientOpenDiskNormalizationComposite (k : ℕ) :=
  forgetIntModules.map
      (CoefficientPairSequence.connecting ℤ
        (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
    forgetIntModules.map
      ((CoefficientRadialPair.F ℤ (k + 1)).map
        (TopCat.ofHom
          (T02A06DiskRadialComparison.radialNormalizeMap (k + 2)))) ≫
    forgetIntModules.map
      (CoefficientSphereAntipodal.normalization ℤ k).hom

noncomputable def productionOpenDiskNormalizationComposite (k : ℕ) :=
  (integralOpenDiskRelativeHomologyComparison k).hom ≫
    singularPairConnecting
      (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1) ≫
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat (k + 1)).obj
      (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom
          (T02A06DiskRadialComparison.radialNormalizeMap (k + 2))) ≫
    (SphereHomology.sphereTopHomologyIsoInt (k + 1) (by omega)).hom

theorem coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_openDisk
    (k : ℕ)
    (hneg :
      (coefficientSphereNormalizationComparisonAutomorphism k).hom = -𝟙 _) :
    productionOpenDiskNormalizationComposite k =
      coefficientOpenDiskNormalizationComposite k ≫ (-𝟙 _) := by
  have hc := coefficientOpenDiskConnecting_comparison k
  have hr := coefficientOpenDiskRadial_forgotten_naturality k
  have hs :=
    coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_endpoints
      k hneg
  unfold productionOpenDiskNormalizationComposite
    coefficientOpenDiskNormalizationComposite
  have h1 := congrArg (fun q => q ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat (k + 1)).obj
        (AddCommGrpCat.of ℤ)).map
          (TopCat.ofHom
            (T02A06DiskRadialComparison.radialNormalizeMap (k + 2))) ≫
      (SphereHomology.sphereTopHomologyIsoInt
        (k + 1) (by omega)).hom) hc.symm
  have h2 := congrArg (fun q =>
      forgetIntModules.map
          (CoefficientPairSequence.connecting ℤ
            (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
        q ≫
        (SphereHomology.sphereTopHomologyIsoInt
          (k + 1) (by omega)).hom) hr.symm
  have h3 := congrArg (fun q =>
      forgetIntModules.map
          (CoefficientPairSequence.connecting ℤ
            (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
        forgetIntModules.map
          ((CoefficientRadialPair.F ℤ (k + 1)).map
            (TopCat.ofHom
              (T02A06DiskRadialComparison.radialNormalizeMap (k + 2)))) ≫ q) hs
  simp only [Category.assoc] at h1 h2 h3 ⊢
  simpa only [Functor.mapIso_hom] using h1.trans (h2.trans h3)

theorem coefficientOpenDiskNormalizationComposite_eq_model (k : ℕ) :
    coefficientOpenDiskNormalizationComposite k =
      forgetIntModules.map
          (HomologicalComplex.homologyMap
            (CoefficientRadialPair.pairMap ℤ
              (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))
              (CoefficientModelLocal.puncture (k + 2))
              (coefficientOpenDiskAmbientInclusion (k + 2))
              (coefficientOpenDiskAmbientInclusion_mapsTo (k + 2))) (k + 2)) ≫
        coefficientModelNormalizationComposite k := by
  have hc := congrArg forgetIntModules.map
    (coefficientOpenDiskConnecting_model_naturality k)
  have hr := congrArg forgetIntModules.map
    (coefficientOpenDiskRadial_homology_factorization (k + 2) (k + 1))
  simp only [Functor.map_comp] at hc hr
  unfold coefficientOpenDiskNormalizationComposite
    coefficientModelNormalizationComposite
  have h1 := congrArg (fun q =>
      forgetIntModules.map
          (CoefficientPairSequence.connecting ℤ
            (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2)) (k + 1)) ≫
        q ≫
        forgetIntModules.map
          (CoefficientSphereAntipodal.normalization ℤ k).hom) hr.symm
  have h2 := congrArg (fun q => q ≫
      forgetIntModules.map
        ((CoefficientRadialPair.F ℤ (k + 1)).map
          (TopCat.ofHom
            (PuncturedNormedSpaceRadialEquivalence.radialNormalize
              (CoefficientModelLocal.E (k + 2))))) ≫
      forgetIntModules.map
        (CoefficientSphereAntipodal.normalization ℤ k).hom) hc
  exact h1.trans h2

theorem productionOpenDiskNormalizationComposite_eq_model (k : ℕ) :
    productionOpenDiskNormalizationComposite k =
      (integralOpenDiskRelativeHomologyComparison k).hom ≫
        (HigherModelLocalHomology.localIsoInt k).hom := by
  unfold productionOpenDiskNormalizationComposite
  rw [HigherModelLocalHomology.comparison]

theorem coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_openDisk_model_factors
    (k : ℕ)
    (hneg :
      (coefficientSphereNormalizationComparisonAutomorphism k).hom = -𝟙 _) :
    (integralOpenDiskRelativeHomologyComparison k).hom ≫
        (HigherModelLocalHomology.localIsoInt k).hom =
      forgetIntModules.map
          (HomologicalComplex.homologyMap
            (CoefficientRadialPair.pairMap ℤ
              (T02A06HemisphereExcision.puncturedOpenDiskSet (k + 2))
              (CoefficientModelLocal.puncture (k + 2))
              (coefficientOpenDiskAmbientInclusion (k + 2))
              (coefficientOpenDiskAmbientInclusion_mapsTo (k + 2))) (k + 2)) ≫
        coefficientModelNormalizationComposite k ≫ (-𝟙 _) := by
  have h :=
    coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_openDisk
      k hneg
  rw [productionOpenDiskNormalizationComposite_eq_model,
    coefficientOpenDiskNormalizationComposite_eq_model] at h
  simpa only [Category.assoc] using h

theorem coefficientPairMap_forgotten_projection_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ A)) ≫
        (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (CoefficientRadialPair.pairMap ℤ A B f hf) =
      (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (CoefficientRadialPair.absoluteMap ℤ f) ≫
        (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (cokernel.π (CoefficientRelativeSmall.subspaceMap ℤ B)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun q => (forgetIntModules.mapHomologicalComplex
      (ComplexShape.down ℕ)).map q)
    (CoefficientRadialPair.projection ℤ A B f hf)

theorem coefficientAbsoluteMap_forgotten_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    (forgetIntModules.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (CoefficientRadialPair.absoluteMap ℤ f) ≫
        (singularChainsComparison (TopCat.of Y)).hom =
      (singularChainsComparison (TopCat.of X)).hom ≫
        absoluteSingularMap f := by
  simpa [CoefficientRadialPair.absoluteMap, absoluteSingularMap] using
    (singularChainsComparison_naturality (TopCat.ofHom f))

end ConstructionTargets.ManifoldFundamentalClass

#print axioms ConstructionTargets.ManifoldFundamentalClass.neighborhoodInclusion_Hsucc_isIso
#print axioms ConstructionTargets.ManifoldFundamentalClass.chartGenerator_eq_of_transitionUnit_eq_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.overlapTransitionUnit_isLocallyConstant
#print axioms ConstructionTargets.ManifoldFundamentalClass.overlapTransitionUnit_eq_of_isPreconnected
#print axioms ConstructionTargets.ManifoldFundamentalClass.overlapTransitionUnit_eq_one_of_isPreconnected
#print axioms ConstructionTargets.ManifoldFundamentalClass.chartGenerator_eq_on_preconnected_overlap_of_baseUnit_eq_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOverlapTransitionUnit_eq_one_or_neg_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOverlapTransitionUnit_eq_one_of_ne_neg_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralChartGenerator_eq_on_preconnected_overlap_of_ne_neg_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.globalGenerator
#print axioms ConstructionTargets.ManifoldFundamentalClass.globalGenerator_generates
#print axioms ConstructionTargets.ManifoldFundamentalClass.mapGlobalGenerator_generates_of_isIso
#print axioms ConstructionTargets.ManifoldFundamentalClass.isIso_of_map_globalGenerator_eq_globalGenerator
#print axioms ConstructionTargets.ManifoldFundamentalClass.localizationMap
#print axioms ConstructionTargets.ManifoldFundamentalClass.localizationMap_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.localizationMap_apply_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator_generates
#print axioms ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap_groupGlobalGenerator_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.localizationMap_groupGlobalGenerator_transport
#print axioms ConstructionTargets.ManifoldFundamentalClass.localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator
#print axioms ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective
#print axioms ConstructionTargets.ManifoldFundamentalClass.localizationCoefficient_eq_one_of_normalized
#print axioms ConstructionTargets.ManifoldFundamentalClass.distinguishedChartGenerator_eq_coefficientGenerator
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralSingularChainsComparison_subtype_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientSubspaceMap_eq_integralSubtypeChainMap
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralMappedRelativeCokernelComparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntegralRelativeCokernelComparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization
#print axioms ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison_generator_of_normalization
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralDirectCokernelComparison_projection
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntegralRelativeCokernelComparison_projection
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport_projection
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralCompositeCokernelComparison_projection
#print axioms ConstructionTargets.ManifoldFundamentalClass.cokernelProjection_comp_relativeSingularChainsIso_inv
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralCompositeRelativeProjection_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport_projection
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport_homology_projection
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientRelativeProjection_mapHomologyIso_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientPairInclusion_mapHomologyIso_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientPairInclusion_mapCyclesIso_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientPairInclusion_mapOpcyclesIso_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientPairInclusion_mapLeftHomologyIso_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientPairInclusion_mapRightHomologyIso_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModules_shortExact
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModulesSnakeInput_zero_squares
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModules_preservesParallelPairLimits
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModules_preservesParallelPairColimits
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModulesSnakeInput_preservedKernelτ₁
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModulesParallelPairZeroIso
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModulesSnakeInput_transportedKernelτ₁
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModulesSnakeInput_kernelτ₁ConeIso
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetIntModulesSnakeInput_kernelτ₁IsLimit
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeKernelτ₂Limit
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeKernelτ₃Limit
#print axioms ConstructionTargets.ManifoldFundamentalClass.scPairZeroπ₁Iso
#print axioms ConstructionTargets.ManifoldFundamentalClass.scPairZeroπ₂Iso
#print axioms ConstructionTargets.ManifoldFundamentalClass.scPairZeroπ₃Iso
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeKernelLimit
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeCokernelτ₁Preserved
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeCokernelτ₁Limit
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeCokernelτ₂Limit
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeCokernelτ₃Limit
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeCokernelLimit
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeInput
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetHomologyRowHom
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetOpcyclesRowHom
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetCyclesRowHom
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetTerminalHomologyRowHom
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetMapHomologyIsoRight_eq
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetHomologyι_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetPOpcycles_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetICycles_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetToCycles_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetOpcyclesToCycles_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetHomologyπ_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetHomologySequenceSnakeInputHom
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetHomologySequence_delta_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeDelta_map_apply_of_witness
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgetSnakeInput_delta_map
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskConnecting_forgotten_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskConnecting_comparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskConnecting_model_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskRadial_homology_factorization
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalization_comparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonAutomorphism_hom_eq_id_or_neg
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_endpoints
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskRadial_forgotten_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_openDisk
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskNormalizationComposite_eq_model
#print axioms ConstructionTargets.ManifoldFundamentalClass.productionOpenDiskNormalizationComposite_eq_model
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientSphereNormalizationComparisonAutomorphism_hom_eq_neg_implies_openDisk_model_factors
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientPairMap_forgotten_projection_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientAbsoluteMap_forgotten_naturality
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_projection
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_generator_of_normalization
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_normalization_of_generator
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_generator_eq_zsmul
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorUnit
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_unit
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_one_or_neg_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_one_of_nonneg
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_one_of_normalization
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_generator_of_coefficient_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_normalization_of_coefficient_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_normalization_of_nonnegative
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_one_of_ne_neg_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalGeneratorCoefficient_eq_automorphism_one
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.ambientChartHomologyIso
#print axioms ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_after_coefficient
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_endpoint_factors
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientLocalForwardComposite
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientProjectedForwardComposite
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientProjection_comp_coefficientLocalForwardComposite
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientLocalIso_hom_eq_forwardComposite
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_coefficient_factors
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_corrected_comparison_factors
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport_homologyMap
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralTransportHomologyComposite
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientProjection_comp_integralTransportHomologyComposite
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_projected_factors
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_concrete_endpoints
#print axioms ConstructionTargets.ManifoldFundamentalClass.productionProjectedChartPrefix
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientProjectedChartPrefix
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_prefix_model_equality
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientModelNormalizationComposite
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientModelLocalIso_forget_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_implies_model_factors
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralBall_forget_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralBall_forget_hom_eq_model_factors
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskRelativeHomologyComparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskRelativeHomologyComparison_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskPunctureHomologyComparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskPunctureHomologyComparison_hom
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskPairShortComplexComparison
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskCoefficientPairShortExact
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskSnakeInput
#print axioms ConstructionTargets.ManifoldFundamentalClass.forgottenCoefficientOpenDiskSnakeInput
#print axioms ConstructionTargets.ManifoldFundamentalClass.openDiskSnakeInputs_delta
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskConnecting_naturality_raw
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralOpenDiskComparison_component_homology_maps
#print axioms ConstructionTargets.ManifoldFundamentalClass.coefficientOpenDiskConnectingTransport_eq
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport_homologyMap_eq_composite
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_transport_homology_factors
