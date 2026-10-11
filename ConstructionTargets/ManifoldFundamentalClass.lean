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
#print axioms ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport_homologyMap_eq_composite
#print axioms ConstructionTargets.ManifoldFundamentalClass.correctedLocalNormalizationAutomorphism_hom_eq_neg_iff_transport_homology_factors
