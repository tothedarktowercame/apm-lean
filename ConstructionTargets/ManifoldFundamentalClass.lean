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
