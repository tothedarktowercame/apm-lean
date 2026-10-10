import ConstructionTargets.LocalHomologyNeighborhoodExcision
import ConstructionTargets.CoefficientChartTransitionUnit
import ConstructionTargets.CoefficientTransitionLocalConstancy

open CategoryTheory
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
