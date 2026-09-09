import ConstructionTargets.OneDiskLocalOrientation

open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.ChartPairRelativeHomologyTransport

variable {X : Type} [TopologicalSpace X]

/-- The ambient deleted-point subspace, with integral relative singular chains. -/
def deletedPoint (x : X) : Set X := {x}ᶜ

/-- The deleted point inside a neighborhood; membership uses the ambient point. -/
def neighborhoodDeletedPoint (U : Set X) (x : X) : Set U :=
  {u | u.1 ≠ x}

def neighborhoodInclusion (U : Set X) : C(U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem neighborhoodInclusion_mapsTo (U : Set X) (x : X) :
    Set.MapsTo (neighborhoodInclusion U) (neighborhoodDeletedPoint U x) (deletedPoint x) :=
  fun _ h => h

/-- Identify the actual neighborhood subtype with the complement of its complement. -/
def neighborhoodExcisionHomeomorph (U : Set X) : U ≃ₜ ((Uᶜ)ᶜ : Set X) :=
  Homeomorph.setCongr (compl_compl U).symm

theorem neighborhoodExcision_pair_iff (U : Set X) (x : X) (u : U) :
    u ∈ neighborhoodDeletedPoint U x ↔
      neighborhoodExcisionHomeomorph U u ∈ excisedSubspace (deletedPoint x) Uᶜ := by
  rfl

/-- Exact map comparison: the chart-neighborhood inclusion is the production
excision map after the canonical subtype identification. -/
theorem neighborhoodInclusion_chain_eq (U : Set X) (x : X) :
    relativeSingularMap (neighborhoodDeletedPoint U x) (deletedPoint x)
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x) =
    relativeSingularMap (neighborhoodDeletedPoint U x) (excisedSubspace (deletedPoint x) Uᶜ)
      (pairContinuousMap (neighborhoodExcisionHomeomorph U))
      (pairContinuousMap_mapsTo _ _ _ (neighborhoodExcision_pair_iff U x)) ≫
      relativeExcisionMap (deletedPoint x) Uᶜ := by
  let e := pairContinuousMap (neighborhoodExcisionHomeomorph U)
  have he := pairContinuousMap_mapsTo (neighborhoodExcisionHomeomorph U)
    (neighborhoodDeletedPoint U x) (excisedSubspace (deletedPoint x) Uᶜ)
    (neighborhoodExcision_pair_iff U x)
  have hf := excisionInclusion_mapsTo (deletedPoint x) Uᶜ
  have hcomp : (excisionInclusion Uᶜ).comp e = neighborhoodInclusion U := by
    ext u
    rfl
  have h := relativeSingularMap_comp (neighborhoodDeletedPoint U x)
    (excisedSubspace (deletedPoint x) Uᶜ) (deletedPoint x)
    e (excisionInclusion Uᶜ) he hf (hf.comp he)
  simpa only [hcomp] using h.symm

/-- Excision makes inclusion of any open neighborhood of a point an
isomorphism on its local H1. T1 supplies openness of the deleted point. -/
theorem neighborhoodInclusion_H1_isIso [T1Space X]
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U x) (deletedPoint x)
        (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)) 1) := by
  have hZ : Uᶜ ⊆ interior (deletedPoint x) := by
    have ho : IsOpen (deletedPoint x) := isClosed_singleton.isOpen_compl
    rw [ho.interior_eq]
    intro y hy hxy
    exact hy (hxy.symm ▸ hx)
  letI := relativeExcisionMap_homologyMap_isIso_one (deletedPoint x) Uᶜ hU.isClosed_compl hZ
  letI := relativeSingularMap_homeomorphPair_isIso (neighborhoodExcisionHomeomorph U)
    (neighborhoodDeletedPoint U x) (excisedSubspace (deletedPoint x) Uᶜ)
    (neighborhoodExcision_pair_iff U x) 1
  rw [neighborhoodInclusion_chain_eq, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Inclusion sends a generator of neighborhood local H1 to a generator of
ambient local H1, through the actual map just compared with excision. -/
theorem neighborhoodInclusion_sends_generator [T1Space X]
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U)
    (g : (RelativeSingularChains (neighborhoodDeletedPoint U x)).homology 1)
    (hg : ∀ z : (RelativeSingularChains (neighborhoodDeletedPoint U x)).homology 1,
      ∃ n : ℤ, n • g = z) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 1, ∃ n : ℤ,
      n • HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U x) (deletedPoint x)
          (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)) 1 g = z := by
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U x) (deletedPoint x)
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)) 1
  letI := neighborhoodInclusion_H1_isIso U x hU hx
  intro z
  obtain ⟨n, hn⟩ := hg ((asIso f).inv z)
  refine ⟨n, ?_⟩
  change n • f g = z
  rw [← map_zsmul, hn]
  exact ConcreteCategory.congr_hom (asIso f).inv_hom_id z

/-- Concrete real-line neighborhood inclusion. This does not construct its chart. -/
theorem lineNeighborhoodInclusion_H1_isIso (x : ℝ) : IsIso (HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (Metric.ball x 1) x) (deletedPoint x)
      (neighborhoodInclusion (Metric.ball x 1))
      (neighborhoodInclusion_mapsTo (Metric.ball x 1) x)) 1) :=
  neighborhoodInclusion_H1_isIso _ _ Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))

/-- Concrete circle neighborhood inclusion; the restricted chart remains separate. -/
theorem circleNeighborhoodInclusion_H1_isIso (x : Circle) : IsIso (HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint (Metric.ball x 1) x) (deletedPoint x)
      (neighborhoodInclusion (Metric.ball x 1))
      (neighborhoodInclusion_mapsTo (Metric.ball x 1) x)) 1) :=
  neighborhoodInclusion_H1_isIso _ _ Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))

end ConstructionTargets.LocalHomologyNeighborhoodExcision
#print axioms ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_chain_eq
#print axioms ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso
#print axioms ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_sends_generator

#print axioms ConstructionTargets.LocalHomologyNeighborhoodExcision.lineNeighborhoodInclusion_H1_isIso
#print axioms ConstructionTargets.LocalHomologyNeighborhoodExcision.circleNeighborhoodInclusion_H1_isIso
