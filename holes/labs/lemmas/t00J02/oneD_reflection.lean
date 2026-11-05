import Mathlib
import ConstructionTargets.RelativeSingularConnectingNaturality
import ConstructionTargets.CollaredConnectedSumHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CircleHomology
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.DiskBoundedPreimageDuality
import ConstructionTargets.EmbeddedCircleLift
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.TransversePreimageDuality
import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.TransversePreimageGeometry
import ConstructionTargets.OrientedSurfacePreimageDuality
import ConstructionTargets.t00J02Closure
import ConstructionTargets.CircleActualLocalization
import ConstructionTargets.HigherChartLocalGenerator
import ConstructionTargets.OneDimensionalChartLocalGenerator

open CategoryTheory Set
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.ChartPairRelativeHomologyTransport
open ConstructionTargets.T02A06HemisphereExcision

noncomputable section

/-- Negation reverses the real local orientation. The model disk reflection
acts by minus the identity on every relative class; neighborhood excision and
the real-line coordinate homeomorphism transport that action to the ambient
real line, without comparing choices of generators. -/
theorem realNegation_realLocalGenerator :
    HomologicalComplex.homologyMap
      (relativeSingularMap (deletedPoint (0 : ℝ)) (deletedPoint (0 : ℝ))
        (⟨fun u : ℝ => -u, continuous_neg⟩ : C(ℝ, ℝ))
        (by intro u hu h; exact hu (neg_eq_zero.mp h))) 1
      (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0) =
    -ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0 := by
  let E := EuclideanSpace ℝ (Fin 1)
  let U : Set E := Metric.ball 0 1
  let P := puncturedOpenDiskSet 1
  let A := deletedPoint (0 : E)
  let B := deletedPoint (0 : ℝ)
  let e := ConstructionTargets.OneDimensionalChartLocalGenerator.realLineCoordinates.symm
  have he0 : e (0 : E) = 0 := rfl
  have hepair : ∀ x, x ∈ A ↔ e x ∈ B := by
    intro x
    change x ≠ 0 ↔ e x ≠ 0
    rw [← he0, e.injective.ne_iff]
  let c := pairContinuousMap e
  have hc : MapsTo c A B := pairContinuousMap_mapsTo e A B hepair
  let i := neighborhoodInclusion U
  have hi : MapsTo i P A := neighborhoodInclusion_mapsTo U 0
  let f := c.comp i
  have hf : MapsTo f P B := hc.comp hi
  let n : C(ℝ, ℝ) := ⟨fun u => -u, continuous_neg⟩
  have hn : MapsTo n B B := by
    intro u hu h
    exact hu (neg_eq_zero.mp h)
  let Hf := HomologicalComplex.homologyMap (relativeSingularMap P B f hf) 1
  haveI : IsIso Hf := by
    haveI : IsIso (HomologicalComplex.homologyMap (relativeSingularMap P A i hi) 1) :=
      neighborhoodInclusion_H1_isIso U (0 : E) Metric.isOpen_ball
        (Metric.mem_ball_self (by norm_num))
    haveI : IsIso (HomologicalComplex.homologyMap (relativeSingularMap A B c hc) 1) :=
      relativeSingularMap_homeomorphPair_isIso e A B hepair 1
    change IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap P B (c.comp i) hf) 1)
    rw [← relativeSingularHomologyMap_comp P A B i c hi hc hf 1]
    infer_instance
  have hs := ConstructionTargets.OneDiskLocalOrientation.relativeH1_square
    P B ConstructionTargets.OneDiskLocalOrientation.reflection n f
    ConstructionTargets.OneDiskLocalOrientation.reflection_mapsTo hn hf (by
      apply ContinuousMap.ext
      intro x
      rfl)
  rw [ConstructionTargets.OneDiskLocalOrientation.reflection_H1_eq_neg_id] at hs
  have hneg : HomologicalComplex.homologyMap (relativeSingularMap B B n hn) 1 = -𝟙 _ := by
    apply (cancel_epi Hf).mp
    simpa only [ConstructionTargets.OneDiskLocalOrientation.RH,
      Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]
      using hs.symm
  have h := ConcreteCategory.congr_hom hneg
    (ConstructionTargets.OneDimensionalChartLocalGenerator.realLocalGenerator 0)
  exact h

#print axioms realNegation_realLocalGenerator
