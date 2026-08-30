import ConstructionTargets.FrozenSimplexIntegralAdapter
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Euclidean triangle measure-coordinate reduction

This file transports the frozen `EuclideanSpace ℝ (Fin 2)` set integral to
the literal two-coordinate function space by Mathlib's volume-preserving
`WithLp.toLp` equivalence.  The final finite-product Fubini normalization is
isolated explicitly when the current API does not rewrite it automatically.
-/

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.EuclideanTriangleMeasureFubini

open ConstructionTargets.ExteriorDerivativeSimplexCalculus
open ConstructionTargets.FrozenSimplexIntegralAdapter

def coordinateTriangle : Set (Fin 2 → ℝ) :=
  {q | 0 ≤ q 0 ∧ 0 ≤ q 1 ∧ q 0 + q 1 ≤ 1}

theorem measurableSet_coordinateTriangle : MeasurableSet coordinateTriangle := by
  have h0 : Continuous (fun q : Fin 2 → ℝ => q 0) := continuous_apply 0
  have h1 : Continuous (fun q : Fin 2 → ℝ => q 1) := continuous_apply 1
  unfold coordinateTriangle
  change MeasurableSet
    ({q : Fin 2 → ℝ | 0 ≤ q 0} ∩
      ({q | 0 ≤ q 1} ∩ {q | q 0 + q 1 ≤ 1}))
  exact (measurableSet_le measurable_const h0.measurable).inter
    ((measurableSet_le measurable_const h1.measurable).inter
      (measurableSet_le (h0.add h1).measurable measurable_const))

theorem measurableSet_frozenTriangleDomain :
    MeasurableSet frozenTriangleDomain := by
  have h0 : Continuous (fun q : E2 => q 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous (fun q : E2 => q 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  unfold frozenTriangleDomain
  change MeasurableSet
    ({q : E2 | 0 ≤ q 0} ∩
      ({q | 0 ≤ q 1} ∩ {q | q 0 + q 1 ≤ 1}))
  exact (measurableSet_le measurable_const h0.measurable).inter
    ((measurableSet_le measurable_const h1.measurable).inter
      (measurableSet_le (h0.add h1).measurable measurable_const))

theorem toLp_mem_frozenTriangleDomain_iff (q : Fin 2 → ℝ) :
    WithLp.toLp 2 q ∈ frozenTriangleDomain ↔ q ∈ coordinateTriangle := by
  rfl

/-- Exact volume-preserving coordinate reduction. -/
theorem frozenTriangleSetIntegral_eq_coordinateIntegral :
    frozenTriangleSetIntegral (fun _ => 2) =
      ∫ q in coordinateTriangle, (2 : ℝ) := by
  unfold frozenTriangleSetIntegral
  rw [← integral_indicator measurableSet_frozenTriangleDomain,
    ← integral_indicator measurableSet_coordinateTriangle]
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ coordinateTriangle
  · rw [indicator_of_mem hq,
      indicator_of_mem ((toLp_mem_frozenTriangleDomain_iff q).mpr hq)]
  · have hnot : WithLp.toLp 2 q ∉ frozenTriangleDomain :=
      fun h => hq ((toLp_mem_frozenTriangleDomain_iff q).mp h)
    simp [Set.indicator, hq, hnot]

/-- The one standard finite-product normalization still not exposed by the
current simplifier: the `Fin 2 → ℝ` triangle set integral is the conventional
iterated integral with `0 ≤ y ≤ 1-x`. -/
def FinTwoTriangleFubini : Prop :=
  (∫ q in coordinateTriangle, (2 : ℝ)) =
    orientedTriangleIntegral (fun _ _ => 2)

theorem frozenTriangleMeasureAdapter_of_finTwoFubini
    (h : FinTwoTriangleFubini) : FrozenTriangleMeasureAdapter := by
  rw [FrozenTriangleMeasureAdapter,
    frozenTriangleSetIntegral_eq_coordinateIntegral]
  exact h

#print axioms measurableSet_coordinateTriangle
#print axioms measurableSet_frozenTriangleDomain
#print axioms toLp_mem_frozenTriangleDomain_iff
#print axioms frozenTriangleSetIntegral_eq_coordinateIntegral
#print axioms frozenTriangleMeasureAdapter_of_finTwoFubini

end ConstructionTargets.EuclideanTriangleMeasureFubini
