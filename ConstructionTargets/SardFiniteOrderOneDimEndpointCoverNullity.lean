import ConstructionTargets.SardFiniteCoverMeasureBound
import ConstructionTargets.SardArbitrarilySmallMeasureLimit

open Metric Set MeasureTheory

noncomputable section

namespace SardFiniteOrderOneDimEndpointCoverNullityProbe

def OneDimEndpointBallCover
    {E F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (ε : ENNReal) : Prop :=
  Module.finrank ℝ F = 1 ∧ ∃ (centres : Finset F) (radius : F → ℝ),
    f '' K ⊆ ⋃ y ∈ centres, closedBall y (radius y) ∧
    ∑ y ∈ centres, volume (closedBall y (radius y)) < ε

theorem volume_image_eq_zero_of_oneDim_endpointBallCovers
    {E F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E)
    (hcover : ∀ ε : ENNReal, 0 < ε → OneDimEndpointBallCover f K ε) :
    volume (f '' K) = 0 := by
  apply measure_eq_zero_of_le_inv_nat volume (f '' K)
  intro n
  cases n with
  | zero => simp
  | succ n =>
      have hε : 0 < ((n + 1 : ℕ) : ENNReal)⁻¹ :=
        ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
      obtain ⟨_, centres, radius, himage, hsum⟩ := hcover _ hε
      exact (measure_le_finset_sum_of_subset_biUnion volume
        (f '' K) centres (fun y => closedBall y (radius y)) himage).trans hsum.le

#print axioms volume_image_eq_zero_of_oneDim_endpointBallCovers

end SardFiniteOrderOneDimEndpointCoverNullityProbe
