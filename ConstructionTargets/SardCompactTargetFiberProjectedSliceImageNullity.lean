import ConstructionTargets.SardCompactProjectedSliceImageNullity

open Set MeasureTheory

namespace SardCompactTargetFiberProjectedSliceImageNullityProbe

/-- Target-coordinate fiber containment in lower-dimensional projected slices
implies nullity of the complete compact localized image. -/
theorem measure_image_zero_of_compact_targetFiber_projectedSlices
    {D Y G R C S X : Type*} [TopologicalSpace X]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    (μY : Measure Y) (μC : Measure C) (μS : Measure S)
    [Measure.IsAddHaarMeasure μY] [Measure.IsAddHaarMeasure μC]
    [Measure.IsAddHaarMeasure μS]
    (n : WithTop ℕ∞)
    (hind : Module.finrank ℝ G < Module.finrank ℝ D →
      ∀ (q : G → S) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (e : Y ≃L[ℝ] C × S) (f : X → Y) (K : Set X)
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (q : C → G → S) (s : C → Set G) (P : S →L[ℝ] R)
    (hparam : ∀ r,
      (fun y => (e y).2) '' (f '' K ∩ {y | (e y).1 = r}) ⊆ q r '' s r)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ D)
    (hn : n ≠ 0)
    (hq : ∀ r z, z ∈ s r → ContDiffAt ℝ n (q r) z)
    (hP : Function.Surjective P)
    (hzero : ∀ r z, z ∈ s r → HasFDerivAt (P ∘ q r) (0 : G →L[ℝ] R) z) :
    μY (f '' K) = 0 := by
  apply SardCompactProjectedSliceImageNullityProbe.measure_image_zero_of_compact_projectedSlices
    μY μC μS n hind e f K hK hf (fun x => (e (f x)).1) (fun x => (e (f x)).2)
    (fun _ => rfl) q s P
  · intro r z hz
    rcases hz with ⟨x, ⟨hx, hr⟩, rfl⟩
    apply hparam r
    exact ⟨f x, ⟨⟨x, hx, rfl⟩, hr⟩, rfl⟩
  · exact hdim
  · exact hn
  · exact hq
  · exact hP
  · exact hzero

#print axioms measure_image_zero_of_compact_targetFiber_projectedSlices

end SardCompactTargetFiberProjectedSliceImageNullityProbe
