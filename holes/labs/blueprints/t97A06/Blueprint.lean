import Mathlib
import ConstructionTargets.ManifoldFormTargets

/-! # t97A06: extending a volume form off an embedded manifold

The definitions used below are the frozen differential-form definitions from
`ConstructionTargets.ManifoldFormTargets`: `Form`, `IsSmooth`, `pullback`,
`IsClosed`, and `IsVolumeForm`.
-/

open scoped Manifold ContDiff
open ConstructionTargets.ManifoldFormTargets
noncomputable section

/-- LIBRARY: a smooth form on a compact embedded submanifold extends smoothly
to the ambient manifold. -/
theorem t97A06_smoothForm_extension_of_compactEmbedding
    (n m : ℕ) {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
    [CompactSpace X]
    [ChartedSpace (Fin n → ℝ) X] [ChartedSpace (Fin m → ℝ) Y]
    [IsManifold 𝓘(ℝ,Fin n → ℝ) ∞ X] [IsManifold 𝓘(ℝ,Fin m → ℝ) ∞ Y]
    (i : X → Y) (hi : ContMDiff 𝓘(ℝ,Fin n → ℝ) 𝓘(ℝ,Fin m → ℝ) ∞ i)
    (hemb : Topology.IsEmbedding i)
    (himm : Manifold.IsImmersion 𝓘(ℝ,Fin n → ℝ) 𝓘(ℝ,Fin m → ℝ) ∞ i)
    (η : Form (Fin n → ℝ) X n) (hη : IsSmooth η) :
    ∃ form : Form (Fin m → ℝ) Y n, IsSmooth form ∧ pullback i form = η := by
  sorry

/-- LIBRARY: a positive-degree volume form cannot be the pullback of a closed
form along a null-homotopic smooth map from a nonempty compact manifold. -/
theorem t97A06_nullHomotopic_pullback_volume_not_closed
    (n m : ℕ) (hn : 0 < Module.finrank ℝ (Fin n → ℝ)) {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
    [Nonempty X] [CompactSpace X]
    [ChartedSpace (Fin n → ℝ) X] [ChartedSpace (Fin m → ℝ) Y]
    [IsManifold 𝓘(ℝ,Fin n → ℝ) ∞ X] [IsManifold 𝓘(ℝ,Fin m → ℝ) ∞ Y]
    (i : X → Y) (hi : ContMDiff 𝓘(ℝ,Fin n → ℝ) 𝓘(ℝ,Fin m → ℝ) ∞ i)
    (η : Form (Fin n → ℝ) X n) (hη : IsVolumeForm η)
    (form : Form (Fin m → ℝ) Y n) (hform : IsSmooth form)
    (hpull : pullback i form = η)
    (hnull : ∃ y : Y, ContinuousMap.Homotopic (⟨i, hi.continuous⟩ : C(X,Y))
      (ContinuousMap.const X y)) :
    ¬ IsClosed form := by
  sorry

theorem apm_t97a06
    (n m : ℕ) (hn : 0 < Module.finrank ℝ (Fin n → ℝ)) {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
    [Nonempty X] [CompactSpace X]
    [ChartedSpace (Fin n → ℝ) X] [ChartedSpace (Fin m → ℝ) Y]
    [IsManifold 𝓘(ℝ,Fin n → ℝ) ∞ X] [IsManifold 𝓘(ℝ,Fin m → ℝ) ∞ Y]
    (i : X → Y) (hi : ContMDiff 𝓘(ℝ,Fin n → ℝ) 𝓘(ℝ,Fin m → ℝ) ∞ i)
    (hemb : Topology.IsEmbedding i)
    (himm : Manifold.IsImmersion 𝓘(ℝ,Fin n → ℝ) 𝓘(ℝ,Fin m → ℝ) ∞ i)
    (η : Form (Fin n → ℝ) X n) (hη : IsVolumeForm η) :
    (∃ form : Form (Fin m → ℝ) Y n, IsSmooth form ∧ pullback i form = η) ∧
    (∀ form : Form (Fin m → ℝ) Y n, IsSmooth form → pullback i form = η →
      (∃ y : Y, ContinuousMap.Homotopic (⟨i, hi.continuous⟩ : C(X,Y))
        (ContinuousMap.const X y)) → ¬ IsClosed form) := by
  constructor
  · exact t97A06_smoothForm_extension_of_compactEmbedding n m i hi hemb himm η hη.1
  · intro form hform hpull hnull
    exact t97A06_nullHomotopic_pullback_volume_not_closed
      n m hn i hi η hη form hform hpull hnull

#print axioms apm_t97a06
