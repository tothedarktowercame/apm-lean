import Mathlib
import ConstructionTargets.ManifoldFormTargets

/-! # t97A06: extending a volume form off an embedded manifold

All source conditions are retained: positive dimension, nonempty compact
oriented smooth X, its smooth submanifold inclusion into Y, and the given
volume form. The nowhere-zero top form encodes the orientation it induces;
a volume form positive for an already specified orientation gives exactly
this data. A smooth embedding with immersion normal form represents the
submanifold inclusion without replacing it by a bare function.

Both parts are stated: some smooth extension exists, and EVERY smooth
extension is nonclosed if the inclusion is null-homotopic. No integration or
Stokes theorem is needed to express either assertion.
-/

open scoped Manifold ContDiff
open ConstructionTargets.ManifoldFormTargets
noncomputable section

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
  sorry
