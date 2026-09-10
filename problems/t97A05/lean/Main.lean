import Mathlib
import ConstructionTargets.ManifoldIntersectionTargets

/-! # t97A05: nonzero intersection prevents separation
All four manifolds are boundaryless. The inclusions are smooth embeddings and
immersions. Orientations are smooth nowhere-zero top forms. The intersection
number is an actual signed count after homotopy to a transverse representative;
no transversality of the original submanifolds is added to the hypotheses.
-/
open scoped Manifold ContDiff
open ConstructionTargets.ManifoldFormTargets ConstructionTargets.ManifoldIntersectionTargets
noncomputable section

theorem apm_t97a05 (n k : ℕ) {X Y W Z : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [TopologicalSpace Z] [T2Space Z] [SecondCountableTopology Z]
    [ChartedSpace (E (n+k)) X] [IsManifold 𝓘(ℝ,E (n+k)) ∞ X]
    [ChartedSpace (E (n+1)) Y] [IsManifold 𝓘(ℝ,E (n+1)) ∞ Y]
    [ChartedSpace (E n) W] [IsManifold 𝓘(ℝ,E n) ∞ W]
    [ChartedSpace (E k) Z] [IsManifold 𝓘(ℝ,E k) ∞ Z]
    [CompactSpace Y] [CompactSpace W] [CompactSpace Z]
    [ConnectedSpace Y] [ConnectedSpace W]
    (volX : Form (E (n+k)) X (n+k)) (volY : Form (E (n+1)) Y (n+1))
    (volW : Form (E n) W n) (volZ : Form (E k) Z k)
    (hvolX : IsVolumeForm volX) (hvolY : IsVolumeForm volY)
    (hvolW : IsVolumeForm volW) (hvolZ : IsVolumeForm volZ)
    (iY : ContinuousMap Y X) (iW : ContinuousMap W Y) (iZ : ContinuousMap Z X)
    (smoothY : ContMDiff 𝓘(ℝ,E (n+1)) 𝓘(ℝ,E (n+k)) ∞ iY)
    (smoothW : ContMDiff 𝓘(ℝ,E n) 𝓘(ℝ,E (n+1)) ∞ iW)
    (smoothZ : ContMDiff 𝓘(ℝ,E k) 𝓘(ℝ,E (n+k)) ∞ iZ)
    (embedY : Topology.IsEmbedding iY) (embedW : Topology.IsEmbedding iW)
    (embedZ : Topology.IsEmbedding iZ)
    (immerseY : Manifold.IsImmersion 𝓘(ℝ,E (n+1)) 𝓘(ℝ,E (n+k)) ∞ iY)
    (immerseW : Manifold.IsImmersion 𝓘(ℝ,E n) 𝓘(ℝ,E (n+1)) ∞ iW)
    (immerseZ : Manifold.IsImmersion 𝓘(ℝ,E k) 𝓘(ℝ,E (n+k)) ∞ iZ)
    (value : ℤ) (hvalue : value ≠ 0)
    (hintersection : HasIntersectionNumber volW volZ volX (iY.comp iW) iZ value) :
    IsConnected ((Set.range iW)ᶜ : Set Y) := by
  sorry
