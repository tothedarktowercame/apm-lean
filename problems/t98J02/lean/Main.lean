import Mathlib
import ConstructionTargets.CoveringDegree

/-! # t98J02: separation and lifts of simple closed curves

A closed surface here is a connected compact Hausdorff second-countable
2-manifold without boundary. Its charts are local homeomorphisms to R2;
no smoothness is inserted into this topological problem. Simple closed
curves and their lifts are actual embedded continuous circles, with p ∘ lift
= baseCurve, which identifies the two image circles homeomorphically.

The source does not say the cover is connected. Part (a) holds for connected
covers, but disjoint copies give a counterexample if disconnected covers are
allowed. Both readings are explicitly recorded. Part (b) has a counterexample
even with connected covering space. All these are geometric propositions;
no separation/homology equivalence is assumed.
-/

open Set ConstructionTargets.CoveringDegree
noncomputable section
namespace T98J02

structure ClosedSurface where
  carrier : Type
  topology : TopologicalSpace carrier
  charts : @ChartedSpace (EuclideanSpace ℝ (Fin 2)) _ carrier topology
  compact : @CompactSpace carrier topology
  hausdorff : @T2Space carrier topology
  secondCountable : @SecondCountableTopology carrier topology
  connected : @ConnectedSpace carrier topology

attribute [instance] ClosedSurface.topology ClosedSurface.charts
  ClosedSurface.compact ClosedSurface.hausdorff ClosedSurface.secondCountable
  ClosedSurface.connected

/-- A degree-one lift, expressed through parametrizations of both image circles. -/
def IsCurveLift {F E : Type} [TopologicalSpace F] [TopologicalSpace E]
    (p : E → F) (c : C(Circle, F)) (l : C(Circle, E)) : Prop :=
  Topology.IsEmbedding c ∧ Topology.IsEmbedding l ∧ ∀ z, p (l z) = c z

def Nonseparating {F : Type} [TopologicalSpace F] (c : C(Circle, F)) : Prop :=
  IsPreconnected (range c)ᶜ

end T98J02
open T98J02

theorem apm_t98j02 :
    (∀ (F : ClosedSurface) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      IsKSheetedCover p n → IsCurveLift p c l →
      Nonseparating c → Nonseparating l) ∧
    (∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ¬ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      Nonseparating c ∧ ¬ Nonseparating l) ∧
    (∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      ¬ Nonseparating c ∧ Nonseparating l) := by
  sorry
