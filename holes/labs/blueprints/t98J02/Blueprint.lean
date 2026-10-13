import Mathlib
import ConstructionTargets.CoveringDegree

/-! # t98J02: separation and lifts of simple closed curves -/

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

/-- LIBRARY: a degree-one lift of a nonseparating embedded circle through a
connected finite cover of closed surfaces remains nonseparating. -/
theorem t98J02_nonseparating_lift_connectedCover :
    ∀ (F : ClosedSurface) (E : Type) [TopologicalSpace E] [ConnectedSpace E]
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      IsKSheetedCover p n → IsCurveLift p c l →
      Nonseparating c → Nonseparating l := by
  sorry

/-- LIBRARY: the trivial double cover of a torus supplies the counterexample
when disconnected covering spaces are allowed. -/
theorem t98J02_disconnected_trivialCover_counterexample :
    ∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ¬ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      Nonseparating c ∧ ¬ Nonseparating l := by
  sorry

/-- LIBRARY: a connected double cover of a genus-two surface can have a
nonseparating degree-one lift of a separating circle. -/
theorem t98J02_connected_doubleCover_counterexample :
    ∃ (F : ClosedSurface) (E : Type) (_ : TopologicalSpace E)
      (n : ℕ) (p : E → F.carrier) (c : C(Circle, F.carrier)) (l : C(Circle, E)),
      0 < n ∧ ConnectedSpace E ∧ IsKSheetedCover p n ∧ IsCurveLift p c l ∧
      ¬ Nonseparating c ∧ Nonseparating l := by
  sorry

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
  exact ⟨t98J02_nonseparating_lift_connectedCover,
    t98J02_disconnected_trivialCover_counterexample,
    t98J02_connected_doubleCover_counterexample⟩

#print axioms apm_t98j02
