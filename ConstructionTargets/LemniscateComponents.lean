import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.CardComponents
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Connected components of polynomial lemniscate complements

This file isolates the construction lemma needed by `a00J04` and `a01A08`.
The component-frontier lemma below closes one of the topology API gaps noted
in those developments.  The final polynomial bound still needs the global
assembly described at the theorem.
-/

open Complex Polynomial Set Topology
open scoped Set.Notation

noncomputable section

namespace ConstructionTargets.LemniscateComponents

/-- The polynomial lemniscate `L = {z | ‖p(z)‖ = 1}`. -/
def lemniscate (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖aeval z p‖ = 1}

/-- The strict superlevel of a polynomial lemniscate. -/
def superlevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | 1 < ‖aeval z p‖}

/-- The strict sublevel of a polynomial lemniscate. -/
def sublevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖aeval z p‖ < 1}

/-- In a locally connected space, the ambient frontier of a connected
component of an open set is contained in the frontier of that open set. -/
lemma frontier_connectedComponentIn_subset_frontier
    {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α]
    {U : Set α} (hU : IsOpen U) {x : α} (hx : x ∈ U) :
    frontier (connectedComponentIn U x) ⊆ frontier U := by
  intro z hz
  have hcomponentOpen : IsOpen (connectedComponentIn U x) :=
    hU.connectedComponentIn
  rw [frontier, hcomponentOpen.interior_eq, mem_diff] at hz
  rw [frontier, mem_diff]
  refine ⟨closure_mono (connectedComponentIn_subset U x) hz.1, ?_⟩
  rw [hU.interior_eq]
  intro hzU
  have hclosed :
      IsClosed (U ↓∩ connectedComponentIn U x) := by
    rw [connectedComponentIn_eq_image hx]
    simpa only [Set.preimage_image_eq _ Subtype.val_injective]
      using (isClosed_connectedComponent :
        IsClosed (connectedComponent (⟨x, hx⟩ : U)))
  have hrelative :
      U ∩ closure (U ∩ connectedComponentIn U x) ⊆
        connectedComponentIn U x :=
    isClosed_preimage_val.mp hclosed
  exact hz.2 (hrelative ⟨hzU, by
    simpa only [inter_eq_right.mpr (connectedComponentIn_subset U x)] using hz.1⟩)

/-- The complement of a polynomial lemniscate has at most `natDegree p + 1`
connected components.

The remaining frontier is the global polynomial-topology assembly:

* every sublevel component is bounded and, by the minimum-modulus argument,
  contains a root of `p`;
* every superlevel component is unbounded, by the maximum-modulus argument;
* polynomial growth puts the complement of a sufficiently large ball inside
  the superlevel, so all its unbounded components meet the same connected
  exterior region.

`frontier_connectedComponentIn_subset_frontier` supplies the previously
missing ambient-frontier fact.  What remains is to formalize the last two
bullets and the injection of sublevel components into the distinct roots. -/
theorem connectedComponents_complement_lemniscate_le
    (p : ℂ[X]) :
    Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1 := by
  sorry

end ConstructionTargets.LemniscateComponents
