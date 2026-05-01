# Informal Solution: t97J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Problem note.** The statement as given omits the hypothesis that X is Hausdorff. Without it, the claim is false. We prove the standard theorem with X Hausdorff.

**Claim.** Let X, Y be connected topological spaces with X Hausdorff. Let p: X → Y be a finite covering map (surjective local homeomorphism with finite fibers). Then Y is Hausdorff.

**Proof.** Let y₁, y₂ ∈ Y with y₁ ≠ y₂. Write p⁻¹(y₁) = {x₁,...,xₘ} and p⁻¹(y₂) = {z₁,...,zₖ} (both finite and nonempty by surjectivity). Since y₁ ≠ y₂, these fibers are disjoint.

*Step 1 (Separate in X).* All xᵢ and zⱼ are distinct points in X Hausdorff. For each pair (xᵢ, zⱼ), separate by disjoint open sets. Also separate xᵢ from xᵢ' and zⱼ from zⱼ'. Take finite intersections to get: for each xᵢ, an open set Wᵢ ∋ xᵢ with all Wᵢ pairwise disjoint, all W'ⱼ pairwise disjoint, and each Wᵢ disjoint from each W'ⱼ. Shrink so p|_{Wᵢ} and p|_{W'ⱼ} are homeomorphisms.

*Step 2 (Push down).* p is an open map (local homeomorphism), so each p(Wᵢ) and p(W'ⱼ) is open. Set U = ∩ᵢ p(Wᵢ) (finite intersection of opens = open, contains y₁) and V = ∩ⱼ p(W'ⱼ) (open, contains y₂).

*Step 3 (Disjoint).* Shrink U further so that p⁻¹(U) ⊆ ∪ᵢ Wᵢ (possible because p is a local homeomorphism and the fibers near y₁ stay near {x₁,...,xₘ}). Similarly shrink V so p⁻¹(V) ⊆ ∪ⱼ W'ⱼ. Now if y ∈ U ∩ V, then p⁻¹(y) ⊆ ∪Wᵢ and p⁻¹(y) ⊆ ∪W'ⱼ, but these unions are disjoint — so p⁻¹(y) = ∅, contradicting surjectivity. Hence U ∩ V = ∅. ∎

(The crux: finite fibers let us do finite intersections upstairs, keeping everything open. The surjectivity of p means p⁻¹(y) ≠ ∅, which forces the disjointness contradiction.)

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Source | Critical? |
|---|-------|--------|-----------|
| 1 | T2 separation of fiber points | [T2Space X] | YES |
| 2 | Local homeomorphism → open map | IsLocalHomeomorph.isOpenMap | YES |
| 3 | Finite intersections of opens are open | Finset.isOpen_iInter | YES |
| 4 | Fiber containment in neighborhoods near a point | Finite covering → evenly covered | YES |
| 5 | Empty fiber contradicts surjectivity | Function.Surjective | YES |

**Stage 3 — LEAN FORMALIZATION**

See Main.lean. The statement uses IsLocalHomeomorph, T2Space, Function.Surjective, Set.Finite for fibers. The theorem "Hausdorff descends through finite covering maps" is not in Mathlib. The proof construction needs explicit separation of fiber points + finite intersection + open map push-down.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The proof is conceptually clear but the bookkeeping is heavy: you must explicitly construct m + k open sets upstairs, verify pairwise disjointness, push down, shrink to ensure fiber containment, and verify the contradiction. On paper this is a 10-line argument; in Lean it would be 50+ lines of set arithmetic. The key Lean tools would be `T2Space.exists_open_nhds_disjoint`, `IsLocalHomeomorph.isOpenMap`, and `Set.Finite.iInter`. The "evenly covered" property (fibers near a point stay in prescribed neighborhoods) is the main missing API — Mathlib has `IsEvenlyCovered` but it's not connected to `IsLocalHomeomorph` in the general finite-fiber case.
