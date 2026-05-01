# Informal Solution: t94A04

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Claim.** If X = U ∪ V with U, V open, path-connected, and simply connected, and U ∩ V is nonempty and path-connected, then X is simply connected.

**Proof (without van Kampen).**

*Step 0: X is path-connected.* Fix x ∈ U ∩ V (nonempty by hypothesis). Any y ∈ X lies in U or V. If y ∈ U: path from x to y inside U (U path-connected). If y ∈ V: same. So X is path-connected.

*Step 1: Subdivide the loop.* Let α : [0,1] → X be a loop based at x. The preimages α⁻¹(U) and α⁻¹(V) are open (α continuous, U and V open) and cover [0,1]. By the Lebesgue number lemma ([0,1] is compact), there exists δ > 0 such that every interval of length < δ maps entirely into U or entirely into V. Choose a subdivision 0 = t₀ < t₁ < ... < tₙ = 1 with each tₖ - tₖ₋₁ < δ. Then each piece αₖ = α|[tₖ₋₁,tₖ] (reparametrized to [0,1]) has image in U or in V.

*Step 2: Insert connecting paths.* Each subdivision point α(tₖ) lies in U or V (or both). Since U ∩ V is path-connected and x ∈ U ∩ V, for each k = 1,...,n-1 choose a path γₖ from x to α(tₖ) such that:
- If α(tₖ) ∈ U: γₖ lies in U (possible since U is path-connected and x ∈ U)
- If α(tₖ) ∈ V: γₖ lies in V
- If α(tₖ) ∈ U ∩ V: γₖ lies in U ∩ V (possible since U ∩ V path-connected)

The key subtlety: if αₖ lies in U and αₖ₊₁ lies in V, then α(tₖ) ∈ U ∩ V, so the connecting path γₖ can be chosen in U ∩ V (which lies in both U and V). This ensures the concatenation αₖ · γₖ⁻¹ stays within U, and γₖ · αₖ₊₁ stays within V.

*Step 3: Factor the loop.* We have:
α ∼ α₁ · α₂ · ... · αₙ (homotopic by reparametrization).

Insert γₖ · γₖ⁻¹ = id between each pair:
α ∼ (α₁ · γ₁⁻¹) · (γ₁ · α₂ · γ₂⁻¹) · ... · (γₙ₋₁ · αₙ).

*Step 4: Each factor is a null-homotopic loop.* Each factor like γₖ₋₁ · αₖ · γₖ⁻¹ is:
- A loop based at x (starts at x via γₖ₋₁, ends at x via γₖ⁻¹)
- Contained entirely in U or entirely in V (by construction of γₖ and the subdivision)

Since U and V are simply connected, each such loop is null-homotopic within U (or V), hence within X.

*Step 5: Conclude.* α is homotopic to a product of null-homotopic loops, hence null-homotopic. Since α was arbitrary, π₁(X, x) = 0. Combined with path-connectedness (Step 0), X is simply connected. ∎

(The crux: the Lebesgue number gives the subdivision, the path-connectedness of U ∩ V provides the connecting paths that STAY in the right set, and simple connectivity of U and V kills each factor. The argument fails without path-connectedness of U ∩ V — without it, you can't connect subdivision points back to x within a single set.)

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Source | Critical? |
|---|-------|--------|-----------|
| 1 | Lebesgue number for [0,1] with open cover | Mathlib: `IsCompact.exists_forall_ge_of_forall_le` or Lebesgue number | YES |
| 2 | Loop subdivision into pieces in U or V | Custom from (1) | YES |
| 3 | Connecting paths γₖ in the right set | IsPathConnected (U ∩ V) + path-connectedness of U, V | YES |
| 4 | Each factor is a loop in U or V | Construction from (2) + (3) | YES |
| 5 | Simply connected ⟹ loop null-homotopic | SimplyConnectedSpace definition | YES |
| 6 | Product of null-homotopic = null-homotopic | Path.Homotopy.trans | YES |

**Stage 3 — LEAN FORMALIZATION**

The theorem `SimplyConnectedSpace X` from the hypotheses is NOT in Mathlib. The proof requires ~80 lines: Lebesgue number subdivision, connecting path construction, loop factoring, and homotopy composition. Each step has partial Mathlib support (Path, Path.Homotopy, IsPathConnected) but the composition is entirely custom.

See Main.lean for the statement.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The proof is conceptually clean (5 steps) but technically involved. The hardest step for students is Step 2: choosing connecting paths γₖ that stay in the right set. The path-connectedness of U ∩ V is used ONLY here — it ensures that when a subdivision point lies in U ∩ V (which happens at every U-to-V transition), the connecting path can be chosen in the intersection.

In Lean, the hardest part would be the loop factoring (Step 3): showing that inserting γₖ · γₖ⁻¹ pairs preserves the homotopy class. Mathlib has `Path.Homotopy.trans` for concatenation but the insertion-of-identity-pairs step needs `Path.Homotopy.symm_trans` or similar.
