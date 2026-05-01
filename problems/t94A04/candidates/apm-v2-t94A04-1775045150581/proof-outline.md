# Proof Outline: t94A04

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal
 "Prove: X = U ∪ V with U, V open simply connected, U ∩ V nonempty path-connected ⟹ X simply connected. Without van Kampen's theorem."
 :terms
 [{:name "simply connected"
   :meaning "path-connected and every loop is null-homotopic (π₁ = 0)"
   :needed-because "this is both the hypothesis on U,V and the conclusion for X"}
  {:name "Lebesgue number"
   :meaning "for an open cover of a compact metric space, ∃ δ > 0 such that every set of diameter < δ is contained in one cover element"
   :needed-because "subdivides any loop into pieces each lying in U or V"}
  {:name "path subdivision"
   :meaning "break a loop α into α₁·α₂·...·αₙ where each αₖ lies in U or V"
   :needed-because "reduces the problem to null-homotopy of pieces in simply connected subsets"}
  {:name "connecting paths"
   :meaning "paths γₖ in U ∩ V from basepoint x to subdivision points α(tₖ)"
   :needed-because "converts pieces into LOOPS in U or V (by prepending/appending γₖ)"}]
 :strategy
 [{:id :subdivide-loop
   :formal-dependency "Lebesgue number lemma for compact metric I = [0,1]"
   :informal-dependency "any loop in X can be subdivided so each piece lies in U or V"
   :why-this-now "this is the first step of the argument"
   :lean-target "∀ α : Path x x, ∃ subdivision with pieces in U or V"
   :mathlib-status "Mathlib has IsCompact.exists_forall_open_ball_subset (Lebesgue number); Path type exists"
   :critical-path true}
  {:id :insert-connecting-paths
   :formal-dependency "path-connectedness of U ∩ V + simply-connectedness of U and V"
   :informal-dependency "insert γₖ·γₖ⁻¹ pairs between pieces to create loops in U or V"
   :why-this-now "this converts path pieces into null-homotopic loops"
   :lean-target "each piece αₖ·γₖ⁻¹ is a loop in U or V, hence null-homotopic"
   :mathlib-status "Mathlib has Path.Homotopy, IsPathConnected; custom composition needed"
   :critical-path true}
  {:id :compose-homotopies
   :formal-dependency "concatenation of null-homotopic loops is null-homotopic"
   :informal-dependency "if each piece is null-homotopic, the whole loop is"
   :why-this-now "final assembly"
   :lean-target "α ≃ₕ const ⟵ each factor ≃ₕ const"
   :mathlib-status "Mathlib has Path.Homotopy.trans; composition is available"
   :critical-path true}]
 :stage-status
 {:stage1 :done
  :stage2 :done
  :stage3 :in-progress
  :stage4 :done}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id "t94A04"
  :frame-id "apm-v2-t94A04-1775045150581"
  :summary "Created isolated proof frame workspace."
  :full-record? false
  :sorry? false
  :fully-closed? false}
 {:kind :target-check
  :summary "Sanity check passed: mentions U,V (open sc), U∩V (nonempty pc), concludes SimplyConnectedSpace X. NOT in Mathlib. Needs Lebesgue number subdivision + connecting paths + homotopy composition."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Clean 5-step proof: (0) X path-connected, (1) Lebesgue number subdivides loop, (2) connecting paths from U∩V, (3) factor loop into pieces, (4) each piece null-homotopic in U or V, (5) product null-homotopic."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :lean-delta
  :summary "Main theorem statement type-checks with 1 sorry. The 'subdivide→insert→factor→kill' pipeline is ~80 lines of custom path manipulation, not in Mathlib."
  :full-record? true
  :sorry? true
  :fully-closed? false}
 {:kind :final-status
  :summary "Classification: partial. Informal proof complete (5 steps). Lean statement type-checks (1 sorry). The theorem is absent from Mathlib; the proof construction needs Lebesgue number + path algebra + homotopy composition — all available in pieces but not composed."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

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
