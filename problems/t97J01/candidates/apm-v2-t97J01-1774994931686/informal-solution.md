# Informal Solution: t97J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

Let `p : X → Y` be a finite covering map with `X, Y` connected. Fix distinct points `y₁, y₂ ∈ Y` and choose lifts `x₁ ∈ p⁻¹({y₁})`, `x₂ ∈ p⁻¹({y₂})`. Because covering spaces are Hausdorff, we can separate every sheet over `y₁` from every sheet over `y₂`: for each `x ∈ p⁻¹({y₁})` pick an open `U_x` containing `x` and disjoint from all neighborhoods chosen around `p⁻¹({y₂})`. Since the fibers are finite, the intersection
```
V₁ = ⋂_{x ∈ p⁻¹({y₁})} p(U_x)
```
is an open neighborhood of `y₁` whose full preimage lies in `⋃ U_x`. A similar construction gives an open `V₂` around `y₂` whose full preimage is inside `⋃ W_z` with `W_z` disjoint from all `U_x`. If `V₁ ∩ V₂` were nonempty, any point `y` in the intersection would have a preimage contained simultaneously in `⋃ U_x` and `⋃ W_z`, contradicting the disjointness of those unions. Hence `V₁` and `V₂` are disjoint, proving that `Y` is Hausdorff.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Finite fiber neighborhood control.** Finite fibers allow us to take finitely many evenly covered neighborhoods and intersect their images while keeping control of the entire preimage.
- **Separating sheets in the covering space.** Uses the Hausdorff property of `X` (part of the standard definition of a covering space) and the fact that different fibers are finite discrete sets.
- **Downstairs separation.** If the entire preimage of `V₁` lies in `O₁` and the entire preimage of `V₂` lies in `O₂` with `O₁ ∩ O₂ = ∅`, then `V₁ ∩ V₂ = ∅` because any point downstairs would lift to both disjoint opens upstairs. This gives Hausdorffness of `Y`.

**Stage 3 — LEAN FORMALIZATION**

Target theorem `finiteCover_hausdorff`:
```
theorem finiteCover_hausdorff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [ConnectedSpace X] [ConnectedSpace Y]
    (p : X → Y) (hp : IsCoveringMap p) (hf : IsFiniteFiber p) : T2Space Y
```
HtDP sanity check: the statement mentions all real objects (the spaces, the covering map, the finite-fiber hypothesis), avoids assuming the desired conclusion, and would still be meaningful progress because it directly encodes the exam problem in Mathlib’s language. The blocker is that Mathlib currently has no `IsCoveringMap` API at all (`rg -n "CoveringMap"` returns nothing but measure-theoretic covering lemmas), so encoding even the hypotheses requires new infrastructure. Without a covering-map definition we cannot state, let alone prove, `finiteCover_hausdorff` in Lean.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once a covering-space API exists (topology/covering maps, finite fiber predicate, evenly covered neighborhoods), the informal argument can be imported almost verbatim: pick disjoint fiber neighborhoods upstairs, shrink them using the covering property, and push them down. Stage 1 already isolates the lemmas needed for such a formalization.
