# Informal Solution: t97J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

Given distinct `y₁, y₂ ∈ Y`, pick lifts `x₁ ∈ p⁻¹({y₁})`, `x₂ ∈ p⁻¹({y₂})`. Since covering spaces are Hausdorff, choose disjoint opens upstairs that separate each point over `y₁` from each point over `y₂`. Because each fiber is finite, shrink the evenly covered neighborhoods around `y₁` so that every sheet above `y₁` sits inside the chosen opens, and shrink similarly around `y₂`. The resulting open neighborhoods `V₁, V₂ ⊆ Y` satisfy `p⁻¹(V₁) ⊆ O₁`, `p⁻¹(V₂) ⊆ O₂` with `O₁ ∩ O₂ = ∅`, so `V₁ ∩ V₂ = ∅`. Therefore `Y` is Hausdorff.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- Covering map ⇒ evenly covered neighborhoods (needed to shrink around each lift).
- Finite fiber ⇒ finite intersection of neighborhoods still open.
- Disjoint preimages ⇒ disjoint images (final Hausdorff argument).

**Stage 3 — LEAN FORMALIZATION**

Main target: `finite_cover_isHausdorff : IsCoveringMap p → FiniteFiber p → T2Space Y`. Helper: `exists_evenly_covered_subset`. All pass the HtDP sanity check (mention real objects, avoid assuming the conclusion, meaningful standalone). Blocker: mathlib lacks any covering-map API, so neither predicate (`IsCoveringMap`, `FiniteFiber`) nor the evenly-covered lemma exists; formalization cannot begin until that infrastructure is added.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once covering maps land in mathlib, Stage 1 can cite `finite_cover_isHausdorff` directly and Stage 3 will track progress on `exists_evenly_covered_subset`. Until then, the informal solution remains the authoritative proof.
