# Proof Outline: t97J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that the base space of a finite covering map is Hausdorff."
 :terms [{:name "covering map"
          :meaning "surjective local homeomorphism with discrete fibers"
          :needed-because "gives evenly covered neighborhoods used to push separation downstairs"}
         {:name "finite fiber"
          :meaning "the preimage of each point contains finitely many sheets"
          :needed-because "allows us to intersect finitely many evenly covered neighborhoods"}
         {:name "Hausdorff separation upstairs"
          :meaning "distinct lifts in X admit disjoint neighborhoods"
          :needed-because "their images define disjoint neighborhoods in Y"}]
 :strategy [{:id :s1
             :formal-dependency "definition of covering map"
             :informal-dependency "Stage 1 selection of evenly covered neighborhoods"
             :why-this-now "Need to shrink around each lift before intersecting"
             :lean-target "exists_evenly_covered_subset"
             :mathlib-status "missing (no covering map API)"}
            {:id :s2
             :formal-dependency "finite intersections"
             :informal-dependency "Stage 1 finite fiber argument"
             :why-this-now "Intersect the finitely many neighborhoods"
             :lean-target "finite_cover_preimage_subset"
             :mathlib-status "blocked by s1"}
            {:id :s3
             :formal-dependency "Hausdorff transfer lemma"
             :informal-dependency "Stage 1 final separation"
             :why-this-now "Push the disjoint preimages down to Y"
             :lean-target "finite_cover_isHausdorff"
             :mathlib-status "blocked by s1"}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't97J01'
  :frame-id 'apm-v2-t97J01-1774999080822'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full reader-facing solution (why hard, key insight, proof, Lean obstacles, connections) into execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the target theorem, key terms, and dependency strategy in proof-plan.edn and aligned it with formal-alignment.edn including the HtDP sanity check."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Formal work blocked: Mathlib lacks any covering-map API (`IsCoveringMap`, finite-fiber helpers), so the Lean theorem `finite_cover_isHausdorff` cannot yet be stated."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

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
