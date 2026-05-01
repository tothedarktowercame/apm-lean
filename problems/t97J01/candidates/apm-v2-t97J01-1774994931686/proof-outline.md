# Proof Outline: t97J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't97J01
 :frame-id 'apm-v2-t97J01-1774994931686
 :goal "Show that finite covering maps force the base to be Hausdorff."
 :terms [{:name "evenly covered neighborhood"
          :meaning "open set whose preimage is disjoint union of sheets mapping homeomorphically"
          :needed-because "lets us control the entire fiber simultaneously"}
         {:name "finite fiber"
          :meaning "only finitely many sheets lie over each point"
          :needed-because "allows intersections over finitely many lifts"}
         {:name "Hausdorff separation upstairs"
          :meaning "distinct lifts can be separated in X"
          :needed-because "feeds the push-down separation argument"}]
 :strategy [{:id :s1
             :formal-dependency "covering map definition"
             :informal-dependency "Stage 1 neighborhoods"
             :why-this-now "Need evenly covered neighborhoods for each lift"
             :lean-target "exists_evenlyCovered_subsets"
             :mathlib-status "missing (no covering-map API)"}
            {:id :s2
             :formal-dependency "finite fibers"
             :informal-dependency "intersection trick"
             :why-this-now "Shrink simultaneously around all lifts"
             :lean-target "finite_intersection_evenlyCovered"
             :mathlib-status "blocked by s1"}
            {:id :s3
             :formal-dependency "Hausdorff property transfers"
             :informal-dependency "final separation argument"
             :why-this-now "Push disjoint preimage data down to Y"
             :lean-target "finiteCover_hausdorff"
             :mathlib-status "blocked by s1/s2"}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.T97J01.Apm_v2_t97J01_1774994931686
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :summary "Opened t97J01 frame and noted finite-cover strategy."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Recorded the classical proof separating fibers and pushing neighborhoods down."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Listed the evenly-covered, finite-fiber, and push-down lemmas in the plan."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Lean work blocked: mathlib currently lacks an `IsCoveringMap` API; need that infrastructure before stating `finiteCover_hausdorff`."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

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
