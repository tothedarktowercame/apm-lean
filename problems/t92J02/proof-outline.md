# Proof Outline: t92J02

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't92J02
 :frame-id 'apm-v2-t92J02-1775008678104
 :goal "Prove (a) continuous images of compact spaces are compact, and (b) a continuous bijection from a compact space onto a Hausdorff space is a homeomorphism."
 :terms [{:name "compactness via open covers"
          :meaning "Every open cover of a compact space admits a finite subcover."
          :needed-because "Part (a) is proved by pulling back an open cover of f(X) to one of X and applying compactness."}
         {:name "compact sets are closed in Hausdorff spaces"
          :meaning "In Hausdorff spaces, compact subsets are closed."
          :needed-because "In (b) we show f is a closed map by sending compact subsets (which stay compact) to closed subsets of Y."}
         {:name "bijective closed map = homeomorphism"
          :meaning "A continuous bijection that is either open or closed has a continuous inverse."
          :needed-because "Once f is proven closed, we can conclude it is a homeomorphism."}]
 :strategy [{:id :s1
             :formal-dependency "compactness lemmas, closed-image property in Hausdorff spaces"
             :informal-dependency "Stage 1 (a): take an open cover of f(X), pull back to X, use compactness to extract finite subcover, push forward again. Stage 1 (b): any compact subset K⊆X maps to compact f(K), hence closed in Y; thus f is a closed bijection between compact and Hausdorff spaces, so its inverse is continuous."
             :why-this-now "Follows the standard proofs and matches mathlib’s `IsCompact.image` and `IsClosedMap.of_compact` lemmas."
             :lean-target "ApmCanaries.Frames.T92J02.Apm_v2_t92J02_1775008678104.image_compact_and_homeo"
             :mathlib-status "mathlib already has `IsCompact.image` and `IsClosed.compact` and the homeomorphism criteria; we’ll restate them in this frame."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't92J02'
  :frame-id 'apm-v2-t92J02-1775008678104'
  :summary "Created isolated proof frame workspace with plan/alignment scaffolding."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full reader-facing solution (why hard, key insight, proof, connections) for both (a) and (b) in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Captured the dependency graph linking IsCompact.image, compact→closed, and the closed-bijection argument."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented `image_of_compact_isCompact` and `homeomorph_of_compact_to_T2` in Main.lean and ran `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Synced the informal write-up with the Lean argument, emphasizing the `g ⁻¹' C = f '' C` observation."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.**  Compactness arguments force you to manipulate entire open covers, but part (a) only gives a cover of the image, not the preimage.  Part (b) then layers Hausdorff separation on top of that: you must remember that “compact in Hausdorff implies closed” in order to convert the surjective map into a homeomorphism.  Many prelim solutions either try to push compactness forward directly (which fails) or forget to prove the inverse is continuous.

**Key insight.**  Pull every open cover of the target back to the source, use compactness of the source to get a finite subcover, and then push those finitely many sets forward again.  In the Hausdorff setting this shows the map is closed; a continuous bijection that is also closed automatically has a continuous inverse, hence is a homeomorphism.

**Complete proof.**
(a) Let `f : X → Y` be continuous and let `K ⊆ X` be compact.  Take an open cover `{V_i}` of `f(K)`.  For each `i`, the preimage `f⁻¹(V_i)` is open in `X`, and the sets `{f⁻¹(V_i) ∩ K}` cover `K`.  Compactness provides finitely many indices `i₁,…,i_m` whose preimages still cover `K`.  Apply `f` to each set: `{V_{i_j}}_{j=1}^m` is a finite subcover of `f(K)`, so `f(K)` is compact.
(b) Now let `f : X → Y` be continuous, bijective, with `X` compact and `Y` Hausdorff.  If `C ⊆ X` is closed, then `C` is compact, so by (a) `f(C)` is compact; in a Hausdorff space every compact set is closed, so `f` is a closed map.  A bijective closed map has a closed inverse-image operator: for every closed `C ⊆ X`, `f(C)` is closed in `Y`, hence the inverse `f^{-1}` pulls closed sets back to closed sets.  Consequently `f^{-1}` is continuous and `f` is a homeomorphism.

**What connects.**  This is the standard toolkit for topological conjugacy problems: “continuous bijection + compact domain + Hausdorff codomain” appears in spectral theory, manifold theory, and any time you glue spaces using quotient maps.  The closed-map trick is the same one used to show proper maps between Hausdorff spaces are closed.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Compactness via covers → part (a).**  Uses the definition of compactness (finite subcovers) together with functoriality of preimages under continuous maps (`IsCompact.image`).
- **Compact subset of Hausdorff is closed.**  Needed to turn the finite-subcover result into the statement “`f` is closed”.
- **Closed bijection ⇒ homeomorphism.**  Once `f` is closed, the inverse map preserves closed sets, so the inverse is continuous and gives a homeomorphism.  Mathlib lemmas `IsCompact.image` and `IsClosed.isCompact` feed directly into this closed-map argument.

**Stage 3 — LEAN FORMALIZATION**

- Added `image_of_compact_isCompact` and `homeomorph_of_compact_to_T2` in `ApmCanaries/Frames/T92J02/Apm_v2_t92J02_1775008678104/Main.lean`.  The first is a thin wrapper around `IsCompact.image`.  The second equips `X` with the compact structure coming from `IsCompact univ`, proves `f` is a closed map by reusing part (a), identifies the inverse’s closed preimages, and packages everything into a `Homeomorph`.
- Ran `lake build` from `/home/joe/code/apm-lean`; it completed successfully (global warnings are pre-existing files noted in the log).  No `sorry` remain in the frame-local files.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof forced an explicit expression for the inverse’s preimage of a closed set (`g ⁻¹' C = f '' C`), which sharpens the informal argument: once you see that equality, continuity of the inverse is immediate.  That perspective is now reflected in Stage 1’s explanation of why closed maps give homeomorphisms.
