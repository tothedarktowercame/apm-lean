# Proof Outline: t97J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Prove that if a connected Hausdorff space X covers Y by a finite-sheeted covering map, then Y is Hausdorff."
 :terms [{:name "covering map"
          :meaning "A surjective local homeomorphism with discrete fibres"
          :needed-because "Evenly covered neighbourhoods let us lift separation data from X to Y."}
         {:name "finite fibre"
          :meaning "Each point of Y has finitely many lifts"
          :needed-because "We can separate finitely many points in a Hausdorff space simultaneously."}
         {:name "evenly covered neighbourhood"
          :meaning "An open set whose preimage splits into disjoint opens mapped homeomorphically onto it"
          :needed-because "Provides the separating neighbourhoods downstairs once the components upstairs are disjoint."}]
 :strategy [{:id :s1
             :formal-dependency "Definition/lemmas about evenly covered neighbourhoods"
             :informal-dependency "Stage 1 step: for each y pick an evenly covered U"
             :why-this-now "Gives control of fibres via disjoint open slices over U."
             :lean-target "exists_evenly_covered_neighbourhood"
             :mathlib-status "To be provided once the covering-space API lands."}
            {:id :s2
             :formal-dependency "Finite set separation in Hausdorff spaces"
             :informal-dependency "Stage 1: separate all fibre points of y1 and y2"
             :why-this-now "Need pairwise disjoint opens above each fibre to descend to disjoint opens below."
             :lean-target "separate_finite_subset"
             :mathlib-status "Follows from T₂ + finiteness."}
            {:id :s3
             :formal-dependency "Push separation along local homeomorphisms"
             :informal-dependency "Stage 1: project disjoint opens to Y"
             :why-this-now "Maps each chosen slice homeomorphically onto the base neighbourhood, so disjointness survives."
             :lean-target "finite_cover_descends_Hausdorff"
             :mathlib-status "Main theorem."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't97J01'
  :frame-id 'apm-v2-t97J01-1775001167604'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full reader-facing solution: why-hard analysis, evenly covered strategy, complete proof, and connections."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Populated proof-plan.edn with goal, key terms, and strategy steps tied to covering-map lemmas."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-in-progress
  :summary "Documented intended Lean theorem and blockers (Mathlib lacks any IsCoveringMap/evenly covered API; see rg search in Stage 3)."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  “Finite cover” usually signals algebraic topology, but the statement only mentions Hausdorffness, so the intended move—pulling Hausdorff separation down the covering map—is easy to miss. Students either (i) forget that a covering map is a *local homeomorphism* and try to argue about global properties of \(p:X\to Y\), or (ii) manage to separate lifts of two points of \(Y\) but fail to intersect finitely many neighbourhoods simultaneously, losing the finiteness hypothesis. Another common trap is secretly assuming \(Y\) is already Hausdorff to use unique limits or diagonal arguments, which is exactly what needs to be proved.

***Key insight.***  Use evenly covered neighbourhoods. Given distinct \(y_1,y_2\in Y\), each has finitely many lifts in \(X\), and \(X\) is Hausdorff. Separate all those finitely many lifts by pairwise disjoint open sets in \(X\), push those opens down through the covering map, and intersect everything to obtain disjoint neighbourhoods of \(y_1\) and \(y_2\) inside \(Y\).

***Complete proof.***  Let \(p:X\to Y\) be a finite-sheeted covering, with \(X\) Hausdorff and connected. Fix \(y_1\neq y_2\) in \(Y\). Choose evenly covered open neighbourhoods \(U_i\ni y_i\) (existence follows from the covering-map definition). The preimage \(p^{-1}(y_i)\) is finite, so for every lift \(x\in p^{-1}(y_i)\) we may pick an evenly covered slice \(V_{i,x}\subseteq p^{-1}(U_i)\) containing \(x\) that maps homeomorphically onto \(U_i\); because the covering is finite-sheeted, only finitely many such slices occur. Since \(X\) is Hausdorff, we can shrink the finitely many \(V_{1,x}\) so that their union \(W_1\) is disjoint from the union \(W_2\) of the finitely many slices above \(y_2\). Each restriction \(p|_{V_{i,x}}:V_{i,x}\to U_i\) is a homeomorphism, hence open. Therefore \(U_i=p(V_{i,x})\) and the images of the disjoint unions remain disjoint: set \(N_i=p(W_i)\subseteq U_i\). The sets \(N_1\) and \(N_2\) are open, contain \(y_1\) and \(y_2\) respectively, and are disjoint. Thus \(Y\) is Hausdorff.

***What connects.***  The argument is the same “finite slicing” trick used in algebraic topology to show that finite covering projections preserve compactness, and it is analogous to the measure-theory principle “almost everywhere injectivity + finite fibres force separation.”  On exams this sits next to problems about local homeomorphisms, deck transformations, and lifting properties.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Evenly covered neighbourhoods exist.*  Inputs: definition of covering map.  Output: for each \(y\) an open \(U\) splitting \(p^{-1}(U)\) into disjoint opens mapped homeomorphically onto \(U\).  Lean target: `exists_evenly_covered_neighborhood`.
- *Finite Hausdorff separation upstairs.*  Inputs: Hausdorffness of \(X\) and finiteness of the fibre.  Statement: finitely many points in a Hausdorff space admit pairwise disjoint open neighbourhoods.  Lean target: `pairwise_disjoint_neighborhoods_of_finite`.
- *Push-down of disjoint opens.*  Inputs: local homeomorphism on each slice.  Statement: if \(U,V\subseteq X\) are unions of slices mapping homeomorphically onto the same base neighbourhoods, then their images remain disjoint.  Lean target: `disjoint_of_homeomorphic_slices`.
- *Main theorem.*  Combine the previous lemmas to produce disjoint neighbourhoods around arbitrary \(y_1\neq y_2\in Y\).  Lean target: `finite_cover_descends_Hausdorff`.

Machine-readable copies live in `proof-plan.edn` and `formal-alignment.edn`.

**Stage 3 — LEAN FORMALIZATION**

- *Type signature.*  Intended statement (from `formal-alignment.edn`):  
  `∀ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] (p : X → Y), IsCoveringMap p → (∀ y, (p ⁻¹' {y}).Finite) → Connected Y → T2Space Y`.
- *Search / inventory.*  `rg -n "CoveringMap" .` and `rg -n "IsCoveringMap" .` (run from `/home/joe/code`) returned no hits, confirming Mathlib currently lacks a covering-space API—there is nothing to import or instantiate.
- *Wiring attempt.*  I created the namespace skeleton in `Main.lean` but could not proceed: all lemmas listed in Stage 2 require a definition of covering map, evenly covered neighbourhoods, and finite-sheetedness. Without these primitives I cannot even state helper lemmas, let alone build tactic proofs. Any honest Lean development must first add a covering-map library (definitions, evenly-covered neighbourhood lemmas, finite-fibre helpers, etc.) to `Mathlib`.
- *Status.*  Blocked at the API level. Stage 3 remains “in-progress” pending the upstream addition of a covering-space framework.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the covering-map API exists, mirror the Stage 1 proof directly:  
1. Encode evenly covered neighbourhood selection.  
2. Formalize the finite Hausdorff separation lemma.  
3. Push the disjointness down via local homeomorphism restrictions.  
Until then, the informal proof stands as the authoritative reference, and the Lean goal is documented (with blockers) in Stage 3 for future completion.
