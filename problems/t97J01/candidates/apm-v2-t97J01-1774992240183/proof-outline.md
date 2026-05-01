# Proof Outline: t97J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Given a finite covering map p : X → Y with X connected (and Hausdorff, as every covering space is), prove that Y is Hausdorff."
 :terms [{:name "evenly covered neighborhoods"
          :meaning "open sets U⊂Y whose preimage splits into finitely many sheets each mapped homeomorphically to U"
          :needed-because "They let us push disjoint neighborhoods of fiber points in X down to neighborhoods in Y."}
         {:name "finite fiber"
          :meaning "p^{-1}(y) has finitely many points"
          :needed-because "We can separate all fiber points simultaneously by intersecting finitely many open sets."}
         {:name "Hausdorff separation lifts"
          :meaning "X being Hausdorff allows disjoint open neighborhoods around any two distinct lifts"
          :needed-because "We build disjoint open sets above y₁ and y₂ and then project them to Y."}]
 :strategy [{:id :s1
             :formal-dependency "Covering map definition, Hausdorff property on X, finite fibers"
             :informal-dependency "Pick disjoint evenly covered neighborhoods around each lift of y₁ and y₂, then push them forward"
             :why-this-now "Finite many lifts ensure the 'shrink and intersect' process terminates and yields disjoint open sets in Y."
             :lean-target "A theorem stating: if p : X → Y is a finite covering map with X Hausdorff, then Y Hausdorff."
             :mathlib-status "Mathlib already has covering maps and Hausdorff spaces, but the finite-cover ⇒ Hausdorff lemma is missing and would need to be added."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :pending :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.T97J01.Apm_v2_t97J01_1774992240183'
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't97J01'
  :frame-id 'apm-v2-t97J01-1774992240183'
  :summary "Created the isolated frame with the standard plan/changelog structure."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the covering-space proof: separate each lift of y₁ from each lift of y₂ inside the Hausdorff space X, then push those disjoint neighborhoods down using evenly covered charts."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage2-completed
  :summary "Logged the dependency plan: finite fibers + evenly covered neighborhoods + Hausdorff separation in X ⇒ Hausdorff base."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :stage3-progress
  :summary "Noted that Main.lean is still empty; the future Lean task is to formalize `hausdorff_of_finite_cover` using Mathlib's covering-space API."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

Let \(p:X\to Y\) be a finite covering with \(X\) connected.  Covering spaces are Hausdorff and every fiber \(p^{-1}(y)\) is finite.  Take distinct \(y_1,y_2\in Y\).  For each \(x\in p^{-1}(y_1)\) choose an evenly covered neighborhood \(U_x\) of \(y_1\) small enough that its sheet \(V_x\subset X\) containing \(x\) is disjoint from every sheet \(W_{x'}\) chosen for points \(x'\in p^{-1}(y_2)\); this is possible because there are only finitely many lifts and \(X\) is Hausdorff, so we shrink neighborhoods and intersect finitely many conditions.  Let
\[
N=\bigcup_{x\in p^{-1}(y_1)} V_x,\qquad M=\bigcup_{x'\in p^{-1}(y_2)} W_{x'}.
\]
Each inclusion \(V_x\hookrightarrow N\) and \(W_{x'}\hookrightarrow M\) is open, the sets \(N\) and \(M\) are disjoint, and by the “evenly covered” condition \(p\) restricts to a homeomorphism from \(V_x\) onto the same open subset \(U_x\subset Y\).  Therefore \(p(N)\) and \(p(M)\) are open neighborhoods of \(y_1\) and \(y_2\) (they are the common images of the \(V_x\)'s and \(W_{x'}\)'s) and, because \(N\cap M=\varnothing\), their images are disjoint.  Hence \(Y\) is Hausdorff.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

*Formal ingredients.*  (i) Finite covering ⇒ every fiber is finite and evenly covered neighborhoods exist.  (ii) Hausdorff X ⇒ disjoint open neighborhoods of finitely many points can be chosen simultaneously.  (iii) Local homeomorphism ⇒ the image of each evenly covered sheet is open and the restriction of \(p\) is a homeomorphism there.  Together these give disjoint open neighborhoods of \(y_1\) and \(y_2\).

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` has not been populated yet.  The Lean task is to prove a lemma along the lines of:
```lean
lemma hausdorff_of_finite_cover
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [HausdorffSpace X] [ConnectedSpace X]
    (p : CoveringSpace Y X) (hp : p.fiber_card_finite) :
    HausdorffSpace Y := ...
```
Mathlib already knows about covering spaces and evenly covered neighborhoods, but it does not yet expose the “finite cover ⇒ Hausdorff base” lemma, so that needs to be implemented from scratch.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean lemma above is proved the formal and informal arguments will coincide: pick evenly covered neighborhoods, separate the finitely many lifts in `X`, and push them down.  Until the `hausdorff_of_finite_cover` lemma exists, the informal proof above is the authoritative one.
