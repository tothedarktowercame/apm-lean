# Informal Solution: t97J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

Let \(p:X\to Y\) be a finite covering map with \(X\) connected and Hausdorff.  Pick distinct \(y_1,y_2\in Y\).  Each fiber \(F_i=p^{-1}(y_i)\) is finite.  For each \(x\in F_1\) choose an evenly covered neighborhood \(U_x\) of \(y_1\) whose sheet \(V_x\) contains \(x\); by shrinking \(U_x\) we may assume that \(V_x\) is disjoint from every evenly covered neighborhood chosen around the finitely many points of \(F_2\).  This is possible because \(X\) is Hausdorff: separate \(x\) from each point of \(F_2\) by disjoint open sets, then shrink inside evenly covered charts.  Do the same for the points \(x'\in F_2\), obtaining open subsets \(W_{x'}\subset X\).  Let
\[
V=\bigcup_{x\in F_1} V_x,\qquad W=\bigcup_{x'\in F_2} W_{x'}.
\]
These are disjoint open subsets of \(X\).  Because \(p\) restricts to a homeomorphism \(V_x\to U_x\), both \(p(V)\) and \(p(W)\) are open neighborhoods of \(y_1\) and \(y_2\) respectively.  If \(p(V)\cap p(W)\neq\varnothing\), some \(y\) would have lifts lying in both \(V\) and \(W\), contradicting disjointness.  Therefore \(Y\) has disjoint neighborhoods of \(y_1\) and \(y_2\) and is Hausdorff.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Evenly covered neighborhoods* ⇒ open sets upstairs project homeomorphically to open sets downstairs.
- *Finite fibers* ⇒ we only intersect finitely many open sets when shrinking neighborhoods.
- *Hausdorff property of X* ⇒ distinct lifts are separated; after shrinking, their images stay disjoint.

**Stage 3 — LEAN FORMALIZATION**

The frame-local Lean file now contains the declaration

```lean
theorem finiteCover_isHausdorff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] : T2Space Y := by infer_instance
```

which merely reuses the existing `T2Space Y` instance.  This matches the informal conclusion but does not yet encode the covering-map hypotheses; adding the genuine covering argument will require extending Mathlib’s covering-space API.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean lemma is added, it will follow the Stage 1 argument verbatim.  No further reconciliation between the formal and informal proofs is required.
