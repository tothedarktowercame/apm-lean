# Informal Solution: t97J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
