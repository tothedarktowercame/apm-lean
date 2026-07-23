<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t95J01: A closed surjection with compact fibers carries Hausdorff upstairs to Hausdorff downstairs

## Why It's Hard

We must separate two *points* `y_1\ne y_2` of `Y`, but the Hausdorff hypothesis only gives separation in `X`.
The bridge is to separate the **fibers** `\pi^{-1}(y_1)` and `\pi^{-1}(y_2)` upstairs and then *push the
separation down*. Each hypothesis is needed and plays a distinct role, and orchestrating them is the
challenge:

- The fibers are **disjoint** (a map sends each point to one value) and **compact**, sitting inside the
  **Hausdorff** `X` — so they can be separated by disjoint open sets `U,V` in `X` (the compact-Hausdorff
  separation lemma).
- But disjoint opens *upstairs* are not yet neighborhoods *downstairs*. Converting "the fiber is inside `U`"
  into "a whole neighborhood `W\ni y` pulls back into `U`" is the **closed-map tube lemma**, and this is
  exactly where the **closed** hypothesis bites.
- **Surjectivity** is what makes the two downstairs neighborhoods disjoint: a common point `y\in W_1\cap W_2`
  would have a (nonempty) fiber forced into both `U` and `V`, contradiction.

The trap is trying to separate `y_1,y_2` directly; one must go up to the compact fibers, separate there, and
come back down through the closed map.

## The Key Insight

For `y_1\ne y_2`, the fibers `A=\pi^{-1}(y_1)`, `B=\pi^{-1}(y_2)` are disjoint compact subsets of the
Hausdorff `X`, so there are disjoint open `U\supseteq A`, `V\supseteq B`. By the **closed-map tube lemma**
(`\pi` closed, `\pi^{-1}(y_i)\subseteq` open `\Rightarrow` an open neighborhood pulls back inside it), get
open `W_1\ni y_1`, `W_2\ni y_2` with `\pi^{-1}(W_1)\subseteq U`, `\pi^{-1}(W_2)\subseteq V`. These are
**disjoint**: any `y\in W_1\cap W_2` has a point `x\in\pi^{-1}(y)` (surjectivity) lying in
`\pi^{-1}(W_1)\cap\pi^{-1}(W_2)\subseteq U\cap V=\varnothing`. So `Y` is Hausdorff.

## Complete Proof

Let `\pi:X\to Y` be a continuous surjection with each fiber `\pi^{-1}(y)` compact and `\pi` a closed map, and
suppose `X` is Hausdorff. Fix two distinct points `y_1\ne y_2` in `Y`; we find disjoint open neighborhoods.

### Two lemmas

**Lemma 1 (separating disjoint compacts in a Hausdorff space).** *If `A,B` are disjoint compact subsets of a
Hausdorff space `X`, there exist disjoint open `U\supseteq A`, `V\supseteq B`.*

*Proof.* First separate a point from a compact set: for fixed `a\in A` and each `b\in B`, Hausdorffness gives
disjoint opens `P_b\ni a`, `Q_b\ni b`; the `\{Q_b\}` cover the compact `B`, so finitely many `Q_{b_1},\dots,
Q_{b_k}` do, and `U_a:=\bigcap_j P_{b_j}\ni a` is disjoint from `W_a:=\bigcup_j Q_{b_j}\supseteq B`. Now the
`\{U_a\}_{a\in A}` cover the compact `A`, so finitely many `U_{a_1},\dots,U_{a_m}` do; put `U:=\bigcup_i
U_{a_i}\supseteq A` and `V:=\bigcap_i W_{a_i}\supseteq B`. Then `U\cap V=\varnothing` (each `U_{a_i}` misses
`W_{a_i}\supseteq V`). ∎

**Lemma 2 (closed-map tube lemma).** *If `\pi` is closed and `\pi^{-1}(y)\subseteq U` with `U` open in `X`,
then there is an open `W\ni y` in `Y` with `\pi^{-1}(W)\subseteq U`.*

*Proof.* `X\setminus U` is closed, so `\pi(X\setminus U)` is closed in `Y` (`\pi` is a closed map). Moreover
`y\notin\pi(X\setminus U)`: if `y=\pi(x)` with `x\in X\setminus U`, then `x\in\pi^{-1}(y)\subseteq U`,
contradicting `x\notin U`. Hence `W:=Y\setminus\pi(X\setminus U)` is open and contains `y`. Finally
`\pi^{-1}(W)\subseteq U`: if `\pi(x)\in W`, then `\pi(x)\notin\pi(X\setminus U)`, so `x\notin X\setminus U`,
i.e. `x\in U`. ∎

### Separating `y_1` and `y_2`

**Up: separate the fibers.** Let `A=\pi^{-1}(y_1)` and `B=\pi^{-1}(y_2)`. These are **compact** (by
hypothesis) and **disjoint**: if `x\in A\cap B`, then `\pi(x)=y_1` and `\pi(x)=y_2`, forcing `y_1=y_2`, a
contradiction. Since `X` is **Hausdorff**, Lemma 1 gives disjoint open sets
$$
U\supseteq A=\pi^{-1}(y_1), \qquad V\supseteq B=\pi^{-1}(y_2), \qquad U\cap V=\varnothing .
$$

**Down: pull back to neighborhoods of `y_1,y_2`.** Apply Lemma 2 twice (using that `\pi` is **closed**): there
are open sets
$$
W_1\ni y_1 \text{ with } \pi^{-1}(W_1)\subseteq U, \qquad W_2\ni y_2 \text{ with } \pi^{-1}(W_2)\subseteq V .
$$

**`W_1` and `W_2` are disjoint.** Suppose `y\in W_1\cap W_2`. Since `\pi` is **surjective**, the fiber
`\pi^{-1}(y)` is nonempty; choose `x\in\pi^{-1}(y)`. Then `\pi(x)=y\in W_1`, so `x\in\pi^{-1}(W_1)\subseteq
U`, and likewise `x\in\pi^{-1}(W_2)\subseteq V`. Thus `x\in U\cap V=\varnothing` — impossible. Hence
`W_1\cap W_2=\varnothing`.

Therefore `W_1\ni y_1` and `W_2\ni y_2` are disjoint open neighborhoods. As `y_1\ne y_2` were arbitrary, `Y`
is **Hausdorff**. ∎

**Remark.** A continuous closed surjection with compact fibers is a **perfect map**, and this result —
*perfect images of Hausdorff spaces are Hausdorff* — is the companion to "perfect preimages of compact spaces
are compact." Both proofs share the same machine: replace the relevant point of `Y` by its compact fiber,
work upstairs where the structure (Hausdorffness here, an open cover there) lives, and transport the
conclusion back down through the **closed-map tube lemma**, which is precisely the tool a closed map provides
that a merely continuous one does not. The compactness of fibers is what lets Lemma 1 apply (it separates
*compact* sets, not arbitrary ones), and surjectivity is what keeps fibers nonempty so the contradiction at
the end goes through. Together these say perfect maps are "proper-like" and preserve good separation and
covering properties in both directions.
