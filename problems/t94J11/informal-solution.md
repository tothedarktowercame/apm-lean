<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94J11: For an open equivalence relation, the relation is closed iff the quotient is Hausdorff

## Why It's Hard

The two conditions live in *different spaces*: `R=\{(x,y):x\sim y\}` is a subset of `X\times X`, while
"Hausdorff" is a property of the quotient `X/\!\sim`. Bridging them requires the right translation, and one
direction needs a hypothesis the other does not.

- The **bridge** is the identity `R=(\pi\times\pi)^{-1}(\Delta)`, where `\Delta` is the diagonal of
  `X/\!\sim`: a pair `(x,y)` is related iff `\pi(x)=\pi(y)` iff `(\pi(x),\pi(y))\in\Delta`. Combined with the
  standard fact **"a space is Hausdorff iff its diagonal is closed,"** the whole problem becomes a statement
  about whether closedness transfers between `\Delta` and its preimage `R`.
- **One direction is free** (continuity): if `X/\!\sim` is Hausdorff, `\Delta` is closed, so its preimage `R`
  under the continuous `\pi\times\pi` is closed — *no* openness needed.
- **The other direction genuinely needs `\sim` open.** From `R` closed one must produce *disjoint open
  neighborhoods* of two distinct classes, and the only way to manufacture open sets *in the quotient* is to
  take **images** `\pi(U),\pi(V)` of open sets in `X` — which are open **precisely because `\pi` is an open
  map**. Without openness, `R` closed need not force Hausdorff; this is exactly where the hypothesis bites.

## The Key Insight

Write `R=(\pi\times\pi)^{-1}(\Delta)` with `\Delta=\{([a],[a])\}\subseteq (X/\!\sim)^2`, and use *`Y` is
Hausdorff iff `\Delta_Y` is closed.*

- **Hausdorff `\Rightarrow` `R` closed:** `\pi\times\pi` is continuous, so `R=(\pi\times\pi)^{-1}(\Delta)` is
  the preimage of the closed `\Delta`, hence closed.
- **`R` closed `\Rightarrow` Hausdorff:** for distinct classes `[a]\ne[b]` (so `(a,b)\notin R`), the open
  complement of `R` contains a box `U\times V\ni(a,b)` with `(U\times V)\cap R=\varnothing`; then `\pi(U)\ni
  [a]` and `\pi(V)\ni[b]` are **open** (since `\pi` is open) and **disjoint** (a common point would give
  `x\in U`, `y\in V` with `x\sim y`, contradicting `(U\times V)\cap R=\varnothing`).

## Complete Proof

Let `\pi:X\to X/\!\sim` be the quotient projection, an **open** map (since `\sim` is an open relation), and
let `\Delta=\{([a],[a]):[a]\in X/\!\sim\}` be the diagonal in `(X/\!\sim)\times(X/\!\sim)`.

### The bridge identity

For `(x,y)\in X\times X`,
$$
(x,y)\in R \iff x\sim y \iff \pi(x)=\pi(y) \iff (\pi(x),\pi(y))\in\Delta \iff (x,y)\in(\pi\times\pi)^{-1}(\Delta),
$$
so
$$
R = (\pi\times\pi)^{-1}(\Delta).
$$

### Lemma (Hausdorff `\iff` diagonal closed)

> A space `Y` is Hausdorff iff `\Delta_Y=\{(y,y)\}` is closed in `Y\times Y`.

*Proof.* (`\Rightarrow`) If `Y` is Hausdorff and `(y,y')\notin\Delta_Y` (so `y\ne y'`), pick disjoint opens
`A\ni y`, `B\ni y'`; then `A\times B` is an open neighborhood of `(y,y')` with `(A\times B)\cap\Delta_Y=
\varnothing` (a point `(z,z)` there would give `z\in A\cap B=\varnothing`). So `Y^2\setminus\Delta_Y` is open,
`\Delta_Y` closed. (`\Leftarrow`) If `\Delta_Y` is closed and `y\ne y'`, then `(y,y')\in Y^2\setminus\Delta_Y`
open, so a basic box `A\times B\subseteq Y^2\setminus\Delta_Y` has `y\in A`, `y'\in B`, and `A\cap B=
\varnothing` (a common point `z` would put `(z,z)\in A\times B`, contradicting disjointness from `\Delta_Y`).
So `Y` is Hausdorff. ∎

### (⇐) If `X/\!\sim` is Hausdorff, then `R` is closed

Suppose `X/\!\sim` is Hausdorff. By the Lemma, `\Delta` is closed in `(X/\!\sim)^2`. The map
`\pi\times\pi:X\times X\to(X/\!\sim)^2` is continuous (a product of the continuous maps `\pi`). Hence
$$
R = (\pi\times\pi)^{-1}(\Delta)
$$
is the preimage of a closed set under a continuous map, so `R` is **closed** in `X\times X`. *(This direction
used only continuity of `\pi`, not openness.)*

### (⇒) If `R` is closed, then `X/\!\sim` is Hausdorff

Suppose `R` is closed, so `(X\times X)\setminus R` is open. Let `[a]\ne[b]` be two distinct points of
`X/\!\sim`; then `a\not\sim b`, i.e. `(a,b)\in (X\times X)\setminus R`. Since this set is open, there is a
**basic open box** `U\times V` with
$$
a\in U,\quad b\in V,\quad (U\times V)\cap R=\varnothing,
$$
where `U,V` are open in `X`. The last condition says: **no** `x\in U` is related to any `y\in V`.

Because `\pi` is an **open** map, the images
$$
\pi(U) \ni [a], \qquad \pi(V) \ni [b]
$$
are **open** in `X/\!\sim`. They are **disjoint**: if some class `[z]\in\pi(U)\cap\pi(V)`, then `[z]=\pi(x)`
for some `x\in U` and `[z]=\pi(y)` for some `y\in V`, so `\pi(x)=\pi(y)`, i.e. `x\sim y` with `x\in U`,
`y\in V` — contradicting `(U\times V)\cap R=\varnothing`. Hence `\pi(U)` and `\pi(V)` are disjoint open
neighborhoods of `[a]` and `[b]`. As `[a]\ne[b]` were arbitrary, `X/\!\sim` is **Hausdorff**. *(This direction
crucially used that `\pi` is open.)*

Combining the two implications, `R` is closed **iff** `X/\!\sim` is Hausdorff. ∎

**Remark.** The hypothesis "`\sim` open" is exactly what makes the equivalence work in *both* directions.
Unified: `\pi\times\pi` is continuous, surjective, and — since `\pi` is open, so is `\pi\times\pi`
(`(\pi\times\pi)(A\times B)=\pi(A)\times\pi(B)`) — therefore a **quotient map**. For a quotient map `q`, a
set `C` is closed iff `q^{-1}(C)` is closed; applying this to `q=\pi\times\pi` and `C=\Delta` gives
`\Delta\text{ closed}\iff R=(\pi\times\pi)^{-1}(\Delta)\text{ closed}`, which together with the Lemma is the
whole theorem in one line. Openness is essential because a product of mere quotient maps need *not* be a
quotient map, but a product of *open* surjections always is — so without it the implication "`R` closed
`\Rightarrow` Hausdorff" can fail.
