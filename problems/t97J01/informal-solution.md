<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97J01: A finite covering with Hausdorff total space has Hausdorff base

## Why It's Hard

The hypothesis is about the **total space** `X` (or, as we'll see, must be), while the conclusion is about the
**base** `Y` — and a covering map `p : X \to Y` goes the "wrong way" for transferring a separation property:
`p` collapses `X` down onto `Y`, so a priori two un-separable points of `Y` could be hiding behind perfectly
separated points of `X`. One has to **push the Hausdorff separation in `X` downward through `p`**, and the only
tools are that `p` is a local homeomorphism (hence **open**) and surjective. The real subtlety — and the reason
the word **finite** is in the problem — is that a covering map is in general **not closed and not proper**; an
*infinite*-sheeted covering with Hausdorff total space can have a non-Hausdorff base. Finiteness is exactly
what licenses the two moves the proof needs: separating a *finite* fiber inside Hausdorff `X`, and intersecting
*finitely many* open images to produce an open neighborhood downstairs.

> **Note on the statement.** As literally written ("`X, Y` connected, `X` a finite cover of `Y` `\Rightarrow Y`
> Hausdorff") the claim is **false**: the identity map is a `1`-sheeted covering, so it would assert that *every*
> connected space is Hausdorff. The intended — and true — statement carries the standard hypothesis that the
> **total space `X` is Hausdorff**. We prove that version: *if `p : X \to Y` is a finite-sheeted covering map,
> `Y` is connected, and `X` is Hausdorff, then `Y` is Hausdorff.*

## The Key Insight

Covering maps are **open** and (over a connected base) **surjective**. To separate `y_1 \ne y_2` in `Y`:

1. Their fibers `p^{-1}(y_1), p^{-1}(y_2)` are **finite** and disjoint, hence two disjoint finite sets in the
   Hausdorff space `X` — so they sit inside disjoint open sets `A \supseteq p^{-1}(y_1)`, `B \supseteq p^{-1}(y_2)`.
2. Push down through the finitely many sheets: shrinking each evenly-covered slice into `A` (resp. `B`) and
   taking the **finite** intersection of its open image gives open neighborhoods `U_1 \ni y_1`, `U_2 \ni y_2`
   over which *every* sheet lands in `A` (resp. `B`).
3. If some `y \in U_1 \cap U_2` existed, then over `U_1` all of `p^{-1}(y)` lies in `A`, and over `U_2` all of
   it lies in `B`; so `p^{-1}(y) \subseteq A \cap B = \varnothing`. But `p` is surjective, so `p^{-1}(y) \ne \varnothing`
   — contradiction. Hence `U_1 \cap U_2 = \varnothing`.

Finiteness is used twice — separating the finite fiber, and the *finite* intersection in step 2 (an infinite
intersection of opens need not be open, which is precisely how infinite covers escape this argument).

## Complete Proof

Let `p : X \to Y` be a covering map with **finitely many sheets**, `Y` connected, and `X` Hausdorff.

**Preliminaries.** A covering map is a local homeomorphism, hence an **open map**. Its image `p(X)` is open
(open map) and closed (the complement is a union of evenly-covered neighborhoods missing the image) and
nonempty, so by connectedness of `Y`, `p` is **surjective**. Because `Y` is connected, the number of sheets is
a constant `n < \infty`: every fiber `p^{-1}(y)` has exactly `n` points, and every point of `Y` has an
**evenly-covered** open neighborhood `U` with `p^{-1}(U) = \bigsqcup_{i=1}^{n} V_i`, each `V_i` mapped
homeomorphically onto `U` by `p`.

Fix `y_1 \ne y_2` in `Y`; we produce disjoint open neighborhoods.

**Step 1 — Separate the finite fibers in `X`.** The fibers `F_1 = p^{-1}(y_1)` and `F_2 = p^{-1}(y_2)` are
finite (each `n` points) and disjoint (since `y_1 \ne y_2`). In a Hausdorff space, two disjoint finite sets can
be enclosed in disjoint open sets: for each pair `(a, b) \in F_1 \times F_2` pick disjoint opens
`a \in O_{ab}`, `b \in O'_{ab}`; then

$$A = \bigcup_{a \in F_1} \Big( \bigcap_{b \in F_2} O_{ab}\Big) \supseteq F_1, \qquad B = \bigcup_{b \in F_2} \Big( \bigcap_{a \in F_1} O'_{ab}\Big) \supseteq F_2$$

are open with `A \cap B = \varnothing` (all intersections are finite, hence open). So `A, B` are **disjoint
open** sets with `F_1 \subseteq A`, `F_2 \subseteq B`.

**Step 2 — Descend to open neighborhoods of `y_1, y_2`.** Take an evenly-covered neighborhood `U` of `y_1`,
with sheets `V_1, \dots, V_n` over the points of `F_1` (`a_i \in V_i`). Since `a_i \in A` and `V_i \cap A` is
open, its image `p(V_i \cap A)` is open (p open) and contains `y_1`. Define

$$U_1 \;=\; \bigcap_{i=1}^{n} p(V_i \cap A),$$

a **finite** intersection of open neighborhoods of `y_1`, hence an open neighborhood of `y_1`. By construction,
for every `y \in U_1` and every sheet `V_i`, the unique preimage of `y` in `V_i` lies in `A`; and since
`U_1 \subseteq U` is evenly covered, these are *all* of `p^{-1}(y)`. Therefore

$$y \in U_1 \;\Longrightarrow\; p^{-1}(y) \subseteq A.$$

Symmetrically, build an open neighborhood `U_2` of `y_2` with `y \in U_2 \Rightarrow p^{-1}(y) \subseteq B`.

**Step 3 — The neighborhoods are disjoint.** Suppose `y \in U_1 \cap U_2`. Then `p^{-1}(y) \subseteq A` (from
`U_1`) and `p^{-1}(y) \subseteq B` (from `U_2`), so `p^{-1}(y) \subseteq A \cap B = \varnothing`. But `p` is
surjective, so `p^{-1}(y) \ne \varnothing` — a contradiction. Hence

$$U_1 \cap U_2 = \varnothing.$$

`U_1, U_2` are thus disjoint open neighborhoods of `y_1, y_2`. As `y_1 \ne y_2` were arbitrary,

$$\boxed{\ Y \text{ is Hausdorff.}\ } \qquad \blacksquare$$

**Remark (why finiteness is essential).** Both uses of finiteness are load-bearing. Step 1 separates a finite
fiber; an infinite fiber in a Hausdorff space need not lie in an open set disjoint from another. Step 2 takes a
*finite* intersection `\bigcap_{i=1}^n p(V_i \cap A)` to keep `U_1` open; with infinitely many sheets this
intersection can fail to be open, and the conclusion genuinely breaks. The classic cautionary example is the
**line with two origins** `Y` (glue two copies of `\mathbb R` along `\mathbb R \setminus \{0\}`): it is
connected, locally Euclidean, `T_1`, but **not** Hausdorff — the two origins cannot be separated — yet it is
locally modeled on the Hausdorff line. A finite covering can never produce such a defect, because the finite
fiber over a "bad" pair would already have to be un-separable upstairs, contradicting Hausdorffness of `X`.
(Equivalently: a finite covering map is **closed and proper**, and a proper map to a locally compact-ish base
transports Hausdorffness — the open-map argument above is the elementary form of that fact.)
