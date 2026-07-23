<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t95A05: Separating hypersurfaces, a Stokes-invariant residue, and finiteness of Lefschetz fixed points

## Why It's Hard

The three parts assemble the analytic toolkit for "counting around a set." (a) asks to *smoothly* separate
two disjoint closed sets by a hypersurface bounding a submanifold — this needs the topological separation
(Urysohn), then a smoothing, then a *regular value* (Sard) to make the level set a manifold. (b) defines a
number `N_\omega = \int_{\partial Y}\omega` and demands it be independent of the auxiliary `Y`; the obstacle
is that different `Y`'s have genuinely different boundaries, and the equality is forced only because the
*region between* two choices is a cobordism on which the closed form integrates to zero by Stokes — but one
must verify that region avoids `A \cup B` (where `\omega` is defined). (c) is the finiteness of fixed points
of a Lefschetz map: the nondegeneracy `+1 \notin \operatorname{spec} df_x` makes each fixed point *isolated*
(inverse function theorem), and compactness caps a discrete closed set at finitely many points. The recurring
theme: combine a smooth-topology input (Sard / IFT) with a global compactness or Stokes argument.

## The Key Insight

- **(a)** Urysohn gives continuous `f` with `f = -1` on `A`, `f = +1` on `B`; smooth-approximate it by `g`
  with `|g - f| < 1`, so `g < 0` on `A` and `g > 0` on `B`. A **regular value** `c \in (\max_A g, \min_B g)`
  (Sard) makes `Y = \{g \le c\}` a compact manifold-with-boundary `\partial Y = g^{-1}(c)` containing `A`, with
  `\partial Y` separating `A` from `B`.
- **(b)** Given two choices `Y_1, Y_2`, build a small `Y_3` near `A` with `A \subset \operatorname{int} Y_3 \subseteq Y_1 \cap Y_2`.
  The region `Z = Y_i \setminus \operatorname{int} Y_3` is a cobordism inside `X \setminus (A \cup B)` with
  `\partial Z = \partial Y_i - \partial Y_3`, so Stokes gives `0 = \int_Z d\omega = \int_{\partial Y_i}\omega - \int_{\partial Y_3}\omega`.
  Hence `N_\omega` is the same for all `Y`.
- **(c)** `+1 \notin \operatorname{spec}(df_x)` means `df_x - I` is invertible, so the displacement `g = f - \mathrm{id}`
  (in a chart) is a local diffeomorphism — each fixed point is **isolated**. `\operatorname{Fix}(f)` is closed in
  the compact `X`, hence compact; a discrete compact set is **finite**.

## Complete Proof

### (a) A separating submanifold-with-boundary

`X` is compact (so normal Hausdorff) and `A, B` are disjoint closed sets. By **Urysohn's lemma** there is a
continuous `f : X \to \mathbb R` with `f \equiv -1` on `A` and `f \equiv +1` on `B`. By the quoted smoothing
theorem, choose a smooth `g : X \to \mathbb R` with `|g - f| < 1` everywhere. Then on `A`, `g < f + 1 = 0`, and
on `B`, `g > f - 1 = 0`. Since `A, B` are compact, `\max_A g < 0 < \min_B g`.

By **Sard's theorem** the regular values of `g` are dense, so pick a regular value
`c \in (\max_A g, \min_B g)`. Set

$$Y = \{x \in X : g(x) \le c\}.$$

As `c` is a regular value, the level set `g^{-1}(c)` is a smooth `(n-1)`-submanifold and `Y` is a smooth
compact `n`-manifold-with-boundary `\partial Y = g^{-1}(c)` (`Y` is closed in compact `X`, hence compact).
Moreover `g < c` on `A` (so `A \subseteq \operatorname{int} Y`) and `g > c` on `B` (so `B \subseteq X \setminus Y`).
Finally `X \setminus \partial Y = \{g < c\} \sqcup \{g > c\}` is a disjoint union of open sets with
`A \subseteq \{g < c\}`, `B \subseteq \{g > c\}`: thus `\partial Y` **separates `A` and `B`**. ✓

### (b) `N_\omega` is independent of `Y`

`\omega` is a closed `(n-1)`-form on `X \setminus (A \cup B)`; for any admissible `Y` (from (a)),
`\partial Y \subseteq X \setminus (A \cup B)` (it avoids `A \subseteq \operatorname{int} Y` and
`B \subseteq X \setminus Y`), so `N_\omega(Y) = \int_{\partial Y}\omega` is defined.

Let `Y_1, Y_2` be two such choices. The set `U = \operatorname{int} Y_1 \cap \operatorname{int} Y_2` is an open
neighborhood of `A` (both contain `A` in their interior). Applying the construction of (a) to the disjoint
closed sets `A` and `X \setminus U`, obtain a compact submanifold-with-boundary `Y_3` with

$$A \subseteq \operatorname{int} Y_3 \subseteq U \subseteq \operatorname{int} Y_1 \cap \operatorname{int} Y_2,$$

so `Y_3 \subseteq Y_1` and `Y_3 \subseteq Y_2` (*"`Y` can be chosen in an arbitrarily small neighborhood of `A`"*).

Fix `i \in \{1,2\}`. Since `Y_3 \subseteq Y_i` with `A \subseteq \operatorname{int} Y_3`, the set

$$Z = Y_i \setminus \operatorname{int} Y_3$$

is a compact `n`-manifold-with-boundary with `\partial Z = \partial Y_i \ \sqcup\ (-\partial Y_3)` (outer
boundary `\partial Y_i` positively, inner boundary `\partial Y_3` with reversed orientation). Crucially
`Z \subseteq X \setminus (A \cup B)`: it avoids `A` (which lies in `\operatorname{int} Y_3`, removed) and avoids
`B` (which lies in `X \setminus Y_i`). So `\omega` is defined and **closed** on `Z`, and **Stokes** gives

$$0 = \int_Z d\omega = \int_{\partial Z}\omega = \int_{\partial Y_i}\omega - \int_{\partial Y_3}\omega.$$

Thus `N_\omega(Y_i) = N_\omega(Y_3)` for `i = 1, 2`, whence `N_\omega(Y_1) = N_\omega(Y_3) = N_\omega(Y_2)`.
So `N_\omega` is **independent of `Y`**. ✓

### (c) A Lefschetz map on a compact manifold has finitely many fixed points

**Each fixed point is isolated.** Let `x` be a fixed point with `+1 \notin \operatorname{spec}(df_x)`, i.e.
`\det(df_x - I) \ne 0`, so `df_x - I` is invertible. In a chart around `x` (sending `x \mapsto 0`, with the
local representative `F` of `f`), define `g(u) = F(u) - u`; its zeros are the fixed points near `x`, `g(0) = 0`,
and `dg_0 = df_x - I` is invertible. By the **inverse function theorem**, `g` is a local diffeomorphism near
`0`, hence injective there, so `0` is its only zero nearby: `x` is an **isolated** fixed point. (This is the
content of the displacement map having nonsingular derivative.)

**`\operatorname{Fix}(f)` is finite.** The fixed-point set `\operatorname{Fix}(f) = \{x : f(x) = x\}` is closed
in `X` (it is the equalizer of the continuous maps `f` and `\mathrm{id}` into the Hausdorff space `X`). A
closed subset of the compact `X` is compact. By the previous paragraph, every point of `\operatorname{Fix}(f)`
is isolated in `X`, hence isolated in `\operatorname{Fix}(f)`, so `\operatorname{Fix}(f)` is a **discrete**
space. A discrete compact space is finite: the isolating open neighborhoods form an open cover, a finite
subcover leaves only finitely many points. Therefore

$$\boxed{\ f \text{ has only finitely many fixed points.}\ }\qquad\blacksquare$$

**Remark.** The three parts share one design: a smooth-topology mechanism feeds a global theorem. In (a),
Sard turns a smoothed Urysohn function into an honest separating hypersurface. In (b), the `Y`-independence is
a *cobordism invariance*: `N_\omega` is a "topological residue" of the closed form `\omega` around `A`, and
Stokes annihilates the cobordism between any two choices (this is exactly how degree/linking numbers are shown
well-defined). In (c), the inverse function theorem (nondegeneracy `+1 \notin \operatorname{spec} df_x`) makes
fixed points isolated, and compactness — a discrete closed set in a compact space is finite — bounds their
number; this finiteness is precisely what lets the Lefschetz fixed-point theorem express `L(f)` as a finite
sum of local indices.
