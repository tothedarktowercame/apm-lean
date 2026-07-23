<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97A07: The critical values of a map from a compact manifold form a nonempty compact set, infinite when n > 1

## Why It's Hard

The set of critical values `I` is `f(C)` for `C` the critical points, and the two parts probe it from
different angles:

- **(a)** *Compactness* is routine (critical points are a closed, hence compact, subset; their image is
  compact). *Nonemptiness* is the surprise: why must a smooth map from a compact manifold have **any**
  critical value? The reason is global — a map with no critical values would be a **submersion everywhere**,
  hence an **open map**, making `f(X)` an open *and* compact (closed, bounded) subset of the connected
  `\mathbb R^n`, forcing `f(X)=\mathbb R^n` — impossible for a bounded set.
- **(b)** Jumping from "nonempty" to "infinite" (for `n>1`, `f` nonconstant) is a *connectivity* argument,
  and the hint is the heart of it: **attained regular values form a clopen piece of `\mathbb R^n\setminus I`**
  (open because submersions are open maps; closed because `f(X)` is closed), so if any exist they
  **disconnect** `\mathbb R^n\setminus I`. A *finite* `I` would leave `\mathbb R^n\setminus I` connected
  (removing finitely many points from `\mathbb R^n`, `n\ge2`) — contradiction. The degenerate case (no
  attained regular value, so `I=f(X)`) is handled separately: a nonconstant map on a connected `X` has
  infinite image.

The dimension hypothesis `n>1` is essential — for `n=1`, `\mathbb R\setminus(\text{finite})` is already
disconnected, and finite critical-value sets genuinely occur (Morse functions).

## The Key Insight

`I=f(C)`, `C=\{x:df_x\text{ not surjective}\}`.

- **(a)** `C` is closed (rank drops are a closed condition), so compact, so `I=f(C)` is compact. If `I=
  \varnothing`, every point is regular, `f` is a submersion / open map, and `f(X)` is a nonempty clopen
  bounded subset of `\mathbb R^n` — impossible. So `I\ne\varnothing`.
- **(b)** Either `f(X)` contains a regular value or not.
  - *If it does:* `\mathbb R^n\setminus I=(f(X)\setminus I)\sqcup(\mathbb R^n\setminus f(X))` is a separation
    (both parts open and nonempty), so `\mathbb R^n\setminus I` is disconnected; a finite `I` (with `n\ge2`)
    would make it connected — so `I` is infinite.
  - *If not:* `I=f(X)`, and a nonconstant map on connected `X` has infinite image.

## Complete Proof

Let `X` be a nonempty compact connected smooth manifold, `m=\dim X`, and `f:X\to\mathbb R^n` smooth. Recall
`y` is a **critical value** if some `x\in f^{-1}(y)` has `df_x:T_xX\to\mathbb R^n` *not* surjective; let
`C=\{x\in X:df_x\text{ not surjective}\}` be the critical points, so `I=f(C)` and `I\subseteq f(X)`.

### (a) `I` is compact and nonempty

**Compact.** Surjectivity of `df_x` means `\operatorname{rank}(df_x)=n`. The set `\{x:\operatorname{rank}(df_x)
\ge n\}` is open (having a nonvanishing `n\times n` minor of the Jacobian is an open condition), so its
complement `C=\{x:\operatorname{rank}(df_x)<n\}` is **closed** in `X`. As `X` is compact, `C` is compact, and
`I=f(C)` is the continuous image of a compact set, hence **compact**.

**Nonempty.** Suppose `I=\varnothing`. Then `f` has no critical values, so for every `x\in X` the value `f(x)`
is regular and therefore `x` is a regular point: `df_x` is surjective for all `x`. Thus `f` is a **submersion**
everywhere, hence an **open map** (submersions are open). Then `f(X)` is **open** in `\mathbb R^n`. But `f(X)`
is also the continuous image of the compact `X`, hence **compact**, so closed and bounded. Since `\mathbb
R^n` is connected and `f(X)` is a nonempty subset that is both open and closed, `f(X)=\mathbb R^n` — impossible,
as `f(X)` is bounded. This contradiction shows `I\ne\varnothing`. ∎

### (b) For `n>1` and `f` nonconstant, `I` is infinite

We split on whether `f(X)` contains a regular value.

**Case B: `f(X)` contains no regular value.** Then every attained value is critical, i.e. `f(X)\subseteq I`;
combined with `I\subseteq f(X)`, this gives `I=f(X)`. Since `X` is connected and `f` is continuous, `f(X)` is
connected; since `f` is **nonconstant**, `f(X)` has at least two points. A connected subset of `\mathbb R^n`
with more than one point is infinite (it contains a nondegenerate continuum). Hence `I=f(X)` is **infinite**.

**Case A: `f(X)` contains a regular value `y_0`.** We show `\mathbb R^n\setminus I` is disconnected. Let
`R:=\mathbb R^n\setminus I` (open, as `I` is closed). Split
$$
R = \underbrace{(f(X)\setminus I)}_{=\,R\cap f(X)} \ \sqcup\ \underbrace{(\mathbb R^n\setminus f(X))}_{\subseteq\, R}
$$
(disjoint: one set lies in `f(X)`, the other in its complement; and `\mathbb R^n\setminus f(X)\subseteq R`
because `I\subseteq f(X)`). We check both pieces are nonempty and open:

- `\mathbb R^n\setminus f(X)` is **open** (`f(X)` is compact, hence closed) and **nonempty** (`f(X)` is
  bounded, so `\ne\mathbb R^n`).
- `f(X)\setminus I=R\cap f(X)` is **nonempty** (it contains `y_0`, the attained regular value). It is **open**:
  let `y\in f(X)\setminus I`. Being a regular value, `y` has a regular preimage `x` with `df_x` surjective, so
  `f` is a submersion near `x`, hence an open map there; thus `f` carries a neighborhood of `x` onto an open
  neighborhood `V\ni y` contained in `f(X)`. Then `V\cap R` is an open subset of `\mathbb R^n` with `y\in V\cap
  R\subseteq f(X)\cap R`. So `f(X)\setminus I` is open.

Thus `R=\mathbb R^n\setminus I` is the disjoint union of two nonempty open sets — a **separation** — so
`\mathbb R^n\setminus I` is **disconnected**.

Now suppose, for contradiction, that `I` is *finite*. Since `n>1`, removing a finite set of points from
`\mathbb R^n` leaves it **connected** (any two points are joined by a path that detours around the finitely
many removed points, possible in dimension `\ge2`). So `\mathbb R^n\setminus I` would be connected,
contradicting the disconnection just established. Therefore `I` is **infinite**.

In both cases `I` is infinite. ∎

**Remark.** Part (a)'s nonemptiness is "compactness forbids a global submersion to `\mathbb R^n`": an
everywhere-submersion has open image, but a compact image is closed and bounded, and the only clopen subsets
of `\mathbb R^n` are `\varnothing` and `\mathbb R^n`. Part (b) upgrades this using the *open-mapping* property
of regular points one more time: attained regular values are interior to `f(X)`, so they form a piece of
`\mathbb R^n\setminus I` that is *separated* from the exterior `\mathbb R^n\setminus f(X)` — the critical
values `I` must "wall off" the image from its complement, and a finite wall cannot separate `\mathbb R^n`
when `n\ge2`. (For `n=1` the conclusion is false: a height/Morse function on a circle has just two critical
values.) The result is a soft cousin of Sard's theorem — Sard says `I` is *small* (measure zero), while this
says `I` is nonetheless *topologically large enough* to disconnect the complement of the image, hence
infinite, whenever the image genuinely sits inside `\mathbb R^n` with regular values on its boundary.
