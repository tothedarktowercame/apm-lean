<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97A05: A nonzero intersection number forces the complement of a hypersurface to be connected

## Why It's Hard

The statement yokes together two things that look unrelated at first: a **separation** property — the topology
of the complement `Y^{n+1}\setminus W^n` — and an **intersection number** `I(W^n, Z^k)`, an oriented algebraic
count taking place in the *larger* manifold `X^{n+k}`. There is no direct way to "see" the complement from the
intersection number. The bridge is a single structural principle of intersection theory: **a hypersurface that
separates must bound, and anything that bounds has intersection number zero with every closed complementary
cycle.** Two subtleties have to be handled cleanly. First, `W` is a hypersurface inside `Y`, but the
intersection number is computed in `X \supsetneq Y`; one must check that bounding *inside `Y`* still kills the
intersection number *in `X`* (the bounding manifold sits inside `Y \subseteq X`, so it works — but it must be
said). Second, "separates `\iff` bounds" for a connected hypersurface relies on **two-sidedness**, which here
comes for free because everything is oriented: the normal bundle of `W` in `Y` is an orientable line bundle,
hence trivial.

## The Key Insight

Argue the **contrapositive**, driven by the *boundary theorem* of oriented intersection theory:

> If a compact oriented `W` is the boundary of a compact oriented manifold `V` whose inclusion into `X` extends
> the inclusion of `W`, then `I(W, Z) = 0` for every closed `Z` of complementary dimension.

Now suppose `Y\setminus W` were **disconnected**. A connected, two-sided, closed hypersurface `W` in a
connected closed manifold `Y` cuts `Y` into at most two pieces; if it is disconnected there are exactly two,
`Y \setminus W = A \sqcup B`, and `V := \overline{A} = A \cup W` is a **compact oriented `(n+1)`-manifold with
`\partial V = W`** sitting inside `Y \subseteq X`. The boundary theorem then forces

$$I(W, Z) = I(\partial V, Z) = 0,$$

contradicting `I(W, Z) \ne 0`. Hence `Y \setminus W` cannot be disconnected. (Homological gloss: `I(W,Z)`
depends only on `[W] \in H_n(X)`; separation makes `[W] = 0` in `H_n(Y)`, hence `i_*[W] = 0` in `H_n(X)`, hence
`I(W,Z)=0`.)

## Complete Proof

Throughout, `Y^{n+1}` and `Z^k` are closed (compact, boundaryless) oriented submanifolds of the oriented
`X^{n+k}`, `W^n \subset Y^{n+1}` is a closed connected oriented submanifold, and `Y` is connected. Since
`\dim W + \dim Z = n + k = \dim X` and both are closed and oriented inside oriented `X`, the **oriented
intersection number** `I(W, Z) \in \mathbb Z` is defined.

Assume, for contradiction, that `Y \setminus W` is **disconnected**.

### Step 1 — `W` is two-sided in `Y`

`W^n` has codimension `1` in `Y^{n+1}`. Its normal bundle `\nu` is a real line bundle over `W`. From
`TY|_W = TW \oplus \nu` and the fact that both `Y` and `W` are oriented, `\nu` is an **orientable** line
bundle, hence **trivial**: `\nu \cong W \times \mathbb R`. By the tubular neighborhood theorem, `W` has a
neighborhood in `Y` diffeomorphic to the product

$$N \;\cong\; W \times (-1, 1), \qquad W \leftrightarrow W \times \{0\}.$$

So `W` is two-sided, and `N \setminus W = \big(W\times(0,1)\big) \sqcup \big(W\times(-1,0)\big)` has exactly two
pieces, each connected because `W` is connected.

### Step 2 — `Y \setminus W` has exactly two components

`Y \setminus W` is open. Every one of its components must contain points arbitrarily close to `W` (otherwise
that component would be a nonempty open-and-closed subset of the connected `Y`, forcing it to equal `Y`,
absurd). Hence every component meets the punctured tube `N \setminus W`, so it contains one of the two
connected halves `W\times(0,1)`, `W\times(-1,0)`. There are only two halves, so there are **at most two**
components; being disconnected, there are **exactly two**:

$$Y \setminus W = A \sqcup B, \qquad W\times(0,1) \subseteq A, \quad W\times(-1,0) \subseteq B.$$

### Step 3 — `W` bounds a compact oriented manifold inside `Y`

Set `V := \overline{A} = A \cup W` (the closure of `A` in `Y`). Near `W`, the collar `W \times [0,1)` from
Step 1 charts `V`, so `V` is a smooth **manifold with boundary**, with

$$\partial V = W.$$

`V` is **compact** (a closed subset of the compact `Y`) and **oriented** (it is the closure of the open subset
`A \subseteq Y`, inheriting `Y`'s orientation; `W` receives the induced boundary orientation). Crucially,
`V \subseteq Y \subseteq X`, so the inclusion `W \hookrightarrow X` **extends** to the smooth map
`V \hookrightarrow X`.

### Step 4 — The boundary theorem kills the intersection number

The boundary theorem of oriented intersection theory states: if a closed oriented manifold `W` of complementary
dimension to `Z` bounds a compact oriented `V` and the map `W \to X` extends over `V`, then `I(W, Z) = 0`.
(Reason: perturb so `Z` is transverse to the compact `V`; then `V \cap Z` is a compact oriented `1`-manifold
whose boundary is exactly the signed intersection `W \cap Z`. A compact oriented `1`-manifold has signed
boundary count zero, so the algebraic count `I(W, Z) = 0`.) Applying this to `V` from Step 3,

$$I(W, Z) \;=\; I(\partial V, Z) \;=\; 0.$$

### Step 5 — Contradiction

Step 4 gives `I(W, Z) = 0`, contradicting the hypothesis `I(W, Z) \ne 0`. Therefore the assumption fails:

$$\boxed{\ Y^{n+1} \setminus W^n \text{ is connected.}\ } \qquad \blacksquare$$

**Remark (homological viewpoint).** The intersection number is the value of the Poincaré pairing
`I(W, Z) = \langle [W], [Z]\rangle` and so depends only on the class `[W] \in H_n(X)`. Step 3 shows that if `W`
separated `Y`, then `[W] = \partial[V] = 0` already in `H_n(Y)`; pushing forward along the inclusion
`i : Y \hookrightarrow X`, `[W] = i_*0 = 0` in `H_n(X)`, whence `I(W, Z) = \langle 0, [Z]\rangle = 0`. The
contrapositive is the statement proved: `I(W, Z) \ne 0 \Rightarrow [W] \ne 0 \Rightarrow W` does not separate
`Y`. Orientation enters twice — to make `W` two-sided (so "separates `\iff` bounds" holds) and to make the
*signed* intersection number a homological invariant. (The same argument runs mod `2` with `I_2` and
`H_*(\,\cdot\,;\mathbb Z/2)` if one drops orientations but keeps two-sidedness.)
