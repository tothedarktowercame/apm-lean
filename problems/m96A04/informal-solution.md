<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96A04: An adjoint pairing forces linearity and continuity (Hellinger–Toeplitz)

## Why It's Hard

Almost nothing is assumed: `A` is merely *linear* (not continuous), and `B` is *just a map* (not even
assumed linear). The only thing tying them together is the single inner-product identity
`\langle Ax, y\rangle = \langle x, By\rangle` for all `x, y`. From this one relation we must manufacture
three increasingly strong conclusions — `B` linear, `B` continuous, `A` continuous — pulling structure out
of essentially nothing.

The surprise is part (b)/(c): operators that are merely linear can be wildly discontinuous (unbounded
operators are everywhere in analysis), so "continuity for free" should feel suspicious. The reason it
works is the **Hellinger–Toeplitz phenomenon**: an everywhere-defined operator that possesses an
everywhere-defined formal adjoint *cannot* be unbounded. The mechanism is the **closed graph theorem** —
the inner-product pairing is exactly rigid enough to force the graph of `B` (and of `A`) to be closed, and
on a Hilbert space a linear map with closed graph is automatically bounded.

## The Key Insight

Everything flows from "test against all `x`, then specialize." The identity `\langle x, By\rangle = \langle Ax, y\rangle`
determines `By` uniquely (an element of a Hilbert space is pinned down by its inner products with
everything), and that uniqueness:

- **(a)** forces `B(y_1+y_2) = By_1 + By_2` and `B(\lambda y) = \lambda By`, because both sides have the
  *same* pairing with every `x` — so their difference is orthogonal to all of `X`, hence zero;
- **(b)** makes the graph of `B` closed: if `y_n \to y` and `By_n \to z`, then for all `x`,
  `\langle x, z\rangle = \lim\langle x, By_n\rangle = \lim\langle Ax, y_n\rangle = \langle Ax, y\rangle = \langle x, By\rangle`,
  so `z = By`. Closed graph theorem `\Rightarrow` `B` bounded;
- **(c)** the relation says precisely `A = B^*` (the Hilbert-space adjoint of the now-bounded `B`), and
  adjoints of bounded operators are bounded, so `A` is continuous.

## Complete Proof

Let `X` be a Hilbert space, `A : X \to X` linear, and `B : X \to X` a map with

$$\langle Ax, y\rangle = \langle x, By\rangle \qquad \text{for all } x, y \in X. \tag{$\ast$}$$

We use repeatedly that a vector `w \in X` is zero iff `\langle x, w\rangle = 0` for all `x` (take `x = w`).

### (a) `B` is linear

*Additivity.* For all `x` and all `y_1, y_2`, by `(\ast)` and linearity of `A` and of the inner product
in its slots,

$$\langle x, B(y_1+y_2)\rangle = \langle Ax, y_1+y_2\rangle = \langle Ax, y_1\rangle + \langle Ax, y_2\rangle
= \langle x, By_1\rangle + \langle x, By_2\rangle = \langle x, By_1 + By_2\rangle.$$

Hence `\langle x,\, B(y_1+y_2) - By_1 - By_2\rangle = 0` for every `x`, so `B(y_1+y_2) = By_1 + By_2`.

*Homogeneity.* For a scalar `\lambda`, `\langle x, B(\lambda y)\rangle = \langle Ax, \lambda y\rangle
= \bar\lambda\langle Ax, y\rangle = \bar\lambda\langle x, By\rangle = \langle x, \lambda By\rangle` for all
`x`, so `B(\lambda y) = \lambda By`. Therefore `B` is **linear**. ∎

### (b) `B` is continuous

`B` is linear (part a) and `X` is a Hilbert (hence Banach) space, so by the **closed graph theorem** it
suffices to show the graph of `B` is closed: if `y_n \to y` and `By_n \to z`, then `By = z`. For every
`x \in X`, using continuity of the inner product and then `(\ast)`,

$$\langle x, z\rangle = \lim_n \langle x, By_n\rangle = \lim_n \langle Ax, y_n\rangle = \langle Ax, y\rangle = \langle x, By\rangle,$$

where `\langle Ax, y_n\rangle \to \langle Ax, y\rangle` because `y_n \to y`. Thus
`\langle x, z - By\rangle = 0` for all `x`, so `z = By`. The graph is closed, and the closed graph theorem
gives that `B` is **bounded** (continuous). ∎

### (c) `A` is continuous

Now `B` is a bounded linear operator, so its Hilbert-space adjoint `B^*` exists and is bounded, with
`\langle x, By\rangle = \langle B^*x, y\rangle` for all `x, y`. Comparing with `(\ast)`,

$$\langle Ax, y\rangle = \langle x, By\rangle = \langle B^*x, y\rangle \qquad \text{for all } y,$$

so `\langle Ax - B^*x, y\rangle = 0` for every `y`, giving `Ax = B^*x` for all `x`. Hence

$$\boxed{\ A = B^*,\ }$$

the adjoint of the bounded operator `B`. Since `\|B^*\| = \|B\| < \infty`, `A = B^*` is **bounded**, i.e.
continuous. ∎

**Remark.** This is the **Hellinger–Toeplitz theorem** in disguise: an everywhere-defined linear operator
`A` that admits an everywhere-defined "adjoint" `B` (via `\langle Ax,y\rangle = \langle x,By\rangle`) is
automatically bounded — there are no everywhere-defined unbounded self-adjoint-type operators on a Hilbert
space. The engine is the closed graph theorem: the inner-product pairing forces graphs to be closed, and
closedness plus everywhere-definedness equals boundedness. (Unbounded symmetric operators in quantum
mechanics evade this only by being defined on *dense proper* subspaces, not on all of `X`.) An alternative
route to (c) repeats the part-(b) argument with the roles of `A` and `B` swapped: `A` linear with the same
pairing has closed graph, hence is continuous.
