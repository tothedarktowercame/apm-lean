<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97J06: A degree-zero torus map that is still not null-homotopic

## Why It's Hard

The map `f(x,y) = (\sin(2\pi x + 4\pi y),\ x+y)` on `T^2 = \mathbb R^2/\mathbb Z^2` is built to bait two
opposite mistakes. The `\sin` in the first coordinate *looks* like it might wind around the circle — but
`\sin` is **bounded**, so as a map to `\mathbb R/\mathbb Z` it lifts to the honest real function
`\sin(2\pi x + 4\pi y) : T^2 \to \mathbb R`, hence is **null-homotopic** (zero winding). That makes the degree
`0`. The second trap is then to conclude `f` is homotopic to a constant *because* its degree is `0`. For torus
self-maps that inference is **false**: degree is only the top-dimensional (`H_2`) datum — the *determinant* of
the action on `H_1` — and it is blind to the rank-`1` part. The honest work is to see that the single matrix
`f_* = \begin{pmatrix}0&0\\1&1\end{pmatrix}` on `H_1(T^2)` has determinant `0` (answering (a)) but is **nonzero**
(answering (b)), because the second coordinate `x+y` collapses the torus onto a circle without dying.

## The Key Insight

For a torus self-map, **degree `= \det` of the induced map on `H_1(T^2) = \mathbb Z^2`**, and a map to `S^1`
that *lifts to `\mathbb R`* is null-homotopic. The first coordinate `\sin(2\pi x + 4\pi y) \bmod 1` lifts to
`\mathbb R`, so it contributes nothing; the second coordinate `x+y \bmod 1` sends each generating loop once
around `S^1`. Therefore `f` is homotopic to

$$g(x,y) = (0,\ x+y), \qquad f_* = \begin{pmatrix} 0 & 0 \\ 1 & 1 \end{pmatrix} \ \text{on } H_1(T^2),\quad g_*(\alpha) = g_*(\beta) = \beta.$$

- **(a)** `\deg f = \det f_* = 0` — equivalently, `g` maps onto the circle `\{0\}\times S^1`, missing an open
  set, so it cannot have nonzero degree.
- **(b)** `f_* \ne 0` (it sends the `x`-loop `\alpha` to `\beta \ne 0`), whereas any **constant** map induces
  the **zero** map on `H_1`. Since homotopic maps induce equal maps on homology, `f` is **not** homotopic to a
  constant.

## Complete Proof

Write `f = (f_1, f_2) : T^2 \to S^1 \times S^1 = T^2`, with `f_1(x,y) = \sin(2\pi x + 4\pi y) \bmod 1` and
`f_2(x,y) = (x+y) \bmod 1`. Let `\alpha, \beta` be the standard generators of `H_1(T^2) = \mathbb Z^2` (the
`x`- and `y`-loops).

### The first coordinate is null-homotopic

The real function `s(x,y) = \sin(2\pi x + 4\pi y)` is well-defined and continuous on `T^2` (it is unchanged
under `(x,y) \mapsto (x+n, y+m)`), and `f_1 = \pi \circ s` where `\pi : \mathbb R \to \mathbb R/\mathbb Z = S^1`.
Thus `f_1` factors through the **contractible** universal cover `\mathbb R` of `S^1`, so

$$H_t(x,y) = \pi\big(t \cdot s(x,y)\big), \qquad t : 1 \to 0,$$

is a homotopy (well-defined on `T^2` for every `t`, since `s` is) from `f_1` to the constant map `0`. Hence the
first coordinate has **winding number `0`** around the circle; geometrically, `\sin` only oscillates in
`[-1,1]` and never accumulates net angle.

### `f` is homotopic to `g(x,y) = (0,\, x+y)`

Carrying the homotopy `H_t` in the first slot while fixing the second,
`F_t(x,y) = (\pi(t\,s(x,y)),\ x+y)` is a homotopy from `f` (at `t=1`) to

$$g(x,y) = (0,\ x+y) \qquad (t = 0).$$

Degree and the induced map on homology are homotopy invariants, so it suffices to study `g`.

### Induced map on `H_1`

`g` sends the `x`-loop `\{(x,0) : x \in [0,1]\}` to `\{(0,x) : x\in[0,1]\}`, i.e. once around the second
circle: `g_*(\alpha) = \beta`. Likewise the `y`-loop maps to `\{(0,y)\}`, so `g_*(\beta) = \beta`. In the basis
`(\alpha, \beta)`,

$$f_* = g_* = \begin{pmatrix} 0 & 0 \\ 1 & 1 \end{pmatrix} \qquad (\text{columns } g_*\alpha = g_*\beta = \beta = (0,1)).$$

### (a) The degree

For a self-map of `T^2`, the action on `H_2(T^2) = \mathbb Z` is multiplication by the degree, and
`H_2(T^2) = \Lambda^2 H_1(T^2)`, so the degree equals `\det` of the `H_1`-matrix:

$$\boxed{\ \deg f = \det f_* = \det\begin{pmatrix}0&0\\1&1\end{pmatrix} = 0.\ }$$

(Geometric confirmation: `g(T^2) = \{0\} \times S^1` is a circle, a proper closed subset of `T^2`. A map
missing an open set is homotopic into that subset, hence factors through a `1`-complex, so it induces the zero
map on `H_2` — degree `0`.)

### (b) `f` is not homotopic to a constant

A **constant** map `c : T^2 \to T^2` factors through a point, so the induced map on first homology is zero:
`c_* = 0 : H_1(T^2) \to H_1(T^2)`. But

$$f_*(\alpha) = \beta = (0,1) \ne 0,$$

so `f_* \ne 0`. Homotopic maps induce **equal** homomorphisms on homology; if `f` were homotopic to a constant
we would have `f_* = c_* = 0`, a contradiction. Therefore

$$\boxed{\ f \text{ is not homotopic to any constant map.}\ } \qquad \blacksquare$$

(Equivalently, on `\pi_1`: the composite `\operatorname{pr}_2 \circ f : T^2 \to S^1`, `(x,y) \mapsto x+y`,
induces the **surjection** `\pi_1(T^2) = \mathbb Z^2 \to \mathbb Z`, `(m,n) \mapsto m+n`, which is nonzero,
while a constant map induces the trivial homomorphism. So `f_\# \ne 0` and `f` is not null-homotopic.)

**Remark.** The whole problem lives in the one matrix `f_* = \begin{pmatrix}0&0\\1&1\end{pmatrix}`. Its
`\det = 0` answers (a); its `\operatorname{rank} = 1 \ne 0` answers (b). The lesson is that **degree `0` does
not imply null-homotopic** for maps between spaces with `H_1 \ne 0`: degree only sees `\Lambda^{\text{top}}`,
i.e. the determinant, and is insensitive to a map that is "partially degenerate" — here `f` crushes the torus
onto a circle (killing `\det`) but still wraps that circle nontrivially (keeping `f_* \ne 0`). The `\sin` is a
deliberate red herring: any *bounded* expression in the circle coordinate lifts to `\mathbb R` and so winds
zero times.
