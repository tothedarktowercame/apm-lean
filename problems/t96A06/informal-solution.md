<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96A06: Complex squaring on RP³ — degree 4 and Lefschetz number −3

## Why It's Hard

The map `f(x,y,z,w) = (x^2-y^2, 2xy, z^2-w^2, 2zw)` looks like an unmotivated quartet of quadratics, and the
first hurdle is recognizing it as **complex squaring on each factor**: under `\mathbb R^4 \cong \mathbb C^2`
with `u = x+iy`, `v = z+iw`, it is `f(u,v) = (u^2, v^2)`. That identification powers everything. Part (a)
needs the map to descend to `\mathbb{RP}^3`, which requires homogeneity *and* that `f` has no zeros off the
origin (else the image line is undefined). Part (b) is a Lefschetz computation where the difficulty is
getting the **degree** of `\bar f` right; the slick route uses that a holomorphic map's topological degree
equals its *local multiplicity*, here `2 \cdot 2 = 4`. Part (c) then plays the degree (or the Lefschetz
number) against the identity. The complex structure is the thread: it makes `f` orientation-preserving and
pins the degree.

## The Key Insight

Write `\mathbb R^4 = \mathbb C^2`, `u = x+iy`, `v = z+iw`. Then `u^2 = (x^2-y^2) + i(2xy)` and `v^2 = (z^2-w^2) + i(2zw)`, so

$$f(u,v) = (u^2, v^2).$$

- **(a)** `f` is homogeneous of degree `2` (`f(ku,kv) = (k^2u^2, k^2v^2) = k^2 f(u,v)`), and `f(u,v) = 0 \iff u = v = 0`,
  i.e. `f^{-1}(0) = \{0\}`. So `f` sends each real line through `0` to a real line through `0`, inducing
  `\bar f : \mathbb{RP}^3 \to \mathbb{RP}^3`, `[x] \mapsto [f(x)]`.
- **(b)** `\mathbb{RP}^3` is a **rational homology `3`-sphere**: `H_*(\mathbb{RP}^3; \mathbb Q) = \mathbb Q`
  in degrees `0, 3` and `0` else (`H_1 = \mathbb Z/2` dies over `\mathbb Q`). So
  `L(\bar f) = 1 - \deg(\bar f)`. The holomorphic map `(u,v) \mapsto (u^2,v^2)` has isolated zero at `0` with
  local multiplicity `2 \cdot 2 = 4`, equal to the degree, so `\deg(\bar f) = 4` and `L(\bar f) = 1 - 4 = -3`.
- **(c)** `L(\mathrm{id}) = \chi(\mathbb{RP}^3) = 0 \ne -3 = L(\bar f)`, so `\bar f \not\simeq \mathrm{id}`.

## Complete Proof

### (a) `f` induces `\bar f : \mathbb{RP}^3 \to \mathbb{RP}^3`

`\mathbb{RP}^3 = (\mathbb R^4 \setminus \{0\})/(\mathbf x \sim k\mathbf x,\ k \in \mathbb R^\times)`. Two
things are needed.

*Homogeneity.* `f` is homogeneous of degree `2`: each component is a quadratic form, and indeed
`f(k\mathbf x) = (k^2x^2 - k^2y^2,\ 2k^2xy,\ \dots) = k^2 f(\mathbf x)`. So `f(k\mathbf x) = k^2 f(\mathbf x)`
lies on the same line as `f(\mathbf x)`.

*No zeros off `0`.* In `\mathbb C^2`, `f(u,v) = (u^2, v^2) = (0,0) \iff u^2 = 0` and `v^2 = 0 \iff u = v = 0`,
i.e. `\mathbf x = 0`. Hence `f(\mathbb R^4 \setminus \{0\}) \subseteq \mathbb R^4 \setminus \{0\}`.

Therefore `\bar f([\mathbf x]) := [f(\mathbf x)]` is well defined (`f(\mathbf x) \ne 0`, and
`[f(k\mathbf x)] = [k^2 f(\mathbf x)] = [f(\mathbf x)]`) and continuous: `\bar f : \mathbb{RP}^3 \to \mathbb{RP}^3`. ∎

### (b) The Lefschetz number of `\bar f`

**Rational homology.** `\mathbb{RP}^3` is a closed orientable `3`-manifold with `H_*(\mathbb{RP}^3; \mathbb Z) = (\mathbb Z, \mathbb Z/2, 0, \mathbb Z)`,
so over `\mathbb Q` (torsion dies):

$$H_0(\mathbb{RP}^3; \mathbb Q) = \mathbb Q, \quad H_1 = H_2 = 0, \quad H_3(\mathbb{RP}^3; \mathbb Q) = \mathbb Q.$$

It is a rational homology sphere. Hence

$$L(\bar f) = \operatorname{tr}(\bar f_*|_{H_0}) - \operatorname{tr}(\bar f_*|_{H_3}) = 1 - \deg(\bar f),$$

since `\bar f_*` is the identity on `H_0` (connected) and is multiplication by the **degree** on
`H_3(\mathbb{RP}^3;\mathbb Q) = \mathbb Q` (`(-1)^3 = -1` carries the sign).

**The degree is `4`.** The map `F(u,v) = (u^2, v^2)` is holomorphic `\mathbb C^2 \to \mathbb C^2` with an
isolated zero at `0`. The topological degree of the induced map on a small sphere `S^3` about `0` equals the
**local multiplicity** of `F` at `0`, which for a monomial map `(u^{a}, v^{b})` is the product `a \cdot b`;
here `2 \cdot 2 = 4`. This sphere degree equals `\deg(\bar f)` (the antipodal map on `S^3` is
orientation-preserving, so `\bar f` lifts to a degree-equal self-map of the double cover `S^3`). Hence
`\deg(\bar f) = 4`. (Equivalently: a generic value, e.g. `[1:0:1:0]`, has exactly the `4` preimages
`[(1,0,\pm1,0)]` and `[(0,1,0,\pm1)]`, and `F` is orientation-preserving — its real Jacobian
`16|u|^2|v|^2 > 0` — so all local degrees are `+1`.)

Therefore

$$\boxed{\ L(\bar f) = 1 - \deg(\bar f) = 1 - 4 = -3.\ }$$

### (c) `\bar f` is not homotopic to the identity

The Lefschetz number is a homotopy invariant, and for the identity `L(\mathrm{id}) = \chi(\mathbb{RP}^3) = 0`
(`\mathbb{RP}^3` is an odd-dimensional closed manifold). If `\bar f \simeq \mathrm{id}` then `L(\bar f) = L(\mathrm{id}) = 0`,
contradicting `L(\bar f) = -3 \ne 0`. So

$$\boxed{\ \bar f \text{ is not homotopic to the identity.}\ }\qquad\blacksquare$$

(Equivalently, degree is a homotopy invariant and `\deg(\bar f) = 4 \ne 1 = \deg(\mathrm{id})`.)

**Remark.** The complex viewpoint does all the work: `f = (u^2, v^2)` is holomorphic, hence
orientation-preserving, and its degree on `\mathbb{RP}^3` is the local multiplicity `2 \cdot 2 = 4` of the
double squaring. `\mathbb{RP}^3` being a *rational* homology sphere collapses the Lefschetz number to
`1 - \deg`, so the degree is the only nontrivial input. The same scheme classifies any
`[\mathbf x] \mapsto [F(\mathbf x)]` for homogeneous `F` with isolated zero: compute the degree, read off
`L = 1 - \deg` (in the `\mathbb Q`-sphere case), and compare to `\deg(\mathrm{id}) = 1`.
