<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t02A07: A level set in S³ as a submanifold, and a dense family of transverse maps (Thom)

## Why It's Hard

Part (a) asks whether two simultaneous equations — the sphere `|x|^2 = 1` and `x^3 x^4 = 1/4` — cut out a
smooth submanifold of `\mathbb A^4`. The danger is that the two level sets might fail to meet transversally
somewhere (parallel gradients), which would create singular points. One must check that the gradients of the
two defining functions stay independent *along the intersection* `Z`, and the verification has to use both
constraints together (the would-be bad points are precisely those ruled out by lying on the sphere with
`x^3 x^4 = 1/4 > 0`).

Part (b) is the genuinely subtle one: prove that *many* of the maps `\varphi_{\lambda,\mu}` are transverse to
`Z`, without checking each parameter individually (impossible — there are uncountably many). The right idea
is **parametric transversality** (Thom): bundle all the maps into one *total* family map `\Phi : S^2 \times C \to X`,
prove the single statement `\Phi \pitchfork Z`, and then let Sard's theorem distribute transversality to
almost every — hence a dense set of — parameter slices. The work is the one transversality computation for
`\Phi`; the genericity is then automatic.

## The Key Insight

**(a)** `Z = f^{-1}(1) \cap g^{-1}(1/4)` with `f = |x|^2`, `g = x^3 x^4`. Their gradients
`\nabla f = 2(x^1,x^2,x^3,x^4)` and `\nabla g = (0,0,x^4,x^3)` are independent on `Z`: if parallel, then
`x^1 = x^2 = 0` and `\lambda = \pm 2`, forcing either `(x^3)^2 + (x^4)^2 = 1/2 \ne 1` or `x^3 x^4 < 0` —
both impossible on `Z`. So `Z` is a codimension-`2` submanifold of `\mathbb A^4`, hence codimension-`1` in
`X = S^3`: `\dim Z = 2`.

**(b)** The maps land in `X` (`|\varphi_{\lambda,\mu}(y)|^2 = \lambda^2 + \mu^2 = 1`). Form the total family
`\Phi : S^2 \times C \to X`, `C = \{\lambda^2 + \mu^2 = 1\}`. Since `Z` is the level set `\{g = 1/4\}` of a
submersion, `\Phi \pitchfork Z \iff G := g\circ\Phi = \lambda^2 y^2 y^3` is submersive on `G^{-1}(1/4)` — a
short computation shows `dG|_{T(S^2\times C)} \ne 0` there. By **Thom's parametric transversality theorem**,
`\varphi_{\lambda,\mu} \pitchfork Z` for almost every `(\lambda,\mu) \in C`, a dense set.

## Complete Proof

`X = S^3 = \{(x^1,x^2,x^3,x^4) : f(x) := \sum (x^i)^2 = 1\}` and `Z = \{x \in X : g(x) := x^3 x^4 = 1/4\}`.

### (a) `Z` is a 2-dimensional submanifold

View `Z = f^{-1}(1) \cap g^{-1}(1/4) \subset \mathbb A^4`. Its gradients are

$$\nabla f = 2(x^1, x^2, x^3, x^4), \qquad \nabla g = (0, 0, x^4, x^3).$$

We show they are linearly independent at every point of `Z`. Suppose `\nabla f = c\,\nabla g` for some scalar
`c` (the other parallel case is symmetric). The first two coordinates give `2x^1 = 0`, `2x^2 = 0`, so
`x^1 = x^2 = 0`; the last two give `2x^3 = c\,x^4` and `2x^4 = c\,x^3`. Multiplying these,
`4 x^3 x^4 = c^2 x^3 x^4`, and since `x^3 x^4 = 1/4 \ne 0` on `Z`, `c^2 = 4`, `c = \pm 2`.

- `c = 2`: then `x^3 = x^4`, so `x^3 x^4 = (x^3)^2 = 1/4` gives `(x^3)^2 + (x^4)^2 = 1/2`; with `x^1 = x^2 = 0`,
  `f = 1/2 \ne 1` — not on the sphere.
- `c = -2`: then `x^3 = -x^4`, so `x^3 x^4 = -(x^4)^2 \le 0 \ne 1/4` — impossible.

So no point of `Z` has parallel gradients; `\nabla f, \nabla g` are independent on `Z`. Hence `df, dg` are
independent there, and by the regular-value / transverse-intersection theorem `Z` is a submanifold of
`\mathbb A^4` of codimension `2`, i.e. `\dim Z = 4 - 2 = 2`. Equivalently, restricting `g` to `X`, the
independence of `dg` from `df` (the conormal of `X`) means `d(g|_X) \ne 0` on `Z`, so `1/4` is a regular value
of `g|_X : X \to \mathbb R` and `Z = (g|_X)^{-1}(1/4)` is a codimension-`1` submanifold of the `3`-manifold
`X`. (Nonempty, e.g. `(1/\sqrt2, 0, 1/2, 1/2) \in Z`.)

$$\boxed{\ Z \text{ is a submanifold of } X \text{ with } \dim Z = 2.\ }$$

### (b) A dense set of transverse maps

Let `C = \{(\lambda,\mu) : \lambda^2 + \mu^2 = 1\}` (a circle) and
`\varphi_{\lambda,\mu}(y) = (\lambda y^1,\ \mu,\ \lambda y^2,\ \lambda y^3)` for `y \in S^2`. First, these land
in `X`:

$$|\varphi_{\lambda,\mu}(y)|^2 = \lambda^2\big((y^1)^2 + (y^2)^2 + (y^3)^2\big) + \mu^2 = \lambda^2 + \mu^2 = 1.$$

**The total family map.** Define `\Phi : S^2 \times C \to X`, `\Phi(y, \lambda, \mu) = \varphi_{\lambda,\mu}(y)`.
Since `Z = \{g = 1/4\}` with `g|_X` a submersion along `Z`, for any map `\psi` into `X` we have
`\psi \pitchfork Z \iff g\circ\psi` is submersive (regular) at each point of `(g\circ\psi)^{-1}(1/4)`. Apply
this to `\psi = \Phi`: the composite is

$$G(y,\lambda,\mu) := g(\Phi(y,\lambda,\mu)) = (\lambda y^2)(\lambda y^3) = \lambda^2\, y^2 y^3.$$

**Claim: `dG|_{T(S^2\times C)} \ne 0` on `G^{-1}(1/4)`,** so `\Phi \pitchfork Z`. The ambient gradient of `G`
(in coordinates `(y^1,y^2,y^3,\lambda,\mu)`) is

$$\nabla G = (0,\ \lambda^2 y^3,\ \lambda^2 y^2,\ 2\lambda y^2 y^3,\ 0).$$

`dG` vanishes on `T(S^2 \times C)` iff `\nabla G` is normal to `S^2 \times C`, i.e.
`\nabla G = \alpha\,(y^1, y^2, y^3, 0, 0) + \beta\,(0,0,0,\lambda,\mu)` for some `\alpha, \beta`. On
`G^{-1}(1/4)` we have `\lambda^2 y^2 y^3 = 1/4`, so `\lambda \ne 0`, `y^2 \ne 0`, `y^3 \ne 0`. Matching
coordinates:

- `\lambda`-slot: `2\lambda y^2 y^3 = \beta\lambda \Rightarrow \beta = 2 y^2 y^3 \ne 0`;
- `\mu`-slot: `0 = \beta\mu \Rightarrow \mu = 0`, hence `\lambda^2 = 1`;
- `y^1`-slot: `0 = \alpha y^1`; `y^2, y^3`-slots: `\lambda^2 y^3 = \alpha y^2`, `\lambda^2 y^2 = \alpha y^3`,
  giving `\alpha^2 = \lambda^4 = 1`, so `y^3 = \pm y^2` and `y^1 = 0`.

But then `(y^2)^2 + (y^3)^2 = 1` with `y^3 = \pm y^2` forces `(y^2)^2 = 1/2`, so
`G = \lambda^2 y^2 y^3 = \pm 1/2 \ne 1/4`. Thus `dG|_{T(S^2\times C)} = 0` cannot happen on `G^{-1}(1/4)`;
`G` is submersive there, so `\Phi \pitchfork Z`.

**Apply Thom.** By the **parametric transversality theorem**: since `\Phi : S^2 \times C \to X` is transverse
to `Z`, the preimage `W = \Phi^{-1}(Z)` is a submanifold of `S^2 \times C`, and a parameter `(\lambda,\mu)` is
a regular value of the projection `\pi : W \to C` iff `\varphi_{\lambda,\mu} \pitchfork Z`. By **Sard's
theorem**, almost every `(\lambda,\mu) \in C` is a regular value of `\pi`. Therefore

$$\boxed{\ \{(\lambda,\mu) \in C : \varphi_{\lambda,\mu} \pitchfork Z\} \text{ has full measure, hence is dense in } C.\ }\qquad\blacksquare$$

**Remark.** Part (a) is transverse intersection of two level sets (independent gradients), and the bad points
are excluded precisely by the *sign and size* constraints `x^3 x^4 = 1/4 > 0` together with `|x| = 1`. Part (b)
is the philosophy of generic transversality: never check the individual maps `\varphi_{\lambda,\mu}`; check the
*one* family map `\Phi`, where the extra parameter directions give enough room for `dG \ne 0`, and then Sard
(via Thom) automatically yields transversality for a residual — in particular dense — set of parameters. The
single computation `G = \lambda^2 y^2 y^3` carries the whole part-(b) argument.
