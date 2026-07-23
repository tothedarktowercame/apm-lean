<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m03J05: Linear and semilinear two-point BVPs via Lax–Milgram and the direct method

## Why It's Hard

The three parts form a single arc — linear solvability, then the analytic
machinery, then nonlinear solvability — and each needs a *different* abstract
theorem, so the trick is recognizing which one and setting up the right function
space for it.

- **(a)** is a linear mixed boundary value problem. "Discuss solvability" is code
  for: identify the coercivity threshold and run the Fredholm alternative at the
  exceptional values of `c`. You must compute the actual eigenvalues of the
  operator with *these* boundary conditions (Dirichlet at `0`, Neumann at `1`),
  because the answer changes at each of them.
- **(b)** asks for *Fréchet* differentiability — a uniform, norm-controlled
  remainder, not just a directional (Gâteaux) derivative. The nonlinear term
  `∫ g(u)` is the obstacle, and the only way to control its remainder uniformly is
  to use the Lipschitz bound on `G = g'` together with the Sobolev embedding
  `H¹(0,1) ↪ C[0,1]`.
- **(c)** is a *nonlinear* BVP where no explicit solution exists. The leverage is
  to realize the BVP is exactly the Euler–Lagrange equation `J'(u) = 0` of the
  functional from (b), and that monotonicity of `G` makes `J` convex — so
  existence and uniqueness come from minimizing `J`, not from solving the PDE
  directly.

The hidden unity: parts (b) and (c) are the same functional seen twice — (b)
proves it is differentiable so that "critical point ⟺ weak solution," and (c)
proves it has a unique minimizer.

## The Key Insight

Everything is organized by the energy space

$$V = \{\,u \in H^1(0,1) : u(0) = 0\,\},$$

in which the Dirichlet condition `u(0)=0` is *essential* (built into `V`) and the
Neumann condition `u'(1)=0` is *natural* (it falls out of integration by parts in
the weak form, never imposed by hand). On `V` the boundary value `u(0)=0` powers a
**Poincaré inequality** `‖u‖_{L²} ≤ ‖u'‖_{L²}`, so `‖u'‖_{L²}` is an equivalent
norm — this is what makes the quadratic form coercive in (a) and the functional
coercive in (c).

The second insight is that **monotone `G` ⟺ convex `g` ⟺ convex `J`**. Once `J`
is convex, coercive, and (by (b)) differentiable, the direct method of the
calculus of variations delivers a unique minimizer, and its Euler–Lagrange
equation *is* the BVP. The Lipschitz hypothesis is what (b) needs for a Fréchet
(not merely Gâteaux) remainder; the monotonicity hypothesis is what (c) needs for
convexity and uniqueness.

## Complete Proof

Work on `V = \{u ∈ H^1(0,1) : u(0)=0\}`, a closed subspace of `H^1(0,1)` (the
evaluation `u ↦ u(0)` is continuous because `H^1(0,1) ↪ C[0,1]`), hence a Hilbert
space. For `u ∈ V`, since `u(0)=0`,

$$|u(x)| = \Big|\int_0^x u'(t)\,dt\Big| \le \int_0^1 |u'| \le \|u'\|_{L^2},
\quad\text{so}\quad \|u\|_{L^\infty} \le \|u'\|_{L^2}\ \text{and}\ \|u\|_{L^2} \le \|u'\|_{L^2}. \tag{P}$$

Thus `\|u\|_V := \|u'\|_{L^2}` is a norm on `V` equivalent to the `H^1`-norm.

---

### (a)  Linear problem `-u'' + cu = F`, `u(0)=0`, `u'(1)=0`

**Weak formulation.** Multiply by `v ∈ V` and integrate by parts:
`∫_0^1 -u''v = [-u'v]_0^1 + ∫_0^1 u'v' = -u'(1)v(1) + u'(0)v(0) + ∫_0^1 u'v'`.
With `v(0)=0` (as `v ∈ V`) and `u'(1)=0` (the natural condition), the boundary
terms drop, giving the weak problem: find `u ∈ V` with

$$a(u,v) := \int_0^1 u'v'\,dx + c\int_0^1 uv\,dx = \int_0^1 Fv\,dx =: \ell(v)
\qquad \forall v \in V.$$

`a` is a bounded bilinear form and `ℓ ∈ V^*` (since `F ∈ L^2`).

**Spectrum of the principal part.** The eigenproblem `-φ'' = λφ`, `φ(0)=0`,
`φ'(1)=0` has solutions `φ_n(x) = \sin(\sqrt{λ_n}\,x)` with `\cos\sqrt{λ_n}=0`,
i.e.

$$λ_n = \Big(\tfrac{(2n-1)\pi}{2}\Big)^2, \quad n = 1,2,\dots,
\qquad λ_1 = \tfrac{\pi^2}{4}.$$

These `\{φ_n\}` form an orthogonal basis of `L^2(0,1)`, and the sharp Poincaré
constant is `\|u'\|_{L^2}^2 \ge λ_1\|u\|_{L^2}^2` (improving (P)).

**Coercivity / Lax–Milgram.** For `u ∈ V`, `a(u,u) = \|u'\|^2 + c\|u\|^2`.
- If `c \ge 0`: `a(u,u) \ge \|u'\|^2 = \|u\|_V^2`, coercive.
- If `c < 0`: using `\|u\|^2 \le λ_1^{-1}\|u'\|^2`,
  `a(u,u) \ge \|u'\|^2 + c\,λ_1^{-1}\|u'\|^2 = (1 + c/λ_1)\,\|u\|_V^2`, coercive
  precisely when `c > -λ_1 = -\pi^2/4`.

So **if `c > -\pi^2/4`, `a` is coercive and Lax–Milgram gives a unique `u ∈ V`
for every `F ∈ L^2`.**

**Fredholm alternative at and below the threshold.** The solution operator of the
principal part `A = -d^2/dx^2` on `V` is compact and self-adjoint (compact
embedding `V \hookrightarrow\hookrightarrow L^2`), so `A` has the discrete
spectrum `\{λ_n\}`. The problem reads `(A + c)u = F`. By the Fredholm
alternative:
- If `-c \notin \{λ_n\}` (in particular whenever `c > -\pi^2/4`): `A+c` is
  invertible — **unique solution for every `F`**.
- If `c = -λ_n` for some `n` (i.e. `c ∈ \{-\pi^2/4, -9\pi^2/4, \dots\}`): the
  kernel is `\mathrm{span}\{φ_n\}`, and the problem is **solvable iff
  `∫_0^1 F\,φ_n\,dx = 0`**, in which case the solution is unique up to adding a
  multiple of `φ_n = \sin\frac{(2n-1)\pi x}{2}`.

This is the complete solvability discussion. ∎

---

### (b)  `J` is Fréchet differentiable on `H^1(0,1)`

Write `J = Q + Φ - L` with
`Q(u) = \frac12\int_0^1 u'^2`, `Φ(u) = \int_0^1 g(u)`, `L(u) = \int_0^1 Fu`.

*Quadratic and linear parts.*
`Q(u+v) - Q(u) = \int u'v' + \frac12\int v'^2`, so `Q'(u)v = \int_0^1 u'v'` with
remainder `\frac12\|v'\|^2 = o(\|v\|_{H^1})`; `Q` is smooth.
`L` is bounded linear (`F ∈ L^2 \subset (H^1)^*`), so `L'(u)v = \int Fv`.

*Nonlinear part — the crux.* Claim `Φ'(u)v = \int_0^1 G(u)\,v\,dx`. This is a
bounded linear functional: `H^1(0,1) ↪ C[0,1]` gives `\|u\|_\infty \le C\|u\|_{H^1}`,
so `G(u)` is bounded on `[0,1]` (hence in `L^2`), and
`|\int G(u)v| \le \|G(u)\|_{L^2}\|v\|_{L^2}`.

For the remainder, use the fundamental theorem of calculus on `g` (with `g'=G`):

$$g(u+v) - g(u) - G(u)v = \int_0^1 \big[G(u + tv) - G(u)\big]\,v\,dt.$$

Since `G` is Lipschitz with constant `L`, `|G(u+tv) - G(u)| \le L\,t\,|v|`, hence
the integrand is `\le L\,t\,|v|^2`, and integrating in `t`,

$$\big|\,g(u+v) - g(u) - G(u)v\,\big| \le \tfrac{L}{2}\,|v(x)|^2.$$

Integrating over `x ∈ (0,1)`,

$$\big|\,Φ(u+v) - Φ(u) - \textstyle\int G(u)v\,\big|
\le \tfrac{L}{2}\int_0^1 |v|^2 = \tfrac{L}{2}\|v\|_{L^2}^2 \le \tfrac{L}{2}\|v\|_{H^1}^2,$$

so the remainder is `o(\|v\|_{H^1})` — **uniformly**, which is exactly Fréchet
differentiability. Therefore

$$J'(u)v = \int_0^1 u'v'\,dx + \int_0^1 G(u)v\,dx - \int_0^1 Fv\,dx,$$

a bounded linear functional, and `J` is Fréchet differentiable on `H^1(0,1)`. ∎

---

### (c)  Unique solution of `-u'' + G(u) = F`, `u(0)=0`, `u'(1)=0`

Here `G` is monotone **nondecreasing** (the case making the operator well-posed),
so `g` — with `g' = G` nondecreasing and `g(0)=0` — is **convex**. We solve the
BVP by minimizing `J` over `V`; restricting `J` to `V` builds in `u(0)=0`, and
`u'(1)=0` will appear naturally.

**Weak form = critical point.** By (b), for `u, v ∈ V`,
`J'(u)v = \int u'v' + \int G(u)v - \int Fv`. So `J'(u) = 0` on `V` is exactly the
weak form of the BVP.

**`J` is convex, coercive, and weakly l.s.c. on `V`.**
- *Convex:* `\frac12\int u'^2` is convex (strictly, in `\|\cdot\|_V`), `\int g(u)`
  is convex (`g` convex), `-\int Fu` is linear; so `J` is convex, and strictly
  convex thanks to the quadratic term.
- *Coercive:* convexity of `g` with `g(0)=0` gives `g(t) \ge G(0)\,t`, so
  `\int g(u) \ge G(0)\int u \ge -|G(0)|\,\|u\|_{L^2}` (using `|(0,1)|=1`). With
  Poincaré (P),
  `J(u) \ge \tfrac12\|u'\|^2 - (|G(0)| + \|F\|_{L^2})\|u\|_{L^2}
  \ge \tfrac12\|u\|_V^2 - (|G(0)| + \|F\|_{L^2})\|u\|_V \to +\infty`
  as `\|u\|_V \to \infty`.
- *Weakly l.s.c.:* `J` is convex and continuous (Fréchet differentiable), hence
  weakly lower semicontinuous on the reflexive space `V`.

**Existence (direct method).** Take a minimizing sequence `u_k`. Coercivity bounds
`\|u_k\|_V`, so along a subsequence `u_k \rightharpoonup u` weakly in `V`. Weak
l.s.c. gives `J(u) \le \liminf J(u_k) = \inf_V J`, so `u` is a minimizer. Being a
minimizer, `J'(u) = 0` on `V`: `u` is a weak solution.

**Uniqueness.** Suppose `u_1, u_2 ∈ V` both solve the weak form. Subtract and test
with `w = u_1 - u_2 ∈ V`:

$$\int_0^1 (u_1' - u_2')w' + \int_0^1 \big(G(u_1) - G(u_2)\big)w = 0.$$

The first term is `\|w'\|_{L^2}^2 \ge 0`; the second is `\ge 0` because `G`
nondecreasing means `(G(u_1)-G(u_2))(u_1-u_2) \ge 0` pointwise. Both being
nonnegative and summing to `0` forces `\|w'\|_{L^2} = 0`, so `w` is constant, and
`w(0)=0` gives `w \equiv 0`. Hence `u_1 = u_2`. (Equivalently, strict convexity of
`J`.)

**Regularity and the natural boundary condition.** Testing with `v ∈ C_c^\infty(0,1)`
gives `\int u'v' = \int (F - G(u))v`, so `u'' = -(F - G(u)) ∈ L^2` weakly; thus
`u ∈ H^2(0,1) \hookrightarrow C^1[0,1]` and `-u'' + G(u) = F` a.e. Integrating by
parts back with a general `v ∈ V`, `\int u'v' = -\int u''v + u'(1)v(1)`, and
comparing with `\int(F - G(u))v = -\int u''v` yields `u'(1)v(1) = 0` for all
`v ∈ V`; since `v(1)` is arbitrary, `u'(1) = 0`. The condition `u(0)=0` holds
because `u ∈ V`.

Therefore the BVP has a **unique** solution `u ∈ H^2(0,1) \cap V`, satisfying
`-u'' + G(u) = F` with `u(0)=0` and `u'(1)=0`. ∎
