<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95A03: The Dirichlet principle for a Sturm–Liouville problem — BVP as Euler–Lagrange, homogenization, and a coercive quadratic minimization

## Why It's Hard

The problem asks you to connect three things that look quite different: a **differential equation**
(the boundary value problem (i)), a **minimization problem** (the energy functional (ii)), and an
**existence theorem**. The conceptual core is the *Dirichlet principle* — "solving the ODE" is
literally the same as "minimizing the energy" — but making this precise requires the calculus of
variations done carefully: deriving the Euler–Lagrange equation with the right boundary handling,
and recognizing that the equivalence is *clean and bidirectional* only because the functional is a
**convex quadratic**.

Two subtleties trip people up. First, the boundary conditions are constraints on the admissible class,
so variations must *vanish* at the endpoints — this is what makes the boundary terms in the
integration by parts disappear and the natural-boundary issue not arise. Second, the existence proof
in (c) needs *coercivity*, which comes from the **Poincaré inequality** — and Poincaré holds only with
**homogeneous** boundary conditions. That is exactly why part (b) (homogenization) is not a detour but
a prerequisite: you must reduce to `\alpha=\beta=0` before the energy norm becomes equivalent to the
`H^1` norm and the direct method can run.

## The Key Insight

Expand the energy around a function `u` using a variation `v` with `v(a)=v(b)=0`:

$$J(u+v) = J(u) + 2\underbrace{\int_a^b\!\big[p\,u'v' + q\,uv + fv\big]dt}_{\text{first variation}} + \underbrace{\int_a^b\!\big[p\,(v')^2 + q\,v^2\big]dt}_{\text{second-order term}}.$$

Integrating the first variation by parts (boundary terms vanish) turns it into
`\int_a^b\big[-(pu')' + qu + f\big]v\,dt`. So:

- **First variation `= 0` for all `v` `\iff` `(pu')' - qu = f`** — the BVP (i) is exactly the
  Euler–Lagrange equation of (ii). This is part (a).
- When `p > 0` and `q \ge 0`, the **second-order term is a positive quadratic** `\int(p(v')^2 + qv^2) \ge 0`,
  vanishing only at `v=0`. Hence a critical point is a *strict global minimizer*, and there is at most
  one. The same positivity, via Poincaré, is **coercivity**, which (after homogenizing in (b)) yields
  existence in (c).

The one identity above does all three jobs: it proves the BVP/minimization equivalence, gives
uniqueness, and supplies the coercivity for existence.

## Complete Proof

Assume `p \in C^1[a,b]` with `p(t) \ge p_0 > 0`, `q \in C[a,b]` with `q(t) \ge 0`, and `f \in L^2(a,b)`.
The natural admissible class for (ii) is `\{u \in H^1(a,b) : u(a)=\alpha,\ u(b)=\beta\}`, and variations
live in `V = H^1_0(a,b) = \{v \in H^1 : v(a)=v(b)=0\}`.

### (a) Equivalence of (i) and (ii)

Let `J(u) = \int_a^b [p(u')^2 + qu^2 + 2uf]\,dt`. Take an admissible `u` and a variation `v \in V`
(so `u + v` is still admissible). Expanding the quadratic exactly,

$$J(u+v) - J(u) = 2\int_a^b \big[p\,u'v' + q\,uv + fv\big]\,dt + \int_a^b \big[p\,(v')^2 + q\,v^2\big]\,dt. \tag{1}$$

Integrate the `p\,u'v'` term by parts; since `v(a)=v(b)=0`, `\int p u'v' = [pu'v]_a^b - \int (pu')'v = -\int (pu')'v`.
Thus the first-order part of (1) is

$$\delta J(u)[v] = 2\int_a^b \big[-(pu')' + qu + f\big]\,v\,dt. \tag{2}$$

**(i) `\Rightarrow` (ii).** If `u` solves `(pu')' - qu = f`, then `-(pu')' + qu + f = 0`, so by (2) the
first variation vanishes for every `v \in V`. By (1), `J(u+v) - J(u) = \int (p(v')^2 + qv^2) \ge 0`
(as `p>0`, `q\ge0`), with equality iff `v' \equiv 0` and (with `v(a)=0`) `v\equiv 0`. Hence `u` is the
**strict global minimizer** of (ii).

**(ii) `\Rightarrow` (i).** If `u` minimizes (ii), then `\delta J(u)[v] = 0` for all `v \in V`, i.e. by
(2) `\int [-(pu')' + qu + f]\,v = 0` for all `v \in V`. By the fundamental lemma of the calculus of
variations, `-(pu')' + qu + f = 0`, i.e. `(pu')' - qu = f`; the constraint gives the boundary values.
So `u` solves (i).

The two problems are therefore equivalent: **(i) is the Euler–Lagrange equation of (ii)**, and (under
`p>0`, `q\ge0`) their common solution is unique and is the unique energy minimizer. (Weak solutions
`u \in H^1` are characterized by the same first-variation identity `\int[pu'v' + quv + fv] = 0`; elliptic
regularity upgrades them to classical `C^2` solutions when `p,q,f` are smooth.)

### (b) Reduction to homogeneous boundary conditions

Pick any fixed `w \in C^2[a,b]` (or `H^1`) meeting the boundary data, e.g. the linear interpolant

$$w(t) = \alpha + (\beta - \alpha)\,\frac{t - a}{b - a}, \qquad w(a) = \alpha,\ w(b) = \beta.$$

Set `v = u - w`, so `v(a) = v(b) = 0`. Substituting `u = v + w` into (i),

$$(pv')' - qv = f - \big[(pw')' - qw\big] =: \tilde f, \qquad v(a)=v(b)=0,$$

with the *known* modified right-hand side `\tilde f = f - (pw')' + qw`. This is the **same** Sturm–Liouville
operator with **homogeneous** boundary conditions. Equivalently, in the variational picture,
`u \mapsto v = u - w` carries (ii) into the minimization of `\tilde J(v) = \int[p(v')^2 + qv^2 + 2v\tilde f]\,dt`
over `V = H^1_0(a,b)` (up to a constant independent of `v`). So we may assume `\alpha = \beta = 0`. ∎

### (c) Existence and uniqueness for `\alpha = \beta = 0`

Now minimize `J(v) = \int_a^b [p(v')^2 + qv^2 + 2vf]\,dt` over the Hilbert space `V = H^1_0(a,b)`. Write

$$J(v) = B(v,v) + 2\ell(v), \quad B(v,w) = \int_a^b (p\,v'w' + q\,vw)\,dt, \quad \ell(v) = \int_a^b f v\,dt.$$

`B` is a symmetric bilinear form and `\ell \in V^*` (since `|\ell(v)| \le \|f\|_{L^2}\|v\|_{L^2} \le \|f\|_{L^2}\|v\|_{H^1}`).

**Coercivity (here the homogeneous BC is essential).** On `V = H^1_0(a,b)` the **Poincaré inequality**
holds: `\int_a^b v^2 \le C_P \int_a^b (v')^2` with `C_P = \big(\tfrac{b-a}{\pi}\big)^2`. Hence, using
`p \ge p_0 > 0`, `q \ge 0`,

$$B(v,v) = \int (p(v')^2 + qv^2) \ge p_0 \int (v')^2 \ge \frac{p_0}{1 + C_P}\,\|v\|_{H^1}^2,$$

so `B` is **coercive**; it is also bounded (`B(v,w) \le (\|p\|_\infty + \|q\|_\infty)\|v\|_{H^1}\|w\|_{H^1}`).
Thus `B` is an inner product on `V` equivalent to the `H^1` inner product.

**Existence and uniqueness.** By the **Riesz representation theorem** (equivalently Lax–Milgram), there
is a *unique* `v^\star \in V` with

$$B(v^\star, w) = -\ell(w) \qquad \text{for all } w \in V. \tag{3}$$

This `v^\star` is the unique minimizer: for any `v \in V`, expanding as in (1) and using (3),

$$J(v^\star + v) = J(v^\star) + 2\big[B(v^\star, v) + \ell(v)\big] + B(v,v) = J(v^\star) + B(v,v) \ge J(v^\star),$$

with equality iff `B(v,v) = 0`, i.e. (by coercivity) `v = 0`. Hence `v^\star` is the **unique global
minimizer** of `J` over `H^1_0(a,b)`.

Equation (3) is precisely the weak form `\int[p (v^\star)' w' + q v^\star w + f w] = 0` of
`(p (v^\star)')' - q v^\star = f` with `v^\star(a)=v^\star(b)=0`; under the smoothness assumptions on
`p,q,f`, regularity theory makes `v^\star \in C^2[a,b]` a classical solution. By part (a) this is also
the unique solution of the BVP (i) with `\alpha=\beta=0`. ∎

**Remark.** The hypotheses earn their keep: `p \ge p_0 > 0` gives ellipticity (the leading term controls
`\int (v')^2`), and `q \ge 0` keeps `B` a genuine positive form. If `q` were allowed sufficiently
negative, coercivity — and with it existence/uniqueness — could fail (resonance with a Sturm–Liouville
eigenvalue), which is the variational shadow of the Fredholm alternative. Homogenizing in (b) is what
lets Poincaré convert `p>0, q\ge0` into coercivity, because Poincaré requires the vanishing boundary
values.
