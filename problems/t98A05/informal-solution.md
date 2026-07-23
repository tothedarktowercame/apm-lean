<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t98A05: Exterior derivatives, a vanishing wedge, a Stokes integral, and the angle form on the circle

## Why It's Hard

The four parts are computations, but each rewards seeing the form's *geometric meaning* rather than grinding
indices:

- **(a)** Routine `d`, but one must track signs (`d(-y\,dx)=+dx\wedge dy`) and recognize `\beta` as the flux
  form of `(x,y,z)`, so `d\beta=(\operatorname{div})\,\gamma=3\gamma`.
- **(b)** The wedge `\alpha\wedge\beta` looks like a `9`-term expansion, but it is the volume form times the
  *dot product* of the vector fields `\alpha\leftrightarrow(-y,x,0)` and `\beta\leftrightarrow(x,y,z)`, which
  is `0` — most students miss that it vanishes identically.
- **(c)** A Stokes/orientation bookkeeping problem; the integrand `d\alpha=2\,dx\wedge dy` is a **2-form**, so
  the domain must be the **2-dimensional** simplex (the triangular face), oriented; the answer drops out
  either by projecting to the `xy`-plane or by `\int_{\partial}\alpha`.
- **(d)** The punchline: restricting `\alpha` to the unit circle gives exactly the **angle form** `d\theta`,
  the canonical *closed-but-not-exact* `1`-form. Its automatic closedness (`d\alpha'=0` on a `1`-manifold)
  must not be confused with exactness; the period `\int_S\alpha'=2\pi\ne0` is the obstruction to a global
  potential `f`.

## The Key Insight

- **(a)** `d\alpha=2\,dx\wedge dy`, `d\beta=3\,dx\wedge dy\wedge dz=3\gamma`, `d\gamma=0`.
- **(b)** `\alpha\wedge\beta=\big((-y,x,0)\cdot(x,y,z)\big)\,dx\wedge dy\wedge dz=(-xy+xy)\,\gamma=0`.
- **(c)** Over the standard `2`-simplex `\Delta^2` (oriented by the outward normal `(1,1,1)`), projecting to
  the `xy`-plane, `\int_{\Delta^2}2\,dx\wedge dy=2\cdot\mathrm{area}=2\cdot\tfrac12=1` (Stokes-checked by
  `\oint_{\partial\Delta^2}\alpha=1`).
- **(d)** `\alpha'=d\theta`, so `d\alpha'=0`; but `\int_S\alpha'=2\pi\ne0` while every exact form has period
  `0` over the closed `S`, so **no** `f` with `df=\alpha'` exists.

## Complete Proof

On `\mathbb R^3`: `\alpha=x\,dy-y\,dx`, `\beta=x\,dy\wedge dz+y\,dz\wedge dx+z\,dx\wedge dy`,
`\gamma=dx\wedge dy\wedge dz`.

### (a) Exterior derivatives

$$
d\alpha = d(x\,dy)-d(y\,dx) = dx\wedge dy - dy\wedge dx = dx\wedge dy + dx\wedge dy = 2\,dx\wedge dy .
$$
For `\beta` (the flux form of `\mathbf F=(x,y,z)`), each term differentiates to `+dx\wedge dy\wedge dz`:
$$
d\beta = (dx\wedge dy\wedge dz)+(dy\wedge dz\wedge dx)+(dz\wedge dx\wedge dy) = 3\,dx\wedge dy\wedge dz = 3\gamma .
$$
(`\operatorname{div}\mathbf F=1+1+1=3`.) Finally `\gamma` is top-degree, so
$$
d\gamma = d(dx\wedge dy\wedge dz) = 0 .
$$

### (b) The wedge `\alpha\wedge\beta`

Expand, keeping only terms without a repeated differential:
$$
\alpha\wedge\beta = (x\,dy-y\,dx)\wedge(x\,dy\wedge dz+y\,dz\wedge dx+z\,dx\wedge dy).
$$
From `x\,dy`: only `x\,dy\wedge(y\,dz\wedge dx)=xy\,dy\wedge dz\wedge dx=xy\,dx\wedge dy\wedge dz` survives.
From `-y\,dx`: only `-y\,dx\wedge(x\,dy\wedge dz)=-xy\,dx\wedge dy\wedge dz` survives. Adding,
$$
\alpha\wedge\beta = xy\,dx\wedge dy\wedge dz - xy\,dx\wedge dy\wedge dz = 0 .
$$
(Vector-field check: `\alpha\leftrightarrow(-y,x,0)`, `\beta\leftrightarrow(x,y,z)`, and `\alpha\wedge\beta=
(\text{dot product})\,\gamma=(-xy+xy+0)\,\gamma=0`.)

### (c) `\int_\Gamma d\alpha` over the standard `2`-simplex

Since `d\alpha=2\,dx\wedge dy` is a **2-form**, the domain is the `2`-dimensional standard simplex
$$
\Gamma = \Delta^2 = \{(x,y,z): x+y+z=1,\ x,y,z\ge0\},
$$
the triangular face with vertices `A=(1,0,0),\ B=(0,1,0),\ C=(0,0,1)`. Orient `\Delta^2` by the outward unit
normal `(1,1,1)/\sqrt3` (equivalently the vertex order `A\to B\to C`).

Parametrize `\Delta^2` by `(x,y)\mapsto(x,y,1-x-y)` over the planar triangle `R=\{x,y\ge0,\ x+y\le1\}` (area
`\tfrac12`). The chosen orientation projects to the *counterclockwise* (positive) orientation of `R` (the
normal has positive `z`-component; shoelace on `A,B,C` gives `+\tfrac12`), so
$$
\int_{\Delta^2} d\alpha = \int_{\Delta^2} 2\,dx\wedge dy = 2\int_R dx\,dy = 2\cdot\tfrac12 = \boxed{1}.
$$
**Stokes check.** `\int_{\Delta^2}d\alpha=\oint_{\partial\Delta^2}\alpha` over the boundary `A\to B\to C\to
A`. On `A\to B` (`(1-t,t,0)`): `\alpha=x\,dy-y\,dx=(1-t)\,dt-t(-dt)=dt`, integral `1`; on `B\to C` and `C\to
A`, `\alpha` pulls back to `0` (one of `x,y` vanishes with the other's differential), integrals `0`. Total
`\oint_{\partial\Delta^2}\alpha=1`, agreeing. *(Had the solid `3`-simplex been intended, the natural top-form
is `d\beta=3\gamma`, giving `\int_{\Delta^3}d\beta=3\cdot\operatorname{vol}=3\cdot\tfrac16=\tfrac12`.)*

### (d) Restriction to the unit circle: `\alpha'` is closed but not exact

Let `S=\{x^2+y^2=1,\ z=0\}` and `\alpha'=\alpha|_S`. Parametrize `S` by `\theta`: `x=\cos\theta`,
`y=\sin\theta`, so `dx=-\sin\theta\,d\theta`, `dy=\cos\theta\,d\theta`, and
$$
\alpha' = x\,dy-y\,dx = \cos\theta(\cos\theta\,d\theta)-\sin\theta(-\sin\theta\,d\theta) = (\cos^2\theta+\sin^2\theta)\,d\theta = d\theta .
$$
So `\alpha'` is the **angle form** `d\theta` on `S`.

**`d\alpha'=0`.** `\alpha'` is a `1`-form on the `1`-manifold `S`, so `d\alpha'` is a `2`-form on a
`1`-dimensional space, hence identically `0`. (`\alpha'` is automatically closed.)

**No `f` with `df=\alpha'` exists.** Suppose, for contradiction, that `f:S\to\mathbb R` is smooth with
`df=\alpha'`. Then `\alpha'` is exact, and `S` is a closed `1`-manifold (a circle, `\partial S=\varnothing`),
so by Stokes' theorem
$$
\int_S \alpha' = \int_S df = \int_{\partial S} f = 0 .
$$
But directly
$$
\int_S \alpha' = \int_0^{2\pi} d\theta = 2\pi \ne 0,
$$
a contradiction. Therefore **no such `f` exists**: `\alpha'=d\theta` is closed but not exact. ∎

**Remark.** The thread is that `\alpha`'s restriction to the circle is the prototypical nontrivial de Rham
class. Although `\theta` "looks like" a potential, it is only *locally* defined (multivalued, jumping by
`2\pi` each loop), so there is no global function `f` with `df=\alpha'`; the obstruction is precisely the
nonzero period `\int_S\alpha'=2\pi`, the generator of `H^1_{dR}(S^1)\cong\mathbb R`. Parts (c) and (d) are two
sides of Stokes: in (c) integrating the exact `d\alpha` over a surface reduces to the boundary integral of
`\alpha` (and gives a finite nonzero number), while in (d) the would-be exactness `\alpha'=df` over the
*closed* circle is forbidden exactly because that boundary is empty, so the period must vanish — but it
doesn't. The `2\pi` is the same winding obstruction that makes `\alpha=x\,dy-y\,dx` the "twice signed area"
form of the plane.
