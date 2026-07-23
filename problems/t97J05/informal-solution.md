<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97J05: Jacobian, regular value, and submersion normal form for f(x,y,z)=(eˣcos y, xz)

## Why It's Hard

The three parts walk up the ladder of the submersion theory, and each has a small twist:

- **(a)** is a Jacobian computation, but one must check **rank**, not just write the matrix: `p` is regular
  iff `df_p:\mathbb R^3\to\mathbb R^2` is *surjective* (rank `2`), which needs a `2\times2` minor to be
  nonzero.
- **(b)** asks whether `W=f^{-1}(0,1)` is a manifold. The slick observation is that `e^x\cos y=0` forces
  `\cos y=0` (since `e^x>0`), and `\cos y=0` has **isolated** solutions — so on `W` the coordinate `y` is
  *locally constant* `=\pi/2`, collapsing `W` near `p` to the planar curve `xz=1`. One must also verify
  `(0,1)` is a regular value (every point of `W` is regular) to *justify* manifoldness.
- **(c)** is the **submersion normal form** in disguise: `\psi\circ f\circ\varphi(x,y,z)=(x,y)` is exactly
  the statement that, after local diffeomorphisms, a submersion looks like the standard projection. It exists
  *because* `p` is regular (part a), and the construction is to **complete `f` to a local diffeomorphism** by
  appending a coordinate — the inverse function theorem then provides `\varphi`.

The unifying thread: *regular point ⇒ submersion ⇒ locally the projection `(x,y,z)\mapsto(x,y)`.*

## The Key Insight

`Df=\begin{psmallmatrix} e^x\cos y & -e^x\sin y & 0\\ z & 0 & x\end{psmallmatrix}`.

- **(a)** At `p=(1,\tfrac\pi2,1)`: `df_p=\begin{psmallmatrix}0&-e&0\\1&0&1\end{psmallmatrix}`, rank `2`
  (the `2\times2` minor in columns `1,2` is `e\ne0`) — `p` is **regular**.
- **(b)** On `W`, `\cos y=0` (so `y=\pi/2` locally) and `xz=1`; `(0,1)` is a regular value, so `W` is a
  smooth `1`-manifold, parametrized near `p` by `\gamma(t)=(t,\tfrac\pi2,1/t)`.
- **(c)** **Yes.** Since `f` is a submersion at `p`, append `z` to form the local diffeomorphism
  `\Phi=(e^x\cos y,\,xz,\,z)` (invertible near `p` because `\det D\Phi_p=e\ne0`); then `\varphi=\Phi^{-1}`
  (recentered) and a translation `\psi` give `\psi\circ f\circ\varphi(x,y,z)=(x,y)`.

## Complete Proof

`f:\mathbb R^3\to\mathbb R^2`, `f(x,y,z)=(f_1,f_2)=(e^x\cos y,\ xz)`.

### (a) `df_p` and regularity

The Jacobian is
$$
Df(x,y,z) = \begin{pmatrix} \partial_x f_1 & \partial_y f_1 & \partial_z f_1\\ \partial_x f_2 & \partial_y f_2 & \partial_z f_2 \end{pmatrix} = \begin{pmatrix} e^x\cos y & -e^x\sin y & 0\\ z & 0 & x \end{pmatrix}.
$$
At `p=(1,\tfrac\pi2,1)` (`\cos\tfrac\pi2=0`, `\sin\tfrac\pi2=1`, `e^1=e`):
$$
df_p = \begin{pmatrix} 0 & -e & 0\\ 1 & 0 & 1 \end{pmatrix}.
$$
`p` is **regular** iff `df_p` is surjective, i.e. `\operatorname{rank}(df_p)=2`. The `2\times2` minor in
columns `1,2` is `\det\begin{psmallmatrix}0&-e\\1&0\end{psmallmatrix}=e\ne0`, so the rank is `2` and `df_p`
is onto `\mathbb R^2`. **Yes, `p` is a regular point.**

### (b) `W=f^{-1}(0,1)` is a manifold; parametrization near `p`

`W=\{(x,y,z): e^x\cos y=0,\ xz=1\}`. Since `e^x>0`, the first equation gives `\cos y=0`, i.e.
`y\in\{\tfrac\pi2+k\pi\}`; the second gives `x\ne0`, `z=1/x`.

**`(0,1)` is a regular value.** At any point of `W` we have `\cos y=0`, hence `\sin y=\pm1`, and `x\ne0`, so
$$
Df = \begin{pmatrix} 0 & \mp e^x & 0\\ 1/x & 0 & x \end{pmatrix},
$$
whose columns-`1,2` minor is `\det\begin{psmallmatrix}0&\mp e^x\\ 1/x&0\end{psmallmatrix}=\pm e^x/x\ne0`. So
every point of `W` is regular, i.e. `(0,1)` is a regular value. By the **regular value theorem**, `W` is a
smooth submanifold of `\mathbb R^3` of dimension `3-2=1` — a `1`-manifold. **Yes, `W` is a manifold.**

**Parametrization near `p`.** Near `p`, `\cos y=0` has the unique solution `y=\tfrac\pi2` (the solutions are
isolated, so `y` is locally constant). Thus, with `xz=1`,
$$
\boxed{\ \gamma(t) = \big(t,\ \tfrac\pi2,\ 1/t\big), \qquad t \text{ near } 1\ }
$$
is an explicit parametrization of `W` near `p`. Indeed `\gamma(1)=(1,\tfrac\pi2,1)=p`,
`f(\gamma(t))=(e^t\cos\tfrac\pi2,\ t\cdot\tfrac1t)=(0,1)`, and `\gamma'(t)=(1,0,-1/t^2)\ne0`, so `\gamma` is a
smooth immersed curve covering `W` near `p`.

### (c) Submersion normal form: yes, such `\varphi,\psi` exist

**Yes.** By part (a), `f` is a submersion at `p` (`df_p` has full rank `2`); rank is locally constant at full
rank, so `f` has constant rank `2` near `p`. The **submersion normal form theorem** (a consequence of the
inverse function theorem) then provides local diffeomorphisms putting `f` into the projection form — we
construct them explicitly.

**Complete `f` to a local diffeomorphism.** Define
$$
\Phi:\mathbb R^3\to\mathbb R^3, \qquad \Phi(x,y,z)=\big(f_1,\,f_2,\,z\big)=\big(e^x\cos y,\ xz,\ z\big),
$$
appending the `z`-coordinate. Its Jacobian at `p`,
$$
D\Phi_p = \begin{pmatrix} 0 & -e & 0\\ 1 & 0 & 1\\ 0 & 0 & 1 \end{pmatrix}, \qquad \det D\Phi_p = 1\cdot\det\begin{pmatrix}0&-e\\1&0\end{pmatrix} = e \ne 0,
$$
is invertible, so by the **inverse function theorem** `\Phi` is a diffeomorphism of a neighborhood of `p`
onto a neighborhood of `\Phi(p)=(0,1,1)`.

**Read off `\varphi,\psi`.** Define
$$
\varphi(x,y,z) = \Phi^{-1}(x,\,y+1,\,z+1), \qquad \psi(u,v) = (u,\,v-1).
$$
Then `\varphi` is a diffeomorphism from a neighborhood of the origin in `\mathbb R^3` onto a neighborhood of
`p` (since `\varphi(0,0,0)=\Phi^{-1}(0,1,1)=p`), and `\psi` is a diffeomorphism from a neighborhood of
`(0,1)\in\mathbb R^2` onto a neighborhood of the origin (`\psi(0,1)=(0,0)`). Because `f` is the first two
components of `\Phi` (i.e. `f=\pi_{12}\circ\Phi` where `\pi_{12}(a,b,c)=(a,b)`),
$$
f\big(\varphi(x,y,z)\big) = f\big(\Phi^{-1}(x,y+1,z+1)\big) = \pi_{12}\big(\Phi\Phi^{-1}(x,y+1,z+1)\big) = (x,\ y+1),
$$
and therefore
$$
\psi\circ f\circ\varphi(x,y,z) = \psi(x,\,y+1) = (x,\,y).
$$
So the required diffeomorphisms exist (with the explicit formulas above). ∎

**Remark.** All three parts are facets of one fact: a **regular point is a submersion point**, and near such
a point `f` is, up to diffeomorphism, the linear projection `(x,y,z)\mapsto(x,y)`. Part (a) checks the
full-rank (surjectivity) condition; part (b) is the *fiber* side of the same coin — the level set `f^{-1}(c)`
through a regular value is a manifold of dimension `\dim(\text{source})-\dim(\text{target})=1`, here the curve
`xz=1` frozen at `y=\pi/2`; part (c) is the *normal-form* side — the projection model is achieved by
completing `f` with extra coordinates (here `z`) into a local diffeomorphism. The reason such `\varphi,\psi`
exist is precisely that `p` is regular: had `p` been a critical point, no choice of diffeomorphisms could
make `f` a submersion locally, since rank is a diffeomorphism invariant.
