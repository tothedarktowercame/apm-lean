<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97J07: Lefschetz fixed points of [z₀:z₁:3z₂] on ℂP² — a fixed line, and χ(ℂP²) = 3

## Why It's Hard

The map `g[z_0:z_1:z_2]=[z_0:z_1:3z_2]` is the projectivization of `\operatorname{diag}(1,1,3)`, and the
trap is that the eigenvalue `1` has **multiplicity 2**, so the fixed-point set is *not* a finite set of
isolated points: there is a whole **projective line** `\mathbb{CP}^1` fixed pointwise, plus one isolated
point. This forces the *generalized* Lefschetz fixed-point theorem (for clean fixed **submanifolds**), where
a fixed submanifold `N` contributes `\chi(N)` times a normal index, rather than the naive `\pm1`.

- **(a)** Fixed points are eigenlines of `\operatorname{diag}(1,1,3)`: the eigenvalue `3` gives an *isolated*
  point, but the eigenvalue `1` (multiplicity `2`) gives an entire `\mathbb{CP}^1`. Recognizing the
  positive-dimensional fixed locus is the key.
- **(b)** Computing local Lefschetz numbers requires the *normal* derivative. The decisive simplification is
  that `g` is **holomorphic**, so every relevant real determinant `\det(I-dg)` is `|\det_{\mathbb C}|^2>0` —
  *all signs are `+1`*. The isolated point contributes `+1`; the fixed line contributes `\chi(\mathbb{CP}^1)=2`.
- **(c)** The payoff: `g` is homotopic to the identity (`\operatorname{diag}(1,1,3)\in GL_3(\mathbb C)`,
  connected), so `L(g)=L(\mathrm{id})=\chi(\mathbb{CP}^2)`. Thus the *fixed-point count of this one map*
  computes the Euler characteristic.

## The Key Insight

`g` is the projectivization of `A=\operatorname{diag}(1,1,3)`. Its fixed points are the projectivized
eigenspaces:
$$
\text{eigenvalue }3:\ \ p=[0:0:1] \ (\text{isolated}); \qquad \text{eigenvalue }1:\ \ N=\{[z_0:z_1:0]\}\cong\mathbb{CP}^1 \ (\text{a fixed line}).
$$
Because `g` is **holomorphic**, all local indices are `+1` (real determinants of complex-linear maps are
positive). So the local Lefschetz numbers are
$$
L_p = +1, \qquad L_N = \chi(\mathbb{CP}^1)\cdot(+1) = 2 .
$$
Since `g\simeq\mathrm{id}`, `\chi(\mathbb{CP}^2)=L(g)=L_p+L_N=1+2=3`.

## Complete Proof

`g:\mathbb{CP}^2\to\mathbb{CP}^2`, `g[z_0:z_1:z_2]=[z_0:z_1:3z_2]`, the projectivization of
`A=\operatorname{diag}(1,1,3)`.

### (a) Fixed points

`g[z]=[z]` iff `A z=\lambda z` for some `\lambda\ne0`, i.e. `[z]` is an eigenline of `A`. The eigenvalues are
`1` (eigenspace `\{z_2=0\}`, complex dimension `2`) and `3` (eigenspace `\mathbb C\!\cdot\!e_2`, dimension `1`).
Projectivizing:

- **eigenvalue `3`:** the single point `p=[0:0:1]`;
- **eigenvalue `1`:** the *entire projective line* `N=\{[z_0:z_1:0]\}\cong\mathbb{CP}^1`, fixed pointwise
  (each `[z_0:z_1:0]\mapsto[z_0:z_1:0]`).

So `\operatorname{Fix}(g)=\{p\}\sqcup N` — an isolated point together with a `\mathbb{CP}^1`.

### (b) Local Lefschetz numbers

Throughout, `\mathbb{CP}^2` is a *real* `4`-manifold and `g` is holomorphic; the relevant determinants are
real determinants of complex-linear maps, and for any complex-linear invertible `T` on `\mathbb C^k`,
`\det_{\mathbb R}(T)=|\det_{\mathbb C}T|^2>0`. So every index sign below is `+1`.

**Isolated point `p=[0:0:1]`.** In the chart `z_2=1` with coordinates `(u_0,u_1)=(z_0/z_2,z_1/z_2)` (`p=0`),
`g[z_0:z_1:z_2]=[z_0:z_1:3z_2]` becomes
$$
g(u_0,u_1)=\Big(\tfrac{z_0}{3z_2},\tfrac{z_1}{3z_2}\Big)=\big(\tfrac{u_0}{3},\tfrac{u_1}{3}\big), \qquad dg_p=\operatorname{diag}\big(\tfrac13,\tfrac13\big).
$$
Then `I-dg_p=\tfrac23\,I` (multiplication by the complex scalar `\tfrac23` on `\mathbb C^2`), with
`\det_{\mathbb R}(I-dg_p)=|\tfrac23|^{4}>0`. The local Lefschetz number is
$$
L_p = \operatorname{sign}\det_{\mathbb R}(I-dg_p) = +1 .
$$

**Fixed line `N=\mathbb{CP}^1`.** This is a clean fixed submanifold: at a point `q\in N`, say `q=[1:0:0]`, use
the chart `z_0=1` with `(v_1,v_2)=(z_1/z_0,z_2/z_0)`, so `N=\{v_2=0\}`. Here
$$
g(v_1,v_2)=\big(\tfrac{z_1}{z_0},\tfrac{3z_2}{z_0}\big)=(v_1,\,3v_2), \qquad dg_q=\operatorname{diag}(1,3).
$$
The tangent direction `v_1` (eigenvalue `1`) is along `N` (`dg=\mathrm{id}` there, consistent with `N` being
fixed); the **normal** direction `v_2` has eigenvalue `3`, so `I-dg_\nu=(1-3)=-2` on the (complex
`1`-dimensional) normal space — invertible, so the fixed-point set is *nondegenerate in the normal
direction*. By the **Lefschetz fixed-point theorem for clean fixed submanifolds**, the local Lefschetz number
of `N` is
$$
L_N = \chi(N)\cdot\operatorname{sign}\det_{\mathbb R}(I-dg_\nu) .
$$
Now `\det_{\mathbb R}(I-dg_\nu)=|-2|^2=4>0`, so the sign is `+1`, and `\chi(N)=\chi(\mathbb{CP}^1)=\chi(S^2)=2`.
Hence
$$
L_N = 2\cdot(+1) = 2 .
$$

### (c) Euler characteristic of `\mathbb{CP}^2`

By the **Lefschetz–Hopf fixed point theorem** (with clean fixed-point set `\{p\}\sqcup N`),
$$
L(g) = L_p + L_N = 1 + 2 = 3 .
$$
On the other hand, `g` is **homotopic to the identity**: `A=\operatorname{diag}(1,1,3)` lies in
`GL_3(\mathbb C)`, which is path-connected, so a path `A_t` from `I` to `A` in `GL_3(\mathbb C)` induces a
homotopy `g_t` from `\mathrm{id}_{\mathbb{CP}^2}` to `g`. The Lefschetz number is a homotopy invariant, and
`L(\mathrm{id})=\chi(\mathbb{CP}^2)` (the Lefschetz number of the identity is the Euler characteristic).
Therefore
$$
\chi(\mathbb{CP}^2) = L(\mathrm{id}) = L(g) = L_p + L_N = 1 + 2 = \boxed{3}.
$$
(Consistent with `H_*(\mathbb{CP}^2;\mathbb Q)=\mathbb Q` in degrees `0,2,4`, giving `\chi=1+1+1=3`.) ∎

**Remark.** The computation is a clean illustration of two phenomena. First, **holomorphic maps have all
fixed-point indices `+1`**: `I-dg` is complex-linear, so its real determinant `|\det_{\mathbb C}|^2` is
automatically positive — there is no sign cancellation, in sharp contrast to real maps (cf. the diagonal
real map on `\mathbb{RP}^3`, where indices alternate `\pm1`). Second, when an eigenvalue is **repeated**, the
fixed locus is positive-dimensional and contributes its **own Euler characteristic** (`\chi(\mathbb{CP}^1)=2`)
rather than a single `\pm1`; the Lefschetz theorem localizes to the fixed submanifold with multiplicity
`\chi(N)`. The trick of part (c) — choosing a *convenient* map homotopic to the identity and counting its
fixed points — is the standard way the Lefschetz theorem computes Euler characteristics; here the count
`1+2=3` recovers `\chi(\mathbb{CP}^2)`, and the same scheme (`\operatorname{diag}(1,\dots,1,\lambda)` on
`\mathbb{CP}^n`) gives a point plus a fixed `\mathbb{CP}^{n-1}`, yielding `\chi(\mathbb{CP}^n)=1+\chi(\mathbb{CP}^{n-1})=n+1`.
