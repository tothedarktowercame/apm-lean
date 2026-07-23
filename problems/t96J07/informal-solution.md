<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96J07: Lefschetz numbers of a diagonal projective map on ℝP³

## Why It's Hard

The map `f[x_0:x_1:x_2:x_3]=[x_0:2x_1:3x_2:4x_3]` is the projectivization of `A=\operatorname{diag}(1,2,3,4)`,
so its fixed points are forced by linear algebra (eigendirections), but extracting the *local* Lefschetz
numbers needs genuine differential topology done in **affine charts**:

- **Fixed points** are projective points fixed by `f`, i.e. eigenlines of `A`. Since the eigenvalues
  `1,2,3,4` are **distinct**, each eigenline is a coordinate axis, giving exactly the four coordinate points
  — no continuum of fixed points to worry about.
- **Local Lefschetz numbers** require the derivative `df_{p}` at each fixed point, and one must pass to an
  affine chart `x_i=1`, where `f` becomes the *linear* map whose diagonal entries are the **ratios**
  `c_j/c_i` of eigenvalues. The local index is then `\operatorname{sign}\det(I-df_p)`, and one must track
  which ratios exceed `1`.
- **The global `L(f)` must be consistent two ways**: as the sum of local indices (Lefschetz–Hopf) *and*
  homologically as `1-\deg(f)`. The check that these agree (both `0`) is a feature, not a coincidence: `ℝP^3`
  has rational homology only in degrees `0` and `3`, and `f` is an orientation-preserving degree-`1`
  diffeomorphism (`\det A=24>0`), which *pins* `L(f)=0` — so the four `\pm1` indices are forced to cancel.

## The Key Insight

`f` is the projectivization of `A=\operatorname{diag}(1,2,3,4)`. Its fixed points are the four coordinate
points `p_i=[e_i]` (distinct eigenvalues ⇒ eigenlines are the axes). In the chart `x_i=1`, `f` is the linear
map with diagonal entries `c_j/c_i` (`j\ne i`, `c=(1,2,3,4)`), so
$$
\text{local index } \iota_{p_i}=\operatorname{sign}\det\!\big(I-df_{p_i}\big)=\operatorname{sign}\prod_{j\ne i}\Big(1-\tfrac{c_j}{c_i}\Big).
$$
This gives `\iota_{p_0}=-1,\ \iota_{p_1}=+1,\ \iota_{p_2}=-1,\ \iota_{p_3}=+1`, so by Lefschetz–Hopf
$$
L(f)=\sum_i\iota_{p_i}=0,
$$
consistent with `L(f)=\operatorname{tr}(f_*|H_0)-\operatorname{tr}(f_*|H_3)=1-\deg(f)=1-1=0`.

## Complete Proof

Write `f:\mathbb{RP}^3\to\mathbb{RP}^3`, `f[x_0:x_1:x_2:x_3]=[x_0:2x_1:3x_2:4x_3]`, the projectivization of
`A=\operatorname{diag}(c_0,c_1,c_2,c_3)` with `(c_0,c_1,c_2,c_3)=(1,2,3,4)`.

### Fixed points

`f[x]=[x]` means `A x=\lambda x` for some `\lambda\ne0`, i.e. `(c_i-\lambda)x_i=0` for each `i`. Since the
`c_i` are **distinct**, for a fixed `\lambda` at most one `c_i` equals `\lambda`, so at most one coordinate
`x_i` is nonzero. Hence the fixed points are exactly the four coordinate points
$$
p_0=[1:0:0:0],\quad p_1=[0:1:0:0],\quad p_2=[0:0:1:0],\quad p_3=[0:0:0:1].
$$

### Local Lefschetz numbers

Near `p_i` use the affine chart `\{x_i\ne0\}`, normalizing `x_i=1` with the other three ratios as
coordinates. In this chart `f` divides every coordinate by the `i`-th eigenvalue, so it is the **linear** map
$$
(u_j)_{j\ne i}\ \longmapsto\ \Big(\tfrac{c_j}{c_i}\,u_j\Big)_{j\ne i}, \qquad df_{p_i}=\operatorname{diag}\Big(\tfrac{c_j}{c_i}\Big)_{j\ne i},
$$
with `p_i` the origin. Each fixed point is **nondegenerate** (no diagonal entry equals `1`, since the `c_j`
are distinct), and the local Lefschetz number is the fixed-point index
$$
\iota_{p_i}=\operatorname{sign}\det\!\big(I-df_{p_i}\big)=\operatorname{sign}\prod_{j\ne i}\Big(1-\tfrac{c_j}{c_i}\Big).
$$

Compute each (`I-df` is diagonal, so the determinant is the product of `1-c_j/c_i`):

- **`p_0`** (`c_0=1`): ratios `c_j/c_0 = 2,3,4`; `I-df=\operatorname{diag}(-1,-2,-3)`, `\det=-6<0`. So
  `\iota_{p_0}=-1`.
- **`p_1`** (`c_1=2`): ratios `c_j/c_1 = \tfrac12,\tfrac32,2`; `I-df=\operatorname{diag}(\tfrac12,-\tfrac12,-1)`,
  `\det=\tfrac14>0`. So `\iota_{p_1}=+1`.
- **`p_2`** (`c_2=3`): ratios `c_j/c_2 = \tfrac13,\tfrac23,\tfrac43`;
  `I-df=\operatorname{diag}(\tfrac23,\tfrac13,-\tfrac13)`, `\det=-\tfrac{2}{27}<0`. So `\iota_{p_2}=-1`.
- **`p_3`** (`c_3=4`): ratios `c_j/c_3 = \tfrac14,\tfrac12,\tfrac34`;
  `I-df=\operatorname{diag}(\tfrac34,\tfrac12,\tfrac14)`, `\det=\tfrac{3}{32}>0`. So `\iota_{p_3}=+1`.

$$
\boxed{\ \iota_{p_0}=-1,\quad \iota_{p_1}=+1,\quad \iota_{p_2}=-1,\quad \iota_{p_3}=+1.\ }
$$

(Intuition: at `p_i`, `df` scales the `j`-th direction by `c_j/c_i`; the factor `1-c_j/c_i` is negative when
`c_j>c_i` and positive when `c_j<c_i`, so the sign of the index is `(-1)^{\#\{j:\,c_j>c_i\}}` — the number
of "larger" eigenvalues. That count is `3,2,1,0` for `p_0,p_1,p_2,p_3`, giving signs `-,+,-,+`.)

### Global Lefschetz number

By the **Lefschetz–Hopf fixed point theorem** (the fixed points are isolated and nondegenerate),
$$
L(f) = \sum_{i=0}^3 \iota_{p_i} = (-1)+(+1)+(-1)+(+1) = \boxed{0}.
$$

**Homological check.** `\mathbb{RP}^3` is orientable, with rational homology `H_0=\mathbb Q`, `H_1=H_2=0`,
`H_3=\mathbb Q` (the integral `H_1=\mathbb Z/2` is torsion and vanishes rationally). Thus
$$
L(f)=\sum_k(-1)^k\operatorname{tr}\big(f_*\mid H_k(\mathbb{RP}^3;\mathbb Q)\big) = \operatorname{tr}(f_*|H_0) - \operatorname{tr}(f_*|H_3) = 1 - \deg(f).
$$
Now `f` is the projectivization of `A=\operatorname{diag}(1,2,3,4)` with `\det A=24>0`; since `GL_4^+(\mathbb
R)` is connected, `A` is joined to `I` by a path of positive-determinant matrices (e.g.
`\operatorname{diag}(1,1+t,1+2t,1+3t)`), inducing a homotopy `f\simeq\mathrm{id}`. Hence `\deg(f)=1` and
$$
L(f)=1-\deg(f)=1-1=0,
$$
agreeing with the sum of local indices. ∎

**Remark.** The local indices alternate `-,+,-,+` because the number of eigenvalues exceeding `c_i`
decreases by one as `i` increases — this is the projective shadow of a Morse function whose critical points
have indices `3,2,1,0`. That `L(f)=0` is not accidental: `\mathbb{RP}^3` has the rational homology of `S^3`
(a `\mathbb Q`-homology sphere), and any orientation-preserving degree-`1` self-map has `L=1-1=0`, so
*any* nondegenerate fixed points must cancel in signed count. Here the cancellation is exact, four points in
two `+`/`-` pairs. (A diagonal map with *positive distinct* eigenvalues always behaves this way; had some
ratio passed through `1`, fixed points would merge and degenerate, but distinctness keeps all four clean.)
