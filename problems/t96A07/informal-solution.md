<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96A07: A quadratic map S²→ℝ³ — descent to ℝP², a non-transverse axis, and infinitely many transverse planes via Sard

## Why It's Hard

The map `f(x,y,z)=(yz,xz,xy)` is even, so it descends to `\mathbb{RP}^2`, but the transversality questions
are where the work lies, and each is a different idea:

- **(b)** Deciding whether the `z`-axis `L` is transverse to `\bar f` requires checking *all* intersection
  points, and the answer is **no** for a structural reason: an entire curve (the equator) maps *into* `L`.
  Since `\dim\mathbb{RP}^2+\dim L=2+1=3=\dim\mathbb R^3`, a transverse preimage `\bar f^{-1}(L)` would be
  `0`-dimensional — but it contains the `1`-dimensional equator, so transversality fails. Seeing that a
  *positive-dimensional* preimage is the obstruction (rather than grinding every Jacobian) is the insight.
- **(c)** The plane question is the productive use of **Sard's theorem**, but only after the right
  translation: `f` is transverse to the horizontal plane `H_{z_0}=\{Z=z_0\}` **iff** `z_0` is a *regular
  value* of the height function `g=xy:S^2\to\mathbb R`. Then Sard gives that almost every `z_0` is regular,
  and one must *also* intersect with the **range** `g(S^2)=[-\tfrac12,\tfrac12]` to guarantee the plane meets
  `\operatorname{im}f`. Combining "regular values are co-null" with "the range has positive length" yields
  infinitely many good planes.

The trap in (c) is forgetting the non-empty-intersection requirement; Sard alone gives transverse planes,
but most of them might miss the image.

## The Key Insight

- **(a)** `f(-\mathbf x)=f(\mathbf x)` (each product `(-y)(-z)=yz`, etc.), so `f` is constant on antipodal
  pairs and factors as `\bar f:\mathbb{RP}^2\to\mathbb R^3`.
- **(b)** The equator `\{z=0\}` maps into `L`: `f(x,y,0)=(0,0,xy)\in L`. So `\bar f^{-1}(L)` contains a
  `1`-dimensional set, whereas transversality (complementary dimensions) would force a `0`-dimensional
  preimage. **Not transverse.**
- **(c)** `f\pitchfork H_{z_0}\iff z_0` is a regular value of `g=xy|_{S^2}`. By **Sard** the critical values
  form a measure-zero set, and `g(S^2)=[-\tfrac12,\tfrac12]`; so all but measure zero of the interval
  `(-\tfrac12,\tfrac12)` are regular values lying in the range — **infinitely many** transverse planes meeting
  `\operatorname{im}f`.

## Complete Proof

`S^2=\{x^2+y^2+z^2=1\}`, `f(x,y,z)=(yz,xz,xy)`.

### (a) `f` descends to `\bar f:\mathbb{RP}^2\to\mathbb R^3`

For `\mathbf x=(x,y,z)`,
$$
f(-\mathbf x) = f(-x,-y,-z) = \big((-y)(-z),\,(-x)(-z),\,(-x)(-y)\big) = (yz,xz,xy) = f(\mathbf x).
$$
So `f` is constant on each antipodal pair `\{\mathbf x,-\mathbf x\}`, i.e. on the fibers of the quotient
`\pi:S^2\to\mathbb{RP}^2=S^2/(\mathbf x\sim-\mathbf x)`. Hence `f` factors through a well-defined map
`\bar f:\mathbb{RP}^2\to\mathbb R^3`, `\bar f([\mathbf x])=f(\mathbf x)`, which is smooth (`\pi` is a local
diffeomorphism, so `\bar f=f\circ\pi^{-1}` locally). ∎

### (b) The `z`-axis is **not** transverse to `\bar f`

Let `L=\{(0,0,z):z\in\mathbb R\}` be the `z`-axis. We find `\bar f^{-1}(L)`. A point `f(x,y,z)=(yz,xz,xy)`
lies on `L` iff its first two coordinates vanish:
$$
yz=0 \quad\text{and}\quad xz=0 .
$$
On the **equator** `\{z=0\}` these hold automatically, and `f(x,y,0)=(0,0,xy)\in L`. So the entire equator
`E=\{(x,y,0):x^2+y^2=1\}` lies in `\bar f^{-1}(L)`; its image in `\mathbb{RP}^2` is a projective line
`\mathbb{RP}^1`, a `1`-dimensional submanifold.

Now a **dimension count**: `\dim\mathbb{RP}^2+\dim L=2+1=3=\dim\mathbb R^3`, so if `\bar f` were transverse to
`L`, the preimage `\bar f^{-1}(L)` would be a submanifold of dimension `2+1-3=0` — a discrete set. But it
contains the `1`-dimensional equator-line. Therefore `\bar f` is **not transverse** to `L`.

*(Direct confirmation at a generic equator point `p=(a,b,0)`, `ab\ne0`: with `Df=\begin{psmallmatrix}0&z&y\\
z&0&x\\ y&x&0\end{psmallmatrix}`, the tangent space `T_pS^2=p^\perp` has basis `v_A=(-b,a,0)` and
`v_B=(0,0,1)`, and `Df(p)v_A=(0,0,a^2-b^2)\in L`, `Df(p)v_B=(b,a,0)`. So `\operatorname{im}df_p\subseteq
\operatorname{span}\{(0,0,1),(b,a,0)\}`, and `\operatorname{im}df_p+T L` is only this `2`-dimensional space,
missing the `(a,-b,0)`-direction — not all of `\mathbb R^3`.)* ∎

### (c) Infinitely many horizontal planes transverse to `f` and meeting `\operatorname{im}f`

Let `H_{z_0}=\{(x,y,z):z=z_0\}`, a plane with tangent space the horizontal plane `\{(u,v,0)\}`. Write `g`
for the **height of `f`**, i.e. the third coordinate restricted to `S^2`:
$$
g:S^2\to\mathbb R, \qquad g(x,y,z) = xy .
$$

**Transversality ⟺ regular value.** `f` is transverse to `H_{z_0}` iff at every `p\in f^{-1}(H_{z_0})` the
image `\operatorname{im}df_p` is *not* contained in the horizontal tangent plane `T H_{z_0}` — equivalently,
`df_p` has nonzero vertical (`Z`-)component, i.e. `dg_p\ne0`. So
$$
f\pitchfork H_{z_0} \iff \text{every } p\in g^{-1}(z_0) \text{ is a regular point of } g \iff z_0 \text{ is a regular value of } g .
$$
(Indeed `H_{z_0}` is the level set `\{Z=z_0\}` of the submersion `(X,Y,Z)\mapsto Z`, and transversality to
this level set is exactly regularity of `z_0` for the composite `g=Z\circ f`.)

**Sard.** `g:S^2\to\mathbb R` is smooth, so by **Sard's theorem** its set of critical values has Lebesgue
measure zero in `\mathbb R`; call it `\Sigma`. Thus every `z_0\notin\Sigma` is a regular value, giving
`f\pitchfork H_{z_0}`.

**Meeting the image.** `H_{z_0}\cap\operatorname{im}f\ne\varnothing` iff `z_0\in g(S^2)` (the value `z_0` is
attained by the height `xy`). Since `S^2` is connected and `g` continuous, `g(S^2)` is an interval; the
maximum of `xy` on the unit sphere is `\tfrac12` (at `x=y=\tfrac1{\sqrt2},z=0`) and the minimum `-\tfrac12`,
so
$$
g(S^2) = \big[-\tfrac12,\ \tfrac12\big].
$$

**Combine.** The interval `(-\tfrac12,\tfrac12)` has positive length, while `\Sigma` has measure zero, so
$$
\big(-\tfrac12,\tfrac12\big)\setminus\Sigma
$$
has full measure in `(-\tfrac12,\tfrac12)`, hence is **uncountably infinite**. For every `z_0` in this set:
`z_0` is a regular value of `g`, so `f\pitchfork H_{z_0}`; and `z_0\in(-\tfrac12,\tfrac12)\subseteq g(S^2)`,
so `H_{z_0}\cap\operatorname{im}f\ne\varnothing`. Thus there are **infinitely many** horizontal planes that
are transverse to `f` and meet its image. ∎

**Remark.** The contrast between (b) and (c) is the contrast between a *coincidental* and a *generic*
position. The `z`-axis is special: the symmetry of `f` forces the whole equator onto it, so the intersection
is degenerate (positive-dimensional preimage) and transversality fails. Horizontal planes, by contrast, are a
`1`-parameter family `\{H_{z_0}\}`, and Sard guarantees that *almost all* of them meet `\operatorname{im}f`
cleanly — non-transversality happens only at the measure-zero set of critical values of the height `xy`
(here the extreme values `\pm\tfrac12` and any interior critical levels). This is the typical division of
labor in transversality theory: a single fixed target may be non-transverse, but within a generic family
almost every member is transverse, by Sard.
