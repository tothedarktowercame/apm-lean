<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t95A04: The Veronese map embeds ℝP² smoothly into ℝ⁶

## Why It's Hard

To prove `\tilde f:\mathbb{RP}^2\to\mathbb R^6` is a *smooth embedding onto a submanifold* one must verify a
whole package — smoothness, injectivity, the immersion (full-rank differential) condition — and then upgrade
to "embedding onto a submanifold." Each piece has its own snag:

- **Smoothness on `\mathbb{RP}^2`** is not automatic from smoothness of `f` on `S^2`: one must use that the
  quotient `\pi:S^2\to\mathbb{RP}^2` is a local diffeomorphism, so `\tilde f` inherits smoothness through
  local sections.
- **Injectivity** is the clever part. The *squares* `x_i^2` only recover each coordinate **up to sign**, so
  they alone cannot distinguish a point from a coordinate-flipped one. The **cross terms** `x_ix_j` are
  exactly what tie the signs together, forcing two points with the same image to differ by a *global* sign,
  i.e. to be the same point of `\mathbb{RP}^2`.
- **The immersion condition** is a Jacobian computation, cleanest when one recognizes `f` as the *symmetric
  square* `x\mapsto x\odot x`, whose differential `v\mapsto x\odot v` has trivial kernel for `x\ne0`.
- Finally, **compactness of `\mathbb{RP}^2`** is what turns an injective immersion into a genuine embedding
  onto a submanifold for free — without it an injective immersion can fail to be an embedding.

## The Key Insight

`f(x)=(x_0^2,x_1^2,x_2^2,x_0x_1,x_0x_2,x_1x_2)` records the symmetric matrix `xx^{\mathsf T}` (its `6`
independent entries), and `f(-x)=f(x)`, so `\tilde f` is well defined on `\mathbb{RP}^2`. Then:

- **Injective:** `f(x)=f(y)` gives `x_i^2=y_i^2` (so `y_i=\pm x_i`) *and* `x_ix_j=y_iy_j`; the cross terms
  force all signs equal, so `y=\pm x`, i.e. `[x]=[y]`.
- **Immersion:** `Df(x)v=0\iff xv^{\mathsf T}+vx^{\mathsf T}=0`; right-multiplying by `x` gives `v\parallel
  x`, and then `2xx^{\mathsf T}=0` forces `v=0`. So `Df(x)` is injective for `x\ne0`, hence `\tilde f` is an
  immersion.
- **Embedding:** an injective immersion from the **compact** `\mathbb{RP}^2` is a homeomorphism onto its
  image (continuous injection compact `\to` Hausdorff) and the image is a submanifold.

## Complete Proof

Let `\pi:S^2\to\mathbb{RP}^2` be the antipodal quotient (a smooth `2`-fold covering, hence a local
diffeomorphism), and `f:S^2\to\mathbb R^6`,
`f(x)=(x_0^2,x_1^2,x_2^2,x_0x_1,x_0x_2,x_1x_2)`. Since `f(-x)=f(x)`, `f` is constant on the fibers `\{x,-x\}`
of `\pi`, so it factors as `f=\tilde f\circ\pi` for a unique map `\tilde f:\mathbb{RP}^2\to\mathbb R^6`.

### Step 1: `\tilde f` is smooth

`f` is smooth (its components are polynomials). Because `\pi` is a local diffeomorphism, each `[x]\in
\mathbb{RP}^2` has a neighborhood on which `\pi` admits a smooth local inverse (section) `s`, and there
`\tilde f=\tilde f\circ\pi\circ s=f\circ s` is a composition of smooth maps. Hence `\tilde f` is smooth.

### Step 2: `\tilde f` is injective

Suppose `\tilde f([x])=\tilde f([y])`, i.e. `f(x)=f(y)` for `x,y\in S^2`. Comparing components:
$$
x_i^2 = y_i^2 \ (i=0,1,2), \qquad x_ix_j = y_iy_j \ (i<j).
$$
From the squares, `y_i=\varepsilon_i x_i` with `\varepsilon_i\in\{+1,-1\}` for each `i` (when `x_i=0` then
`y_i=0` too, and we may take `\varepsilon_i=+1`). Since `x\in S^2` is nonzero, fix an index `k` with `x_k\ne
0`. For any `j` with `x_j\ne0`, the cross-term equation gives
$$
x_kx_j = y_ky_j = (\varepsilon_k x_k)(\varepsilon_j x_j) = \varepsilon_k\varepsilon_j\,x_kx_j,
$$
and dividing by `x_kx_j\ne0` yields `\varepsilon_k\varepsilon_j=1`, i.e. `\varepsilon_j=\varepsilon_k`. So all
signs at nonzero coordinates equal a common `\varepsilon:=\varepsilon_k`, and at zero coordinates the value
matches regardless. Hence `y=\varepsilon x=\pm x`, so `[x]=[y]` in `\mathbb{RP}^2`. Thus `\tilde f` is
injective.

### Step 3: `\tilde f` is an immersion

It suffices to show the differential of `\tilde f` is injective at each point; since `\pi` is a local
diffeomorphism, this is equivalent to `df_x:T_xS^2\to\mathbb R^6` being injective, for which it is enough that
the full Jacobian `Df(x):\mathbb R^3\to\mathbb R^6` is injective at each `x\in S^2`.

Differentiating, for `v=(v_0,v_1,v_2)`,
$$
Df(x)v = \big(2x_0v_0,\,2x_1v_1,\,2x_2v_2,\ x_0v_1+x_1v_0,\ x_0v_2+x_2v_0,\ x_1v_2+x_2v_1\big).
$$
These six numbers are exactly the independent entries of the symmetric `3\times3` matrix `xv^{\mathsf
T}+vx^{\mathsf T}`. So
$$
Df(x)v = 0 \iff xv^{\mathsf T}+vx^{\mathsf T}=0 .
$$
Right-multiply this matrix equation by `x`:
$$
x\,(v^{\mathsf T}x) + v\,(x^{\mathsf T}x) = (v\cdot x)\,x + |x|^2\,v = 0,
$$
so `v=-\dfrac{v\cdot x}{|x|^2}\,x`, i.e. `v=\lambda x` for some scalar `\lambda` (here `|x|=1`). Substituting
back, `xv^{\mathsf T}+vx^{\mathsf T}=2\lambda\,xx^{\mathsf T}`, which vanishes (for `x\ne0`, so `xx^{\mathsf
T}\ne0`) only if `\lambda=0`, giving `v=0`. Therefore `\ker Df(x)=\{0\}`: `Df(x)` is injective for every
`x\in S^2`. In particular its restriction `df_x` to `T_xS^2` is injective, so `\tilde f` is an **immersion**.

### Step 4: `\tilde f` is an embedding onto a submanifold

`\mathbb{RP}^2` is **compact** (a quotient of the compact `S^2`), and `\mathbb R^6` is Hausdorff. `\tilde f`
is a continuous injection (Steps 1–2) from a compact space to a Hausdorff space, hence a **homeomorphism onto
its image** (a continuous bijection from compact to Hausdorff is a homeomorphism). Combined with `\tilde f`
being a smooth **immersion** (Step 3), the standard theorem — *an injective immersion of a compact manifold
is a smooth embedding, and its image is an embedded submanifold* — applies. Therefore
$$
\tilde f:\mathbb{RP}^2 \to \mathbb R^6
$$
is a **smooth embedding onto a submanifold** of `\mathbb R^6`. ∎

**Remark.** This is the **Veronese embedding**: `f` sends `x` to the symmetric tensor `x\odot x`
(equivalently the matrix `xx^{\mathsf T}`), and the antipodal invariance `f(-x)=f(x)` is precisely why it
descends to `\mathbb{RP}^2` — a point of `\mathbb{RP}^2` is a line `\pm x`, and `xx^{\mathsf T}` is the
orthogonal projection onto that line, an honest function of the line. Injectivity says "the projection matrix
remembers its line," and the immersion computation says the assignment line `\mapsto` projection is an
immersion. Compactness then hands over the embedding for free; without it (e.g. the figure-eight injective
immersion of a line) an injective immersion can have a non-submanifold image. The image actually lies in the
`5`-dimensional affine slice `\{x_0^2+x_1^2+x_2^2=1\}` (the trace-one projections), recovering the classical
fact that `\mathbb{RP}^2` embeds in `\mathbb R^5`.
