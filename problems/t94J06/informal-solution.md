<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94J06: z⁴+5z³+iz³+cos|z|=0 has a root — a winding-number argument (the equation is not holomorphic)

## Why It's Hard

The instinct is Rouché's theorem or the argument principle, but **the equation is not holomorphic**: the term
`\cos|z|` depends on `|z|=\sqrt{x^2+y^2}`, which is real-analytic, *not* complex-analytic. So Rouché and the
argument principle — both of which require holomorphy — **do not directly apply**, and one cannot simply
count zeros by a contour integral.

The escape is to recognize that "the equation has a root" is fundamentally a **topological / degree**
statement, needing only **continuity**:

- The function `f(z)=z^4+(5+i)z^3+\cos|z|` is continuous on `\mathbb C`, and on a large circle the leading
  term `z^4` **dominates** everything else (the cubic grows like `R^3\ll R^4`, and `\cos|z|` is *bounded* by
  `1`). So `f` restricted to that circle is homotopic, through nonvanishing maps, to `z\mapsto z^4`, which has
  **winding number `4`** about the origin.
- A continuous map on a disk whose boundary has *nonzero* winding number about `0` must **vanish** somewhere
  inside (otherwise the boundary map would extend over the contractible disk into `\mathbb C\setminus\{0\}`
  and have winding number `0`).

The key realization is that the bounded, non-holomorphic perturbation `\cos|z|` is invisible to the degree —
it cannot change the winding number set by the dominant `z^4`.

## The Key Insight

Let `f(z)=z^4+(5+i)z^3+\cos|z|`, continuous on `\mathbb C`. On `|z|=R` with `R` large,
$$
|f(z)-z^4| = \big|(5+i)z^3+\cos|z|\big| \le \sqrt{26}\,R^3 + 1 < R^4 = |z^4|,
$$
so `f|_{|z|=R}` is homotopic to `z^4|_{|z|=R}` within `\mathbb C\setminus\{0\}`; hence its **winding number is
`4\ne0`**. A nonzero winding number on the boundary of the disk `|z|\le R` forces `f` to have a zero inside.

## Complete Proof

Combine the two cubic terms: `5z^3+iz^3=(5+i)z^3`, and write
$$
f(z) = z^4 + (5+i)z^3 + \cos|z|, \qquad z\in\mathbb C .
$$
`f` is **continuous** on `\mathbb C` (sums and products of continuous functions; `z\mapsto|z|` and
`\cos` are continuous). We seek a zero of `f`. *(Note: `\cos|z|` is not holomorphic, so we argue
topologically rather than by Rouché.)*

### Step 1: choose a large radius on which `z^4` dominates

Since `|5+i|=\sqrt{26}` and `|\cos|z||\le1`, for any `z` with `|z|=R`,
$$
|f(z)-z^4| = \big|(5+i)z^3+\cos|z|\big| \le |5+i|\,R^3 + |\cos|z|| \le \sqrt{26}\,R^3 + 1 .
$$
Choose `R` large enough that `R^4 > \sqrt{26}\,R^3 + 1` — e.g. `R=10` gives `R^4=10000` and
`\sqrt{26}\cdot1000+1<5100`. Then on the circle `C_R=\{|z|=R\}`,
$$
|f(z)-z^4| < R^4 = |z^4| . \tag{$\ast$}
$$

### Step 2: `f|_{C_R}` is homotopic to `z^4|_{C_R}` in `\mathbb C\setminus\{0\}`

Define the straight-line homotopy
$$
H:C_R\times[0,1]\to\mathbb C, \qquad H(z,t) = z^4 + t\big(f(z)-z^4\big),
$$
so `H(\cdot,0)=z^4` and `H(\cdot,1)=f`. `H` is continuous, and it **never vanishes** on `C_R`: by the reverse
triangle inequality and `(\ast)`,
$$
|H(z,t)| \ge |z^4| - t\,|f(z)-z^4| \ge R^4 - |f(z)-z^4| > 0 \qquad (z\in C_R,\ t\in[0,1]).
$$
Hence `H` is a homotopy *within `\mathbb C\setminus\{0\}`* from `z^4|_{C_R}` to `f|_{C_R}`. Since the
**winding number** about `0` (the degree of `g\mapsto g/|g|:C_R\to S^1`) is a homotopy invariant of maps into
`\mathbb C\setminus\{0\}`,
$$
\operatorname{wind}_0\big(f|_{C_R}\big) = \operatorname{wind}_0\big(z^4|_{C_R}\big) = 4 \ne 0 ,
$$
the last equality because `z=Re^{i\theta}\mapsto R^4 e^{4i\theta}` circles the origin `4` times as `\theta`
runs over `[0,2\pi]`.

### Step 3: nonzero boundary winding number forces an interior zero

Let `D=\{|z|\le R\}`, so `\partial D=C_R`. Suppose, for contradiction, that `f` has **no zero** in `D`. Then
`f:D\to\mathbb C\setminus\{0\}` is a continuous map from the disk into the punctured plane. Restricting to the
boundary, `f|_{C_R}` extends to the continuous map `f` over all of `D`; since `D` is contractible, `f|_{C_R}`
is **null-homotopic in `\mathbb C\setminus\{0\}}`** (contract `C_R` to a point inside `D` and carry the values
along by `f`). A null-homotopic loop has winding number
$$
\operatorname{wind}_0\big(f|_{C_R}\big) = 0 .
$$
This contradicts Step 2, where `\operatorname{wind}_0(f|_{C_R})=4`.

Therefore the assumption is false: `f` has a zero `z_0\in D`. That is, the equation
$$
z^4 + 5z^3 + iz^3 + \cos|z| = 0
$$
has a solution `z_0\in\mathbb C` (with `|z_0|\le R`). ∎

**Remark.** The argument is the topological skeleton of the fundamental theorem of algebra, and it is *robust*
precisely because it ignores holomorphy. Only two features of the extra terms mattered: the cubic is
lower-order (`R^3\ll R^4`) and `\cos|z|` is **bounded** — so neither can disturb the winding number `4` that
the dominant `z^4` imposes on large circles, and a nonzero winding number is an existence certificate for a
root. This is why "perturbing a degree-`n` polynomial by any bounded continuous function" still leaves a
zero: the degree (a homotopy invariant) is unmoved. By contrast, Rouché's *theorem* would let us also *count*
the roots (with multiplicity, inside `C_R`) — but only for holomorphic perturbations; here the bounded
non-holomorphic `\cos|z|` forces us down to the purely continuous, winding-number version, which still yields
existence.
