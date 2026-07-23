<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J05: Taylor coefficients converge to minus the residue of the nearest pole

## Why It's Hard

The statement links two things that look unrelated at first glance: a **local** datum (the residue $A$ of $f$ at the single pole $z=1$) and a **global asymptotic** (the limit of the Maclaurin coefficients $a(n)$ as $n\to\infty$). There is no direct formula reading $\lim a(n)$ off of $A$ by inspection.

The naive attack — write $a(n) = \frac{1}{2\pi i}\oint_{|z|=r} \frac{f(z)}{z^{n+1}}\,dz$ and try to estimate — stalls, because the only contour available to the bare series is $|z| = r < 1$, and on such contours $|f|$ blows up as $r \to 1$ (the pole sits *on the boundary* $|z|=1$ of the disk of convergence). You cannot push the contour past the pole without accounting for it.

The real content is the principle that **the singularity nearest the origin controls the growth of the coefficients**. Here the nearest singularity is a simple pole exactly on the circle of convergence, which is precisely why the coefficients converge to a nonzero constant rather than decaying or blowing up. Recognizing that you must *remove* that pole — and that doing so reveals both the value $-A$ and the rate of convergence — is the crux.

## The Key Insight

Subtract off the **principal part** of the pole. Near $z=1$ a simple pole with residue $A$ means $f(z) = \dfrac{A}{z-1} + (\text{analytic})$. So define
$$g(z) := f(z) - \frac{A}{z-1}.$$
The singular part cancels, so $g$ extends analytically across $z=1$ and is therefore analytic on the **entire** disk $|z|<2$.

Two consequences interlock:

1. The principal part has an explicit geometric expansion on $|z|<1$:
$$\frac{A}{z-1} = -\frac{A}{1-z} = -A\sum_{n=0}^\infty z^n,$$
so it contributes the *constant* coefficient $-A$ to every power of $z$. Hence the Taylor coefficients $b(n)$ of $g$ are exactly $b(n) = a(n) + A$.

2. Because $g$ is analytic on all of $|z|<2$, its radius of convergence is $\ge 2$, which forces $b(n) \to 0$ (in fact geometrically). 

Combine: $a(n) + A = b(n) \to 0$, i.e. $a(n) \to -A$. The "$-A$" is nothing but the coefficient handed over by the geometric series of the principal part.

## Complete Proof

**Setup.** By hypothesis $f$ is analytic on $D_2 := \{|z|<2\}$ except for a simple (order-1) pole at $z=1$ with residue $A$, and on the unit disk $\{|z|<1\}$ it is represented by its Maclaurin series $f(z) = \sum_{n=0}^\infty a(n)\,z^n$.

### Step 1 — Remove the pole

Define
$$g(z) := f(z) - \frac{A}{z-1}, \qquad z \in D_2 \setminus \{1\}.$$
Since the pole at $z=1$ is simple with residue $A$, the Laurent expansion of $f$ about $z=1$ is
$$f(z) = \frac{A}{z-1} + c_0 + c_1(z-1) + c_2(z-1)^2 + \cdots$$
valid in a punctured neighborhood of $1$. Subtracting $\dfrac{A}{z-1}$ cancels the only negative-index term, so
$$g(z) = c_0 + c_1(z-1) + c_2(z-1)^2 + \cdots$$
near $z=1$. Thus $z=1$ is a **removable singularity** of $g$, and after filling in the value $g(1)=c_0$, the function $g$ is analytic on **all** of $D_2 = \{|z|<2\}$ — the pole of $f$ and the pole of $A/(z-1)$ exactly annihilate each other, and there are no other singularities in $D_2$.

### Step 2 — Identify the Taylor coefficients of $g$

For $|z|<1$ the geometric series gives
$$\frac{A}{z-1} = -\frac{A}{1-z} = -A\sum_{n=0}^\infty z^n,$$
converging absolutely. On the same disk $f(z) = \sum_{n=0}^\infty a(n) z^n$. Subtracting termwise (both series converge absolutely on $|z|<1$),
$$g(z) = f(z) - \frac{A}{z-1} = \sum_{n=0}^\infty a(n) z^n + A\sum_{n=0}^\infty z^n = \sum_{n=0}^\infty \big(a(n) + A\big)\,z^n, \qquad |z|<1.$$
By uniqueness of power-series (Taylor) coefficients, the Maclaurin coefficients $b(n)$ of $g$ at the origin are
$$b(n) = a(n) + A \qquad \text{for all } n \ge 0. \tag{$\star$}$$

### Step 3 — The coefficients of $g$ tend to $0$

Because $g$ is analytic on the disk $D_2 = \{|z|<2\}$, its Maclaurin series converges throughout $D_2$; equivalently, its radius of convergence satisfies $R \ge 2$.

Fix any radius $r$ with $1 < r < 2$. The circle $|z| = r$ lies inside $D_2$, where $g$ is continuous, so
$$M(r) := \max_{|z|=r} |g(z)| < \infty.$$
By **Cauchy's coefficient estimates** (from $b(n) = \frac{1}{2\pi i}\oint_{|z|=r}\frac{g(z)}{z^{n+1}}\,dz$),
$$|b(n)| \le \frac{M(r)}{r^n} \qquad (n \ge 0).$$
Since $r > 1$, we have $r^n \to \infty$, hence
$$b(n) \to 0 \qquad \text{as } n \to \infty$$
(indeed geometrically, like $r^{-n}$ for any $r<2$).

### Step 4 — Conclude

Combining $(\star)$ with Step 3,
$$a(n) + A = b(n) \longrightarrow 0,$$
therefore
$$\boxed{\;\lim_{n\to\infty} a(n) = -A.\;} \qquad \blacksquare$$

### Remark — what makes it work

The argument is an instance of *singularity analysis*: the asymptotics of $a(n)$ are dictated by the singularity of $f$ nearest the origin. Subtracting the principal part of that singularity (here $A/(z-1)$, whose own coefficients are the constant $-A$) leaves a function analytic out to the *next* singularity, at radius $2$. The new radius of convergence $\ge 2 > 1$ is exactly what makes the residual coefficients decay, pinning $a(n)$ to the constant $-A$. Had the pole been of higher order, the same subtraction-of-principal-part technique would produce polynomial-in-$n$ growth governed by the higher Laurent coefficients.
