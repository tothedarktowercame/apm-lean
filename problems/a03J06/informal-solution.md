# APM a03J06: Polynomial growth forces an entire function to be a polynomial

## Why It's Hard

Liouville's theorem is the case $m = 0$: a bounded entire function is constant. Here the
bound is allowed to grow, and the conclusion has to grow with it — degree at most $m$
rather than degree $0$. The hypothesis only controls $f$ outside the unit disc, so it says
nothing directly about the Taylor coefficients at the origin, which is where the
conclusion lives. Nothing about the local behaviour of $f$ is given; the whole argument
has to transport information from infinity back to a single point.

## The Key Insight

The Cauchy estimates do exactly that transport. If $f(z) = \sum_{k \ge 0} a_k z^k$, then for
every $R > 0$

$$|a_k| \le \frac{M(R)}{R^k}, \qquad M(R) = \sup_{|z| = R} |f(z)|.$$

The growth hypothesis gives $M(R) \le A R^m$ for $R > 1$, so $|a_k| \le A R^{m-k}$. The
exponent $m - k$ is negative precisely when $k > m$, and then letting $R \to \infty$ forces
$a_k = 0$. The bound is available for *every* large $R$, and that is what turns a growth
estimate into an exact vanishing statement.

## Complete Proof

**Theorem.** Let $f$ be entire and let $m$ be a positive integer. Suppose there is a
constant $A$ with $|f(z)| \le A|z|^m$ whenever $|z| > 1$. Then $f$ is a polynomial of degree
at most $m$.

**Proof.**

**Step 1: Expand $f$ in a power series valid on all of $\mathbb{C}$.** Since $f$ is entire, it
is analytic on every disc centred at the origin, so its Taylor series at $0$,

$$f(z) = \sum_{k=0}^{\infty} a_k z^k, \qquad a_k = \frac{f^{(k)}(0)}{k!},$$

converges to $f(z)$ for every $z \in \mathbb{C}$.

**Step 2: Cauchy's estimate.** Fix $R > 0$ and $k \ge 0$. By the Cauchy integral formula for
derivatives, applied on the circle $|z| = R$,

$$a_k = \frac{1}{2\pi i} \oint_{|z| = R} \frac{f(z)}{z^{k+1}}\,dz .$$

Estimating the integral by the length of the contour times the maximum of the integrand,

$$|a_k| \le \frac{1}{2\pi} \cdot 2\pi R \cdot \frac{M(R)}{R^{k+1}} = \frac{M(R)}{R^k},
\qquad M(R) = \sup_{|z| = R}|f(z)| .$$

**Step 3: Insert the growth hypothesis.** Let $R > 1$. Every $z$ with $|z| = R$ satisfies
$|z| > 1$, so the hypothesis gives $|f(z)| \le A|z|^m = A R^m$, whence $M(R) \le A R^m$.
Combining with Step 2,

$$|a_k| \le \frac{A R^m}{R^k} = A R^{m-k} \qquad \text{for every } R > 1 .$$

**Step 4: Let $R \to \infty$.** Suppose $k > m$. Then $m - k \le -1 < 0$, so $R^{m-k} \to 0$ as
$R \to \infty$. The left-hand side $|a_k|$ does not depend on $R$, so $|a_k| \le \inf_{R > 1} A R^{m-k} = 0$,
that is, $a_k = 0$.

**Step 5: Conclude.** Every coefficient of index $k > m$ vanishes, so the series of Step 1
terminates:

$$f(z) = \sum_{k=0}^{m} a_k z^k .$$

This is a polynomial of degree at most $m$. $\blacksquare$

## What Connects

The proof is the standard Liouville argument with the constant bound replaced by a
power. Taking $m = 0$ recovers Liouville's theorem verbatim, and the same computation with
$M(R) \le A R^{\alpha}$ for real $\alpha > 0$ shows $f$ is a polynomial of degree at most
$\lfloor \alpha \rfloor$. The mechanism — an estimate valid for arbitrarily large radii,
with a coefficient that is independent of the radius — is the same one behind the
Schwarz lemma and the Cauchy estimates for normal families. The restriction to $|z| > 1$
is harmless for exactly the reason exploited in Step 3: only large circles are ever used.
