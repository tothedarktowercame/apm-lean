# APM a93J07: A locally uniform limit of zero-free analytic functions is zero-free or identically zero

## Why It's Hard

Uniform convergence on compacta is a strong hypothesis for analytic functions, but
"having no zeros" is not obviously preserved by it: zeros can march in from the boundary,
and a limit can acquire a zero that none of the approximants had. The functions
$f_n(z) = z + 1/n$ on the unit disc are zero-free for $n \ge 2$, converge uniformly on
compacta to $f(z) = z$, which does vanish — except that this is not a counterexample,
because those $f_n$ *do* have a zero, at $-1/n$, which is in the disc for large $n$. Getting
the statement right requires an argument that counts zeros rather than merely detecting
them, and that can see a zero of the limit reflected back into the approximants. The
dichotomy in the conclusion is also essential: the constant sequence $f_n \equiv 0$ is not
zero-free, so the second alternative cannot be dropped.

## The Key Insight

Zeros of a nonzero analytic function on a domain are isolated. So if the limit $f$ is not
identically zero but vanishes at $z_0$, we can draw a small circle around $z_0$ on which
$f$ has a strictly positive minimum modulus $\delta$. Uniform convergence on that compact
circle eventually makes $|f_n - f| < \delta \le |f|$ there, and Rouché's theorem then says
$f_n$ and $f$ have the *same number* of zeros inside — at least one. That contradicts
$f_n$ being zero-free. Rouché is what converts a statement about sizes on a circle into a
statement about zeros inside it.

## Complete Proof

**Theorem.** Let $D \subseteq \mathbb{C}$ be a domain (a nonempty connected open set) and let
$\{f_n\}$ be analytic and zero-free on $D$. Suppose $f_n \to f$ uniformly on compact subsets
of $D$. Then either $f$ has no zeros in $D$, or $f \equiv 0$ on $D$.

**Proof.**

**Step 1: $f$ is analytic on $D$.** Let $\Delta \subset D$ be any closed triangle. Its boundary
is compact, so $f_n \to f$ uniformly on $\partial\Delta$, and $f$ is continuous there as a
uniform limit of continuous functions. Each $f_n$ is analytic, so $\oint_{\partial\Delta} f_n\,dz = 0$
by Cauchy's theorem, and uniform convergence permits passing to the limit under the
integral:

$$\oint_{\partial\Delta} f\,dz = \lim_{n \to \infty} \oint_{\partial\Delta} f_n\,dz = 0 .$$

Since $f$ is continuous on $D$ and its integral over the boundary of every triangle in $D$
vanishes, Morera's theorem gives that $f$ is analytic on $D$.

**Step 2: Set up the dichotomy.** Suppose $f \not\equiv 0$ on $D$, and suppose towards a
contradiction that $f(z_0) = 0$ for some $z_0 \in D$. We derive a contradiction; this
establishes that if $f \not\equiv 0$ then $f$ has no zero, which is the assertion.

**Step 3: Isolate the zero.** Since $D$ is connected and $f$ is analytic and not
identically zero on $D$, the identity theorem says the zero set of $f$ has no accumulation
point in $D$; that is, the zeros of $f$ are isolated. Hence there is $r > 0$ such that the
closed disc $\overline{D}(z_0, r) \subset D$ and

$$f(z) \ne 0 \quad \text{for all } z \text{ with } 0 < |z - z_0| \le r .$$

Let $C = \{z : |z - z_0| = r\}$, a compact subset of $D$ on which $f$ does not vanish, and put

$$\delta = \min_{z \in C} |f(z)| .$$

The minimum is attained and is strictly positive, because $|f|$ is continuous and
zero-free on the compact set $C$.

**Step 4: Apply Rouché on $C$.** By hypothesis $f_n \to f$ uniformly on the compact set $C$,
so there is $N$ with

$$|f_n(z) - f(z)| < \delta \le |f(z)| \qquad \text{for all } z \in C \text{ and all } n \ge N .$$

Fix any $n \ge N$. Writing $f_n = f + (f_n - f)$, the strict inequality $|f_n - f| < |f|$ on $C$ is
exactly the hypothesis of Rouché's theorem for the pair $f$ and $f_n$ on the disc
$D(z_0, r)$. Therefore $f$ and $f_n$ have the same number of zeros in $D(z_0, r)$, counted
with multiplicity.

**Step 5: Contradiction.** The function $f$ has at least one zero in $D(z_0, r)$, namely
$z_0$. Hence $f_n$ has at least one zero in $D(z_0, r) \subseteq D$. This contradicts the
hypothesis that $f_n$ is zero-free on $D$.

Therefore no such $z_0$ exists: if $f \not\equiv 0$ then $f$ has no zeros in $D$. Together with
the remaining case $f \equiv 0$, this is the claimed dichotomy. $\blacksquare$

## What Connects

This is Hurwitz's theorem, and the proof is the standard one: analyticity of the limit
from Morera, isolation of zeros from the identity theorem, and transfer of zero-counts by
Rouché. Connectedness of $D$ is used exactly once, in Step 3, and it is indispensable — on
a disjoint union of two discs one can take $f_n$ to be a fixed zero-free function on one
component and a sequence converging to $0$ on the other, so that the limit neither is
zero-free nor vanishes identically. The same Rouché argument proves the companion
statement that a locally uniform limit of injective analytic functions is injective or
constant, and it is the engine behind the compactness half of the Riemann mapping
theorem, where one must know that the limit of a sequence of injective maps does not
degenerate.
