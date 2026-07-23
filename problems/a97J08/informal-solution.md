<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J08: Zeros are stable under locally uniform convergence (Rouché + Hurwitz)

## Why It's Hard

The conclusion is a statement about *integers* — the number of zeros, counted with
multiplicity, enclosed by $\Gamma$ — but the hypothesis is *analytic and
approximate*: $f_n \to g$ uniformly on compact sets. Zero-counts are notoriously
unstable to sloppy limits: under a bad limiting process zeros can collide, split,
escape to the boundary, or wink in and out. So the heart of the problem is
converting "the functions are eventually close" into "the integer counts are
eventually equal," and doing so requires three things to line up:

1. **The limit must itself be analytic.** Otherwise "zeros of $g$" is not even an
   analytic-function question. This is the Weierstrass convergence theorem.

2. **The interior of $\Gamma$ must actually live inside $D$.** We are told $f_n, g$
   are analytic on $D$ and that $\Gamma \subset D$, but Rouché / the argument
   principle need analyticity on the *closed region bounded by* $\Gamma$. That the
   inside of a Jordan curve drawn in a simply connected domain stays in the domain
   is a genuine topological fact, not a freebie — it is exactly where "simply
   connected" is used.

3. **A quantitative margin on the boundary.** Closeness of $f_n$ to $g$ only helps
   if $g$ is bounded *away from zero* on $\Gamma$; the assumption $g \neq 0$ on
   $\Gamma$ plus compactness supplies the margin $m = \min_\Gamma |g| > 0$ that the
   approximation must eventually beat.

The rectifiability of $\gamma$ is the regularity needed to make the relevant
contour integrals (winding numbers, argument-principle integrals) well-defined,
even though $\gamma$ need not be smooth.

## The Key Insight

There is a positive distance between $g$ and $0$ along $\Gamma$: by compactness of
$\Gamma$ and continuity and non-vanishing of $g$,
$$m := \min_{z \in \Gamma} |g(z)| > 0.$$
Locally uniform convergence forces $f_n \to g$ uniformly on the compact set
$\Gamma$, so eventually the *error* $|f_n - g|$ on $\Gamma$ is smaller than this
margin $m$ — and hence smaller than $|g|$ itself, pointwise on $\Gamma$:
$$|f_n(z) - g(z)| < |g(z)| \qquad (z \in \Gamma,\ n \ge N).$$
That single inequality is precisely the hypothesis of **Rouché's theorem**, whose
conclusion is that $f_n = g + (f_n - g)$ and $g$ enclose the same number of zeros.
(Equivalently: the zero-count is an integer-valued contour integral via the
**argument principle**, and a continuous integer is eventually constant.)

## Complete Proof

Throughout, "number of zeros inside $\Gamma$" means the number counted with
multiplicity in the bounded open region enclosed by the Jordan curve $\Gamma$.

**Step 0: $g$ is analytic on $D$.** A sequence of analytic functions converging
uniformly on compact subsets of an open set has an analytic limit (Weierstrass
convergence theorem: by Morera's theorem the limit is analytic, since
$\oint_T g = \lim_n \oint_T f_n = 0$ for every triangle $T$ contained in $D$, using
uniform convergence on the compact $T$). So $g$ is analytic on $D$, and "zeros of
$g$" is a meaningful analytic question.

**Step 1: The closed region bounded by $\Gamma$ lies in $D$.** Since $\gamma$ is a
simple closed curve, the Jordan curve theorem splits $\C \setminus \Gamma$ into a
bounded component $\Omega$ (the inside) and an unbounded component. We claim
$\Omega \subseteq D$, so that $\overline{\Omega} = \Omega \cup \Gamma$ is a compact
subset of $D$.

If $D = \C$ this is trivial. Otherwise work in the Riemann sphere
$\C_\infty = \C \cup \{\infty\}$. Because $D$ is simply connected and $D \neq \C$,
its complement $\C_\infty \setminus D$ is connected, and it contains $\infty$. Now
$\C_\infty \setminus D$ is disjoint from $\Gamma$ (as $\Gamma \subset D$), so this
connected set lies entirely in $\C_\infty \setminus \Gamma = \Omega \sqcup (\text{
outside})$; containing $\infty$, it must lie in the outside component. Hence no
point of $\C_\infty \setminus D$ lies in $\Omega$, i.e. $\Omega \subseteq D$. Thus
$\overline{\Omega} \subset D$ is compact, and both $g$ and every $f_n$ are analytic
on a neighborhood of $\overline{\Omega}$.

**Step 2: A positive margin on the boundary.** $g$ is continuous on the compact set
$\Gamma$ and $g(z) \neq 0$ there, so $|g|$ attains a positive minimum:
$$m := \min_{z \in \Gamma} |g(z)| > 0.$$

**Step 3: The approximation eventually beats the margin.** $\Gamma$ is a compact
subset of $D$, so the hypothesis gives $f_n \to g$ uniformly on $\Gamma$. Choose $N$
such that
$$n \ge N \quad\Longrightarrow\quad \sup_{z \in \Gamma} |f_n(z) - g(z)| < m.$$
Then for every $n \ge N$ and every $z \in \Gamma$,
$$|f_n(z) - g(z)| < m \le |g(z)|. \tag{$\ast$}$$
In particular $f_n(z) \neq 0$ on $\Gamma$ for $n \ge N$ (if $f_n(z) = 0$ then
$(\ast)$ reads $|g(z)| < |g(z)|$), so the zero-count of $f_n$ inside $\Gamma$ is
itself well-defined — there are no zeros sitting on the contour.

**Step 4: Rouché's theorem.** Fix $n \ge N$. The functions $g$ and $f_n$ are
analytic on the neighborhood of $\overline{\Omega}$ from Step 1, and on the
rectifiable Jordan curve $\Gamma$ they satisfy the strict inequality $(\ast)$,
$$|f_n(z) - g(z)| < |g(z)|.$$
By Rouché's theorem, $g$ and $f_n = g + (f_n - g)$ have the **same number of zeros**
(with multiplicity) inside $\Gamma$. Since $n \ge N$ was arbitrary, this $N$ works
for all $n \ge N$, which is exactly the claim. $\blacksquare$

**The mechanism, via the argument principle.** Rouché here is shorthand for an
integer-continuity argument that also proves it directly. For $n \ge N$ none of
$f_n, g$ vanish on $\Gamma$, so the zero counts are the contour integrals
$$Z_{f_n} = \frac{1}{2\pi i}\oint_\Gamma \frac{f_n'(z)}{f_n(z)}\,dz,
\qquad
Z_{g} = \frac{1}{2\pi i}\oint_\Gamma \frac{g'(z)}{g(z)}\,dz.$$
On $\Gamma$ we have $f_n \to g$ uniformly with $|g| \ge m > 0$, and by the
Weierstrass theorem $f_n' \to g'$ uniformly on $\Gamma$ as well (derivatives
converge locally uniformly), with $f_n$ bounded below by $m/2$ for large $n$ by
$(\ast)$. Hence $\frac{f_n'}{f_n} \to \frac{g'}{g}$ uniformly on $\Gamma$, the
integrals converge, and $Z_{f_n} \to Z_g$. But each $Z_{f_n}$ and $Z_g$ is a
nonnegative integer, and an integer sequence converging to an integer is eventually
constant; so $Z_{f_n} = Z_g$ for all large $n$ — the same conclusion. This is the
content of Hurwitz's theorem.

**Remark.** The non-vanishing of $g$ on $\Gamma$ is essential, not cosmetic: it both
guarantees the boundary margin $m > 0$ and rules out the degenerate case where a
zero of the limit sits exactly on the contour, where the count "inside" would be
ill-posed and could genuinely jump in the limit.
