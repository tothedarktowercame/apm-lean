# APM a92J01: Four inclusions among $L^p$, $\ell^p$ and $C$ — one true, three false

## Why It's Hard

The four assertions look like instances of one pattern, and the temptation is to answer
them uniformly. They do not have a uniform answer: the first is true, the other three are
false, and the reason the first works is precisely the reason the others fail. Everything
turns on the measure space, not on the exponents. On $[0,1]$ the measure is finite, on
$\mathbb{Z}$ it is atomic with atoms of size $1$, and on $\mathbb{R}$ it is infinite and
non-atomic; each geometry breaks a different link. The fourth assertion adds a second
trap: elements of $L^p$ are equivalence classes, so "is contained in $C([0,1])$" has to be
read as "has a continuous representative", and a counterexample must rule out *every*
representative, not just the obvious one.

## The Key Insight

A single function family settles the first three. On a finite measure space, Hölder's
inequality gives $\|f\|_q \le \|f\|_p\, m(X)^{1/q - 1/p}$ for $q < p$, so large exponents
control small ones — the inclusion runs $L^p \subseteq L^q$. On $\ell^p$ the inclusion runs
the *other* way, because a sequence in $\ell^q$ has terms tending to $0$, and small terms
raised to a larger power only get smaller; the tail $n^{-1/q}$ separates the two. On
$\mathbb{R}$ neither inclusion holds, because the tail and the singularity can be tuned
independently; the same tail $x^{-1/q}$ pushed out to $[1,\infty)$ lies in $L^p$ and not in
$L^q$. For the last, no integrability hypothesis can produce continuity: an indicator
function is in every $L^p$ and differs from every continuous function on a set of positive
measure.

## Complete Proof

Throughout, $p > q \ge 1$, and $m$ denotes Lebesgue measure.

### (a) $L^p([0,1]) \subseteq L^q([0,1])$ — **true**

**Proof.** Let $f \in L^p([0,1])$. Apply Hölder's inequality to the pair $|f|^q \cdot 1$ with
exponents $r = p/q > 1$ and its conjugate $r' = r/(r-1)$:

$$\int_0^1 |f|^q \cdot 1 \,dm \ \le\ \left(\int_0^1 |f|^{qr}\,dm\right)^{1/r}\left(\int_0^1 1^{r'}\,dm\right)^{1/r'}
= \left(\int_0^1 |f|^{p}\,dm\right)^{q/p} \cdot 1 .$$

Hence $\|f\|_q^q \le \|f\|_p^q < \infty$, so $f \in L^q([0,1])$ and moreover $\|f\|_q \le \|f\|_p$.
The step $\int_0^1 1\,dm = 1 < \infty$ is where finiteness of the measure enters, and it is
the only place. $\blacksquare$

### (b) $\ell^p \subseteq \ell^q$ — **false**

**Counterexample.** Let $a = (a_n)_{n \ge 1}$ with $a_n = n^{-1/q}$.

*It is not in $\ell^q$:* $\sum_n |a_n|^q = \sum_n n^{-1}$, the harmonic series, which diverges.

*It is in $\ell^p$:* $\sum_n |a_n|^p = \sum_n n^{-p/q}$, and $p/q > 1$ since $p > q$, so this is a
convergent $p$-series.

Thus $a \in \ell^p \setminus \ell^q$, and the asserted inclusion fails. $\blacksquare$

**Remark.** The reverse inclusion $\ell^q \subseteq \ell^p$ *is* true for $q < p$: if
$\sum |a_n|^q < \infty$ then $|a_n| \to 0$, so $|a_n| \le 1$ for all large $n$, and for those $n$
we have $|a_n|^p \le |a_n|^q$. Counting measure on $\mathbb{Z}$ has no sets of small positive
measure, which is exactly the feature that reverses the inclusion relative to (a).

### (c) $L^p(\mathbb{R}) \subseteq L^q(\mathbb{R})$ — **false**

**Counterexample.** Let $f(x) = x^{-1/q}$ for $x \ge 1$ and $f(x) = 0$ otherwise.

*It is not in $L^q$:* $\int_{\mathbb{R}} |f|^q\,dm = \int_1^{\infty} x^{-1}\,dx = \infty$.

*It is in $L^p$:* $\int_{\mathbb{R}} |f|^p \,dm = \int_1^{\infty} x^{-p/q}\,dx$, which is finite because
$p/q > 1$.

Thus $f \in L^p(\mathbb{R}) \setminus L^q(\mathbb{R})$. $\blacksquare$

**Remark.** The reverse inclusion fails too, so on $\mathbb{R}$ the two spaces are
genuinely incomparable. For that direction take $g(x) = x^{-1/p}$ on $(0,1)$ and $0$
elsewhere: $\int_0^1 x^{-q/p}\,dx < \infty$ since $q/p < 1$, while $\int_0^1 x^{-1}\,dx = \infty$, so
$g \in L^q \setminus L^p$. Splitting $\mathbb{R}$ into a part of finite measure and a part where
the function is small is what makes both failures possible at once.

### (d) $L^p([0,1]) \subseteq C([0,1])$ for $p > 2$ — **false**

**Counterexample.** Let $f = \chi_{[0,1/2]}$, the indicator of $[0,1/2]$. Then
$\int_0^1 |f|^p \,dm = 1/2 < \infty$, so $f \in L^p([0,1])$ for every $p$.

Suppose some continuous $g \in C([0,1])$ satisfied $g = f$ almost everywhere. Consider the
point $1/2$. For every $\delta > 0$ the set $(1/2, 1/2 + \delta) \cap [0,1]$ has positive measure and
$f = 0$ on it, so $g$ takes the value $0$ somewhere in it; likewise $(1/2 - \delta, 1/2)$ has
positive measure with $f = 1$, so $g$ takes the value $1$ somewhere in it. Hence every
neighbourhood of $1/2$ contains points where $g$ equals $0$ and points where it equals $1$,
contradicting continuity of $g$ at $1/2$ (take $\varepsilon = 1/2$ in the definition). So no
continuous representative exists. $\blacksquare$

**Remark.** The restriction $p > 2$ is a red herring: no exponent makes the statement true,
since $\chi_{[0,1/2]}$ lies in $L^p$ for every $p \in [1, \infty]$. What *is* true is a Sobolev-type
statement about derivatives, not about the function itself: if $f$ and $f'$ both lie in
$L^p([0,1])$ with $p > 1$, then $f$ has a continuous — indeed Hölder — representative.

## What Connects

The single organising fact is that inclusions between $L^p$ spaces are a statement about
the measure space, not about the exponents. Finite measure gives $L^p \subseteq L^q$ for
$p > q$ (part a); a measure with no sets of arbitrarily small positive measure gives the
reverse, $\ell^q \subseteq \ell^p$ (part b); and a measure with both large total mass and
sets of small mass gives neither (part c). Part (d) is a different point entirely: $L^p$
membership is invariant under modification on null sets, and continuity is not, so no
implication from the first to the second can hold.
