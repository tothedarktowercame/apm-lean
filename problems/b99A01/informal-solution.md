<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->
<!-- NOTE: the source b99A01.tex bundles TWO independent prelim problems: a complex-analysis
     maximum-principle statement (opening paragraph) and a 5-part valuation-domain problem
     (the alist (a)-(e)). Both are well-posed; both are proved below, in that order. -->


# APM b99A01: A boundary maximum principle on the half-plane, and the structure of valuation domains

## Why It's Hard

The source file holds two unrelated problems, each with its own snare. The
**analysis** problem — bounded continuous $f$ on $\overline{H}$, analytic on the
open upper half-plane, with $|f|\le M$ on $\mathbb{R}$ — asks for $|f|\le M$
*inside* $H$, but the maximum-modulus principle only governs **bounded** domains
and $H$ is unbounded: the missing boundary piece is "$\infty$," and the whole
difficulty is taming the point at infinity (a baby Phragmén–Lindelöf). The fix is
to multiply $f$ by a factor that is harmless on $\mathbb{R}$ yet forces decay at
$\infty$, so a finite half-disk argument applies. The **algebra** problem
develops valuation domains, where the one axiom "$\alpha$ or $\alpha^{-1}$ lies in
$V$" silently makes the ideals **totally ordered** — and once you see that, (a)
locality, (b) Bézout (f.g. $\Rightarrow$ principal), and (c) integral-closedness
all fall out of comparing principal ideals or dividing an equation by a power of
$\alpha$. The subtleties: (b) reduces $n$ generators to $2$ by induction; (c)
hinges on "$\alpha\notin V\Rightarrow\alpha^{-1}\in V$"; and (e) is really the
identification $W=V_{\mathfrak p}$, a localization, where "$s\notin M$" must be
recognized as "$s$ is a unit of $W$."

## The Key Insight

**Analysis.** For $z\in\overline H$, $\Re(-iz)=\Im z\ge0$, so $|1-i\varepsilon z|
\ge1$ on $\mathbb{R}$ and $\to\infty$ as $|z|\to\infty$. Thus
$g_\varepsilon=f/(1-i\varepsilon z)$ stays $\le M$ on $\mathbb{R}$ and decays at
$\infty$, so the ordinary maximum principle on a half-disk gives
$|g_\varepsilon|\le M$; letting $\varepsilon\to0$ yields $|f|\le M$.

**Algebra.** The valuation axiom forces, for ideals $I,J$, that $I\subseteq J$ or
$J\subseteq I$ — because a witness $a\in I\setminus J$, $b\in J\setminus I$ makes
$a/b$ or $b/a$ lie in $V$, pulling one generator into the other ideal. Total
ordering of ideals gives at once: a unique maximal ideal (a); two-generator
ideals collapse to the bigger principal one, hence all f.g. ideals are principal
(b). Dividing $\alpha^n+\cdots+a_0\in V$ by $\alpha^{n-1}$ and using
$\alpha^{-1}\in V$ shows $\alpha\in V$ — integral closedness (c). Any overring
$V\subseteq W\subseteq F$ inherits the axiom verbatim (d), and the local structure
of $W$ identifies it with the localization $W=\{a/s:a\in V,\ s\in V\setminus M\}$
(e).

## Complete Proof

---

### Problem 1 (Complex analysis): $|f|\le M$ throughout $H$

Let $H=\{z:\Im z>0\}$, $f:\overline H\to\mathbb{C}$ bounded and continuous with
$f|_H$ analytic, and $|f(x)|\le M$ for all $x\in\mathbb{R}$. Let $B=\sup_{\overline
H}|f|<\infty$. We may assume $M>0$ (otherwise replace $M$ by $M+\delta$ in what
follows and let $\delta\to0$ at the end).

For $\varepsilon>0$ define on $\overline H$
$$
g_\varepsilon(z)=\frac{f(z)}{1-i\varepsilon z}.
$$
**The denominator is bounded below.** Writing $-iz$, we have
$\Re(-iz)=\Im z\ge0$ on $\overline H$, so
$1-i\varepsilon z=1+\varepsilon(-iz)$ has $\Re(1-i\varepsilon z)=1+\varepsilon
\Im z\ge1$. Hence $|1-i\varepsilon z|\ge1$ on $\overline H$; in particular the
denominator never vanishes, so $g_\varepsilon$ is continuous on $\overline H$ and
analytic on $H$.

**Bound on $\mathbb{R}$.** For $z=x\in\mathbb{R}$, $|1-i\varepsilon x|=
\sqrt{1+\varepsilon^2x^2}\ge1$, so
$$
|g_\varepsilon(x)|=\frac{|f(x)|}{|1-i\varepsilon x|}\le\frac{M}{1}=M.
$$

**Decay at infinity.** For $z\in\overline H$, $|1-i\varepsilon z|\ge\varepsilon
|z|-1$, so
$$
|g_\varepsilon(z)|\le\frac{B}{\varepsilon|z|-1}\xrightarrow[\;|z|\to\infty\;]{}0 .
$$
Pick $R_0$ with $\dfrac{B}{\varepsilon R_0-1}\le M$; then $|g_\varepsilon(z)|\le M$
whenever $|z|\ge R_0$, $z\in\overline H$.

**Half-disk maximum principle.** Fix $z_0\in H$ and choose $R>\max(|z_0|,R_0)$.
On the bounded half-disk $D_R=\{z\in H:|z|<R\}$, $g_\varepsilon$ is analytic and
continuous up to the boundary $\partial D_R$, which consists of the diameter
$[-R,R]\subseteq\mathbb{R}$ (where $|g_\varepsilon|\le M$) and the upper
semicircle $|z|=R$ (where $|g_\varepsilon|\le M$ since $R\ge R_0$). By the maximum
modulus principle, $|g_\varepsilon(z_0)|\le M$, i.e.
$$
|f(z_0)|\le M\,|1-i\varepsilon z_0| .
$$
Letting $\varepsilon\to0^+$ gives $|1-i\varepsilon z_0|\to1$, hence
$|f(z_0)|\le M$. As $z_0\in H$ was arbitrary, $|f(z)|\le M$ for all $z\in H$.
$\quad\checkmark$

---

### Problem 2 (Valuation domains)

Let $V$ be a commutative integral domain with quotient field $F$ such that for
every $\alpha\in F^\times$, $\alpha\in V$ or $\alpha^{-1}\in V$.

#### Part (a): ideals are totally ordered; $V$ is local

Let $I,J$ be ideals and suppose $I\not\subseteq J$ and $J\not\subseteq I$. Choose
$a\in I\setminus J$ and $b\in J\setminus I$; both are nonzero (a zero element lies
in every ideal). Apply the valuation axiom to $a/b\in F^\times$:
- if $a/b\in V$, then $a=(a/b)\,b\in J$ (as $b\in J$ and $J$ is an ideal),
  contradicting $a\notin J$;
- if $b/a\in V$, then $b=(b/a)\,a\in I$, contradicting $b\notin I$.

Either way a contradiction, so $I\subseteq J$ or $J\subseteq I$.

**Uniqueness of the maximal ideal.** By Zorn's lemma $V$ has at least one maximal
ideal. If $\mathfrak m_1,\mathfrak m_2$ are both maximal, then by the total
ordering $\mathfrak m_1\subseteq\mathfrak m_2$ or $\mathfrak m_2\subseteq\mathfrak
m_1$; maximality forces equality. Hence $V$ has a **unique maximal ideal** (it is
local). $\quad\checkmark$

#### Part (b): finitely generated ideals are principal

**Two generators.** Let $I=(a,b)$. By part (a) applied to the principal ideals
$(a),(b)$, one contains the other; say $(a)\subseteq(b)$. Then $a\in(b)$, so
$I=(a,b)=(b)$ is principal. (If instead $(b)\subseteq(a)$, then $I=(a)$.)

**Induction on the number of generators.** A principal ideal is the case $n=1$.
Assume every ideal generated by $n-1$ elements is principal, and let
$I=(a_1,\dots,a_n)$. By the inductive hypothesis $(a_1,\dots,a_{n-1})=(c)$ for
some $c\in V$, so $I=(c,a_n)$, which is principal by the two-generator case.
Hence every finitely generated ideal of $V$ is principal. $\quad\checkmark$

#### Part (c): $V$ is integrally closed in $F$

Let $\alpha\in F^\times$ and suppose $a_0,\dots,a_{n-1}\in V$ with
$$
\beta:=\alpha^{n}+a_{n-1}\alpha^{n-1}+\cdots+a_1\alpha+a_0\in V .
$$
Suppose, for contradiction, that $\alpha\notin V$. By the valuation axiom
$\alpha^{-1}\in V$; write $u=\alpha^{-1}\in V$. Divide the defining equation by
$\alpha^{n-1}$:
$$
\alpha+a_{n-1}+a_{n-2}\alpha^{-1}+\cdots+a_0\alpha^{-(n-1)}=\beta\,\alpha^{-(n-1)},
$$
so, solving for $\alpha$,
$$
\alpha=\beta u^{\,n-1}-a_{n-1}-a_{n-2}u-a_{n-3}u^{2}-\cdots-a_0u^{\,n-1}.
$$
Every term on the right lies in $V$ (as $\beta,u,a_0,\dots,a_{n-1}\in V$ and $V$
is a ring), so $\alpha\in V$ — contradicting $\alpha\notin V$. Therefore
$\alpha\in V$. $\quad\checkmark$

(Equivalently: $\alpha$ satisfies the monic equation $\alpha^n+a_{n-1}\alpha^{n-1}
+\cdots+a_1\alpha+(a_0-\beta)=0$ with all coefficients in $V$, so $\alpha$ is
integral over $V$; the computation shows integral elements of $F$ already lie in
$V$.)

#### Part (d): every intermediate ring $V\subseteq W\subseteq F$ is a valuation domain

First, $W$ is an integral domain (given) with quotient field $F$: since
$V\subseteq W\subseteq F$ and $F=\operatorname{Frac}(V)$, we have
$F=\operatorname{Frac}(V)\subseteq\operatorname{Frac}(W)\subseteq F$, so
$\operatorname{Frac}(W)=F$.

Now verify the valuation axiom for $W$. Let $\alpha\in F^\times$. Because $V$ is a
valuation domain, $\alpha\in V$ or $\alpha^{-1}\in V$; and $V\subseteq W$, so
$\alpha\in W$ or $\alpha^{-1}\in W$. Hence $W$ is a valuation domain (with the same
quotient field $F$). $\quad\checkmark$

#### Part (e): $W=\{a/s:\ a\in V,\ s\in V\setminus M\}$, where $M$ is the maximal ideal of $W$

By (d), $W$ is a valuation domain, so by (a) it is local with unique maximal
ideal $M$; recall that in a local ring the non-units are **exactly** $M$, i.e.
$W^\times=W\setminus M$. Write $R=\{a/s:a\in V,\ s\in V,\ s\notin M\}$.

**$R\subseteq W$.** Take $a/s\in R$ with $a\in V$, $s\in V\setminus M$. Then
$s\in W$ and $s\notin M$, so $s\in W^\times$, giving $s^{-1}\in W$; and $a\in
V\subseteq W$. Hence $a/s=a\,s^{-1}\in W$.

**$W\subseteq R$.** Take $w\in W\subseteq F$.
- If $w\in V$: then $w=w/1$ with $1\in V$ and $1\notin M$ (units are not in $M$),
  so $w\in R$.
- If $w\notin V$: by the valuation axiom for $V$, $w^{-1}\in V$. Moreover $w\in W$
  inverts $w^{-1}$, so $w^{-1}\in W^\times=W\setminus M$; thus $w^{-1}\in
  V\setminus M$. Taking $a=1\in V$ and $s=w^{-1}\in V\setminus M$ gives
  $w=\dfrac{1}{w^{-1}}=\dfrac{a}{s}\in R$.

Therefore $W=R=\{a/s:a\in V,\ s\in V\setminus M\}$. $\quad\blacksquare$

### Remark

The algebra problem is the standard portrait of a valuation domain: the lone
axiom "$\alpha$ or $\alpha^{-1}$ is in $V$" linearly orders the ideal lattice,
which instantly yields **local** (a), **Bézout** — indeed every f.g. ideal
principal (b) — and **integrally closed** (c). Part (e) recognizes the
intermediate ring $W$ as the **localization** $W=V_{\mathfrak p}$ at the prime
$\mathfrak p=M\cap V$: "$s\in V\setminus M$" is exactly "$s$ is a unit of $W$,"
and $V\setminus M=V\setminus\mathfrak p$ is the multiplicative set being inverted.
So the overrings of a valuation domain inside $F$ are precisely its localizations
at primes — a lattice anti-isomorphic to the chain of primes of $V$. The analysis
problem is the half-plane case of **Phragmén–Lindelöf**: boundedness supplies
control at $\infty$, and the vanishing factor $1/(1-i\varepsilon z)$ converts
that into a genuine boundary value there, after which the finite maximum principle
closes the argument.
