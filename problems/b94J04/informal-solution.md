<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b94J04: Localization is an exact functor — but not a faithful one

## Why It's Hard

Part (b) is the theorem "$S^{-1}A$ is flat over $A$," and the work is three small
diagram chases, each of which hinges on the same move: an equation in a localization
$m/s=0$ does **not** mean the numerator is zero, only that it is killed by *some* $t\in
S$. You must insert that $t$ to descend to a true equation in the original module, apply
the original exactness, and lift back. Part (c) is the conceptual sting: exactness does
not run backwards, because localization can **erase** a failure of exactness whenever
the offending homology is $S$-torsion — and the simplest torsion module, $\mathbb{Z}/2$,
vanishes after inverting the nonzero integers.

## The Key Insight

- **(a)** $S^{-1}M=(M\times S)/\!\sim$, $\ (m,s)\sim(m',s')\iff \exists\,t\in S:\
  t(s'm-sm')=0$; write $m/s$, an $S^{-1}A$-module.
- **(b)** With $S^{-1}f(m/s)=f(m)/s$, $S^{-1}g(n/s)=g(n)/s$: surjectivity is immediate;
  injectivity uses $f(m)/s=0\Rightarrow t\,f(m)=0\Rightarrow f(tm)=0\Rightarrow tm=0
  \Rightarrow m/s=0$; the middle uses $g(n)/s=0\Rightarrow g(tn)=0\Rightarrow
  tn\in\ker g=\operatorname{im}f$.
- **(c)** Localization is exact but not faithful: $0\to 0\to \mathbb{Z}/2\to 0\to 0$ is
  *not* exact, yet inverting $S=\mathbb{Z}\setminus\{0\}$ kills $\mathbb{Z}/2$
  ($\mathbb{Z}/2\otimes\mathbb{Q}=0$), making the localized sequence exact.

## Complete Proof

Let $A$ be commutative and $S\subseteq A$ multiplicative ($1\in S$, closed under
products).

### (a) Definition of $S^{-1}M$

For an $A$-module $M$, define on $M\times S$ the relation
$$
(m,s)\sim(m',s')\quad\Longleftrightarrow\quad \exists\,t\in S:\ t(s'm-sm')=0 .
$$
This is an equivalence relation (the auxiliary $t$ makes transitivity work even when $A$
has zero divisors). Write $m/s$ for the class of $(m,s)$ and
$$
S^{-1}M=\{\,m/s : m\in M,\ s\in S\,\}.
$$
It is an $S^{-1}A$-module under
$$
\frac{m}{s}+\frac{m'}{s'}=\frac{s'm+sm'}{ss'},\qquad
\frac{a}{u}\cdot\frac{m}{s}=\frac{am}{us}\quad(a/u\in S^{-1}A),
$$
which are well defined. A key fact used below: $m/s=0$ in $S^{-1}M$ iff $tm=0$ for some
$t\in S$. Any $A$-linear map $h:M\to N$ induces $S^{-1}h:S^{-1}M\to S^{-1}N$,
$\ (S^{-1}h)(m/s)=h(m)/s$.

### (b) Localization preserves short exact sequences

Let $0\to M\xrightarrow{f} N\xrightarrow{g} Q\to 0$ be exact, i.e. $f$ injective, $g$
surjective, and $\operatorname{im}f=\ker g$. Apply $S^{-1}(-)$ to get
$$
0\to S^{-1}M\xrightarrow{S^{-1}f} S^{-1}N\xrightarrow{S^{-1}g} S^{-1}Q\to 0 .
$$

**$S^{-1}g$ is surjective.** Given $q/s\in S^{-1}Q$, surjectivity of $g$ gives $n\in N$
with $g(n)=q$; then $(S^{-1}g)(n/s)=g(n)/s=q/s$.

**$S^{-1}f$ is injective.** Suppose $(S^{-1}f)(m/s)=f(m)/s=0$ in $S^{-1}N$. Then there is
$t\in S$ with $t\,f(m)=0$; since $f$ is $A$-linear, $f(tm)=0$. Injectivity of $f$ gives
$tm=0$, and as $t\in S$ this means $m/s=0$. So $\ker(S^{-1}f)=0$.

**Exactness at $S^{-1}N$.** First, $S^{-1}g\circ S^{-1}f=S^{-1}(g\circ f)=S^{-1}(0)=0$,
so $\operatorname{im}(S^{-1}f)\subseteq\ker(S^{-1}g)$. Conversely, take $n/s$ with
$(S^{-1}g)(n/s)=g(n)/s=0$. Then $t\,g(n)=0$ for some $t\in S$, i.e. $g(tn)=0$, so
$tn\in\ker g=\operatorname{im}f$. Write $tn=f(m)$ for some $m\in M$. Using
$n/s=tn/(ts)$ (both differ by the unit $t/t$),
$$
\frac{n}{s}=\frac{tn}{ts}=\frac{f(m)}{ts}=(S^{-1}f)\!\left(\frac{m}{ts}\right)\in
\operatorname{im}(S^{-1}f).
$$
Hence $\ker(S^{-1}g)\subseteq\operatorname{im}(S^{-1}f)$, giving equality.

Therefore the localized sequence is exact. $\quad\blacksquare$

### (c) The converse fails: localized-exact does not imply exact

Take $A=\mathbb{Z}$ and $S=\mathbb{Z}\setminus\{0\}$, so $S^{-1}A=\mathbb{Q}$ and
$S^{-1}(-)=(-)\otimes_{\mathbb{Z}}\mathbb{Q}$. Consider the sequence of $\mathbb{Z}$-modules
with $M=0$, $N=\mathbb{Z}/2\mathbb{Z}$, $Q=0$ and the (only possible, zero) maps:
$$
0\ \longrightarrow\ 0\ \longrightarrow\ \mathbb{Z}/2\mathbb{Z}\ \longrightarrow\ 0\ \longrightarrow\ 0 .
$$
This is **not exact**: exactness at $N$ would require
$\operatorname{im}(0\to N)=\ker(N\to 0)$, i.e. $0=\mathbb{Z}/2\mathbb{Z}$, which is false.

Now localize. Every nonzero integer is inverted, and $2\in S$ kills $\mathbb{Z}/2$: for
any $x/s\in S^{-1}(\mathbb{Z}/2)$ we have $2x=0$ with $2\in S$, so $x/s=0$. Thus
$S^{-1}(\mathbb{Z}/2)=0$ (equivalently $\mathbb{Z}/2\otimes\mathbb{Q}=0$), and the
localized sequence is
$$
0\ \longrightarrow\ 0\ \longrightarrow\ 0\ \longrightarrow\ 0\ \longrightarrow\ 0,
$$
which **is** exact. So the localized sequence is exact while the original is not: the
converse of (b) does not hold. $\quad\blacksquare$

### Remark

(b) says localization is an *exact* functor; (c) says it is not *faithful* (it can send a
nonzero — here non-exact — situation to zero). The obstruction it erases is exactly
$S$-torsion: a complex localizes to an exact one iff its homology is $S$-torsion, and
$\mathbb{Z}/2$ is $S$-torsion for $S=\mathbb{Z}\setminus\{0\}$. The same phenomenon
underlies the local–global slogan "$M=0$ iff $M_{\mathfrak p}=0$ for all primes
$\mathfrak p$": a single localization loses information, and only the *family* over all
primes is faithful.
