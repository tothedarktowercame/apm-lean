<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b96A04: The fraction field K is a free/projective/finitely-generated R-module only when R = K

## Why It's Hard

Five parts that look unrelated are really one theorem seen five ways: **$K=\operatorname
{Frac}(R)$ is a divisible $R$-module** (every nonzero $d$ acts surjectively, since
$k=d\cdot(k/d)$), and divisibility is incompatible with being free, projective, or
finitely generated over $R$ — unless $R$ has no nonzero nonunits, i.e. $R=K$. The
difficulty is building the bridge: a single divisibility atom (a) must be amplified to
free modules (b), and then the same clash is dressed three times (submodule-of-free,
projective, finitely generated). Spotting that "$d$ a nonunit $\Rightarrow$ $d$ is not
surjective on a free module" is the crux, and it is exactly where (a) is used.

## The Key Insight

- **(a)** $dy\mid y$, $y\neq0$ $\Rightarrow$ $y=dyc\Rightarrow y(1-dc)=0\Rightarrow dc=1$:
  $d$ is a unit.
- **(b)** Free modules are torsion-free; and if $0\neq m\in F$ has a nonzero coordinate
  $a_j$, then for a nonunit $d$, taking $x=a_j$ makes $(dx)y=m$ unsolvable — because a
  solution would give $da_j\mid a_j$, forcing $d$ to be a unit by (a).
- **(c),(e)** $K$ is divisible: $dK=K$ for every $0\neq d$. So $K$ can solve every
  $(dx)y=m$ that a free module cannot — contradiction unless $R=K$; likewise $rK=K$
  blocks finite generation.
- **(d)** $R/I$ projective splits $0\to I\to R\to R/I\to0$, but $R$ is indecomposable (a
  domain has only the idempotents $0,1$), so $I=0$.

## Complete Proof

$R$ is a commutative domain with fraction field $K$. Note $R=K$ means precisely that
$R$ is a field. We use throughout that $K$ is **divisible**: for $0\neq d\in R$ and
$k\in K$, the element $k/d\in K$ satisfies $d\cdot(k/d)=k$, so $dK=K$.

### (a) If $y\neq0$ and $dy\mid y$, then $d$ is a unit

$dy\mid y$ means $y=(dy)c$ for some $c\in R$, i.e. $y(1-dc)=0$. Since $R$ is a domain and
$y\neq0$, $1-dc=0$, so $dc=1$ and $d$ is a unit. $\quad\checkmark$
(For $y=0$ the hypothesis $0\mid0$ holds vacuously and imposes nothing on $d$; the
statement is meant for $y\neq0$.)

### (b) Free modules are torsion-free, and a nonunit is not surjective on them

Let $F$ be free with basis $\{e_i\}$, so each element is a unique finite sum $\sum a_i
e_i$.

**Torsion-free.** If $0\neq m=\sum a_i e_i$ (some $a_j\neq0$) and $rm=0$, then $\sum
(ra_i)e_i=0$ forces $ra_i=0$ for all $i$; in particular $ra_j=0$ with $a_j\neq0$, so
$r=0$ (domain).

**A nonunit fails to be surjective.** Let $0\neq d\in R$ be a nonunit and fix any $0\neq
m=\sum a_i e_i\in F$; pick a coordinate $a_j\neq0$ and set $x:=a_j\neq0$. We claim
$(dx)y=m$ has no solution $y\in F$. Indeed, if $y=\sum b_i e_i$ solved it, comparing the
$e_j$-coordinates gives $dx\,b_j=a_j$, i.e. $d a_j\,b_j=a_j$, so $da_j\mid a_j$. By (a)
(with $y=a_j\neq0$) this forces $d$ to be a unit — contradiction. Hence no solution
exists. $\quad\checkmark$

### (c) If $K$ embeds in a free module, or is projective, then $R=K$

**Submodule of free.** Suppose $K$ is (isomorphic to) a submodule of a free module $F$;
regard $K\subseteq F$. Suppose toward contradiction $R\neq K$, i.e. $R$ has a nonzero
nonunit $d$. Take $m=1\in R\subseteq K\subseteq F$ (so $m\neq0$). By (b) there is a
nonzero $x\in R$ with $(dx)y=m$ unsolvable in $F$. But $dx\neq0$ (domain) and $m\in K$,
and $K$ is divisible, so $y:=m/(dx)\in K\subseteq F$ solves $(dx)y=m$ — contradiction.
Hence $R$ has no nonzero nonunit: $R$ is a field, i.e. $R=K$.

**Projective.** If $K$ is projective, it is a direct summand of a free module, in
particular a submodule of a free module. By the previous paragraph, $R=K$. $\quad\checkmark$

### (d) If $I\subsetneq R$ is proper and $R/I$ is projective, then $I=0$

Projectivity of $R/I$ means the canonical surjection $\pi:R\to R/I$ splits: there is an
$R$-linear section $s:R/I\to R$ with $\pi\circ s=\mathrm{id}$. Then
$$
R = \ker\pi \oplus \operatorname{im}s = I \oplus s(R/I),
$$
an internal direct sum of ideals, with $s(R/I)\cong R/I$. But $R$ is **indecomposable**
as a module over itself: a decomposition $R=I\oplus J$ yields complementary idempotents
($1=e+f$, $e\in I$, $f\in J$, $ef=0$, $e^2=e$), and in a domain the only idempotents are
$0$ and $1$, so one summand is $0$. Thus $I=0$ or $s(R/I)=0$. If $s(R/I)=0$ then
$R/I\cong0$, i.e. $I=R$, contradicting properness. Therefore $I=0$. $\quad\checkmark$

### (e) Finitely generated submodules between $R$ and $K$, and $K$ f.g. $\Rightarrow R=K$

Let $R\subseteq M\subseteq K$ with $M=R m_1+\cdots+R m_k$ finitely generated, $m_i\in
K$. Write $m_i=a_i/b_i$ with $a_i,b_i\in R$, $b_i\neq0$, and set
$$
r:=b_1b_2\cdots b_k\neq0 .
$$
Then for each $i$, $r\,m_i=\Big(\prod_{j\neq i}b_j\Big)a_i\in R$, so every generator of
$M$ is sent into $R$, giving $rM\subseteq R$. $\quad\checkmark$

Now suppose $K$ itself is finitely generated as an $R$-module. Apply the above with
$M=K$: there is $0\neq r\in R$ with $rK\subseteq R$. But $K$ is divisible, so $rK=K$.
Hence $K=rK\subseteq R\subseteq K$, forcing $R=K$. $\quad\blacksquare$

### Remark

Every part is the same collision between **divisibility of $K$** and the rigidity of
free modules. (a)→(b) is the load-bearing step: a nonunit cannot be a surjection on a
free module, whereas it is a surjection (indeed a bijection) on $K$. Consequences: over a
domain that is not a field, $K$ is never free, never projective (so $K$ is a standard
example of a flat-but-not-projective module — e.g. $\mathbb{Q}$ over $\mathbb{Z}$), and
never finitely generated; and (d) says the only projective cyclic module $R/I$ is $R$
itself ($I=0$), i.e. proper quotients of a domain are never projective. The slogan: "you
cannot generate denominators from finitely much, nor split them off freely."
