<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b98A04: A faithful module over an Artinian ring carries every simple as a composition factor

## Why It's Hard

The destination — *every* simple $R$-module $V$ shows up as some
$N_i/N_{i-1}$ in a composition series of a faithful module $M$ — sounds like it
needs heavy machinery (Wedderburn, Hopkins–Levitzki), but the problem engineers a
completely elementary route, and the only real difficulty is *trusting the
scaffolding*. Parts (a)–(b) build a finite list of elements whose **common
annihilator is zero**; this is where faithfulness and the descending chain
condition (DCC) interlock — faithfulness says "a nonzero $r$ fails to kill
*something*," DCC says "you can't keep shrinking annihilators forever," and the
two together force the common annihilator down to $0$. Part (c) turns that list
into an embedding $R\hookrightarrow M\oplus\cdots\oplus M$ — the regular module
sits inside a finite sum of copies of $M$. The subtlety in (d) is realizing you
get **finite length of $R$ for free** (it embeds in the finite-length $M^s$), so
no Hopkins–Levitzki is needed: $V$ is a simple quotient of $R$, hence a
composition factor of $R$, hence — by Jordan–Hölder applied to $R\le M^s$ — a
composition factor of $M$.

## The Key Insight

For $m_1,\dots,m_k\in M$ the common annihilator $\bigcap_i\operatorname{Ann}(m_i)$
is a left ideal (a), and **DCC + faithfulness** drive a minimal such ideal to
$0$: if a minimal common annihilator $I_0\neq0$, pick $0\neq r\in I_0$;
faithfulness gives $m$ with $rm\neq0$, and adjoining $m$ strictly shrinks $I_0$ —
contradiction (b). With $\bigcap_{i=1}^s\operatorname{Ann}(m_i)=0$, the map
$$
\varphi:R\to M^{\oplus s},\qquad \varphi(r)=(rm_1,\dots,rm_s)
$$
is $R$-linear with kernel $=0$, embedding $_RR\hookrightarrow M^{\oplus s}$ (c).
Now $M^{\oplus s}$ has finite length with composition factors exactly the
$N_i/N_{i-1}$ (each $s$ times), so its submodule $R$ has finite length and its
composition factors are among the $N_i/N_{i-1}$. Finally a simple $V$ is a quotient
$R/\mathfrak m$ ($\mathfrak m$ maximal left ideal), hence a composition factor of
$R$, hence some $N_i/N_{i-1}$ (d).

## Complete Proof

For $m\in M$ write $\operatorname{Ann}(m)=\{r\in R:rm=0\}$.

### Part (a): the common annihilator is a left ideal

Let $I=\{r\in R: rm_i=0\text{ for }1\le i\le k\}=\bigcap_{i=1}^k\operatorname{Ann}
(m_i)$. We check $I$ is a left ideal.

- **Contains $0$:** $0\cdot m_i=0$ for all $i$, so $0\in I$.
- **Closed under subtraction:** if $r,s\in I$ then $(r-s)m_i=rm_i-sm_i=0-0=0$ for
  all $i$, so $r-s\in I$; thus $I$ is an additive subgroup.
- **Absorbs left multiplication:** if $r\in I$ and $a\in R$ then
  $(ar)m_i=a(rm_i)=a\cdot0=0$ for all $i$, so $ar\in I$.

Hence $I$ is a left ideal of $R$. (Each $\operatorname{Ann}(m_i)$ is the kernel of
the $R$-linear map $R\to M,\ r\mapsto rm_i$, and $I$ is their intersection.)
$\quad\checkmark$

### Part (b): finitely many elements with common annihilator $0$

Consider the family
$$
\mathcal{S}=\Bigl\{\,\textstyle\bigcap_{i=1}^k\operatorname{Ann}(m_i)\ :\ k\ge1,\
m_1,\dots,m_k\in M\,\Bigr\}
$$
of left ideals (each is a left ideal by (a)); $\mathcal S\neq\varnothing$ since
$\operatorname{Ann}(m)\in\mathcal S$ for any $m\in M$. (If $M=0$ then
faithfulness forces $R=0$ and the claim is trivial, so assume $M\neq0$.) Because
$R$ is left Artinian, the DCC on left ideals is equivalent to the **minimal
condition**: every nonempty family of left ideals has a minimal member. Let
$$
I_0=\operatorname{Ann}(m_1)\cap\cdots\cap\operatorname{Ann}(m_s)
$$
be a minimal element of $\mathcal S$.

**Claim: $I_0=0$.** Suppose not, and choose $0\neq r\in I_0$. Since $M$ is
**faithful** and $r\neq0$, we have $rM\neq0$, so there exists $m_{s+1}\in M$ with
$rm_{s+1}\neq0$. Set
$$
I_1=I_0\cap\operatorname{Ann}(m_{s+1})
=\bigcap_{i=1}^{s+1}\operatorname{Ann}(m_i)\in\mathcal S .
$$
Then $I_1\subseteq I_0$, and the inclusion is **strict**: $r\in I_0$ but
$r\notin\operatorname{Ann}(m_{s+1})$ (as $rm_{s+1}\neq0$), so $r\notin I_1$. This
contradicts the minimality of $I_0$. Therefore $I_0=0$.

So there are finitely many $m_1,\dots,m_s\in M$ with
$\{r\in R:rm_i=0,\ 1\le i\le s\}=0$. $\quad\checkmark$

### Part (c): $R$ embeds in a finite direct sum of copies of $M$

Fix $m_1,\dots,m_s$ from part (b), so $\bigcap_{i=1}^s\operatorname{Ann}(m_i)=0$.
Define
$$
\varphi:\ {}_RR\ \longrightarrow\ M^{\oplus s}=\underbrace{M\oplus\cdots\oplus
M}_{s},\qquad \varphi(r)=(rm_1,rm_2,\dots,rm_s),
$$
viewing $R$ as a left module over itself.

**$\varphi$ is a left $R$-module homomorphism.** Additivity:
$\varphi(r+r')=((r+r')m_i)_i=(rm_i)_i+(r'm_i)_i=\varphi(r)+\varphi(r')$. And for
$a\in R$, $\varphi(ar)=((ar)m_i)_i=(a(rm_i))_i=a\,(rm_i)_i=a\,\varphi(r)$.

**$\varphi$ is injective.** $r\in\ker\varphi\iff rm_i=0$ for all $i\iff
r\in\bigcap_{i=1}^s\operatorname{Ann}(m_i)=0$. So $\ker\varphi=0$.

Therefore $\varphi$ is an injective $R$-module map, giving an isomorphism
$R\cong\varphi(R)$ onto a **submodule** of $M^{\oplus s}$. $\quad\checkmark$

### Part (d): every simple $V$ is some $N_i/N_{i-1}$

Let $0=N_0\subset N_1\subset\cdots\subset N_t=M$ be the given composition series,
so $M$ has finite length $t$ with composition factors $N_1/N_0,\dots,N_t/N_{t-1}$.
Let $V$ be a simple left $R$-module.

**Composition factors of $M^{\oplus s}$ are the $N_i/N_{i-1}$.** For any modules
$A,B$ the short exact sequence $0\to A\to A\oplus B\to B\to0$ shows the multiset
of composition factors of $A\oplus B$ is the union of those of $A$ and $B$ (splice
a composition series of $A$ with the preimage of one of $B$). By induction,
$M^{\oplus s}$ has finite length $st$, and **each** of its composition factors is
isomorphic to some $N_i/N_{i-1}$ (each occurring $s$ times).

**$R$ has finite length, with factors among the $N_i/N_{i-1}$.** By part (c),
$R\cong R':=\varphi(R)\le M^{\oplus s}$. From $0\to R'\to M^{\oplus s}\to
M^{\oplus s}/R'\to0$, the composition factors of $M^{\oplus s}$ are those of $R'$
together with those of the quotient; in particular $R'$ has finite length and
**every composition factor of $R'$ is isomorphic to some $N_i/N_{i-1}$**.
Transporting along $R\cong R'$, the same holds for $_RR$.

**$V$ is a composition factor of $R$.** Choose $0\neq v\in V$. Then $Rv$ is a
nonzero submodule of the simple module $V$, so $Rv=V$, and $r\mapsto rv$ is a
surjection $R\twoheadrightarrow V$ of left modules with kernel a left ideal
$\mathfrak m$; since $R/\mathfrak m\cong V$ is simple, $\mathfrak m$ is a
**maximal** left ideal. As $_RR$ has finite length (previous step), take a
composition series of $\mathfrak m$ and cap it with $R$:
$$
0=L_0\subset L_1\subset\cdots\subset L_{n-1}=\mathfrak m\subset L_n=R,
$$
a composition series of $R$ whose top factor is $L_n/L_{n-1}=R/\mathfrak m\cong V$.
So $V$ is a composition factor of $_RR$.

**Conclusion.** By the Jordan–Hölder theorem the composition factors of $_RR$ are
well defined up to isomorphism and permutation; $V$ is one of them, and by the
second step every composition factor of $R$ is isomorphic to some $N_i/N_{i-1}$.
Hence
$$
V\cong N_i/N_{i-1}\quad\text{for some }1\le i\le t.
$$
$\blacksquare$

### Remark

The whole argument is the slogan **"a faithful module sees the whole regular
representation."** Faithfulness + DCC compress $M$'s annihilators to $0$ (b),
which is exactly the data needed to embed the regular module $_RR$ into a finite
power $M^{\oplus s}$ (c). Once $R$ lives inside a finite-length module, two
standard facts finish the job: simples are quotients of $R$, and composition
factors only travel *downward* into submodules (Jordan–Hölder). Note the
embedding also hands us, for free, that $R$ is left Noetherian of finite length —
a baby case of Hopkins–Levitzki — without invoking that theorem. The upshot:
$M$'s composition factors already exhaust the isomorphism classes of simple
$R$-modules.
