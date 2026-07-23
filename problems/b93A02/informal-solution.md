<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b93A02: CRT, and the prime structure of an Artinian ring

## Why It's Hard

This is a five-step climb from a single computation to a structural finiteness theorem,
and the glue is the **descending chain condition** (Artinian), used twice in genuinely
different ways: on the powers $(x)\supseteq(x^2)\supseteq\cdots$ to make a domain a
field (b), and on the intersections $P_1\supseteq P_1\cap P_2\supseteq\cdots$ to force
finiteness (e). In between, the standard facts "quotient of Artinian is Artinian,"
"field $\iff$ maximal," "maximal ideals are incomparable," and the Chinese Remainder
Theorem from (a) all have to be marshalled in the right order. The subtlety in (e) is
recognizing that the DCC must clash with the *coprimality* of (d) — a chain that
stabilizes says one intersection sits inside the next prime, which coprimality forbids.

## The Key Insight

- **(a)** $I+J=R$ gives $1=a+b$ ($a\in I,b\in J$); CRT surjectivity follows by lifting
  $(x,y)\mapsto xb+ya$.
- **(b)** DCC stabilizes $(x^n)=(x^{n+1})$, so $x^n=rx^{n+1}$, and cancelling
  $x^n\neq0$ in the domain gives $rx=1$: $x$ is a unit.
- **(c)** $P$ prime $\Rightarrow R/P$ is an Artinian domain $\Rightarrow$ (by b) a field
  $\Rightarrow P$ maximal.
- **(d)** Distinct maximal ideals are incomparable, so pick $a_i\in P_i\setminus P_n$;
  the product $a_1\cdots a_{n-1}$ lies in $\bigcap_{i<n}P_i$ but not in the *prime*
  $P_n$, so $\bigcap_{i<n}P_i+P_n=R$.
- **(e)** If there were infinitely many primes, the DCC chain $P_1\cap\cdots\cap P_k$
  stabilizes, giving $P_1\cap\cdots\cap P_n\subseteq P_{n+1}$ — contradicting the
  coprimality (d).

## Complete Proof

$R$ is a commutative ring with $1$.

### (a) Chinese Remainder Theorem

Suppose $I+J=R$. Define $\varphi:R\to R/I\times R/J$ by $\varphi(r)=(r+I,\,r+J)$, a ring
homomorphism. Its kernel is $\{r: r\in I \text{ and } r\in J\}=I\cap J$, so by the first
isomorphism theorem $R/(I\cap J)\cong \operatorname{im}\varphi$. It remains to show
$\varphi$ is **surjective**.

Since $I+J=R$, write $1=a+b$ with $a\in I$, $b\in J$. Given any $(x+I,\,y+J)$, set
$r:=xb+ya$. Then, using $a\in I$ and $b=1-a$:
$$
r = xb+ya \equiv x(1-a) \equiv x \pmod I \qquad(\text{as } xa,\,ya\in I),
$$
and using $b\in J$ and $a=1-b$:
$$
r = xb+ya \equiv y(1-b) \equiv y \pmod J \qquad(\text{as } xb,\,yb\in J).
$$
So $\varphi(r)=(x+I,\,y+J)$, proving surjectivity. Hence
$$
R/(I\cap J)\cong R/I\times R/J \;(=R/I\oplus R/J). \quad\checkmark
$$

*From here on $R$ is Artinian (DCC on ideals).*

### (b) An Artinian integral domain is a field

Let $R$ be a domain and $0\neq x\in R$. Consider the descending chain of ideals
$$
(x)\supseteq(x^2)\supseteq(x^3)\supseteq\cdots .
$$
By DCC it stabilizes: there is $n$ with $(x^n)=(x^{n+1})$. Then $x^n\in(x^{n+1})$, so
$x^n=r\,x^{n+1}$ for some $r\in R$, i.e. $x^n(1-rx)=0$. As $R$ is a domain and $x\neq0$,
also $x^n\neq0$, so we may cancel it: $1-rx=0$, i.e. $rx=1$. Thus every nonzero $x$ is a
unit, and $R$ is a field. $\quad\checkmark$

### (c) Every prime ideal is maximal

Let $P$ be a prime ideal. Then $R/P$ is an integral domain. It is also Artinian: any
descending chain of ideals of $R/P$ corresponds (by the correspondence theorem) to a
descending chain of ideals of $R$ containing $P$, which stabilizes by DCC. So $R/P$ is
an Artinian domain, hence a field by (b). A quotient $R/P$ is a field iff $P$ is
maximal; therefore $P$ is maximal. $\quad\checkmark$

### (d) Distinct primes are pairwise "co-intersection"-prime

Let $P_1,\dots,P_n$ be distinct prime ideals; by (c) each is maximal. For $i<n$, since
$P_i$ and $P_n$ are distinct maximal ideals they are incomparable (if $P_i\subseteq
P_n$ then $P_i\subsetneq P_n\subsetneq R$ contradicts maximality of $P_i$). Hence there
is $a_i\in P_i$ with $a_i\notin P_n$.

Set $a:=a_1a_2\cdots a_{n-1}$. Since $a_i\in P_i$ and $P_i$ is an ideal,
$a\in P_i$ for every $i<n$, so $a\in P_1\cap\cdots\cap P_{n-1}$. Since $P_n$ is prime
and no factor $a_i$ lies in $P_n$, the product $a\notin P_n$ (a prime ideal contains a
product only if it contains a factor).

Thus $a\in (P_1\cap\cdots\cap P_{n-1})\setminus P_n$. The ideal
$(P_1\cap\cdots\cap P_{n-1})+P_n$ contains $P_n$ and the element $a\notin P_n$, so it
strictly contains the maximal ideal $P_n$; therefore it equals $R$:
$$
(P_1\cap\cdots\cap P_{n-1})+P_n=R. \quad\checkmark
$$

### (e) $R$ has only finitely many primes

Suppose not. Then we may choose an infinite sequence of *distinct* prime ideals
$P_1,P_2,P_3,\dots$ Form the descending chain
$$
P_1\ \supseteq\ P_1\cap P_2\ \supseteq\ P_1\cap P_2\cap P_3\ \supseteq\ \cdots .
$$
By DCC it stabilizes: there is $n$ with
$$
P_1\cap\cdots\cap P_n = P_1\cap\cdots\cap P_n\cap P_{n+1},
\qquad\text{i.e.}\qquad P_1\cap\cdots\cap P_n\subseteq P_{n+1}.
$$
But $P_1,\dots,P_{n+1}$ are distinct primes, so by (d) (with $P_{n+1}$ as the last one)
$$
(P_1\cap\cdots\cap P_n)+P_{n+1}=R .
$$
The inclusion $P_1\cap\cdots\cap P_n\subseteq P_{n+1}$ makes this sum equal to
$P_{n+1}$, a proper ideal — contradicting that it is all of $R$. Hence there is no such
infinite sequence: $R$ has only finitely many prime ideals. $\quad\blacksquare$

### Remark

The chain of implications is the skeleton of the classification of Artinian rings:
(b)+(c) say $\dim R=0$ (every prime is maximal), (e) says $\operatorname{Spec}R$ is
finite, and (a)+(d) are exactly the CRT input that then splits $R$ as a finite product
of local Artinian rings $R\cong\prod_i R/P_i^{\,k_i}$. The DCC is doing all the work,
appearing once as "powers terminate" (units) and once as "intersections terminate"
(finiteness).
