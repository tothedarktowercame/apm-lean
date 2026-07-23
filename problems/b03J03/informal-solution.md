<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b03J03: A UFD is integrally closed; but a square-free quadratic extension need not be

## Why It's Hard

**Part (a)** is a "use the hypothesis precisely" proof: integral closure is about
*monic* relations, and the only way to exploit "UFD" is to write a putative integral
element as a fraction in **lowest terms** and watch a prime in the denominator collide
with coprimality. Get the bookkeeping of "clear denominators" slightly wrong and the
argument evaporates.

**Part (b)** is a trap. Part (a) makes it tempting to believe square-freeness is the
right hypothesis to propagate integral-closedness to the quadratic extension
$D[\sqrt a]$ — and square-freeness *does* guarantee $a$ is not a square, so the
extension is a genuine quadratic field. But integral closure of a quadratic ring has a
second, sneakier obstruction: **half-integer elements** $\frac{1+\sqrt a}{2}$ become
integral exactly when $a\equiv 1\pmod 4$, and square-freeness says nothing about that
congruence. So the statement is **false**, and the cleanest witness is the golden-ratio
order $\mathbb{Z}[\sqrt 5]$.

## The Key Insight

**(a)** If $\alpha=b/c\in K$ is integral over $D$ with $\gcd(b,c)=1$ (possible in a
UFD), clearing denominators in a monic relation gives $c\mid b^n$; any prime $\pi\mid
c$ would then divide $b$, contradicting $\gcd(b,c)=1$. So $c$ is a unit and
$\alpha\in D$.

**(b)** Disproof. Take $D=\mathbb{Z}$, $a=5$ (square-free). In
$K[x]/(x^2-5)=\mathbb{Q}(\sqrt 5)$ the element $\varphi=\frac{1+\sqrt 5}{2}$ satisfies
$\varphi^2-\varphi-1=0$ (monic over $\mathbb{Z}$), so it is integral over
$\mathbb{Z}\subseteq\mathbb{Z}[\sqrt 5]$, yet $\varphi\notin\mathbb{Z}[\sqrt
5]=\{m+n\sqrt5: m,n\in\mathbb{Z}\}$. Hence $\mathbb{Z}[\sqrt 5]$ is **not** integrally
closed.

## Complete Proof

### Part (a): a UFD $D$ is integrally closed in $K=\operatorname{Frac}(D)$

Let $\alpha\in K$ be integral over $D$. Since $K$ is the fraction field, write
$\alpha=b/c$ with $b,c\in D$, $c\neq 0$. Because $D$ is a UFD we may cancel common
prime factors and assume $\gcd(b,c)=1$ (no prime of $D$ divides both $b$ and $c$).

Integrality gives a monic relation with coefficients $d_i\in D$:
$$
\alpha^n + d_{n-1}\alpha^{n-1}+\cdots+d_1\alpha+d_0 = 0 .
$$
Substitute $\alpha=b/c$ and multiply through by $c^n$:
$$
b^n + d_{n-1}b^{n-1}c + \cdots + d_1 b\,c^{n-1} + d_0 c^n = 0 .
$$
Every term after the first is divisible by $c$, so
$$
b^n = -c\big(d_{n-1}b^{n-1}+\cdots+d_0 c^{n-1}\big),
\qquad\text{i.e.}\qquad c \mid b^n .
$$
Suppose, for contradiction, that $c$ is not a unit. Then some prime $\pi\in D$ divides
$c$, hence $\pi\mid b^n$. As $\pi$ is prime, $\pi\mid b$. But then $\pi$ divides both
$b$ and $c$, contradicting $\gcd(b,c)=1$. Therefore $c$ is a unit, and
$\alpha=b c^{-1}\in D$.

Thus every element of $K$ integral over $D$ already lies in $D$: $D$ is integrally
closed in $K$. $\qquad\checkmark$

### Part (b): the analogous statement for $D[x]/(x^2-a)$ is FALSE

We disprove it with $D=\mathbb{Z}$ (a UFD, $K=\mathbb{Q}$) and $a=5$, which is
square-free (a single prime, to the first power).

First, $5$ is not a square in $\mathbb{Q}$, so $x^2-5$ is irreducible over $\mathbb{Q}$
and
$$
L := K[x]/(x^2-5) = \mathbb{Q}(\sqrt 5)
$$
is a field, the fraction field of $R := D[x]/(x^2-5) = \mathbb{Z}[\sqrt 5] = \{m+n\sqrt
5 : m,n\in\mathbb{Z}\}$. (Square-freeness is exactly what makes $L$ a field rather than
a product; that part of the intuition is correct.)

Consider
$$
\varphi := \frac{1+\sqrt 5}{2}\in L .
$$
Compute its minimal relation. Since $\varphi^2 = \frac{1+2\sqrt5+5}{4} =
\frac{6+2\sqrt5}{4} = \frac{3+\sqrt5}{2}$, we get
$$
\varphi^2-\varphi = \frac{3+\sqrt5}{2}-\frac{1+\sqrt5}{2} = \frac{2}{2}=1,
\qquad\text{so}\qquad \varphi^2-\varphi-1=0 .
$$
This is a **monic** polynomial with coefficients in $\mathbb{Z}\subseteq R$, so
$\varphi$ is integral over $R$ (indeed already over $\mathbb{Z}$).

However $\varphi\notin R$: if $\frac{1+\sqrt5}{2}=m+n\sqrt5$ with $m,n\in\mathbb{Z}$,
then comparing the $\mathbb{Q}$- and $\sqrt5$-coordinates (which are unique, as
$1,\sqrt5$ are a $\mathbb{Q}$-basis of $L$) gives $m=\tfrac12\notin\mathbb{Z}$, a
contradiction.

Therefore $\varphi$ is an element of $L$ that is integral over $R$ but not in $R$:
$R=\mathbb{Z}[\sqrt5]$ is **not** integrally closed in $L=\mathbb{Q}(\sqrt5)$. The
statement is false. $\qquad\blacksquare$

### Remark — why square-free is not enough

The integral closure of $\mathbb{Z}$ in $\mathbb{Q}(\sqrt a)$ (the ring of integers,
for $a$ square-free) is
$$
\mathcal{O}=\begin{cases}\mathbb{Z}[\sqrt a], & a\equiv 2,3 \pmod 4,\\[2pt]
\mathbb{Z}\!\left[\frac{1+\sqrt a}{2}\right], & a\equiv 1 \pmod 4.\end{cases}
$$
So $\mathbb{Z}[\sqrt a]$ is integrally closed **iff** $a\not\equiv 1\pmod 4$.
Square-freeness guarantees only that $a$ is not a square (hence $L$ is a field and the
$\sqrt a$-coordinate argument is valid); it does not control the residue of $a$ mod
$4$. Our witness $a=5\equiv 1\pmod 4$ is the smallest failure; $a=-3$ (giving the
Eisenstein integers $\mathbb{Z}[\frac{1+\sqrt{-3}}{2}]\supsetneq\mathbb{Z}[\sqrt{-3}]$)
is another. A *correct* repaired statement would add the hypothesis $a\not\equiv
1\pmod 4$ (or work with $D$ in which $2$ is a unit, where the obstruction disappears).
