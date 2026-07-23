<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM aunk04: A Rouché zero-count and the generalized Liouville theorem

## Why It's Hard

The two parts test the same meta-skill — *converting a global inequality on $|f|$ into discrete information* (a zero count; a degree) — through two different classical theorems, and each has one genuine decision point.

- **Part (a)** lives or dies on choosing the right comparison function for **Rouché's theorem**. The natural reflex is to peel off the highest-degree term $z^4$, but on the *unit* circle every power $|z^k|=1$, so degree is irrelevant — what matters is sheer magnitude, and the **constant term $6$** is the giant. One must notice that $6$ outweighs *the sum of all the other terms' moduli* ($1+3+1=5$), and that this is a strict inequality everywhere on the circle. A wrong split (dominant $z^4$ or $-3z^3$) simply fails to satisfy Rouché's hypothesis.

- **Part (b)** requires building the bridge from a *pointwise growth bound* $|f(z)|\le A+B|z|^m$ to a *statement about Taylor coefficients*. That bridge is **Cauchy's estimates**, and the decisive move is letting the radius $R\to\infty$: coefficients of index $n>m$ are squeezed to zero, while those with $n\le m$ are unconstrained. The subtlety is bookkeeping with non-integer $m$ — the true degree bound is $\lfloor m\rfloor$, and one should recover Liouville's theorem ($m<1\Rightarrow$ constant) as a special case.

## The Key Insight

**(a)** On $|z|=1$ the constant dominates: $|{-}(z^4-3z^3+z^2)|\le 1+3+1=5<6=|6|$. Rouché then says $f$ has the *same* number of zeros in the disk as the constant function $6$ — namely **zero**.

**(b)** Cauchy's inequality $|a_n|\le M(R)/R^n$ converts growth into coefficient decay: with $M(R)\le A+BR^m$,
$$
|a_n|\le\frac{A+BR^m}{R^n}=\frac{A}{R^n}+\frac{B}{R^{\,n-m}}\xrightarrow[R\to\infty]{}0\quad\text{whenever }n>m,
$$
so every coefficient beyond index $m$ vanishes and $f$ is a polynomial of degree $\le\lfloor m\rfloor$.

## Complete Proof

### Part (a): the number of zeros of $f(z)=z^4-3z^3+z^2+6$ in $|z|<1$

**Theorem used (Rouché).** *If $g$ and $h$ are holomorphic on and inside a simple closed contour $\gamma$ and $|h(z)|<|g(z)|$ for all $z\in\gamma$, then $g$ and $g+h$ have the same number of zeros (with multiplicity) inside $\gamma$.*

Take $\gamma=\{|z|=1\}$ and split $f=g+h$ with the dominant constant as $g$:
$$
g(z)=6,\qquad h(z)=z^4-3z^3+z^2 .
$$
Both are entire (polynomials), so the hypotheses on holomorphy hold. On $|z|=1$ we have $|z|=1$, hence by the triangle inequality
$$
|h(z)|=|z^4-3z^3+z^2|\le|z|^4+3|z|^3+|z|^2=1+3+1=5<6=|g(z)|.
$$
The inequality is strict at every point of the circle. By Rouché's theorem, $f=g+h$ has the same number of zeros in $|z|<1$ as $g(z)=6$. Since the constant $6$ has **no** zeros,
$$
\boxed{f\text{ has }0\text{ zeros in the unit disk.}}
$$
(As a bonus, $|f|\ge|g|-|h|>0$ on $|z|=1$, so $f$ has no zeros on the boundary either; all four roots of this degree-4 polynomial lie in $|z|>1$.)

### Part (b): polynomial growth forces $f$ to be a polynomial

**Theorem used (Cauchy's estimates).** *If $f$ is holomorphic on $|z|\le R$ with Taylor expansion $f(z)=\sum_{n\ge0}a_n z^n$, then from $a_n=\frac{1}{2\pi i}\oint_{|z|=R}\frac{f(z)}{z^{n+1}}\,dz$ one gets*
$$
|a_n|\le\frac{M(R)}{R^n},\qquad M(R):=\max_{|z|=R}|f(z)|.
$$

Since $f$ is entire it has a Taylor series $f(z)=\sum_{n=0}^\infty a_n z^n$ valid on all of $\mathbb{C}$, so the estimate holds for **every** $R>0$. The growth hypothesis gives $M(R)\le A+BR^m$, hence for each fixed $n$ and every $R>0$,
$$
|a_n|\le\frac{A+BR^m}{R^n}=\frac{A}{R^n}+\frac{B}{R^{\,n-m}}.
$$
Now fix any integer $n>m$. Then $n>0$ and $n-m>0$, so both terms on the right tend to $0$ as $R\to\infty$; since the left side does not depend on $R$,
$$
|a_n|\le\inf_{R>0}\Big(\frac{A}{R^n}+\frac{B}{R^{\,n-m}}\Big)=0\quad\Longrightarrow\quad a_n=0\qquad\text{for all integers }n>m .
$$
Therefore the only possibly-nonzero coefficients are $a_0,a_1,\dots,a_{\lfloor m\rfloor}$, and
$$
f(z)=\sum_{n=0}^{\lfloor m\rfloor}a_n z^n,
$$
a **polynomial**. $\qquad\blacksquare$

**Conclusions about this polynomial.**
- $f$ is a polynomial of **degree at most $\lfloor m\rfloor$** (the greatest integer $\le m$). In particular, if $m$ is itself a positive integer, $\deg f\le m$.
- This is the **generalized Liouville theorem**: the classical Liouville theorem is the case $m<1$ (e.g. $f$ bounded, $|f|\le A$), where the bound forces $a_n=0$ for all $n\ge1$ and $f$ is **constant**.
- The bound is sharp: any polynomial of degree exactly $d\le m$ satisfies $|f(z)|\le A+B|z|^m$ for suitable $A,B$, so every degree up to $\lfloor m\rfloor$ actually occurs.

### Remark — one principle, two theorems

Both parts extract integer data from a modulus inequality. In (a), Rouché reads the inequality $|h|<|g|$ on a circle as "$f$ and $g$ wind the same number of times," i.e. enclose the same number of zeros — a topological count. In (b), Cauchy's estimates read the inequality $|f|\le A+B|z|^m$ on circles of growing radius as a ceiling on the Taylor coefficients, i.e. on the degree. The shared moral is that for holomorphic functions, control of $|f|$ on circles is enormously rigid — it pins down zeros and coefficients exactly, with no slack.
