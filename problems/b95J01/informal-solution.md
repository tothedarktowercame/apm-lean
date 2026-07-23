<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b95J01: The order of g modulo a finite-index subgroup, and why normality is needed

## Why It's Hard

The whole problem turns on a quantity that *looks* like "the order of $g$ in
$G/H$" — but $G/H$ is only a **group** when $H$ is normal, and the problem
deliberately makes you work with $H$ that need not be normal. So in part (a) you
cannot invoke quotient-group machinery; you must produce $k$ and its divisibility
property from the coset combinatorics alone. The clean move is to recognize the
set $\{m\in\mathbb{Z}:g^m\in H\}$ as a **subgroup of $\mathbb{Z}$**, which both
manufactures the smallest $k$ and forces the divisibility in one stroke. Part (b)
is then a one-line Lagrange argument — *once you are allowed to form the group
$G/H$*. The sting is part (c): you must realize that the only thing (b) used was
normality, and exhibit a case where dropping it breaks the conclusion. The trap
is reflexively trying $S_3$ with a $3$-cycle (which still divides the index and
proves nothing); the counterexample has to use an element whose coset-orbit
length is *coprime-ish* to the index — an involution against an index-$3$
subgroup.

## The Key Insight

Let $T=\{m\in\mathbb{Z}:g^m\in H\}$. Because $m\mapsto g^m$ is a homomorphism
$\mathbb{Z}\to G$ and $H\le G$, $T$ is the preimage of a subgroup, hence a
**subgroup of $(\mathbb{Z},+)$**. Every subgroup of $\mathbb{Z}$ is $k\mathbb{Z}$
for a unique $k\ge0$, so:

- finite index forces $T\neq\{0\}$ (the $n+1$ cosets $H,gH,\dots,g^nH$ can't be
  distinct), giving a **smallest positive** $k$ with $g^k\in H$;
- $g^m\in H\iff m\in k\mathbb{Z}\iff k\mid m$. That is part (a).

The geometric reading: $\langle g\rangle$ acts on the $n$ left cosets $G/H$ by
left multiplication, and $k$ is the **length of the orbit of the coset $H$**
(since $g^iH=H\iff g^i\in H$). Now the dichotomy is transparent:

- **$H$ normal** $\Rightarrow$ $G/H$ is a *group* of order $n$, $k=\operatorname{ord}(gH)$,
  and Lagrange gives $k\mid n$ — part (b).
- **$H$ not normal** $\Rightarrow$ $G/H$ is only a *set*; orbit lengths under
  $\langle g\rangle$ merely **sum** to $n$, they need not divide it. An
  involution $g$ ($k=2$) acting on $3$ cosets has orbit lengths $2+1$ — and
  $2\nmid 3$. That is part (c): $G=S_3$, $H=\langle(1\,2)\rangle$, $g=(1\,3)$.

## Complete Proof

Let $[G:H]=n<\infty$, and fix $g\in G$. Write $g^iH$ for left cosets.

### Part (a): existence of the smallest $k$, and $k\mid m$ whenever $g^m\in H$

Consider
$$
T=\{m\in\mathbb{Z}: g^m\in H\}.
$$
**$T$ is a subgroup of $\mathbb{Z}$.** Indeed $0\in T$ (as $g^0=e\in H$), and if
$m,m'\in T$ then $g^{m-m'}=g^m(g^{m'})^{-1}\in H$ because $H$ is closed under
products and inverses; so $m-m'\in T$. (Equivalently: $\varphi:\mathbb{Z}\to G$,
$\varphi(m)=g^m$, is a homomorphism and $T=\varphi^{-1}(H)$ is the preimage of a
subgroup, hence a subgroup.)

**$T\neq\{0\}$.** The $n+1$ cosets $H=g^0H,\,g^1H,\dots,g^nH$ lie among the only
$n$ distinct left cosets of $H$, so by pigeonhole $g^aH=g^bH$ for some
$0\le a<b\le n$. Then $g^{b-a}H=H$, i.e. $g^{b-a}\in H$ with $b-a$ a positive
integer; thus $T$ contains a positive integer.

Every nontrivial subgroup of $\mathbb{Z}$ is $k\mathbb{Z}$ where $k$ is its
smallest positive element. Concretely: let $k=\min\{m\in T:m>0\}$ (exists by
well-ordering). For any $m\in T$, divide $m=qk+r$ with $0\le r<k$; then
$$
g^{r}=g^{m-qk}=g^m\,(g^k)^{-q}\in H
$$
since $g^m\in H$ and $g^k\in H$. So $r\in T$ with $0\le r<k$; minimality of $k$
forces $r=0$, i.e. $k\mid m$. Conversely if $k\mid m$ then $g^m=(g^k)^{m/k}\in H$.

Therefore $k$ is the smallest positive integer with $g^k\in H$, and **$k$ divides
every integer $m$ (in particular every positive integer) for which $g^m\in H$**.
$\quad\checkmark$

### Part (b): if $H\trianglelefteq G$ then $k\mid [G:H]$

When $H$ is normal, the left cosets form the **quotient group** $G/H$, of order
$|G/H|=[G:H]=n$. In this group the coset $gH$ has a well-defined order, namely
the smallest positive integer $j$ with
$$
(gH)^j=g^jH=H\iff g^j\in H .
$$
By part (a) that smallest $j$ is exactly $k$, so $\operatorname{ord}(gH)=k$ in
$G/H$. By Lagrange's theorem the order of an element divides the order of the
group, hence
$$
k=\operatorname{ord}(gH)\ \big|\ |G/H|=[G:H].
$$
$\quad\checkmark$

### Part (c): a counterexample when $H$ is not normal

Take
$$
G=S_3,\qquad H=\langle (1\,2)\rangle=\{e,\,(1\,2)\},\qquad g=(1\,3).
$$

*$H$ has finite index $3$ but is not normal.* $|G|=6$, $|H|=2$, so
$[G:H]=3$. Normality fails: conjugating the generator,
$(1\,3)(1\,2)(1\,3)^{-1}=(2\,3)\notin H$, so $(1\,3)H(1\,3)^{-1}\neq H$.

*Compute $k$ for $g=(1\,3)$.* We need the smallest positive $k$ with
$g^k\in H=\{e,(1\,2)\}$. Now $g^1=(1\,3)\notin H$, while $g^2=e\in H$. Hence
$$
k=2 .
$$

*The conclusion of (b) fails.* Here $k=2$ and $[G:H]=3$, and $2\nmid 3$. So the
statement "$k$ divides the index" is **false** for this non-normal $H$.
$\quad\blacksquare$

*Why it breaks, conceptually.* $\langle g\rangle=\{e,(1\,3)\}$ acts on the three
left cosets of $H$ by left multiplication. The orbit of the coset $H$ is
$\{H,\,gH\}$, of length $k=2$, and the remaining coset
$\{(2\,3),(1\,2\,3)\}$ is a fixed point — so the orbit lengths are $2+1=3=[G:H]$.
Orbit lengths must **sum** to the index, but with $H$ non-normal there is no
group structure on $G/H$ to force each length to **divide** the index. Normality
is exactly what upgrades "sums to $n$" into "divides $n$" (via Lagrange in
$G/H$).

### Remark

The single idea is that $\{m:g^m\in H\}=k\mathbb{Z}$, so $k$ is "the order of $g$
relative to $H$." Normality is the hinge: it makes the coset space a quotient
*group*, and only then does Lagrange convert the orbit-length $k$ into a divisor
of the index. Part (c) is the minimal witness — the smallest symmetric group and
its smallest non-normal subgroup — that the hinge is essential.
