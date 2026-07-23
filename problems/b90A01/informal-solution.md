<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b90A01: Simple groups embed in A_k via Sylow conjugation; no simple group has order 120

## Why It's Hard

This is a four-rung ladder, and each rung reuses one idea — **a nontrivial
homomorphism out of a simple group is injective** — against a different action:
conjugation on Sylow subgroups (a), the sign character (b), and left multiplication on
cosets (c). The genuine difficulty is (d): you must pick the *right* prime so the
embedding from (b) lands in an alternating group that is just barely too small for the
index bound (c) to tolerate. For $|G|=120$ the magic prime is $5$ (six Sylow
$5$-subgroups), which forces $G\hookrightarrow A_6$ at index $3$ — and $3$ is fatally
below the threshold $6$ that (c) requires.

## The Key Insight

A simple group $G$ has only the trivial quotients, so **any homomorphism
$\varphi:G\to H$ is either trivial or injective** (its kernel is normal, hence $\{e\}$
or $G$). Run this three times:
- conjugation on the $k>1$ Sylow $p$-subgroups is transitive (so nontrivial)
  $\Rightarrow$ $G\hookrightarrow S_k$;
- composing with $\operatorname{sgn}$ can't be injective (that would force
  $|G|\le 2$), so it is trivial $\Rightarrow$ $\varphi(G)\subseteq A_k$;
- for $A_k$ simple ($k\ge5$), left multiplication on the $m=[A_k:G]$ cosets embeds
  $A_k\hookrightarrow S_m$, so $k!/2\le m!$, forcing $m\ge k$.

Then $|G|=120$: $n_5=6$, so $G\hookrightarrow A_6$ with $[A_6:G]=3<6$, contradicting
(c). Hence no simple group of order $120$.

## Complete Proof

We use repeatedly: **(\*)** if $G$ is simple and $\varphi:G\to H$ is a group
homomorphism, then $\ker\varphi\trianglelefteq G$ is $\{e\}$ or $G$; so $\varphi$ is
injective or trivial.

### (a) $G\hookrightarrow S_k$

Let $X$ be the set of the $k$ Sylow $p$-subgroups of $G$, and let $G$ act on $X$ by
conjugation, $g\cdot P = gPg^{-1}$ (this is well defined: a conjugate of a Sylow
$p$-subgroup is a Sylow $p$-subgroup). This gives a homomorphism
$$
\varphi: G \to \operatorname{Sym}(X)\cong S_k .
$$
By Sylow's theorem the Sylow $p$-subgroups form a single conjugacy class, so the action
is **transitive**; since $k>1$, the action moves points, so $\varphi$ is **not
trivial**. By (\*), $\varphi$ is injective. Hence $G\cong\varphi(G)\le S_k$.
$\quad\checkmark$

### (b) $G\hookrightarrow A_k$

Compose $\varphi$ from (a) with the sign homomorphism $\operatorname{sgn}:S_k\to\{\pm
1\}$ to get $\psi=\operatorname{sgn}\circ\varphi:G\to\{\pm1\}$, with
$\ker\psi=\varphi^{-1}(A_k)\trianglelefteq G$. By (\*), $\ker\psi$ is $\{e\}$ or $G$.

If $\ker\psi=\{e\}$ then $\psi$ embeds $G$ into $\{\pm1\}$, so $|G|\le 2$. But the
action in (a) is transitive on $k$ points, so $k\mid|G|$, and $n_p=k$ with
$n_p\equiv1\pmod p$, $k>1$ gives $k\ge p+1\ge 3$; thus $|G|\ge k\ge 3>2$, a
contradiction. Therefore $\ker\psi=G$, i.e. $\psi$ is trivial: every $\varphi(g)$ is an
even permutation. Hence $\varphi(G)\subseteq A_k$, and $\varphi$ embeds
$G\hookrightarrow A_k$. $\quad\checkmark$

### (c) If $G$ is simple and a proper subgroup of $A_k$ with $k\ge5$, then $[A_k:G]\ge k$

Let $m=[A_k:G]$ and let $A_k$ act on the set of $m$ left cosets $A_k/G$ by left
multiplication, $\rho:A_k\to \operatorname{Sym}(A_k/G)\cong S_m$. The kernel
$\ker\rho=\bigcap_{a\in A_k} aGa^{-1}\subseteq G$ is normal in $A_k$. For $k\ge 5$,
$A_k$ is **simple**, so $\ker\rho\in\{\{e\},A_k\}$; since $\ker\rho\subseteq G\subsetneq
A_k$ it cannot be $A_k$, so $\ker\rho=\{e\}$ and $\rho$ is injective:
$$
A_k\hookrightarrow S_m,\qquad\text{hence}\qquad |A_k|=\frac{k!}{2}\le m! .
$$
Suppose for contradiction $m\le k-1$. Then $m!\le (k-1)!$, so $\frac{k!}{2}\le(k-1)!$,
i.e. $\frac{k}{2}\le 1$, i.e. $k\le 2$ — contradicting $k\ge5$. Therefore
$m=[A_k:G]\ge k$. $\quad\checkmark$

### (d) No group of order $120$ is simple

Suppose, for contradiction, that $G$ is simple with $|G|=120=2^3\cdot3\cdot5$.

Count Sylow $5$-subgroups: $n_5\equiv1\pmod5$ and $n_5\mid 120/5=24$. The divisors of
$24$ that are $\equiv1\pmod5$ are $1$ and $6$. If $n_5=1$ the unique Sylow $5$-subgroup
would be normal, contradicting simplicity (it is a proper nontrivial subgroup). Hence
$n_5=6>1$.

Apply (b) with $p=5$, $k=n_5=6\ (\ge5)$: $G$ embeds as a subgroup of $A_6$. Since
$|A_6|=\tfrac{6!}{2}=360$,
$$
[A_6:G]=\frac{360}{120}=3 .
$$
Thus $G$ is a simple subgroup of $A_6$ of index $3$, in particular **proper**, and
$k=6\ge5$. By (c), $[A_6:G]\ge 6$. But $[A_6:G]=3<6$ — contradiction.

Therefore $G$ cannot be simple: every group of order $120$ has a proper nontrivial
normal subgroup. $\quad\blacksquare$

### Remark

The whole argument is the slogan "nontrivial out of simple $\Rightarrow$ injective"
applied to three natural actions, plus the simplicity of $A_k$ ($k\ge5$) for the index
bound. Part (d) is a template: a simple group of order $n$ with $n_p=k$ embeds in
$A_k$, and if $|A_k|/n<k$ then (c) is violated. (For $120$ one could also finish from
$G\hookrightarrow A_6$ by noting $A_6$ is simple and a proper subgroup of index $3$
would give $A_6\hookrightarrow S_3$, absurd since $360>6$ — which is exactly the
mechanism of (c).)
