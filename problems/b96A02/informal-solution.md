<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b96A02: Order-30 groups, the core–splitting-field dictionary, and degree constraints via core-free subgroups

## Why It's Hard

This problem welds a Sylow-counting exercise (a) to a Galois-theory translation
(b) and then *uses the dictionary* to convert two delicate degree questions into
pure group theory (c, d). The conceptual hinge is part (b): the splitting field
of $\alpha$'s minimal polynomial is exactly the **normal closure** of $F(\alpha)$,
whose Galois group is the **core** of $H=\operatorname{Gal}(L/F(\alpha))$ — so
"$L$ is *already* the splitting field" becomes "the core is trivial," i.e. $H$ is
**core-free**. Once you see that, (c) and (d) are: *what indices can a core-free
subgroup have?* The traps are (i) in (a), forgetting that "a subgroup of order 15"
is automatically index $2$ hence normal, and that the order-$3$/$5$ subgroups are
normal because they are *characteristic inside* the normal order-$15$ subgroup;
(ii) in (c), realizing that a core-free $H$ can contain **no** subgroup of order
$3,5,15$, which by (a) are all normal — pinning $|H|\in\{1,2\}$; (iii) in (d),
recognizing that "splitting field of a degree-$d$ polynomial" means "core-free
subgroup of index $d$," so the task is the group-theoretic implication *core-free
index 6 $\Rightarrow$ core-free index 9* in a group of order $18$.

## The Key Insight

For $L/F$ Galois with group $G$ and $K=F(\alpha)$, $H=\operatorname{Gal}(L/K)$:

$$
\boxed{\ L^{\operatorname{core}_G(H)}=\text{normal closure of }K=\text{splitting field of }\min(\alpha,F)\ }
$$

because $\operatorname{core}_G(H)=\bigcap_g gHg^{-1}$ has fixed field the
compositum $\prod_g g(K)=\prod_g F(g\alpha)=F(\{g\alpha\}_{g\in G})$, and the
$g\alpha$ are exactly the roots of $f=\min(\alpha,F)$. Hence

$$
L\text{ is the splitting field of }f\iff \operatorname{core}_G(H)=\{1\}
\iff H\text{ is core-free},
$$

and by the index–degree correspondence $\deg f=[K:F]=[G:H]$. So:

- **(c)** $|G|=30$: a core-free $H$ contains no normal subgroup $\neq1$; but by
  (a) *every* subgroup of order $3,5,15$ of $G$ is normal, so $H$ has order prime
  to $15$, i.e. $|H|\in\{1,2\}$ and $[G:H]\in\{30,15\}$.
- **(d)** $|G|=18$: "core-free of index $6$" means a **non-normal subgroup of
  order $3$**; "core-free of index $9$" means a **non-normal subgroup of order
  $2$**. The first forces $G$ non-abelian, hence the complement $\langle
  t\rangle$ to the normal Sylow $3$-subgroup is non-normal — supplying the second.

## Complete Proof

### Part (a): a normal subgroup of order 15, and normality of all order-3,5,15 subgroups

Let $|G|=30=2\cdot3\cdot5$. Write $n_p$ for the number of Sylow $p$-subgroups.

**Some Sylow subgroup of order $3$ or $5$ is normal.** By Sylow, $n_5\equiv
1\!\pmod5$ and $n_5\mid6$, so $n_5\in\{1,6\}$; and $n_3\equiv1\!\pmod3$,
$n_3\mid10$, so $n_3\in\{1,10\}$. Suppose $n_5=6$ and $n_3=10$. Distinct Sylow
$5$-subgroups meet trivially (prime order), so they contribute $6\cdot(5-1)=24$
elements of order $5$; likewise $n_3=10$ gives $10\cdot(3-1)=20$ elements of
order $3$. That is $24+20=44>30$ elements, impossible. Hence $n_5=1$ or $n_3=1$:
a Sylow $5$-subgroup $P$ ($|P|=5$) or a Sylow $3$-subgroup $Q$ ($|Q|=3$) is
normal.

**A normal subgroup of order $15$.** With (say) $P\trianglelefteq G$, the set
$N=PQ$ is a subgroup (product of a normal subgroup with any subgroup is a
subgroup), and since $\gcd(|P|,|Q|)=1$ we have $P\cap Q=\{1\}$, so
$|N|=|P||Q|=15$. (Symmetrically if $Q\trianglelefteq G$.) A subgroup of order
$15$ has index $[G:N]=30/15=2$, and **every index-$2$ subgroup is normal**; hence
$N\trianglelefteq G$ is a normal subgroup of order $15$. The same argument shows
*every* subgroup of order $15$ is normal (each has index $2$).

**The order-$3$ and order-$5$ subgroups are normal.** Apply Sylow inside the
group $N$ of order $15$: $n_5(N)\equiv1\!\pmod5$ and $\mid3$ gives $n_5(N)=1$;
$n_3(N)\equiv1\!\pmod3$ and $\mid5$ gives $n_3(N)=1$. So $N$ has a **unique**
subgroup $P_0$ of order $5$ and a **unique** subgroup $Q_0$ of order $3$; being
unique, each is **characteristic** in $N$. Since $N\trianglelefteq G$, a
characteristic subgroup of $N$ is normal in $G$; thus $P_0,Q_0\trianglelefteq G$.
These are Sylow $5$- and $3$-subgroups of $G$, and a normal Sylow subgroup is the
only one of its order, so $n_5(G)=n_3(G)=1$. Therefore every subgroup of order
$5$ (it must equal $P_0$) and every subgroup of order $3$ (must equal $Q_0$) is
normal. Combined with the index-$2$ remark, **every subgroup of $G$ of order
$3,5,$ or $15$ is normal.** $\quad\checkmark$

### Part (b): $L$ is the splitting field of $f$ iff $\operatorname{core}_G(H)=\{1\}$

By hypothesis $L/F$ is Galois with $G=\operatorname{Gal}(L/F)$, $\alpha\in L$,
$f=\min(\alpha,F)$, $K=F(\alpha)$, and $H=\operatorname{Gal}(L/K)$ is the subgroup
fixing $K$ (so $L^H=K$). Recall $\operatorname{core}_G(H)=\bigcap_{g\in
G}gHg^{-1}$, the largest normal subgroup of $G$ inside $H$.

**Fixed field of the core = normal closure of $K$.** Taking fixed fields turns
intersections of subgroups into composita of their fixed fields, and
$L^{gHg^{-1}}=g(L^H)=g(K)$, so
$$
L^{\operatorname{core}_G(H)}
=L^{\bigcap_g gHg^{-1}}
=\prod_{g\in G} g(K).
$$
Since $g$ fixes $F$ pointwise, $g(K)=g\bigl(F(\alpha)\bigr)=F(g\alpha)$, whence
$$
L^{\operatorname{core}_G(H)}=\prod_{g\in G}F(g\alpha)=F\bigl(\{g\alpha:g\in
G\}\bigr).
$$

**That field is the splitting field of $f$.** Because $L/F$ is normal and $f$ has
the root $\alpha\in L$, $f$ splits in $L$; and the roots of the *minimal*
polynomial $f$ are precisely the Galois conjugates $\{g\alpha:g\in G\}$ (the
$G$-orbit of $\alpha$). Hence the splitting field of $f$ inside $L$ is exactly
$F(\{g\alpha\})=L^{\operatorname{core}_G(H)}$.

**Conclusion.** $L$ is the splitting field of $f$ iff
$L=F(\{g\alpha\})=L^{\operatorname{core}_G(H)}$. By the Galois correspondence the
fixed field equals all of $L$ iff the group is trivial:
$$
L=L^{\operatorname{core}_G(H)}\iff \operatorname{core}_G(H)=\{1\}.
$$
Thus $L$ is the splitting field of $f$ $\iff\operatorname{core}_G(H)=\{1\}$, i.e.
$H$ is core-free. $\quad\checkmark$

*(Degree bookkeeping for (c),(d): $\deg f=[K:F]=[G:H]$.)*

### Part (c): if $|G|=30$ and $L$ is the splitting field of $f$, then $\deg f\in\{15,30\}$

Let $H=\operatorname{Gal}(L/F(\alpha))$, so $\deg f=[G:H]$ and, by (b),
$\operatorname{core}_G(H)=\{1\}$ — meaning $H$ contains **no** nontrivial normal
subgroup of $G$.

Suppose $3\mid|H|$. By Cauchy, $H$ has an element of order $3$, generating a
subgroup of order $3$; but by part (a) that subgroup is **normal in $G$** — a
nontrivial normal subgroup of $G$ inside $H$, contradicting
$\operatorname{core}_G(H)=\{1\}$. Hence $3\nmid|H|$. Identically, $5\nmid|H|$
(an order-$5$ subgroup would be normal in $G$ by (a)). Since $|H|\mid30=2\cdot3
\cdot5$ and is divisible by neither $3$ nor $5$, we get $|H|\mid2$, i.e.
$|H|\in\{1,2\}$. Therefore
$$
\deg f=[G:H]=\frac{30}{|H|}\in\{30,\,15\}.
$$
$\checkmark$

### Part (d): if $|G|=18$ and $L$ is the splitting field of a (degree-6) polynomial, it is the splitting field of a degree-9 polynomial

We read "$L$ is the splitting field of a polynomial of degree $d$" as for an
*irreducible* polynomial — consistent with (b),(c), where $f$ is a minimal
polynomial. By (b) this is equivalent to:
$$
G\text{ has a core-free subgroup }H\text{ with }[G:H]=d
$$
(forward: $H=\operatorname{Gal}(L/F(\alpha))$; backward: take $\alpha$ a
primitive element of $L^H/F$, then $\min(\alpha,F)$ has degree $[G:H]=d$ and, the
core being trivial, $L$ is its splitting field). Since $|G|=18$, index $6$ means
$|H|=3$ and index $9$ means $|H|=2$. For a subgroup of **prime order** the only
proper subgroup is trivial, so $\operatorname{core}_G(H)=\{1\}$ iff $H$ is not
normal. Thus the claim becomes the group statement:

> If $G$ ($|G|=18$) has a **non-normal subgroup of order $3$**, then it has a
> **non-normal subgroup of order $2$**.

*Setup.* $|G|=18=2\cdot3^2$. The Sylow $3$-subgroup $P$ has order $9$ and index
$2$, hence $P\trianglelefteq G$. Let $\langle t\rangle$ be a Sylow $2$-subgroup
($t^2=1$); since $P\cap\langle t\rangle=\{1\}$ and $|P||\langle t\rangle|=18$, we
have $G=P\rtimes\langle t\rangle$. Let $\tau:P\to P$, $\tau(p)=tpt^{-1}$, be the
conjugation action of $t$ (an automorphism with $\tau^2=\mathrm{id}$).

*The hypothesis forces $G$ non-abelian, hence $\tau\neq\mathrm{id}$.* In an
abelian group every subgroup is normal; a non-normal subgroup of order $3$
therefore makes $G$ non-abelian. If $\tau=\mathrm{id}$, then $t$ centralizes $P$,
so $G=P\times\langle t\rangle$; as $|P|=3^2$ makes $P$ abelian, $G$ would be
abelian — contradiction. Hence $\tau\neq\mathrm{id}$: there is $p\in P$ with
$tpt^{-1}\neq p$.

*Therefore $\langle t\rangle$ is non-normal.* For $p\in P$,
$$
p\,t\,p^{-1}=t\,(t^{-1}pt)\,p^{-1}=t\cdot\bigl(\tau^{-1}(p)\,p^{-1}\bigr),
$$
and $\tau^{-1}(p)p^{-1}\in P$. Thus $ptp^{-1}\in\langle t\rangle=\{1,t\}$ iff
$\tau^{-1}(p)p^{-1}=1$, i.e. $\tau(p)=p$. Choosing $p$ with $\tau(p)\neq p$ (which
exists since $\tau\neq\mathrm{id}$) gives $ptp^{-1}\notin\langle t\rangle$, so
$\langle t\rangle$ is **not normal** in $G$. It has order $2$, hence is a
core-free subgroup of index $9$.

*Translation back.* By (b) applied to $\langle t\rangle$: let $K'=L^{\langle
t\rangle}$, $[K':F]=[G:\langle t\rangle]=9$, take $\beta$ primitive for $K'/F$
with $g=\min(\beta,F)$ of degree $9$; since $\operatorname{core}_G(\langle
t\rangle)=\{1\}$, $L$ is the splitting field of $g$. Thus $L$ is the splitting
field of a (degree-$9$) polynomial. $\quad\blacksquare$

### Remark

The spine of the problem is the equivalence
$$
\text{“$L$ is the splitting field of }\min(\alpha,F)\text{”}\iff
\operatorname{core}_G\!\bigl(\operatorname{Gal}(L/F(\alpha))\bigr)=\{1\},
$$
i.e. *splitting-field-ness is core-freeness*, with the realized degree being the
index $[G:H]$. Parts (c) and (d) are then "which indices can a core-free subgroup
have?": for $|G|=30$ the abundance of normal subgroups (a) forces index $15$ or
$30$; for $|G|=18$ the single normal Sylow $3$-subgroup means a core-free index-6
subgroup (non-normal order $3$) can only occur in the non-abelian $C_3\times S_3$,
where the order-$2$ complement is itself non-normal, giving a core-free index-$9$
subgroup. (A check over all five groups of order $18$ confirms that a non-normal
order-$3$ subgroup occurs *only* in $C_3\times S_3$, which indeed has non-normal
order-$2$ subgroups; for the other four the hypothesis is vacuous.) The
divisibility/normality facts of (a) and the core dictionary of (b) are doing all
the work.
