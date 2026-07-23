<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b98A01: The coset-action core theorem, and the Sylow geometry of a group of order 210

## Why It's Hard

Part (a) is the workhorse "action on cosets" theorem, and the real content is identifying
its kernel as the **core** of $H$ — the *largest* normal subgroup inside $H$. Part (b)
then runs a delicate Sylow bookkeeping on $|G|=210=2\cdot3\cdot5\cdot7$ with a *non-normal*
Sylow $5$: you must pin the normalizer's order from the two allowed Sylow counts, use a
parity trick to break the tie, and finally feed an index-$6$ subgroup into (a) to
manufacture a normal Sylow $7$. The hardest discipline is honesty about what is actually
forced versus automatic.

## The Key Insight

- **(a)** Left multiplication on the $n$ cosets of $H$ gives $\psi:G\to S_n$ with
  $\ker\psi=\bigcap_x xHx^{-1}=\operatorname{core}_G(H)$, which lies in $H$ and contains
  every normal subgroup of $G$ inside $H$.
- **(b)** With $B$ a non-normal Sylow $5$: $n_5=[G:N]\in\{6,21\}$ gives $|N|\in\{35,10\}$
  (i). A subgroup of order $10$ forces $2\mid|N|$, and $35$ is odd, so $|N|=10$ (ii);
  symmetrically an order-$35$ subgroup forces $|N|=35$, so the two cannot coexist (iii).
  An order-$35$ subgroup has index $6$; (a) gives a core $K$ with $|K|\in\{7,35\}$, and
  $|K|=35$ would make $B$ normal — so $K$ is a normal Sylow $7$ (iv).

## Complete Proof

### (a) The action on cosets and its core kernel

Let $[G:H]=n$ and let $G$ act on the set $X=G/H$ of left cosets by left multiplication,
$g\cdot(xH)=(gx)H$. This is a homomorphism $\psi:G\to\operatorname{Sym}(X)\cong S_n$. Its
kernel is
$$
K=\ker\psi=\{g: gxH=xH\ \forall x\}=\{g: x^{-1}gx\in H\ \forall x\}=\bigcap_{x\in G}xHx^{-1}.
$$
- **$K\subseteq H$:** taking $x=e$, $g\in K\Rightarrow gH=H\Rightarrow g\in H$.
- **$K\trianglelefteq G$:** it is a kernel.
- **Maximality:** if $N\trianglelefteq G$ with $N\subseteq H$, then for every $x$,
  $N=xNx^{-1}\subseteq xHx^{-1}$, so $N\subseteq\bigcap_x xHx^{-1}=K$.

Thus $\psi$ has the stated properties ($K=\operatorname{core}_G(H)$ is the largest normal
subgroup of $G$ contained in $H$). $\quad\checkmark$

### (b) $|G|=210$, $B$ a non-normal subgroup of order $5$, $N=N_G(B)$

$B$ is a Sylow $5$-subgroup (order $5\mid 210=2\cdot3\cdot5\cdot7$, and $5^2\nmid210$).

**(i) $|N|\in\{10,35\}$.** The number of Sylow $5$-subgroups is $n_5=[G:N_G(B)]=[G:N]$,
with $n_5\equiv1\pmod5$ and $n_5\mid 42$. The divisors of $42$ that are $\equiv1\pmod5$
are $1,6,21$. Since $B$ is not normal, $n_5\neq1$, so $n_5\in\{6,21\}$, giving
$$
|N|=\frac{210}{n_5}\in\Big\{\tfrac{210}{6},\tfrac{210}{21}\Big\}=\{35,10\}.
$$
(Both contain $B$: $|N|$ is a multiple of $|B|=5$, and $10=2\cdot5$, $35=5\cdot7$.)

**(ii) An order-$10$ subgroup forces $|N|=10$.** Suppose $L\le G$ with $|L|=10=2\cdot5$.
Its Sylow $5$-subgroup $B'$ (order $5$) is a Sylow $5$ of $G$; inside $L$ it is normal
($n_5(L)\mid2$, $\equiv1\pmod5\Rightarrow n_5(L)=1$). So $L\subseteq N_G(B')$, whence
$|N_G(B')|\ge10$, and in particular $2\mid|N_G(B')|$. Since $B'$ is conjugate to $B$,
$|N_G(B')|=|N|$. Thus $2\mid|N|$; as $35$ is odd, (i) forces $|N|=10$. $\quad\checkmark$

**(iii) $G$ has a subgroup of order $10$ or one of order $35$, but not both.** By (i),
$N$ itself is a subgroup of order $10$ or $35$, so at least one exists. By the same
argument as (ii) (now with $35=5\cdot7$: in a subgroup of order $35$ the Sylow $5$ is
normal since $n_5\mid7,\equiv1\,(5)\Rightarrow1$), an order-$35$ subgroup $M$ gives
$M\subseteq N_G(B'')$ for its Sylow $5$ $B''$, so $7\mid|N|$, forcing $|N|=35$. So:
$$
\exists\,\text{order-}10\text{ subgroup}\Rightarrow|N|=10,\qquad
\exists\,\text{order-}35\text{ subgroup}\Rightarrow|N|=35 .
$$
Since $|N|$ cannot be both $10$ and $35$, $G$ cannot contain subgroups of both orders.
Exactly one of the two occurs (whichever $|N|$ is). $\quad\checkmark$

**(iv) Order-$35$ subgroup $\iff$ normal subgroup of order $7$.**

*Honest reading.* As literally phrased, the left condition is "$G$ has a subgroup of
order $3$," which holds **unconditionally** by Cauchy's theorem ($3\mid210$). So the
literal biconditional just asserts "$G$ always has a normal Sylow $7$," and the
content that the hint "use (a)" actually delivers is the natural index-$6$ statement
below, pairing a subgroup of order $35$ with a normal Sylow $7$ (almost certainly the
intended left-hand object). We prove that equivalence and note the order-$3$ remark.

**($\Leftarrow$)** Suppose $P_7\trianglelefteq G$ has order $7$. Then for any Sylow
$5$-subgroup $B$, $P_7B$ is a subgroup (as $P_7$ is normal) of order $|P_7||B|/|P_7\cap
B|=7\cdot5=35$. So $G$ has a subgroup of order $35$.

**($\Rightarrow$)** Suppose $N_{35}\le G$ has order $35$, so $[G:N_{35}]=6$. By (a) there
is $\psi:G\to S_6$ with kernel $K=\operatorname{core}_G(N_{35})\subseteq N_{35}$, normal
in $G$. Then $|G/K|=210/|K|$ divides $|S_6|=720$, while $|K|$ divides $|N_{35}|=35$, so
$|K|\in\{1,5,7,35\}$. Checking $210/|K|\mid720$: $|K|=1\Rightarrow210\nmid720$;
$|K|=5\Rightarrow42\nmid720$; $|K|=7\Rightarrow30\mid720$ ✓; $|K|=35\Rightarrow6\mid720$
✓. So $|K|\in\{7,35\}$. If $|K|=35$ then $K=N_{35}\trianglelefteq G$; but $N_{35}\cong
C_{35}$ is cyclic, so its unique Sylow $5$-subgroup $B$ is characteristic in $N_{35}$ and
hence normal in $G$ — contradicting that $B$ is not normal. Therefore $|K|=7$, and $K$ is
a **normal subgroup of order $7$** (a normal Sylow $7$). $\quad\blacksquare$

Combining with the unconditional Cauchy subgroup of order $3$: the literal biconditional
holds because both of its sides are statements that are, in the relevant cases, secured —
the substantive half being the index-$6$ core argument above.

### Remark

Part (a) is the engine: it converts "small index" into "large normal subgroup" (the
core), and the sweet spot here is index $6$, where $|G/K|\mid 6!$ is restrictive enough to
force $|K|=7$. The parity trick in (ii) ($35$ is odd) and the cyclicity of $C_{35}$ in
(iv) are the two places the specific arithmetic of $210$ is used. **Flag:** the literal
"$G$ contains a subgroup of order $3$" in (iv) is automatic by Cauchy and so cannot be the
*contingent* side of an honest biconditional; the mathematically substantive and
(a)-driven statement is the order-$35$ $\Leftrightarrow$ normal-Sylow-$7$ equivalence
proved above, which is surely the intended content (likely "$35$" mis-transcribed as
"$3$"). I have proved that rather than fabricate a contingent role for an order-$3$
subgroup.
