<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b01A02: Smallest-prime-index subgroups are normal, and every group of order 255 is cyclic

## Why It's Hard

**Part (a)** looks like it should follow from Sylow theory, but it does not: index $p$ says nothing about $H$ being a Sylow subgroup, and $H$ can be enormous. The only handle is the **action of $G$ on the $p$ cosets of $H$**, which lands $G$ in $S_p$ — and then the proof rests entirely on a divisibility *squeeze* that secretly uses the easily-overlooked hypothesis that $p$ is the **smallest** prime dividing $|G|$. The image order must divide both $|G|$ and $p!$; minimality of $p$ is exactly what forces those two constraints to intersect in the single value $p$, which collapses $H$ onto a kernel. Drop "smallest" and the statement fails: in $S_4$ (order $24$, smallest prime $2$) the Sylow $2$-subgroups have order $8$, i.e. index $3$, and there are three of them — non-normal. So index $3$ guarantees normality only when $3$ is the minimal prime, as in part (b).

**Part (b)** is a full classification, and the difficulty is *orchestration*: Sylow gives one normal subgroup for free, but the Sylow $5$-count is **not** immediately forced to be $1$. The elegant escape is to *build* an order-$85$ subgroup using the normal Sylow-$17$, then deploy **part (a)** at index $3$ (the smallest prime!) to get its normality — sidestepping the stubborn $n_5$ entirely. The final cyclicity comes from a **coprimality of $\gcd$ with $|\mathrm{Aut}|$** argument that kills the semidirect-product twisting.

## The Key Insight

**(a)** A subgroup of index $p$ yields a homomorphism $\varphi:G\to S_p$ (left multiplication on cosets) whose kernel $K$ lies in $H$. Then $|G/K|$ divides **both** $|G|$ and $p!=p\cdot(p-1)!$. Every prime $q\mid |G/K|$ divides $|G|$ (so $q\ge p$, by minimality) and divides $p!$ (so $q\le p$); hence $q=p$, and the exact power of $p$ in $p!$ is $p^1$, so $|G/K|=p$. With $K\subseteq H$ and $[G:K]=p=[G:H]$, we get $H=K$ — a kernel, hence normal.

**(b)** Normality cascades, with $255=3\cdot5\cdot17$ and smallest prime $3$:
$$
\underbrace{P_{17}\trianglelefteq G}_{\text{Sylow}}\ \Rightarrow\ \underbrace{P_{17}Q\ \text{has order }85}_{\text{product, }P_{17}\text{ normal}}\ \xrightarrow[\text{part (a)}]{\text{index }3}\ \underbrace{H\trianglelefteq G}_{|H|=85}\ \Rightarrow\ \underbrace{H\cong\mathbb{Z}/85}_{\text{coprime Sylows}}\ \xrightarrow[\gcd(3,\,64)=1]{G=H\rtimes\mathbb{Z}/3}\ G\cong\mathbb{Z}/255 .
$$

## Complete Proof

### Part (a): a subgroup of index = smallest prime divisor is normal

Let $|G|=n$, let $p$ be the smallest prime dividing $n$, and let $H\le G$ with $[G:H]=p$. Let $G$ act on the set $X$ of $p$ left cosets of $H$ by left multiplication, giving a homomorphism
$$
\varphi:G\to \mathrm{Sym}(X)\cong S_p,\qquad K:=\ker\varphi .
$$
The kernel of this action is the **normal core** $K=\bigcap_{g\in G} gHg^{-1}\subseteq H$. By the first isomorphism theorem $G/K\hookrightarrow S_p$, so $m:=|G/K|$ satisfies
$$
m\mid p!\qquad\text{and}\qquad m\mid n \ \ (\text{as }m=[G:K]\text{ divides }|G|).
$$
Let $q$ be any prime dividing $m$. From $q\mid m\mid n$ and minimality of $p$, $q\ge p$. From $q\mid m\mid p!$, $q\le p$ (every prime factor of $p!$ is $\le p$). Hence $q=p$, so $m$ is a power of $p$. But $p!=p\cdot(p-1)!$ with $p\nmid (p-1)!$, so the largest power of $p$ dividing $p!$ is $p^1$; thus $m\mid p!$ forces $m\le p$, i.e. $m\in\{1,p\}$.

Finally, $K\subseteq H$ gives $[G:K]=[G:H]\,[H:K]=p\,[H:K]$, so $p\mid m$ and therefore $m=p$. Then $[H:K]=1$, i.e.
$$
H=K=\ker\varphi\ \trianglelefteq\ G. \qquad\checkmark
$$

### Part (b): every group of order 255 is cyclic

Let $|G|=255=3\cdot 5\cdot 17$. The smallest prime divisor is $3$.

**Step 1 — a normal subgroup of order $17$.** By Sylow, the number $n_{17}$ of Sylow $17$-subgroups satisfies $n_{17}\equiv 1\pmod{17}$ and $n_{17}\mid 255/17=15$. The divisors of $15$ are $1,3,5,15$, and only $1$ is $\equiv 1\pmod{17}$. Hence $n_{17}=1$: the Sylow $17$-subgroup $P_{17}$ is unique, hence **normal**, of order $17$.

**Step 2 — a cyclic normal subgroup of order $85$.** Let $Q$ be a Sylow $5$-subgroup ($|Q|=5$). Since $P_{17}\trianglelefteq G$, the product $H:=P_{17}Q$ is a subgroup, with
$$
|H|=\frac{|P_{17}|\,|Q|}{|P_{17}\cap Q|}=\frac{17\cdot 5}{1}=85
$$
(the intersection is trivial as $\gcd(17,5)=1$). Now $[G:H]=255/85=3$, and $3$ is the **smallest prime dividing** $|G|$, so by **part (a)** $H\trianglelefteq G$. Finally $H$ is cyclic: for $|H|=85=5\cdot 17$, Sylow gives $n_{17}\mid 5,\ n_{17}\equiv1\,(17)\Rightarrow n_{17}=1$ and $n_5\mid 17,\ n_5\equiv1\,(5)\Rightarrow n_5=1$ (since $17\equiv 2\pmod 5$), so both Sylow subgroups of $H$ are normal and
$$
H\cong \mathbb{Z}/5\times\mathbb{Z}/17\cong\mathbb{Z}/85 .
$$
Thus $H$ is a **cyclic normal subgroup of order $85$**.

**Step 3 — $G$ is cyclic.** Let $P_3$ be a Sylow $3$-subgroup, $|P_3|=3$. Since $H\trianglelefteq G$, $H\cap P_3=\{e\}$ (coprime orders), and $|HP_3|=85\cdot 3=255=|G|$, we have
$$
G=H\rtimes P_3,
$$
a semidirect product determined by a homomorphism $\theta:P_3\to\mathrm{Aut}(H)$. But
$$
|\mathrm{Aut}(H)|=|\mathrm{Aut}(\mathbb{Z}/85)|=\varphi(85)=\varphi(5)\varphi(17)=4\cdot 16=64,
$$
and a homomorphism from $P_3\cong\mathbb{Z}/3$ into a group of order $64$ has image of order dividing $\gcd(3,64)=1$. Hence $\theta$ is trivial, the semidirect product is direct, and
$$
G\cong H\times P_3\cong\mathbb{Z}/85\times\mathbb{Z}/3\cong\mathbb{Z}/255
$$
(the last isomorphism because $\gcd(85,3)=1$). Therefore $G$ is **cyclic**. $\qquad\blacksquare$

### Remark — the pattern and the role of arithmetic

Part (a) is the workhorse "smallest-prime-index $\Rightarrow$ normal" theorem; the index-$2$ case (always normal) is its most familiar instance. Part (b) shows how a numerical coincidence — $255=3\cdot5\cdot17$ with these particular primes — forces a unique group up to isomorphism. The deep reason order-$255$ groups are all cyclic is that $255$ is a **cyclic number**: $\gcd(255,\varphi(255))=\gcd(255,128)=1$. By a theorem of (essentially) Burnside/Hölder, a group order $n$ forces cyclicity exactly when $\gcd(n,\varphi(n))=1$, and the three places we invoked "$\gcd(\cdot,\cdot)=1$" (in $n_{17}$, in building $H$, and in $\gcd(3,64)$) are local manifestations of that single global fact. Part (a)'s use at index $3$ is the linchpin that converts the free normal Sylow-$17$ into the order-$85$ normal subgroup without ever having to pin down $n_5$ directly.
