<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00A03: Pants decompositions of a genus-$g$ surface — complementary pieces are pairs of pants, and there are $3g-3$ curves

## Why It's Hard

This is the **pants decomposition** theorem for a closed orientable surface $F$ of genus $g\ge2$, and it asks for two things that feed each other:

- **(a) Identifying the pieces.** One must show that cutting along a *maximal* system of disjoint, essential, pairwise-nonparallel simple closed curves leaves only **three-holed spheres** (pairs of pants). The difficulty is turning the three hypotheses — *essential*, *disjoint*, *nonparallel*, plus *maximal* — into exactly the right structural constraint: essentialness rules out disk pieces, nonparallelism rules out annulus pieces, and **maximality** rules out everything more complicated than a pair of pants (because any more complicated piece would contain *another* curve you could add).
- **(b) Counting.** Showing the maximal number is $3g-3$ (the statement's "$3g-g$" is a typo) is a bookkeeping miracle that drops out of **two conservation laws**: the Euler characteristic is preserved under cutting, and each curve contributes exactly two boundary circles. The trap is trying to count curves directly; the clean route counts *pieces* via $\chi$ and then converts to curves via boundary circles.

A subtler hazard is rigor about "essential/nonparallel in a complementary piece $\Rightarrow$ essential/nonparallel in $F$," which rests on the **incompressibility** of an essential curve system.

## The Key Insight

Cut $F$ along the curve system $\mathcal C=\{c_1,\dots,c_n\}$ to get a compact surface $F_{\mathcal C}$ (with boundary). Two invariants govern everything:

1. **Euler characteristic is preserved by cutting along circles** (a circle has $\chi=0$): $\chi(F_{\mathcal C})=\chi(F)=2-2g$.
2. **Each two-sided curve becomes two boundary circles**: $F_{\mathcal C}$ has exactly $2n$ boundary circles.

The pair of pants $\Sigma_{0,3}$ (sphere with $3$ holes) is the unique "atom": it has $\chi=2-0-3=-1$ and admits **no** essential non-peripheral simple closed curve. Maximality forces every complementary piece to be exactly such an atom — not a disk (essentialness), not an annulus (nonparallelism), and not anything with $\chi\le-2$ (else it contains another addable curve). Then, with $P$ pieces:
$$
\underbrace{-P=\chi(F)=2-2g}_{\Rightarrow\ P=2g-2}\qquad\text{and}\qquad \underbrace{3P=2n}_{\text{boundary count}}\ \Rightarrow\ n=\tfrac{3}{2}P=3g-3 .
$$

## Complete Proof

Throughout, "curve" means simple closed curve, and a compact orientable surface of genus $h$ with $b$ boundary circles, $\Sigma_{h,b}$, has Euler characteristic $\chi(\Sigma_{h,b})=2-2h-b$. A **pair of pants** is $\Sigma_{0,3}$, the thrice-holed sphere, with $\chi=-1$. Since $F$ is orientable, every simple closed curve in $F$ is two-sided.

Let $\mathcal C=\{c_1,\dots,c_n\}$ be a maximal collection of essential, pairwise disjoint, pairwise nonparallel curves, and let $F_{\mathcal C}$ be the result of cutting $F$ along $\mathcal C$.

### Preliminary: two conservation laws

**($\chi$ is preserved.)** If a surface $F$ is split by a circle $c$ into $F=A\cup B$ with $A\cap B=c$, then by inclusion–exclusion $\chi(F)=\chi(A)+\chi(B)-\chi(c)=\chi(A)+\chi(B)$ since $\chi(c)=0$; the cut surface is the disjoint union $A\sqcup B$ with the same total $\chi$. Iterating over all $n$ curves,
$$
\chi(F_{\mathcal C})=\chi(F)=2-2g .
$$

**(Boundary count.)** Each $c_i$ is two-sided, so cutting along it replaces $c_i$ by **two** boundary circles. The curves are disjoint, so cutting is done independently, and $F_{\mathcal C}$ has exactly $2n$ boundary circles in total. Every such circle is a copy of some $c_i$.

### Part (a): every complementary piece is a pair of pants

Let $R$ be a connected component of $F_{\mathcal C}$; it is a compact orientable surface with boundary, each boundary circle a copy of some $c_i$. We show $R\cong\Sigma_{0,3}$ by excluding all other possibilities.

**$R$ is not a disk $\Sigma_{0,1}$.** If $R$ were a disk, its single boundary circle — a copy of some $c_i$ — would bound a disk in $F$, contradicting that $c_i$ is **essential**.

**$R$ is not an annulus $\Sigma_{0,2}$.** Suppose $R$ is an annulus, with boundary circles copies of $c_i$ and $c_j$.
- If $c_i\ne c_j$, then $c_i$ and $c_j$ cobound the annulus $R$ in $F$, i.e. they are **parallel** — contradicting nonparallelism.
- If $c_i=c_j$ (both boundaries are the two sides of the *same* curve), then a regular neighborhood of $c_i$ together with $R$ shows $c_i$ has an annular complement on that side; gluing the two ends realizes a subsurface that makes $c_i$ either inessential or parallel to itself in a way already excluded — concretely, then $F$ would be a torus (if $n=1$) or $c_i$ would be removable, impossible for $g\ge2$ with $\mathcal C$ essential. Either way $R$ is not an annulus.

**$R$ has $\chi(R)=-1$, hence $R\cong\Sigma_{0,3}$.** It remains to exclude $\chi(R)\le-2$. We use:

> **Lemma.** A compact orientable surface $R$ with $\chi(R)\le-2$ contains an essential, non-boundary-parallel simple closed curve $\gamma$ in its interior.

*Proof of Lemma.* Write $R=\Sigma_{h,b}$, so $\chi(R)=2-2h-b\le-2$, i.e. $2h+b\ge4$.
- If $h\ge1$: take a **nonseparating** curve $\gamma$ in $R$ (e.g. a meridian of a handle). A nonseparating curve cannot bound a disk (disks separate) and cannot be boundary-parallel (boundary-parallel curves are separating). So $\gamma$ is essential and non-peripheral.
- If $h=0$ and $b\ge4$: $R$ is a planar sphere-with-holes. Take a curve $\gamma$ partitioning the $b$ boundary circles into two groups of sizes $\ge2$ and $\ge2$. Then each side of $\gamma$ is a planar surface with $\ge3$ boundary circles ($\ge2$ originals plus $\gamma$), hence is neither a disk (so $\gamma$ is essential) nor an annulus (so $\gamma$ is not boundary-parallel). $\square$

Now suppose, for contradiction, some piece $R$ has $\chi(R)\le-2$. By the Lemma it contains an essential, non-peripheral curve $\gamma$, which we push into the interior of $R\subset F$, so $\gamma$ is **disjoint** from every $c_i$. We claim $\gamma$ contradicts maximality, i.e. $\mathcal C\cup\{\gamma\}$ is again a system of essential, disjoint, pairwise-nonparallel curves:

- *$\gamma$ is essential in $F$.* If $\gamma$ bounded a disk $D$ in $F$, consider $D\cap\mathcal C$. An innermost circle of $D\cap\mathcal C$ on $D$ would bound a subdisk of $D$ meeting no $c_i$ in its interior; that subdisk shows the corresponding $c_i$ bounds a disk, contradicting essentialness — unless $D\cap\mathcal C=\varnothing$, in which case $D\subset R$ and $\gamma$ bounds a disk *in $R$*, contradicting the Lemma's conclusion. So $\gamma$ is essential.
- *$\gamma$ is nonparallel to each $c_i$.* If $\gamma$ and $c_i$ cobounded an annulus $A$ in $F$, a similar innermost argument confines $A$ to $R$, making $\gamma$ boundary-parallel in $R$ — again contradicting the Lemma.

Thus $\mathcal C\cup\{\gamma\}$ is a strictly larger admissible system, contradicting the maximality of $\mathcal C$. Therefore no piece has $\chi\le-2$.

Combining: each piece $R$ is connected, orientable, not a disk, not an annulus, and has $\chi(R)>-2$. The only such surface is $\chi(R)=-1$ with $(h,b)=(0,3)$, i.e. $R\cong\Sigma_{0,3}$, a **pair of pants** (three-holed sphere). Hence $\mathcal C$ cuts $F$ into pairs of pants. $\qquad\checkmark$

### Part (b): the maximal number of curves is $3g-3$

Let $P$ be the number of complementary pieces; by part (a) each is a pair of pants with $\chi=-1$ and exactly $3$ boundary circles.

**Count pieces via Euler characteristic.** Since $F_{\mathcal C}$ is the disjoint union of the $P$ pieces,
$$
2-2g=\chi(F)=\chi(F_{\mathcal C})=\sum_{\text{pieces}}\chi(\Sigma_{0,3})=P\cdot(-1)=-P,
$$
so
$$
P=2g-2 .
$$

**Count curves via boundary circles.** Summing boundary circles over the pieces gives $3P$ (three per pair of pants). On the other hand, the boundary circles of $F_{\mathcal C}$ are exactly the $2n$ copies of the curves $c_i$ (two per curve). Every boundary circle is counted once on each side of the ledger, so
$$
3P=2n\ \Longrightarrow\ n=\frac{3P}{2}=\frac{3(2g-2)}{2}=3(g-1)=3g-3 .
$$

Therefore the maximal number of curves is $\boxed{\,n=3g-3\,}$ (and the decomposition has $P=2g-2$ pairs of pants). $\qquad\blacksquare$

### Remark — why the atoms are pants, and a sanity check

The argument is a clean instance of a recurring principle: a *maximal* disjoint collection of essential, nonparallel curves is exactly a collection whose complementary pieces have **minimal complexity** $|\chi|=1$, the pairs of pants — the surfaces that are "rigid" in that they carry no further essential non-peripheral curve. Two conservation laws then pin the numbers down with no further geometry: additivity of $\chi$ under cutting fixes the number of pieces, and the two-to-one correspondence between curves and boundary circles fixes the number of curves.

As a check, the genus-$2$ surface gives $n=3\cdot2-3=3$ curves cutting it into $P=2\cdot2-2=2$ pairs of pants — the familiar picture of two pants glued along three cuffs. The complexity $3g-3$ is also the dimension of Teichmüller space's "length" coordinates (half of its real dimension $6g-6$), reflecting that a pants decomposition has exactly $3g-3$ cuff-length parameters, the Fenchel–Nielsen lengths.
