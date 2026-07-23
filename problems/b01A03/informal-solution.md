<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b01A03: For a submodule of a f.g. free module over a PID, complemented = free quotient = saturated

## Why It's Hard

The three conditions are stated in three different dialects: (a) is a **splitting**
($M = S\oplus T$), (b) is a **freeness** of the quotient, and (c) is a
**divisibility/saturation closure** (you can't have a multiple $ay$ land in $S$
without $y$ itself being in $S$). Nothing on the surface connects "splits off as a
summand," "quotient has a basis," and "closed under division." The bridge is the
*structure theory of finitely generated modules over a PID*, which supplies three
otherwise-magical facts — submodules of free are free, finitely generated
torsion-free is free, and free is projective — and the entire equivalence is the
shadow these cast.

## The Key Insight

Condition (c) is exactly "**$M/S$ is torsion-free**" in disguise: $ay\in S$ with
$a\neq 0$ says $a\cdot\overline{y}=0$ in $M/S$, and (c) demands $\overline{y}=0$. So
(c) $\iff$ $M/S$ has no nonzero torsion. Over a PID, for the finitely generated
module $M/S$,
$$
\text{torsion-free} \iff \text{free} \iff \text{projective} \iff \text{the sequence } 0\to S\to M\to M/S\to 0 \text{ splits},
$$
and "splits" is precisely "$S$ is complemented." The whole problem collapses to this
single chain. The one direction that uses $M$ being free is (a)$\Rightarrow$(b),
where the complement $T\cong M/S$ is a submodule of a free module, hence free.

## Complete Proof

Throughout, $R$ is a PID, $M$ is a finitely generated free $R$-module, $S\subseteq M$
a submodule, and $\pi:M\to M/S$ the quotient map. We use three standard facts about a
PID $R$:

- **(F1)** every submodule of a finitely generated free $R$-module is free (of rank
  $\le \operatorname{rank}M$);
- **(F2)** a finitely generated torsion-free $R$-module is free;
- **(F3)** a free module is projective, so any short exact sequence $0\to A\to B\to
  C\to 0$ with $C$ free **splits** (a basis of $C$ lifts to a section $C\to B$),
  giving $B\cong A\oplus C$.

We prove (a) $\Rightarrow$ (b) $\Rightarrow$ (c) $\Rightarrow$ (a).

### (a) $\Rightarrow$ (b)

Suppose $M = S\oplus T$ for some submodule $T\subseteq M$. The projection
$M\to M/S$ restricted to $T$ is an isomorphism $T\xrightarrow{\sim} M/S$ (it is
surjective since $M=S+T$, and injective since $T\cap S=0$). Now $T$ is a submodule of
the finitely generated free module $M$, so by **(F1)** $T$ is free. Hence
$M/S\cong T$ is free.

### (b) $\Rightarrow$ (c)

Suppose $M/S$ is free, and let $x\in S$, $x=ay$ with $a\neq 0$ in $R$ and $y\in M$.
Apply $\pi$: since $x\in S$, $\pi(x)=0$, while $\pi(x)=\pi(ay)=a\,\pi(y)$. Thus
$$
a\,\pi(y)=0 \quad\text{in } M/S .
$$
A free module is torsion-free (a basis is $R$-linearly independent, and $R$ is a
domain), so from $a\neq 0$ we conclude $\pi(y)=0$, i.e. $y\in S$. This is exactly (c).

### (c) $\Rightarrow$ (a)

**Step 1: (c) says $M/S$ is torsion-free.** Let $\overline{y}=\pi(y)\in M/S$ be a
torsion element: $a\,\overline{y}=0$ for some $a\neq 0$ in $R$. Then $ay\in S$; set
$x:=ay\in S$. Now $x=ay$ with $a\neq 0$ and $y\in M$, so (c) gives $y\in S$, i.e.
$\overline{y}=0$. Hence $M/S$ has no nonzero torsion element — it is torsion-free.

**Step 2: $M/S$ is free.** As a quotient of the finitely generated module $M$, the
module $M/S$ is finitely generated; being also torsion-free over the PID $R$, by
**(F2)** it is free.

**Step 3: the sequence splits.** Consider the short exact sequence
$$
0 \longrightarrow S \longrightarrow M \xrightarrow{\ \pi\ } M/S \longrightarrow 0 .
$$
By Step 2, $M/S$ is free, hence projective, so by **(F3)** the sequence splits: there
is a section $\sigma:M/S\to M$ with $\pi\circ\sigma=\mathrm{id}$, and
$$
M = S \oplus \sigma(M/S).
$$
Taking $T:=\sigma(M/S)$ exhibits $S$ as complemented, which is (a).

This closes the cycle, so (a), (b), and (c) are equivalent. $\qquad\blacksquare$

### Remark

The argument shows the content is entirely in the quotient: **(b) and (c) are the
same statement** ("$M/S$ is free" $\equiv$ "$M/S$ is torsion-free", by (F2)), and (a)
is their splitting consequence (by (F3)). The hypothesis that $M$ is *free* is used
only lightly — in (a)$\Rightarrow$(b) via (F1) to see the complement is free; the
heart (c)$\Rightarrow$(a) needs only that $M/S$ is finitely generated. Over a general
integral domain the chain breaks: (F2) fails (torsion-free need not be free, e.g. a
non-principal ideal), so a saturated submodule need not be complemented.
