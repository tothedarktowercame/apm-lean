<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b90A02: Free ⟹ projective ⟹ flat, and ℚ as the flat-but-not-projective ℤ-module

## Why It's Hard

The four parts climb a ladder of increasing subtlety and end on a deliberate contrast. Parts (a)–(b) are "soft" homological algebra: the real work is *knowing which structural lemmas to invoke* — that tensoring with $R$ is the identity, that $\otimes$ commutes with direct sums, that direct sums and direct summands preserve exactness — and assembling them cleanly. The trap is being vague about what "exact" means after applying $\otimes$ and $\bigoplus$.

Part (c) demands recognizing $\mathbb{Q}$ in a useful guise: either as the **localization** $S^{-1}\mathbb{Z}$ (and knowing localization is exact) or as a **directed union of copies of $\mathbb{Z}$**. Neither is visible from the bare symbol "$\mathbb{Q}$"; the elementary verification (clearing denominators to check injectivity is preserved) is easy to fumble.

Part (d) is the punchline and the genuinely instructive part: it forces you to see that **flatness is strictly weaker than projectivity**. The obstruction is not homological bookkeeping but a concrete structural fact — $\mathbb{Q}$ is *divisible*, and over $\mathbb{Z}$ projective $=$ free, while a nonzero free abelian group is never divisible. Recognizing divisibility as the precise wedge between "flat" and "projective" is the insight the whole problem is built toward.

## The Key Insight

**Flatness propagates upward through gentle operations, starting from $R$ itself:**
$$
\underbrace{R\ \text{flat}}_{R\otimes M\cong M}\ \xrightarrow{\ \bigoplus\ }\ \underbrace{\text{free flat}}_{(a)}\ \xrightarrow{\ \text{summand}\ }\ \underbrace{\text{projective flat}}_{(b)}\ \xrightarrow{\ \text{colimit / localization}\ }\ \underbrace{\mathbb{Q}=S^{-1}\mathbb{Z}\ \text{flat}}_{(c)} .
$$
Each arrow is a closure property of flat modules: $\otimes$ commutes with $\bigoplus$ and with filtered colimits, and a direct summand of a flat module is flat.

**But projectivity is rigid.** Over the PID $\mathbb{Z}$, *projective $=$ free*, and $\mathbb{Q}$ is **divisible** ($q=n\cdot\frac{q}{n}$ for every $n\ne 0$) while a nonzero free abelian group $\bigoplus\mathbb{Z}$ is not (a basis vector is not divisible by $2$). So $\mathbb{Q}$ is flat but **not** projective — flatness tolerates the "infinitely divisible" colimit structure that freeness cannot.

## Complete Proof

We use three standard facts about the tensor product of $R$-modules: **(T1)** $R\otimes_R M\cong M$ naturally; **(T2)** $\otimes$ commutes with arbitrary direct sums, $\big(\bigoplus_i F_i\big)\otimes M\cong\bigoplus_i(F_i\otimes M)$; **(T3)** a sequence of direct sums $\bigoplus_i X_i\to\bigoplus_i Y_i\to\bigoplus_i Z_i$ (componentwise maps) is exact iff each component $X_i\to Y_i\to Z_i$ is exact (the direct-sum functor is exact, computing kernels and images componentwise).

### Part (a): free modules are flat

First, $R$ is flat: by **(T1)**, the functor $R\otimes_R-$ is naturally isomorphic to the identity functor, which sends exact sequences to exact sequences. So for any exact $A\to B\to C$, $R\otimes A\to R\otimes B\to R\otimes C$ is exact.

Let $F=\bigoplus_{i\in I}R$ be free. Given an exact sequence $A\to B\to C$ of left $R$-modules, apply **(T2)**:
$$
F\otimes A\cong\bigoplus_{i\in I}(R\otimes A)\cong\bigoplus_{i\in I}A,
$$
and similarly for $B,C$, with the induced maps acting componentwise. Each component sequence $R\otimes A\to R\otimes B\to R\otimes C$ is exact (just shown), so by **(T3)** the direct sum
$$
F\otimes A\to F\otimes B\to F\otimes C
$$
is exact. Hence $F$ is flat. $\qquad\checkmark$

### Part (b): projective modules are flat

$P$ is projective iff it is a **direct summand of a free module**: there is a module $Q$ and a free module $F$ with $P\oplus Q\cong F$. By part (a), $F$ is flat.

Let $A\to B\to C$ be exact. Since $F=P\oplus Q$ is flat, $F\otimes A\to F\otimes B\to F\otimes C$ is exact. Using **(T2)** for the finite direct sum, this sequence is
$$
(P\otimes A)\oplus(Q\otimes A)\ \to\ (P\otimes B)\oplus(Q\otimes B)\ \to\ (P\otimes C)\oplus(Q\otimes C),
$$
with componentwise maps. By **(T3)**, exactness of this direct sum is equivalent to exactness of *each* summand sequence; in particular $P\otimes A\to P\otimes B\to P\otimes C$ is exact. Hence $P$ is flat. $\qquad\checkmark$

*(The argument shows the general principle: a direct summand of a flat module is flat.)*

### Part (c): $\mathbb{Q}$ is flat as a $\mathbb{Z}$-module

Recognize $\mathbb{Q}=S^{-1}\mathbb{Z}$, the localization of $\mathbb{Z}$ at $S=\mathbb{Z}\setminus\{0\}$, and recall the natural isomorphism $\mathbb{Q}\otimes_{\mathbb{Z}}M\cong S^{-1}M$ (elements $m/s$, $m\in M$, $s\in S$). Tensoring is always right exact, so to prove flatness it suffices to show $\mathbb{Q}\otimes_{\mathbb{Z}}-$ **preserves injections**.

Let $f:A\hookrightarrow B$ be an injective map of $\mathbb{Z}$-modules; the induced map is $S^{-1}f:S^{-1}A\to S^{-1}B$, $a/n\mapsto f(a)/n$. Suppose $f(a)/n=0$ in $S^{-1}B$. By definition of localization there is $m\in S$ (so $m\ne0$) with $m\,f(a)=0$ in $B$, i.e. $f(ma)=0$; injectivity of $f$ gives $ma=0$ in $A$, and since $m\ne 0$ this means $a/n=0$ in $S^{-1}A$. Thus $S^{-1}f$ is injective. Therefore $\mathbb{Q}\otimes_{\mathbb{Z}}-$ preserves injections and, being right exact, is exact: $\mathbb{Q}$ is flat. $\qquad\checkmark$

*(Equivalently: $\mathbb{Q}=\bigcup_{n\ge 1}\tfrac1{n!}\mathbb{Z}$ is a directed union (filtered colimit) of free $\mathbb{Z}$-modules $\tfrac1{n!}\mathbb{Z}\cong\mathbb{Z}$, each flat by (a); a filtered colimit of flat modules is flat, since $\otimes$ commutes with colimits and filtered colimits are exact.)*

### Part (d): $\mathbb{Q}$ is NOT projective as a $\mathbb{Z}$-module

**No.** Over the PID $\mathbb{Z}$, a projective module is free: a projective module is a direct summand — hence a submodule — of a free module $\bigoplus_I\mathbb{Z}$, and a submodule of a free module over a PID is free. So it suffices to show $\mathbb{Q}$ is **not free**.

Use the structural contrast **divisibility**:

- $\mathbb{Q}$ is *divisible*: for every $q\in\mathbb{Q}$ and nonzero $n\in\mathbb{Z}$, $q=n\cdot(q/n)$ with $q/n\in\mathbb{Q}$.
- A nonzero free $\mathbb{Z}$-module $F=\bigoplus_{i\in I}\mathbb{Z}$ is *not divisible*: a basis element $e_{i_0}$ has no solution to $2x=e_{i_0}$ (comparing the $i_0$-coordinate, $2x_{i_0}=1$ is unsolvable in $\mathbb{Z}$).

Since $\mathbb{Q}\ne 0$ is divisible, it cannot be free. Hence $\mathbb{Q}$ is not projective over $\mathbb{Z}$. $\qquad\blacksquare$

*(Alternatively, $\mathbb{Q}$ has $\mathbb{Z}$-rank $1$ — any two rationals $p_1/n,p_2/n$ satisfy the dependence $p_2\cdot(p_1/n)-p_1\cdot(p_2/n)=0$ — so a basis would have one element and force $\mathbb{Q}\cong\mathbb{Z}$, impossible as $\mathbb{Q}$ is not finitely generated. Either way, not free.)*

### Remark — flat ⊋ projective, and the role of $\mathbb{Q}$

Parts (a)–(c) build the implications **free $\Rightarrow$ projective $\Rightarrow$ flat** (the first being trivial, the second part (b), and flatness then inherited), while part (d) shows the last implication is **strict**: $\mathbb{Q}$ is the textbook flat-but-not-projective $\mathbb{Z}$-module. The conceptual reason is that flatness is preserved by filtered colimits but projectivity (over $\mathbb{Z}$, freeness) is not: $\mathbb{Q}=\varinjlim\tfrac1{n!}\mathbb{Z}$ is a colimit of free modules that is itself flat yet acquires divisibility in the limit, which destroys freeness. More generally over any integral domain, a localization $S^{-1}R$ is always flat but projective only in degenerate cases — the divisible/torsion-free structure of fields of fractions is exactly what separates the two notions. (A finitely generated flat module over a Noetherian ring *is* projective; $\mathbb{Q}$ evades this because it is not finitely generated.)
