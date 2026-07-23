<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b90A03: Sylow subgroups as intermediate fields — existence and uniqueness ⟺ Galois over K

*(Note: part (b) as printed asks to show the set equals $\{L\}$ iff "$L$ is a Galois
extension of $L$"; the intended statement is plainly "$L$ is a Galois extension of
$K$" — $L/L$ is trivially Galois — and that is what is proved below.)*

## Why It's Hard

The problem is entirely a **translation exercise** between two theories, and the work
is in lining up the dictionaries exactly. The Galois correspondence converts
intermediate fields into subgroups, but you must track which numerical datum goes
where: $[F:L]$ is the *order* of the subgroup $\mathrm{Gal}(F/L)$ (not its index), so
"$[F:L]=p^n$" is "subgroup of order $p^n$" — and since $p^n$ is the full $p$-part of
$|G|=p^nq^m$, that is exactly a **Sylow $p$-subgroup**. Part (b) then needs the *other*
half of the correspondence — that "$L/K$ is Galois" matches "$\mathrm{Gal}(F/L)$ is
normal in $G$" — and the Sylow fact that uniqueness of a Sylow subgroup is the same as
its normality. Misalign any one of these and the equivalence falls apart.

## The Key Insight

Let $G=\mathrm{Gal}(F/K)$, $|G|=p^nq^m$. Under the Galois correspondence
$L\leftrightarrow H=\mathrm{Gal}(F/L)$ with $[F:L]=|H|$:
$$
\{\,L: K\subseteq L\subseteq F,\ [F:L]=p^n\,\}\ \longleftrightarrow\ \{\text{subgroups of order } p^n\}=\{\text{Sylow }p\text{-subgroups of }G\}.
$$
Sylow guarantees at least one (part a). The set has exactly one element $\iff$ $G$ has
a unique Sylow $p$-subgroup $\iff$ that subgroup $P$ is **normal** $\iff$ (fundamental
theorem) the fixed field $L=F^{P}$ is **Galois over $K$** (part b). Every clause is
secretly "$P\trianglelefteq G$."

## Complete Proof

Since $F/K$ is finite Galois, set $G=\mathrm{Gal}(F/K)$, a finite group of order
$$
|G|=[F:K]=p^n q^m,\qquad p\neq q\ \text{prime},\ n,m>1 .
$$
The **fundamental theorem of Galois theory** gives an inclusion-reversing bijection
between intermediate fields $K\subseteq L\subseteq F$ and subgroups $H\le G$, via
$L\mapsto \mathrm{Gal}(F/L)$ and $H\mapsto F^{H}$, satisfying
$$
[F:L]=|\mathrm{Gal}(F/L)|,\qquad [L:K]=[G:\mathrm{Gal}(F/L)],
$$
and moreover $L/K$ is Galois $\iff$ $\mathrm{Gal}(F/L)\trianglelefteq G$.

### Part (a): an $L$ with $[F:L]=p^n$ exists

The highest power of $p$ dividing $|G|=p^nq^m$ is $p^n$ (as $p\neq q$). By **Sylow's
theorem**, $G$ has a Sylow $p$-subgroup $P$ with $|P|=p^n$. Put
$$
L:=F^{P}\quad(\text{the fixed field of }P).
$$
By the correspondence $\mathrm{Gal}(F/L)=P$, so $[F:L]=|P|=p^n$. The inclusions are
proper: $P\neq\{e\}$ (since $p^n>1$, as $n>1$) gives $L\subsetneq F$, and $P\neq G$
(since $|P|=p^n<p^nq^m=|G|$, as $q^m>1$) gives $K\subsetneq L$. Thus $K\subset
L\subset F$ with $[F:L]=p^n$. $\quad\checkmark$

### Part (b): uniqueness of such $L$ $\iff$ $L/K$ is Galois

Let $L=F^{P}$ be as in (a), with $P$ a Sylow $p$-subgroup. Define
$$
\mathcal{L}=\{\,L': K\subseteq L'\subseteq F,\ [F:L']=p^n\,\}.
$$
Under the correspondence, $L'\in\mathcal{L}$ iff $H':=\mathrm{Gal}(F/L')$ has order
$p^n$. Since $p^n$ is the full $p$-part of $|G|$, a subgroup of order $p^n$ is precisely
a Sylow $p$-subgroup. Hence the bijection restricts to
$$
\mathcal{L}\ \longleftrightarrow\ \mathrm{Syl}_p(G),\qquad L'\mapsto \mathrm{Gal}(F/L'),
$$
and in particular $|\mathcal{L}|=n_p$, the number of Sylow $p$-subgroups, with $L$
corresponding to $P$.

Now chain three equivalences:
$$
\mathcal{L}=\{L\}
\iff n_p=1
\iff P\trianglelefteq G
\iff L=F^{P}\ \text{is Galois over }K .
$$
- The first $\iff$ is the bijection $\mathcal{L}\leftrightarrow\mathrm{Syl}_p(G)$:
  $\mathcal{L}$ is a singleton iff there is exactly one Sylow $p$-subgroup.
- The second $\iff$ is Sylow's theorem: all Sylow $p$-subgroups are conjugate, so there
  is a unique one iff $P$ is its own (only) conjugate, i.e. $P\trianglelefteq G$.
  (Equivalently $n_p=[G:N_G(P)]=1\iff N_G(P)=G$.)
- The third $\iff$ is the normality clause of the fundamental theorem applied to
  $\mathrm{Gal}(F/L)=P$: $L/K$ is Galois iff $P\trianglelefteq G$.

Therefore $\mathcal{L}=\{L\}$ if and only if $L$ is a Galois extension of $K$.
$\quad\blacksquare$

### Remark

The hypotheses $n,m>1$ only ensure the inclusions in (a) are proper (so $L$ is a
genuine intermediate field); the existence and the equivalence work whenever $p^n\|
|G|$. The conceptual content is that **three a priori different conditions collapse to
one** — "only one such field," "only one Sylow $p$-subgroup," and "$L/K$ Galois" are
all the single statement $P\trianglelefteq G$. The $q^m$ factor plays no role beyond
making $p^n$ a *proper* nontrivial Sylow order.
