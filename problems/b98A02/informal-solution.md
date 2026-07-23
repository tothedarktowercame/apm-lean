<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b98A02: The maximal abelian subextension A = E^{G'}, and A(E∩L) = A(E)∩A(L)

## Why It's Hard

The problem builds a four-floor tower and the whole thing rests on one
translation: the **maximal abelian subextension** of a Galois extension is the
fixed field of the **commutator subgroup**, $A=E^{G'}$. Part (a) is where the
given "Well Known" theorem ($G'\subseteq H\iff H\trianglelefteq G$ and $G/H$
abelian) earns its keep — it converts "largest abelian Galois subextension" into
"smallest subgroup with abelian quotient," which is exactly $G'$, via the
inclusion-*reversing* Galois correspondence (largest field $\leftrightarrow$
smallest subgroup). Part (b) packages (a) into a clean iff that becomes a
*black box* for everything after. The traps are altitude-management ones: in (c)
you must prove normality of an *intersection* without coordinates (use stability
under $F$-automorphisms of $\Omega$, not generators); and in (d) the temptation
is to chase Galois groups, when the slick path is to invoke (b) twice and (c)
once and never compute a single commutator. The elegance is that (d) follows
formally from (b)+(c) — recognizing that is the point.

## The Key Insight

For finite Galois $E/F$ with $G=\operatorname{Gal}(E/F)$, set
$$
\boxed{A=E^{G'}}\qquad(G'=\text{commutator subgroup}).
$$
The Galois correspondence (inclusion-reversing) plus the given theorem give
everything:
- $G'\trianglelefteq G$ and $G/G'$ abelian (the theorem, with $H=G'$), so $A/F$
  is Galois with $\operatorname{Gal}(A/F)\cong G/G'$ **abelian** — (i),(ii);
- if $K/F$ is abelian Galois with $H=\operatorname{Gal}(E/K)$, then $H
  \trianglelefteq G$ and $G/H$ abelian, so the theorem gives $G'\subseteq H$,
  hence $K=E^H\subseteq E^{G'}=A$ — maximality (iii).

This yields the **characterization** that drives (b)–(d): for $F\subseteq
K\subseteq E$,
$$
K\subseteq A\iff K/F\text{ is Galois with abelian Galois group.}
$$
Then (c) "intersection of Galois is Galois" comes from $\sigma(E\cap L)=\sigma E
\cap\sigma L=E\cap L$ for every $F$-automorphism $\sigma$ of $\Omega$, and (d)
$A(E\cap L)=A(E)\cap A(L)$ is two applications of the characterization plus (c).

## Complete Proof

Throughout, $E/F$ is finite Galois, $G=\operatorname{Gal}(E/F)$, and we use the
**Fundamental Theorem of Galois Theory**: intermediate fields $F\subseteq
K\subseteq E$ correspond bijectively and inclusion-reversingly to subgroups
$\operatorname{Gal}(E/K)\le G$, with $K=E^{\operatorname{Gal}(E/K)}$; moreover
$K/F$ is **Galois iff $\operatorname{Gal}(E/K)\trianglelefteq G$**, in which case
$\operatorname{Gal}(K/F)\cong G/\operatorname{Gal}(E/K)$.

### Part (a): existence of the maximal abelian subextension $A$

Let $A=E^{G'}$, the fixed field of the commutator subgroup $G'$.

**(i),(ii).** Apply the Well-Known theorem with $H=G'$: since $G'\subseteq G'$
trivially holds, the theorem gives that $G'\trianglelefteq G$ **and** $G/G'$ is
abelian. By the correspondence, $G'\trianglelefteq G$ makes $A=E^{G'}$ a **Galois**
extension of $F$ (i), with
$$
\operatorname{Gal}(A/F)\cong G/G'\quad\text{abelian (ii).}
$$

**(iii) Maximality.** Let $K$ be any field with $F\subseteq K\subseteq E$ such
that $K/F$ is Galois with $\operatorname{Gal}(K/F)$ abelian. Put
$H=\operatorname{Gal}(E/K)$. Since $K/F$ is Galois, $H\trianglelefteq G$, and
$G/H\cong\operatorname{Gal}(K/F)$ is abelian. By the Well-Known theorem (the
direction "$H\trianglelefteq G$ and $G/H$ abelian $\Rightarrow G'\subseteq H$"),
$$
G'\subseteq H .
$$
Taking fixed fields reverses inclusion: $K=E^{H}\subseteq E^{G'}=A$. Hence every
abelian Galois subextension is contained in $A$, so $A$ is the unique largest
field satisfying (i),(ii). $\quad\checkmark$

### Part (b): $K\subseteq A\iff K/F$ Galois with abelian group

Let $F\subseteq K\subseteq E$.

**(i)$\Rightarrow$(ii).** If $K/F$ is Galois with abelian Galois group, then by
part (a)(iii), $K\subseteq A$.

**(ii)$\Rightarrow$(i).** Suppose $K\subseteq A$. Then $F\subseteq K\subseteq A$
with $A/F$ Galois and $\operatorname{Gal}(A/F)\cong G/G'$ **abelian**. Apply the
Fundamental Theorem to the Galois extension $A/F$: $K$ corresponds to the
subgroup $\bar H=\operatorname{Gal}(A/K)\le\operatorname{Gal}(A/F)$. Since
$\operatorname{Gal}(A/F)$ is abelian, **every** subgroup is normal, so $\bar
H\trianglelefteq\operatorname{Gal}(A/F)$; hence $K/F$ is **Galois**, with
$$
\operatorname{Gal}(K/F)\cong\operatorname{Gal}(A/F)/\bar H,
$$
a quotient of an abelian group, therefore **abelian**. So (i) holds.

Thus (i)$\iff$(ii). $\quad\checkmark$

### Part (c): $E\cap L$ is Galois over $F$

Here $F\subseteq E,L\subseteq\Omega$ with $\Omega$ an algebraic closure of $F$
and $E/F$, $L/F$ Galois (finite). Since $E\cap L\subseteq E$ is finite over $F$,
it suffices to show $E\cap L$ is **separable** and **normal** over $F$.

**Separable.** $E/F$ is separable (being Galois), and any subextension of a
separable extension is separable; as $E\cap L\subseteq E$, the extension $(E\cap
L)/F$ is separable.

**Normal.** Recall an algebraic extension $M/F$ inside $\Omega$ is normal iff it
is stable under every $F$-automorphism of $\Omega$ (equivalently, every
$F$-embedding $M\hookrightarrow\Omega$ has image $M$). Let $\sigma$ be any
$F$-automorphism of $\Omega$. Because $E/F$ and $L/F$ are normal, $\sigma(E)=E$
and $\sigma(L)=L$; therefore
$$
\sigma(E\cap L)=\sigma(E)\cap\sigma(L)=E\cap L .
$$
(The middle equality holds because $\sigma$ is a bijection: $x\in E\cap L\iff
\sigma x\in\sigma E\cap\sigma L$.) Any $F$-embedding $\tau:E\cap L\to\Omega$
extends to an $F$-automorphism $\sigma$ of $\Omega$ (since $\Omega$ is
algebraically closed), and then $\tau(E\cap L)=\sigma(E\cap L)=E\cap L$. Hence
$E\cap L$ is normal over $F$.

Being finite, separable, and normal over $F$, $E\cap L$ is **Galois over $F$**.
$\quad\checkmark$

### Part (d): $A(E\cap L)=A(E)\cap A(L)$

By part (c), $E\cap L$ is Galois over $F$, so $A(E\cap L)$ is defined; and each of
$A(E),A(L),A(E\cap L)$ is, by part (a)(i),(ii), an **abelian Galois** extension
of $F$. We use the characterization of part (b): *for a finite Galois extension
$M/F$ and $F\subseteq K\subseteq M$,*
$$
K\subseteq A(M)\iff K/F\text{ is Galois with abelian Galois group.}\tag{$\star$}
$$

**$A(E\cap L)\subseteq A(E)\cap A(L)$.** The field $A(E\cap L)$ is abelian Galois
over $F$ and satisfies $A(E\cap L)\subseteq E\cap L\subseteq E$. Applying
$(\star)$ with $M=E$ and $K=A(E\cap L)$ gives $A(E\cap L)\subseteq A(E)$.
Symmetrically (with $M=L$), $A(E\cap L)\subseteq A(L)$. Hence
$A(E\cap L)\subseteq A(E)\cap A(L)$.

**$A(E)\cap A(L)\subseteq A(E\cap L)$.** Set $B=A(E)\cap A(L)$, a field with
$F\subseteq B$. Since $B\subseteq A(E)\subseteq E$, applying $(\star)$ with $M=E$
(direction $\Leftarrow$: $B\subseteq A(E)\Rightarrow B/F$ abelian Galois) shows
$$
B/F\text{ is Galois with abelian Galois group.}
$$
Moreover $B\subseteq A(E)\cap A(L)\subseteq E\cap L$. Now apply $(\star)$ with
$M=E\cap L$ (direction $\Rightarrow$: $B/F$ abelian Galois and $B\subseteq E\cap
L$ $\Rightarrow B\subseteq A(E\cap L)$):
$$
B=A(E)\cap A(L)\subseteq A(E\cap L).
$$

Combining the two inclusions,
$$
\boxed{A(E\cap L)=A(E)\cap A(L).}
$$
$\blacksquare$

### Remark

The organizing idea is the dictionary entry **"maximal abelian subextension $=$
fixed field of the commutator subgroup,"** i.e. $A(E)=E^{\operatorname{Gal}
(E/F)'}$ — the field-side image of the abelianization $G\twoheadrightarrow
G/G'$. Part (b) distills this into a membership test ($\star$) that no longer
mentions groups, and once you have ($\star$), parts (c) and (d) are pure lattice
formalism: $A(-)$ is the largest abelian-Galois subfield, intersection of
Galois is Galois, and a subfield of an abelian-Galois field is again
abelian-Galois — so $A(-)$ commutes with intersection. The same argument shows
$A(-)$ is *monotone* ($E_1\subseteq E_2\Rightarrow A(E_1)\subseteq A(E_2)$),
of which (d)'s "$\subseteq$" direction is the special case applied to $E\cap
L\subseteq E$ and $E\cap L\subseteq L$.
