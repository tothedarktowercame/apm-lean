<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b00J04: Rings between a PID and its fraction field are localizations

## Why It's Hard

The hypothesis $R\subseteq S\subseteq F$ feels almost contentless — $S$ is just "some subring of the fraction field containing $R$" — and the three parts ask you to wring a lot of structure out of it. The central realization, which all three parts circle, is that **$S$ must be the localization of $R$ at its own set of admissible denominators**, $D=\{b\in R\setminus\{0\}:1/b\in S\}$. Nothing in the problem hands you that; you have to manufacture it, and part (a) is precisely the lever.

Each part has a genuine sticking point:

- **(a)** A fraction $\alpha=a/b$ lies in $S$, but that says nothing a priori about $1/b$. The non-obvious move is to first reduce $a/b$ **to lowest terms** and then invoke **Bézout** ($\gcd(a,b)=1\Rightarrow xa+yb=1$) to express $1/b$ as an $R$-combination of $\alpha$ and $1$ — both already in $S$. Coprimality is essential; without it the conclusion is false.
- **(b)** One must recognize $S=D^{-1}R$ and prove every ideal is principal. The engine is the **contraction $J\mapsto J\cap R$** to an ideal of the PID $R$; clearing denominators (part (a) again) is what makes the contracted generator generate all of $J$.
- **(c)** Finiteness over $R$ caps every denominator by a single $b$, so $S\subseteq\frac1b R$. The clever finish is **self-referential**: $1/b^2\in S\subseteq\frac1bR$ forces $1/b\in R$, i.e. $b$ is a unit — collapsing $S$ to $R$. Spotting that squaring the denominator detects non-units is the trick.

## The Key Insight

Set $D=\{b\in R\setminus\{0\}:1/b\in S\}$, the **admissible denominators**. Part (a) says membership in $S$ is *visible in lowest terms*: if $a/b\in S$ with $\gcd(a,b)=1$, then $1/b\in S$, i.e. $b\in D$. Hence
$$
S=D^{-1}R=\{a/b: a\in R,\ b\in D\},
$$
a **localization of the PID $R$** — and localizations of PIDs are PIDs, because ideals correspond to ideals of $R$, all principal. The finiteness hypothesis in (c) means $S$ is squeezed into $\frac1b R$ for one fixed $b$; a self-multiplication argument then forces $b$ to be a unit, so the localization is trivial and $S=R$. The whole problem is the slogan: *intermediate rings of a PID are exactly its localizations, and a module-finite localization is no localization at all.*

## Complete Proof

$R$ is a PID with fraction field $F$, and $R\subseteq S\subseteq F$ is a subring. Note $S$ is automatically an integral domain (a subring of the field $F$). Recall $R$, being a PID, is a UFD and a Bézout domain: $\gcd$s exist and $\gcd(a,b)=1\Rightarrow \exists\,x,y\in R,\ xa+yb=1$.

### Part (a): every $\alpha\in S$ is $a/b$ with $a,b\in R$ and $1/b\in S$

Let $\alpha\in S\subseteq F$. Write $\alpha=a/b$ with $a,b\in R$, $b\ne0$, **in lowest terms**, i.e. $\gcd(a,b)=1$ (possible since $R$ is a UFD). By Bézout there are $x,y\in R$ with $xa+yb=1$. Then, computing inside $S$,
$$
\frac1b=\frac{xa+yb}{b}=x\cdot\frac{a}{b}+y=x\,\alpha+y .
$$
Since $\alpha\in S$ and $x,y\in R\subseteq S$, the right side lies in $S$, so $1/b\in S$. Thus $\alpha=a/b$ with $a,b\in R$ and $1/b\in S$. $\qquad\checkmark$

### Part (b): $S$ is a PID

Let $J\subseteq S$ be any ideal; we show $J$ is principal. Set
$$
I:=J\cap R,
$$
an ideal of $R$ (it is closed under addition and under multiplication by $R\subseteq S$). Since $R$ is a PID, $I=(d)$ for some $d\in R$. We claim $J=dS$.

**$dS\subseteq J$:** $d\in I=J\cap R\subseteq J$, and $J$ is an ideal of $S$, so $dS\subseteq J$.

**$J\subseteq dS$:** Let $\alpha\in J$. By part (a), $\alpha=a/b$ with $a,b\in R$ and $1/b\in S$. Then
$$
a=b\alpha\in J\quad(\text{since }b\in R\subseteq S,\ \alpha\in J),\qquad\text{and}\qquad a\in R,
$$
so $a\in J\cap R=I=(d)$, say $a=dr$ with $r\in R$. Therefore
$$
\alpha=\frac{a}{b}=\frac{dr}{b}=d\cdot\Big(r\cdot\frac1b\Big)\in dS,
$$
because $r\in R\subseteq S$ and $1/b\in S$ give $r/b\in S$.

Hence $J=dS$ is principal. As $S$ is a domain in which every ideal is principal, $S$ is a PID. $\qquad\checkmark$

*(Equivalently: $S=D^{-1}R$ with $D=\{b:1/b\in S\}$ a multiplicative set — part (a) gives $S\subseteq D^{-1}R$, and $a/b=a\cdot(1/b)\in S$ gives $\supseteq$ — and a localization of a PID is a PID by exactly the contraction argument above.)*

### Part (c): if $S$ is finitely generated as an $R$-module, then $S=R$

Suppose $S=R s_1+\cdots+R s_n$ for some $s_1,\dots,s_n\in S\subseteq F$. By part (a), write each $s_i=a_i/b_i$ with $a_i,b_i\in R$ and $1/b_i\in S$. Put
$$
b:=b_1 b_2\cdots b_n .
$$
Then $1/b=\prod_{i=1}^n(1/b_i)\in S$ (a product of elements of the ring $S$). Moreover each generator lies in $\tfrac1b R$, since $s_i=a_i/b_i=\big(a_i\,b/b_i\big)/b$ with $a_i\,b/b_i\in R$; as $\tfrac1bR$ is an $R$-submodule of $F$ containing all the $s_i$,
$$
S=\sum_i R\,s_i\subseteq \tfrac1b R. \tag{$\ast$}
$$
Now apply $(\ast)$ to the element $1/b^2=(1/b)^2\in S$: there is $r\in R$ with
$$
\frac{1}{b^2}=\frac{r}{b}\quad\Longrightarrow\quad \frac1b=r\in R .
$$
So $1/b\in R$, i.e. $b$ is a **unit** of $R$. Consequently $\tfrac1b R=R$, and combining with $(\ast)$,
$$
R\subseteq S\subseteq \tfrac1b R=R\quad\Longrightarrow\quad S=R. \qquad\blacksquare
$$

### Remark — the localization picture and where each hypothesis bites

Parts (a)–(b) prove the structural fact that **every ring between a PID $R$ and its fraction field is a localization $D^{-1}R$**, hence again a PID (this is the $1$-dimensional/Dedekind phenomenon: overrings of a Dedekind domain are localizations/intersections of localizations). The set $D$ ranges over saturated multiplicative sets, and the extreme cases are $D=R\setminus\{0\}$ (giving $S=F$) and $D=R^\times$ (giving $S=R$). Part (c) says the *only* localization that is module-finite over $R$ is the trivial one $S=R$: a proper localization inverts some non-unit $b$, and then $1,1/b,1/b^2,\dots$ generate an $R$-module $\frac1{b^\infty}R$ with strictly increasing denominators that no finite generating set can contain — exactly the obstruction the $1/b^2$ step detects. The UFD property of $R$ (finite, bounded prime factorizations) is what makes "ever-increasing denominators" genuinely impossible inside a finitely generated module.
