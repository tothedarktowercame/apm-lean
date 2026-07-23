<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b95J03: The map E⊗_F E → End_F(E) is "multiply then represent" — image, kernel, and the ℂ/ℝ case

## Why It's Hard

The problem dresses up a very simple map in tensor-product clothing, and the
difficulty is entirely about *seeing through the costume*. Part (a) demands the
universal property done correctly: you must check the recipe
$(a,b)\mapsto(c\mapsto abc)$ is **$F$-bilinear and $F$-balanced** so that it
factors through $\otimes_F$ — and it is balanced precisely because $E$ is
commutative and scalars come from $F$. Once that is done, the real insight is
that $\varphi(a\otimes b)$ is *just multiplication by the single element $ab$*, so
$\varphi$ secretly factors as
$$
E\otimes_F E \xrightarrow{\ \mu\ } E \xrightarrow{\ m\ } \operatorname{Hom}_F(E,E),
\qquad \mu(a\otimes b)=ab,\quad m(e)=(c\mapsto ec),
$$
with $m$ **injective** (it's the regular representation of the field $E$). Every
later part is then forced: image $\cong E$ has dimension $n$; kernel $=\ker\mu$
has dimension $n^2-n$ by rank–nullity on the $n^2$-dimensional domain; and the
$\mathbb{C}/\mathbb{R}$ basis is found by solving $\mu=0$ on the four basis
tensors. The trap is treating $\varphi$ as a mysterious map on a big space rather
than recognizing it as "multiply, then act."

## The Key Insight

**$\varphi=m\circ\mu$**, where $\mu:E\otimes_F E\to E$ is the multiplication map
and $m:E\to\operatorname{Hom}_F(E,E)$ sends $e$ to the left-multiplication
operator $m_e:c\mapsto ec$. Because $E$ is a field:

- $m$ is **injective** — if $m_e=0$ then $e=e\cdot 1=m_e(1)=0$;
- $\mu$ is **surjective** — $\mu(a\otimes 1)=a$ realizes every $a\in E$.

Therefore $\varphi$ inherits everything from $\mu$:
$$
\operatorname{im}\varphi=m(\operatorname{im}\mu)=m(E)\cong E,
\qquad
\ker\varphi=\ker\mu
$$
(the second because $m$ is injective, so $m(\mu(t))=0\iff\mu(t)=0$). With
$\dim_F(E\otimes_F E)=n^2$ and $\dim_F\operatorname{im}\mu=\dim_F E=n$,
rank–nullity gives $\dim\ker=n^2-n$. For $\mathbb{C}/\mathbb{R}$ ($n=2$) the
kernel is the $2$-dimensional space of tensors that multiply to $0$.

## Complete Proof

### Part (a): existence and uniqueness of $\varphi$

Define $\beta:E\times E\to\operatorname{Hom}_F(E,E)$ by
$\beta(a,b)=\bigl(c\mapsto abc\bigr)$.

*$\beta(a,b)$ is an $F$-linear endomorphism of $E$.* For fixed $a,b$ and
$c_1,c_2\in E$, $\lambda\in F$: $ab(c_1+c_2)=abc_1+abc_2$ and
$ab(\lambda c)=\lambda(abc)$ (using that $\lambda\in F\subseteq E$ is central in
the commutative ring $E$). So $\beta(a,b)\in\operatorname{Hom}_F(E,E)$.

*$\beta$ is $F$-bilinear and $F$-balanced.* In each slot it is additive,
$\beta(a_1+a_2,b)(c)=(a_1+a_2)bc=\beta(a_1,b)(c)+\beta(a_2,b)(c)$ and likewise in
$b$; and for $\lambda\in F$,
$$
\beta(\lambda a,b)=\lambda\,\beta(a,b)=\beta(a,\lambda b),
$$
since $(\lambda a)bc=\lambda(abc)=a(\lambda b)c$ in the commutative algebra $E$.
The middle equality is exactly the balancing condition that makes $\beta$ factor
through the tensor product over $F$.

By the **universal property of $\otimes_F$**, there is a unique $F$-linear map
$$
\varphi:E\otimes_F E\to\operatorname{Hom}_F(E,E)
\quad\text{with}\quad
\varphi(a\otimes b)=\beta(a,b),
\ \text{i.e.}\ \varphi(a\otimes b)(c)=abc .
$$
*Uniqueness* also follows directly: the simple tensors $a\otimes b$ span
$E\otimes_F E$, and any $F$-linear map is determined by its values on a spanning
set; two solutions agree on all $a\otimes b$, hence everywhere. $\quad\checkmark$

### The factorization (engine for (b)–(d))

Let $\mu:E\otimes_F E\to E$ be the unique $F$-linear map with $\mu(a\otimes b)=ab$
(it exists by the same universal property, as $(a,b)\mapsto ab$ is $F$-bilinear
and balanced), and let $m:E\to\operatorname{Hom}_F(E,E)$, $m(e)=(c\mapsto ec)$.
Both are $F$-linear, and on simple tensors
$$
m\bigl(\mu(a\otimes b)\bigr)=m(ab)=(c\mapsto abc)=\varphi(a\otimes b),
$$
so $\varphi=m\circ\mu$. Moreover $m$ is **injective** ($m(e)(1)=e$) and $\mu$ is
**surjective** ($\mu(a\otimes 1)=a$).

### Part (b): dimension of the image

Since $m$ is injective and $\mu$ is surjective,
$$
\operatorname{im}\varphi=m(\operatorname{im}\mu)=m(E),
$$
and $m$ injective gives $\dim_F m(E)=\dim_F E=n$. Concretely $\operatorname{im}
\varphi$ is the algebra of multiplication operators $\{m_e:e\in E\}\cong E$.
$$
\boxed{\dim_F\operatorname{im}\varphi=n=[E:F].}
$$
$\checkmark$

### Part (c): dimension of the kernel

If $\{e_1,\dots,e_n\}$ is an $F$-basis of $E$, then $\{e_i\otimes e_j\}_{1\le
i,j\le n}$ is an $F$-basis of $E\otimes_F E$, so
$\dim_F(E\otimes_F E)=n^2$. By rank–nullity applied to $\varphi$ (whose image has
dimension $n$ by (b)),
$$
\boxed{\dim_F\ker\varphi=n^2-n=n(n-1).}
$$
(Equivalently $\ker\varphi=\ker\mu$, since $m$ is injective; and $\mu$ surjective
onto $E$ gives the same count.) $\checkmark$

### Part (d): a basis of $\ker\varphi$ for $F=\mathbb{R}$, $E=\mathbb{C}$

Here $n=[\mathbb{C}:\mathbb{R}]=2$, so by (c) the kernel has dimension
$n^2-n=2$. Since $\ker\varphi=\ker\mu$, we look for tensors that multiply to $0$.

Take the $\mathbb{R}$-basis $\{1\otimes 1,\ 1\otimes i,\ i\otimes 1,\ i\otimes i\}$
of $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{C}$. The multiplication map acts by
$$
\mu(1\otimes 1)=1,\quad \mu(1\otimes i)=i,\quad \mu(i\otimes 1)=i,\quad
\mu(i\otimes i)=i^2=-1 .
$$
For $t=a(1\otimes1)+b(1\otimes i)+c(i\otimes 1)+d(i\otimes i)$ with
$a,b,c,d\in\mathbb{R}$,
$$
\mu(t)=(a-d)+(b+c)\,i,
$$
which is $0$ iff $a=d$ and $c=-b$. This $2$-parameter solution space (parameters
$a,b$) has the basis
$$
\boxed{\;1\otimes 1+i\otimes i\;}\qquad\text{and}\qquad
\boxed{\;1\otimes i-i\otimes 1\;}.
$$
Indeed $\mu(1\otimes1+i\otimes i)=1+(-1)=0$ and
$\mu(1\otimes i-i\otimes 1)=i-i=0$, and the two are $\mathbb{R}$-linearly
independent (they involve disjoint basis tensors), so they form a basis of the
$2$-dimensional kernel. $\quad\blacksquare$

### Remark

The whole problem is the observation that "act by $a$ then by $b$" is the same as
"act by $ab$," i.e. $\varphi$ collapses through the multiplication map $\mu$ and
then embeds $E$ into its own endomorphism algebra via the regular representation.
The image is the copy of $E$ inside $\operatorname{Hom}_F(E,E)$ (dimension $n$);
the kernel measures the failure of $\otimes_F$ to already *be* multiplication —
it is the space of relations $\sum a_k\otimes b_k$ with $\sum a_k b_k=0$, of
dimension $n^2-n$. For $\mathbb{C}/\mathbb{R}$ those relations are generated by
$i^2=-1$ (giving $1\otimes1+i\otimes i$) and the commutativity/symmetry
$1\otimes i\sim i\otimes 1$ (giving $1\otimes i-i\otimes 1$).
