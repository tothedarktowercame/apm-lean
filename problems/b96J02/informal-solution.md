<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b96J02: The R = F₂[x]/(x²) modules of order 16 — exactly three

## Why It's Hard

The ring $R=\mathbb{F}_2[x]/(x^2)$ is tiny ($|R|=4$) but not a field and not reduced, so
"module over $R$" is richer than "vector space." The trick is to see what an $R$-module
*is*: an $\mathbb{F}_2$-vector space $V$ together with the action of $x$, a linear
operator $T$ with $T^2=0$. Classifying $R$-modules is therefore classifying **nilpotent
operators of square zero** — i.e. Jordan form with all blocks of size $\le 2$. After
that, the only work is a counting constraint to pin down which block multiplicities give
exactly $16$ elements.

## The Key Insight

An $R$-module is $(V,T)$ with $T=x\cdot(-)$, $T^2=0$. By Jordan form over $\mathbb{F}_2$
(eigenvalue $0$, block sizes $\le 2$), every finite $R$-module is
$$
M\cong R^{a}\oplus \mathbb{F}_2^{\,b},
$$
where $R\cong R/(x^2)$ is the size-$2$ block and $\mathbb{F}_2\cong R/(x)$ is the
size-$1$ block. Then $|M|=4^{a}2^{b}=2^{2a+b}$, so $|M|=16$ iff $2a+b=4$, giving exactly
$(a,b)\in\{(2,0),(1,2),(0,4)\}$ — three classes, separated by $a=\dim_{\mathbb{F}_2}(xM)$.

## Complete Proof

### The ring and what its modules are

$R=\mathbb{F}_2[x]/(x^2)=\{0,1,x,1+x\}$ is a local ring with maximal ideal $\mathfrak
m=(x)$, $\mathfrak m^2=(x^2)=0$. An $R$-module $M$ is the same data as an
$\mathbb{F}_2$-vector space $V=M$ together with the $\mathbb{F}_2$-linear map
$T:V\to V$, $T(v)=x\cdot v$, subject to the single relation $T^2=x^2\cdot(-)=0$.
Conversely any $(V,T)$ with $T^2=0$ defines an $R$-module. A module with finitely many
elements is finite-dimensional over $\mathbb{F}_2$.

### Classification of finite $R$-modules

We classify pairs $(V,T)$ with $\dim_{\mathbb F_2}V<\infty$ and $T^2=0$, up to
isomorphism. Since $T$ is nilpotent with $T^2=0$, its Jordan canonical form (over any
field, here $\mathbb{F}_2$) consists of nilpotent Jordan blocks of size at most $2$:
- a size-$1$ block is a $1$-dimensional space with $T=0$: this is the $R$-module
  $\mathbb{F}_2=R/(x)$ (where $x$ acts as $0$);
- a size-$2$ block is a $2$-dimensional space with $T=\begin{psmallmatrix}0&1\\0&0
  \end{psmallmatrix}$ ($T\neq0$, $T^2=0$): this is the $R$-module $R=R/(x^2)$ (where $x$
  acts as the order-$2$ nilpotent).

Hence every finite $R$-module is isomorphic to
$$
M\cong R^{a}\oplus\mathbb{F}_2^{\,b}\qquad(a,b\ge0),
$$
and the pair $(a,b)$ is an isomorphism invariant (uniqueness of Jordan form, equivalently
Krull–Schmidt for the local Artinian ring $R$). A clean way to read off the invariants:
$$
\dim_{\mathbb{F}_2}M = 2a+b,\qquad \dim_{\mathbb{F}_2}(xM)=a,
$$
since each $R$-summand contributes a $1$-dimensional image $xR=(x)$ while each
$\mathbb{F}_2$-summand has $x\cdot\mathbb{F}_2=0$. So $a=\dim(xM)$ and then
$b=\dim M-2a$ are determined by $M$.

### The constraint $|M|=16$

Counting elements,
$$
|M| = |R|^{a}\,|\mathbb{F}_2|^{b} = 4^{a}\,2^{b} = 2^{\,2a+b}.
$$
Thus $|M|=16=2^4$ iff $2a+b=4$ with $a,b\ge0$. The nonnegative solutions are exactly
$$
(a,b)=(2,0),\quad (1,2),\quad (0,4).
$$

### The answer: three isomorphism classes

There are **exactly three** isomorphism classes of $R$-modules with $16$ elements:

| $(a,b)$ | module | $\dim_{\mathbb F_2}M$ | $\dim(xM)=a$ |
|---|---|---|---|
| $(2,0)$ | $R\oplus R$ | $4$ | $2$ |
| $(1,2)$ | $R\oplus\mathbb{F}_2\oplus\mathbb{F}_2$ | $4$ | $1$ |
| $(0,4)$ | $\mathbb{F}_2\oplus\mathbb{F}_2\oplus\mathbb{F}_2\oplus\mathbb{F}_2$ | $4$ | $0$ |

All three are $4$-dimensional over $\mathbb{F}_2$ (hence all have $2^4=16$ elements), and
they are pairwise non-isomorphic because the invariant $a=\dim_{\mathbb{F}_2}(xM)$ takes
the three distinct values $2,1,0$. Equivalently: $R\oplus R$ is free of rank $2$;
$\mathbb{F}_2^{4}$ is the module on which $x$ acts as zero; and $R\oplus\mathbb{F}_2^2$ is
the mixed case. $\quad\blacksquare$

### Remark

$R=\mathbb{F}_2[x]/(x^2)$ is the smallest non-semisimple commutative ring, and it is of
*finite representation type*: it has only two indecomposable modules, $\mathbb{F}_2$ and
$R$, so module classification reduces to choosing multiplicities $(a,b)$ — i.e. to a
nilpotent Jordan form with blocks of size $\le 2$. The order-$16$ count $2a+b=4$ is just
the partition of the exponent $4$ into parts $2$ (an $R$) and $1$ (an $\mathbb{F}_2$):
$2+2,\ 2+1+1,\ 1+1+1+1$.
