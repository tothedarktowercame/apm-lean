<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b94J02: Three faces of the trace — nilpotents, the trace pairing, and idempotents

## Why It's Hard

The three parts look unrelated but are united by one object — the trace as a
*linear* functional — probed three ways, and each part is a small trap for the
wrong tool. Part (a) tempts you to write "trace = sum of eigenvalues = 0," which
is morally right but technically loose: the field $K$ is **arbitrary**, so
eigenvalues live in an extension and you owe an argument that the *characteristic
polynomial* is $t^n$ — the clean fix is to work with minimal/characteristic
polynomials, which stay inside $K[t]$. Part (b) is a nondegeneracy statement
about the bilinear form $(B,C)\mapsto\operatorname{tr}(BC)$; the only difficulty
is resisting an abstract argument when a single well-chosen $B$ does everything.
Part (c) is the one place "trace = rank" can read as a type error — the rank is
an integer, the trace is an element of $K$ — and the honest reading is
$\operatorname{tr}(D)=r\cdot 1_K$, which the eigenvalue/decomposition argument
delivers *without* ever dividing (so it survives positive characteristic). The
real test is whether you pick, in each part, the argument that does not secretly
assume $\operatorname{char}K=0$.

## The Key Insight

All three parts come down to **putting the matrix in a form where the trace is
read off the diagonal, using only operations that preserve the trace**:

- **(a)** Nilpotent $\Rightarrow$ minimal polynomial is $t^k$ $\Rightarrow$
  characteristic polynomial is $t^n$ $\Rightarrow$ the coefficient
  $-\operatorname{tr}(A)$ of $t^{n-1}$ vanishes. (Equivalently: over
  $\overline{K}$ every eigenvalue is a root of $t^m$, hence $0$, so the diagonal
  of a triangularization is all zeros.)
- **(b)** Trace is the **nondegenerate pairing**
  $\langle B,C\rangle=\operatorname{tr}(BC)$. Feeding it the elementary matrix
  $B=E_{ij}$ extracts a single entry: $\operatorname{tr}(E_{ij}C)=C_{ji}$. If all
  these vanish, $C=0$.
- **(c)** An idempotent splits the space, $K^n=\operatorname{im}D\oplus\ker D$,
  with $D=\mathrm{id}$ on the image and $0$ on the kernel. In an adapted basis
  $D=\begin{psmallmatrix}I_r&0\\0&0\end{psmallmatrix}$, and since the trace is a
  similarity invariant, $\operatorname{tr}(D)=r=\operatorname{rank}(D)$.

The connective tissue is **$\operatorname{tr}(PQ)=\operatorname{tr}(QP)$**, which
makes the trace a similarity invariant ($\operatorname{tr}(S^{-1}MS)=
\operatorname{tr}(MSS^{-1})=\operatorname{tr} M$) and is also the engine behind
the entry-extraction in (b).

## Complete Proof

Throughout, $K$ is an arbitrary field and all matrices are $n\times n$ over $K$.
We use freely the cyclic property $\operatorname{tr}(PQ)=\operatorname{tr}(QP)$
(immediate from $\sum_{i}\sum_{k}P_{ik}Q_{ki}=\sum_k\sum_i Q_{ki}P_{ik}$) and its
corollary that **similar matrices have equal trace**.

### Part (a): $A^m=0\Rightarrow\operatorname{tr}(A)=0$

Because $A^m=0$, the polynomial $t^m$ annihilates $A$, so the **minimal
polynomial** $\mu_A(t)$ divides $t^m$. The only monic divisors of $t^m$ in
$K[t]$ are the powers $t^k$, hence $\mu_A(t)=t^k$ for some $1\le k\le m$.

Now recall the standard relation between minimal and characteristic polynomials:
$\mu_A$ and $\chi_A$ have the **same irreducible factors** in $K[t]$ (each
eigenvalue/irreducible factor of one is one of the other; concretely
$\mu_A\mid\chi_A$ and $\chi_A\mid\mu_A^{\,n}$). Since the only irreducible factor
of $\mu_A=t^k$ is $t$, the only irreducible factor of the monic degree-$n$
polynomial $\chi_A$ is also $t$; therefore
$$
\chi_A(t)=t^n .
$$
But the characteristic polynomial always expands as
$$
\chi_A(t)=t^n-\operatorname{tr}(A)\,t^{n-1}+\cdots+(-1)^n\det(A),
$$
so the coefficient of $t^{n-1}$ is $-\operatorname{tr}(A)$. Comparing with
$\chi_A(t)=t^n$ (whose $t^{n-1}$-coefficient is $0$) gives
$\operatorname{tr}(A)=0$.

*Remark (the eigenvalue picture).* Over an algebraic closure $\overline{K}$, $A$
is triangularizable; its diagonal entries are the eigenvalues $\lambda_1,\dots,
\lambda_n$, each a root of the annihilator $t^m$, hence every $\lambda_i=0$.
Then $\operatorname{tr}(A)=\sum_i\lambda_i=0$. This is the same computation,
phrased over $\overline{K}$; the polynomial argument above keeps everything
inside $K$ and works in every characteristic. $\quad\checkmark$

### Part (b): $\operatorname{tr}(BC)=0$ for all $B\Rightarrow C=0$

Fix indices $i,j$ and let $E_{ij}$ be the **elementary matrix** with a $1$ in
position $(i,j)$ and $0$ elsewhere, i.e. $(E_{ij})_{kp}=\delta_{ik}\delta_{jp}$.
Compute the product entrywise:
$$
(E_{ij}C)_{kl}=\sum_p (E_{ij})_{kp}\,C_{pl}
=\sum_p \delta_{ik}\delta_{jp}\,C_{pl}=\delta_{ik}\,C_{jl}.
$$
Hence its trace is
$$
\operatorname{tr}(E_{ij}C)=\sum_k (E_{ij}C)_{kk}
=\sum_k \delta_{ik}\,C_{jk}=C_{ji}.
$$
By hypothesis $\operatorname{tr}(BC)=0$ for **every** $B$; taking $B=E_{ij}$
gives $C_{ji}=0$. Since $i,j$ were arbitrary, every entry of $C$ vanishes, so
$C=0$.

*Remark.* This is exactly the statement that the bilinear form
$\langle B,C\rangle=\operatorname{tr}(BC)$ on $M_n(K)$ is **nondegenerate**: the
elementary matrices $\{E_{ij}\}$ form a basis, and the computation shows
$\langle E_{ij},C\rangle=C_{ji}$ reads off the coordinates of $C$ in the dual
basis. A matrix orthogonal to everything is therefore zero. $\quad\checkmark$

### Part (c): $D^2=D\Rightarrow\operatorname{tr}(D)=\operatorname{rank}(D)$

Let $D$ be idempotent and set $r=\operatorname{rank}(D)=\dim\operatorname{im}D$.
We show $K^n=\operatorname{im}D\oplus\ker D$ with $D$ acting as the identity on
$\operatorname{im}D$ and as $0$ on $\ker D$.

*$D$ is the identity on its image.* If $w\in\operatorname{im}D$, say $w=Du$, then
$Dw=D^2u=Du=w$.

*The sum is direct and fills $K^n$.* For any $v\in K^n$ write
$v=\underbrace{Dv}_{\in\operatorname{im}D}+\underbrace{(v-Dv)}_{\in\ker D}$,
where $v-Dv\in\ker D$ because $D(v-Dv)=Dv-D^2v=Dv-Dv=0$; thus
$\operatorname{im}D+\ker D=K^n$. And if $w\in\operatorname{im}D\cap\ker D$, then
$w=Dw$ (image) and $Dw=0$ (kernel), so $w=0$. Hence
$$
K^n=\operatorname{im}D\oplus\ker D,
\qquad \dim\ker D=n-r .
$$

Choose a basis of $K^n$ consisting of a basis $w_1,\dots,w_r$ of
$\operatorname{im}D$ followed by a basis $u_1,\dots,u_{n-r}$ of $\ker D$. Since
$Dw_s=w_s$ and $Du_t=0$, the matrix of $D$ in this basis is the block-diagonal
$$
[D]=\begin{pmatrix} I_r & 0\\ 0 & 0\end{pmatrix}.
$$
The trace is unchanged under the change of basis (similar matrices have equal
trace, by the cyclic property), so
$$
\operatorname{tr}(D)=\operatorname{tr}[D]=\underbrace{1+1+\cdots+1}_{r}
= r\cdot 1_K=\operatorname{rank}(D).
$$
$\blacksquare$

*Remark on characteristic.* The rank $r$ is an integer while $\operatorname{tr}D$
lives in $K$; the precise meaning of the identity is
$\operatorname{tr}(D)=r\cdot 1_K$, the image of $r$ under
$\mathbb{Z}\to K$. The proof never divides, so it holds in every characteristic
(in $\operatorname{char}p$ the equality is read modulo $p$). The eigenvalue view
matches: an idempotent satisfies $D(D-I)=0$, so its eigenvalues lie in
$\{0,1\}$, the algebraic multiplicity of $1$ equals $\dim\operatorname{im}D=r$,
and the trace is the sum of eigenvalues $=r\cdot 1_K$.

### Remark — one functional, three probes

Part (a) reads the trace off the *characteristic polynomial* (diagonal after
triangularizing), part (b) uses the trace as a *nondegenerate pairing* to extract
matrix entries, and part (c) reads it off a *diagonal block form* obtained from
an invariant subspace decomposition. The common discipline is to move to a basis
(or polynomial) where the trace is manifest while changing nothing the trace
depends on — and to avoid any step (eigenvalues over $K$, dividing by $r$) that
would silently assume the wrong field.
