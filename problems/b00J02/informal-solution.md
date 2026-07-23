<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b00J02: The order of GL_3(Z/4Z)

## Why It's Hard

$\Z/4\Z$ is a *ring, not a field*. It has a zero divisor ($2\cdot 2 = 0$) and a
nontrivial unit group ($(\Z/4\Z)^\times = \{1,3\}$). The standard way to count
$|GL_n(\mathbb{F}_q)|$ — build an invertible matrix one column at a time, each new
column chosen outside the span of the previous ones — relies on Gaussian
elimination, which needs a field: over $\Z/4\Z$ you cannot divide by $2$, and
"nonzero" no longer means "invertible" (the column $(2,0,0)^\top$ is nonzero but a
zero divisor). So the field formula does not apply directly. The fix is to exploit
the structure of $\Z/4\Z$ as a **local ring with residue field $\mathbb{F}_2$**.

## The Key Insight

Invertibility of a matrix over a commutative ring is detected by its determinant:
$A$ is invertible iff $\det A$ is a *unit*. Over $\Z/4\Z$ the units are exactly the
odd residues, and "$\det A$ is odd" is the same as "$\det A \not\equiv 0 \pmod 2$",
i.e. the mod-$2$ reduction $\bar A$ is invertible over $\mathbb{F}_2$. Hence

$$A \in GL_n(\Z/4\Z) \iff \bar A \in GL_n(\mathbb{F}_2).$$

Reduction mod $2$ is applied entrywise, and each entry's mod-$2$ value has exactly
two lifts in $\Z/4\Z$ ($x$ and $x+2$). So every matrix in $GL_n(\mathbb{F}_2)$ has
exactly $2^{n^2}$ preimages, all invertible. Counting fibers gives the whole answer:

$$|GL_n(\Z/4\Z)| = |GL_n(\mathbb{F}_2)| \cdot 2^{n^2}.$$

## Complete Proof

Let $R = \Z/4\Z$. Its unique maximal ideal is $\mathfrak{m} = \{0,2\} = 2R$, its
unit group is $R^\times = \{1,3\}$ (the odd residues), and the residue field is
$R/\mathfrak{m} \cong \mathbb{F}_2$. Let $\pi : M_n(R) \to M_n(\mathbb{F}_2)$ be
entrywise reduction mod $2$. It is a ring homomorphism and commutes with the
determinant: $\det(\pi(A)) = \pi(\det A)$.

**Step 1 — invertibility is detected by the determinant.** Over any commutative
ring $R$, a matrix $A \in M_n(R)$ is invertible iff $\det A \in R^\times$.
*Proof.* If $\det A$ is a unit, then $A^{-1} = (\det A)^{-1}\,\operatorname{adj}(A)$,
because $A\cdot\operatorname{adj}(A) = (\det A)\,I$ (the adjugate identity, valid over
any commutative ring). Conversely, if $AB = I$ then $\det(A)\det(B) = \det(I) = 1$,
so $\det A$ is a unit.

**Step 2 — reduction characterizes $GL_n(\Z/4\Z)$.** Over $R = \Z/4\Z$ we have
$R^\times = \{1,3\}$, the odd elements. So
$$
\det A \in R^\times
\iff \det A \text{ is odd}
\iff \pi(\det A) \neq 0 \text{ in } \mathbb{F}_2
\iff \det(\pi(A)) \neq 0
\iff \pi(A) \in GL_n(\mathbb{F}_2),
$$
using $\det(\pi(A)) = \pi(\det A)$ and the fact that over the field $\mathbb{F}_2$
invertibility is exactly nonvanishing determinant. Combined with Step 1,
$$A \in GL_n(\Z/4\Z) \iff \pi(A) \in GL_n(\mathbb{F}_2),$$
that is, $GL_n(\Z/4\Z) = \pi^{-1}\big(GL_n(\mathbb{F}_2)\big)$.

**Step 3 — fiber size.** The reduction $\Z/4\Z \to \mathbb{F}_2$ is two-to-one
($\{0,2\}\mapsto 0$, $\{1,3\}\mapsto 1$). A matrix in $M_n(R)$ has $n^2$ entries that
may be chosen independently, so each $B \in M_n(\mathbb{F}_2)$ has exactly
$|\pi^{-1}(B)| = 2^{n^2}$ preimages. By Step 2, the entire fiber over a
$B \in GL_n(\mathbb{F}_2)$ lies inside $GL_n(\Z/4\Z)$, while fibers over singular $B$
contribute nothing. Therefore
$$|GL_n(\Z/4\Z)| = |GL_n(\mathbb{F}_2)|\cdot 2^{n^2}.$$

**Step 4 — the field count.** Over a field, columns can be chosen greedily:
$$|GL_n(\mathbb{F}_2)| = \prod_{i=0}^{n-1}\big(2^n - 2^i\big),$$
the first column any nonzero vector ($2^n-1$ choices), the $k$-th any vector outside
the $(k-1)$-dimensional span of those already chosen ($2^n - 2^{k-1}$). For $n=3$:
$$|GL_3(\mathbb{F}_2)| = (2^3-1)(2^3-2)(2^3-4) = 7\cdot 6\cdot 4 = 168.$$

**Step 5 — assemble for $n=3$.** Here $2^{n^2} = 2^{9} = 512$, so
$$|GL_3(\Z/4\Z)| = 168 \cdot 512 = 86016 = 2^{12}\cdot 3\cdot 7. \qquad \blacksquare$$

**Answer.** $\;|GL_3(\Z/4\Z)| = 86016 = 2^{12}\cdot 3\cdot 7.$

*(Remark: the same argument gives the general formula
$|GL_n(\Z/p^k\Z)| = p^{(k-1)n^2}\prod_{i=0}^{n-1}(p^n-p^i)$, since $\Z/p^k\Z$ is local
with residue field $\mathbb{F}_p$ and reduction mod $p$ is $p^{k-1}$-to-one per entry;
this problem is the case $p=2,\,k=2,\,n=3$.)*
