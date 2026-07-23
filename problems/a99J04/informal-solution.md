<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J04: Lebesgue decompositions among three measures on $[-2,2]$

## Why It's Hard

There are **six ordered pairs** $i\ne j$ to decompose, and the Lebesgue decomposition $\mu_i = f_{i,j}\,d\mu_j + \nu_{i,j}$ ($\nu_{i,j}\perp\mu_j$) bundles two different objects: a Radon–Nikodym derivative $f_{i,j}$ (a function) *and* a singular measure $\nu_{i,j}$. The trap is treating each pair as a fresh problem instead of noticing the unifying structure: **all three measures are absolutely continuous with respect to Lebesgue measure $dx$**, with explicit densities, so every decomposition is just a comparison of densities. Two further subtleties bite. First, locating the singular part correctly: it is exactly the mass $\mu_i$ places on the set where the *reference* density $g_j$ vanishes — so you must track supports, not just formulas. Second, a Radon–Nikodym derivative can be **unbounded**: $d\mu_1/d\mu_3 = 1/x^2$ blows up at $0$, yet it is a perfectly valid density because the point $x=0$ is Lebesgue-null and $\int (1/x^2)\,x^2\,dx=\int 1\,dx$. Keeping the "where" (supports) and the "ratio" (densities) straight across all six cases is the whole task.

## The Key Insight

Write each measure as a density against Lebesgue measure on $[-2,2]$:
$$d\mu_1 = \underbrace{1}_{g_1}\,dx,\qquad d\mu_2 = \underbrace{\mathbf 1_{(0,1)}}_{g_2}\,dx,\qquad d\mu_3 = \underbrace{x^2}_{g_3}\,dx.$$

**Density-comparison lemma.** If $d\mu_i=g_i\,dx$ and $d\mu_j=g_j\,dx$ with $g_i,g_j\ge0$, split $[-2,2]$ into $A=\{g_j>0\}$ and $A^c=\{g_j=0\}$. Then
$$d\mu_i = \underbrace{\frac{g_i}{g_j}\,\mathbf 1_A}_{=f_{i,j}}\,d\mu_j \;+\; \underbrace{g_i\,\mathbf 1_{A^c}\,dx}_{=\,d\nu_{i,j}},$$
and $\nu_{i,j}\perp\mu_j$ because $\nu_{i,j}$ lives on $A^c$ while $\mu_j$ lives on $A$ (and $\mu_j(A^c)=0$). The decomposition is **a.c.** ($\nu_{i,j}=0$) precisely when $\mu_i$ puts no mass on $\{g_j=0\}$, i.e. when $\operatorname{supp}\mu_i\subseteq\operatorname{supp}\mu_j$ (up to null sets).

The consequence is immediate: $\mu_1$ and $\mu_3$ have full support $[-2,2]$ (since $1>0$ and $x^2>0$ off the null point $0$), while $\mu_2$ is supported only on $(0,1)$. So **a singular part appears only when we decompose against $\mu_2$** — namely for $(1,2)$ and $(3,2)$, where $\mu_1$/$\mu_3$ carry mass on $[-2,0]\cup[1,2]$ that $\mu_2$ cannot see. All four other pairs are purely absolutely continuous.

## Complete Proof

Throughout, "on $A$" means $\mu_j$-a.e.; values of $f_{i,j}$ on $\{g_j=0\}$ are irrelevant (that set is $\mu_j$-null) and we set them to $0$. We verify each pair by checking $\int_E f_{i,j}\,d\mu_j+\nu_{i,j}(E)=\mu_i(E)$ and that $\nu_{i,j}\perp\mu_j$. Endpoints $\{0,1\}$ are Lebesgue-null and ignored.

**Pair (2,1): $\mu_2$ w.r.t. $\mu_1$ (Lebesgue).** Here $g_1=1>0$ everywhere, so $A=[-2,2]$, $A^c=\varnothing$.
$$f_{2,1}=\frac{g_2}{g_1}=\mathbf 1_{(0,1)},\qquad \nu_{2,1}=0.$$
Check: $\int_E \mathbf 1_{(0,1)}\,dx = m(E\cap(0,1)) = \mu_2(E)$. ($\mu_2\ll\mu_1$.)

**Pair (3,1): $\mu_3$ w.r.t. $\mu_1$ (Lebesgue).** Again $A=[-2,2]$.
$$f_{3,1}=\frac{g_3}{g_1}=x^2,\qquad \nu_{3,1}=0.$$
Check: $\int_E x^2\,dx = \mu_3(E)$ by definition. ($\mu_3\ll\mu_1$.)

**Pair (1,3): $\mu_1$ w.r.t. $\mu_3$.** $g_3=x^2>0$ except at $x=0$; so $A=[-2,2]\setminus\{0\}$, $A^c=\{0\}$.
$$f_{1,3}=\frac{g_1}{g_3}=\frac{1}{x^2},\qquad \nu_{1,3}=\mu_1\big|_{\{0\}}=0.$$
Check: $\int_E \frac{1}{x^2}\,d\mu_3=\int_E \frac{1}{x^2}\,x^2\,dx=\int_E 1\,dx=m(E)=\mu_1(E)$. The RN derivative $1/x^2$ is unbounded near $0$ but valid: $\{0\}$ is null, so $\mu_1(\{0\})=0$ and $\nu_{1,3}=0$ ($\mu_1\ll\mu_3$).

**Pair (2,3): $\mu_2$ w.r.t. $\mu_3$.** $A=[-2,2]\setminus\{0\}$, and $g_2=\mathbf 1_{(0,1)}$.
$$f_{2,3}=\frac{g_2}{g_3}=\frac{\mathbf 1_{(0,1)}}{x^2}\;\Big(=\tfrac{1}{x^2}\text{ on }(0,1),\ 0\text{ else}\Big),\qquad \nu_{2,3}=\mu_2\big|_{\{0\}}=0.$$
Check: $\int_E \frac{\mathbf 1_{(0,1)}}{x^2}\,x^2\,dx=\int_E \mathbf 1_{(0,1)}\,dx=m(E\cap(0,1))=\mu_2(E)$. ($\mu_2\ll\mu_3$.)

**Pair (1,2): $\mu_1$ w.r.t. $\mu_2$ — singular part appears.** $g_2=\mathbf 1_{(0,1)}$, so $A=(0,1)$ and $A^c=[-2,0]\cup[1,2]$.
$$f_{1,2}=\frac{g_1}{g_2}=1\ \text{on }(0,1),\qquad d\nu_{1,2}=g_1\,\mathbf 1_{A^c}\,dx=\mathbf 1_{[-2,0]\cup[1,2]}\,dx,$$
i.e. $\nu_{1,2}(E)=m\big(E\cap([-2,0]\cup[1,2])\big)$ — Lebesgue measure restricted to $[-2,0]\cup[1,2]$.
Check: $\int_E 1\,d\mu_2+\nu_{1,2}(E)=m(E\cap(0,1))+m(E\cap([-2,0]\cup[1,2]))=m(E)=\mu_1(E)$. Singular: $\nu_{1,2}$ lives on $[-2,0]\cup[1,2]$, $\mu_2$ on $(0,1)$ — disjoint, so $\nu_{1,2}\perp\mu_2$. ✓

**Pair (3,2): $\mu_3$ w.r.t. $\mu_2$ — singular part appears.** Same split $A=(0,1)$, $A^c=[-2,0]\cup[1,2]$.
$$f_{3,2}=\frac{g_3}{g_2}=x^2\ \text{on }(0,1),\qquad d\nu_{3,2}=g_3\,\mathbf 1_{A^c}\,dx=x^2\,\mathbf 1_{[-2,0]\cup[1,2]}\,dx,$$
i.e. $\nu_{3,2}(E)=\int_{E\cap([-2,0]\cup[1,2])} x^2\,dx$.
Check: $\int_E x^2\,d\mu_2+\nu_{3,2}(E)=\int_{E\cap(0,1)}x^2\,dx+\int_{E\cap([-2,0]\cup[1,2])}x^2\,dx=\int_E x^2\,dx=\mu_3(E)$. Singular: $\nu_{3,2}$ on $[-2,0]\cup[1,2]$, $\mu_2$ on $(0,1)$ — disjoint, $\nu_{3,2}\perp\mu_2$. ✓

### Summary table

| pair $(i,j)$ | $\mu_i$ vs $\mu_j$ | $f_{i,j}(x)$ | $\nu_{i,j}$ |
|---|---|---|---|
| $(2,1)$ | $\mathbf 1_{(0,1)}\!\cdot dx$ vs $dx$ | $\mathbf 1_{(0,1)}$ | $0$ |
| $(3,1)$ | $x^2 dx$ vs $dx$ | $x^2$ | $0$ |
| $(1,3)$ | $dx$ vs $x^2 dx$ | $1/x^2$ | $0$ |
| $(2,3)$ | $\mathbf 1_{(0,1)}\!\cdot dx$ vs $x^2 dx$ | $\mathbf 1_{(0,1)}/x^2$ | $0$ |
| $(1,2)$ | $dx$ vs $\mathbf 1_{(0,1)}\!\cdot dx$ | $1$ on $(0,1)$ | $dx$ on $[-2,0]\cup[1,2]$ |
| $(3,2)$ | $x^2 dx$ vs $\mathbf 1_{(0,1)}\!\cdot dx$ | $x^2$ on $(0,1)$ | $x^2 dx$ on $[-2,0]\cup[1,2]$ |

All six decompositions are exhibited with $\nu_{i,j}\perp\mu_j$. $\qquad\blacksquare$

## What Connects

**Within measure theory.** This is the **Lebesgue–Radon–Nikodym theorem** made concrete: when all measures share a common dominating measure (here $dx$), decomposition is pure density arithmetic — $f_{i,j}=g_i/g_j$ on the support of $g_j$, with the singular part being $\mu_i$ "stranded" on $\{g_j=0\}$. The example is designed to exercise the three qualitatively different outcomes: **equivalent** measures (same support, $\nu=0$, RN derivative bounded away from $0$ and $\infty$ — e.g. $(3,1)$ on compact pieces), **a.c. with unbounded derivative** ($(1,3)$, where $1/x^2$ shows a valid RN derivative need not be bounded), and **a genuine singular part** ($(1,2),(3,2)$, where the smaller support of $\mu_2$ forces mass outside $(0,1)$ into $\nu$). The guiding principle — *singular part = mass on the null set of the reference* — is the same one behind the decomposition of a distribution into a.c. + singular-continuous + atomic parts, and behind mutual singularity of e.g. Lebesgue vs. the Cantor measure.
