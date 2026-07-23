<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02J03: Weak convergence in Hilbert space — boundedness, the Radon–Riesz property, and Mazur's theorem

## Why It's Hard

The three parts probe how far weak convergence sits from strong convergence in a Hilbert space, and each invokes a different cornerstone of functional analysis:

- **(a)** that weakly convergent sequences are bounded is *not* elementary — it is the **Uniform Boundedness Principle** (Banach–Steinhaus) in disguise, applied to the functionals $y\mapsto\langle y,x_n\rangle$, and it crucially needs completeness of $H$.
- **(b)** the equivalence "strong $\iff$ norms converge" is the **Radon–Riesz / Kadec–Klee property**, special to Hilbert (and uniformly convex) spaces. The whole content is hidden in the expansion of $\|x_n-x\|^2$, where weak convergence silently kills the cross term, leaving the norms as the *only* obstruction to strong convergence.
- **(c)** the existence of convex combinations converging *strongly* to the weak limit is **Mazur's theorem**, whose proof requires the nontrivial topological fact (Hahn–Banach separation) that a convex *strongly* closed set is *weakly* closed. The surprise is that although the $x_n$ themselves may not converge strongly (e.g. an orthonormal sequence $\rightharpoonup 0$), suitable *averages* of them do.

## The Key Insight

Weak convergence means $\langle x_n,y\rangle\to\langle x,y\rangle$ for all $y\in H$. Three consequences, each from one principle:

- **(a)** The functionals $f_n(y)=\langle y,x_n\rangle$ satisfy $\|f_n\|=\|x_n\|$ and are *pointwise bounded* (each $f_n(y)$ converges, hence is bounded in $n$); the **UBP** upgrades this to $\sup_n\|x_n\|<\infty$.
- **(b)** From $\|x_n-x\|^2=\|x_n\|^2-2\,\mathrm{Re}\langle x_n,x\rangle+\|x\|^2$ and $\langle x_n,x\rangle\to\|x\|^2$ (weak convergence with $y=x$), the middle term $\to-2\|x\|^2$, so $\|x_n-x\|^2\to\|x\|^2-\|x\|^2$ collapses to $0$ **iff** $\|x_n\|\to\|x\|$.
- **(c)** The strong closure of $\operatorname{conv}\{x_n\}$ is convex and strongly closed, hence **weakly closed** (Hahn–Banach); since $x_n\rightharpoonup x$ and $x_n$ lie in it, so does $x$ — i.e. convex combinations of the $x_n$ converge strongly to $x$.

## Complete Proof

Throughout $H$ is a Hilbert space and $x_n\rightharpoonup x$: $\langle x_n,y\rangle\to\langle x,y\rangle$ for every $y\in H$.

### Part (a): $\{x_n\}$ is bounded

For each $n$ define the linear functional $f_n:H\to\mathbb{C}$ by $f_n(y)=\langle y,x_n\rangle$. By Cauchy–Schwarz $|f_n(y)|\le\|x_n\|\,\|y\|$, and taking $y=x_n$ shows $\|f_n\|=\|x_n\|$; in particular each $f_n$ is bounded.

For every fixed $y\in H$, $f_n(y)=\langle y,x_n\rangle=\overline{\langle x_n,y\rangle}\to\overline{\langle x,y\rangle}$ converges, hence $\sup_n|f_n(y)|<\infty$ (a convergent scalar sequence is bounded). So $\{f_n\}$ is *pointwise bounded* on the **complete** space $H$. By the **Uniform Boundedness Principle** (Banach–Steinhaus),
$$
\sup_n\|x_n\|=\sup_n\|f_n\|<\infty .
$$
Thus $\{x_n\}$ is bounded in $H$. $\qquad\checkmark$

### Part (b): $x_n\to x$ strongly $\iff$ $\|x_n\|\to\|x\|$

Expand, using the inner product structure:
$$
\|x_n-x\|^2=\langle x_n-x,\,x_n-x\rangle=\|x_n\|^2-2\,\mathrm{Re}\langle x_n,x\rangle+\|x\|^2 .
$$
Taking $y=x$ in the definition of weak convergence gives $\langle x_n,x\rangle\to\langle x,x\rangle=\|x\|^2$, so $\mathrm{Re}\langle x_n,x\rangle\to\|x\|^2$. Hence
$$
\|x_n-x\|^2=\big(\|x_n\|^2-\|x\|^2\big)+2\big(\|x\|^2-\mathrm{Re}\langle x_n,x\rangle\big),
$$
where the **second term tends to $0$ automatically** (weak convergence).

- **($\Leftarrow$)** If $\|x_n\|\to\|x\|$, then $\|x_n\|^2-\|x\|^2\to0$, so $\|x_n-x\|^2\to0$, i.e. $x_n\to x$ strongly.
- **($\Rightarrow$)** If $x_n\to x$ strongly, then by the reverse triangle inequality $\big|\,\|x_n\|-\|x\|\,\big|\le\|x_n-x\|\to0$, so $\|x_n\|\to\|x\|$. (This direction holds in any normed space.)

Therefore, given $x_n\rightharpoonup x$, strong convergence is equivalent to convergence of the norms. $\qquad\checkmark$

### Part (c): convex combinations converge strongly to $x$ (Mazur's theorem)

Let $C=\operatorname{conv}\{x_n:n\ge1\}$ be the convex hull, and $\overline C$ its **strong** closure. We claim $x\in\overline C$; granting this, by definition of closure there is a sequence of points of $C$ — i.e. finite convex combinations $z_n=\sum_i\alpha_i^{(n)}x_i$ with $\alpha_i^{(n)}\ge0$, $\sum_i\alpha_i^{(n)}=1$ — converging strongly to $x$, which is the assertion.

**Lemma (convex + strongly closed $\Rightarrow$ weakly closed).** Let $K\subseteq H$ be convex and strongly closed, and suppose $z\notin K$. By the **Hahn–Banach separation theorem** applied to the point $\{z\}$ and the closed convex set $K$, there exist a continuous linear functional $f$ and $\alpha\in\mathbb{R}$ with
$$
\mathrm{Re}\,f(z)>\alpha\ge\mathrm{Re}\,f(w)\quad\text{for all }w\in K .
$$
The set $\{u:\mathrm{Re}\,f(u)>\alpha\}$ is **weakly open** (preimage of an open set under the weakly continuous $f$), contains $z$, and is disjoint from $K$. So $H\setminus K$ is weakly open, i.e. $K$ is weakly closed.

Apply the lemma to $K=\overline C$ (convex, strongly closed). Then $\overline C$ is weakly closed. Since every $x_n\in C\subseteq\overline C$ and $x_n\rightharpoonup x$, weak closedness gives $x\in\overline C$. Hence $x$ lies in the strong closure of the convex hull, and the desired strongly convergent convex combinations exist. $\qquad\blacksquare$

*(One may arrange the combinations to use only initial segments $x_1,\dots,x_{m_n}$: given $\varepsilon=1/n$, pick a convex combination within $1/n$ of $x$; it involves finitely many indices, so taking $m_n$ to be the largest gives $z_n\to x$ as in the statement.)*

### Remark — the three faces of weak convergence

Together these results delineate exactly how weak and strong convergence relate in Hilbert space. (a) is the structural fact that weak convergence cannot blow up — a consequence of completeness via Banach–Steinhaus, and the reason bounded sequences are the natural setting (in a Hilbert space, *every* bounded sequence has a weakly convergent subsequence, by reflexivity). (b) is the **Radon–Riesz property**: the only thing weak convergence lacks to be strong is convergence of norms — geometrically, weak convergence plus "no loss of mass" forces strong convergence; this fails in general Banach spaces but holds in uniformly convex ones, of which Hilbert spaces are the model. (c) is **Mazur's theorem**, the bridge that recovers *strong* information from weak: although an orthonormal sequence $e_n\rightharpoonup 0$ never converges strongly, the averages $\frac1n\sum_{k=1}^n e_k\to 0$ strongly ($\|\tfrac1n\sum e_k\|=1/\sqrt n$), illustrating exactly the convex-combination phenomenon. This is the analytic foundation for extracting strongly convergent minimizing sequences in the calculus of variations and convex optimization.
