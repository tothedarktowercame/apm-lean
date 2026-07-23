<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02A01: Weak vs strong convergence — uniqueness, the one-way implication, and the finite-dimensional collapse

## Why It's Hard

Weak convergence is defined by *testing against every continuous functional*, and the whole point of this problem is that this is genuinely coarser than norm convergence — but only in infinite dimensions. The difficulties are conceptual rather than computational:

- **(a)** Uniqueness of weak limits is *not* obvious: it requires that the dual space $X^*$ be rich enough to **separate points**, which is a nontrivial consequence of the **Hahn–Banach theorem** (in a bare normed space one cannot take this for granted).
- **(c)** The gap between weak and strong is a purely *infinite-dimensional* phenomenon, and producing the right counterexample means recognizing that an orthonormal/basis sequence can "escape to weak zero" while keeping norm $1$ — a manifestation of the non-compactness of the unit ball.
- **(d)** Showing the two notions coincide in finite dimensions requires seeing that weak convergence is exactly *coordinatewise* convergence with respect to a basis, and that with only finitely many coordinates this forces norm convergence.

## The Key Insight

Weak convergence $x_n\rightharpoonup x$ means $f(x_n)\to f(x)$ for **all** $f\in X^*$ — convergence "seen by every functional." Two facts organize everything:

- **Hahn–Banach makes $X^*$ separate points** (for $z\ne 0$ there is $f\in X^*$ with $f(z)=\|z\|\ne 0$), so $f(x)=f(y)\ \forall f$ forces $x=y$: weak limits are **unique** (a). The same bound $|f(x_n)-f(x)|\le\|f\|\,\|x_n-x\|$ gives strong $\Rightarrow$ weak instantly (b).
- The converse fails exactly because the unit ball is **non-compact** in infinite dimensions: in $\ell^2$, the basis vectors $e_n\rightharpoonup 0$ (each coordinate $\to 0$) yet $\|e_n\|=1$ (c). In **finite** dimensions there are only finitely many coordinate functionals, so weak = coordinatewise = norm convergence (d).

## Complete Proof

### Part (a): definition and uniqueness

**Definition.** A sequence $(x_n)$ in $X$ **converges weakly** to $x\in X$, written $x_n\rightharpoonup x$, if
$$
f(x_n)\to f(x)\qquad\text{for every }f\in X^* \ (\text{the continuous dual of }X).
$$

**Uniqueness.** Suppose $x_n\rightharpoonup x$ and $x_n\rightharpoonup y$. Then for every $f\in X^*$, $f(x)=\lim f(x_n)=f(y)$, so $f(x-y)=0$ for all $f\in X^*$. By a standard corollary of the **Hahn–Banach theorem**, if $x-y\ne 0$ there exists $f\in X^*$ with $f(x-y)=\|x-y\|\ne 0$ — a contradiction. Hence $x-y=0$, i.e. $x=y$. So weak limits are **unique**. (This rests on $X^*$ separating the points of $X$, which is exactly what Hahn–Banach guarantees; in a general normed space it is not automatic.) $\qquad\checkmark$

### Part (b): strong convergence implies weak convergence

Suppose $x_n\to x$ strongly, i.e. $\|x_n-x\|\to 0$. For any $f\in X^*$,
$$
|f(x_n)-f(x)|=|f(x_n-x)|\le\|f\|\,\|x_n-x\|\to 0 .
$$
Thus $f(x_n)\to f(x)$ for every $f\in X^*$, i.e. $x_n\rightharpoonup x$. $\qquad\checkmark$

### Part (c): weak convergence does not imply strong convergence

Take $X=\ell^2$ (square-summable sequences) and let $e_n=(0,\dots,0,1,0,\dots)$ be the $n$-th standard basis vector. By the Riesz representation theorem, every $f\in(\ell^2)^*$ is given by some $a=(a_k)\in\ell^2$ via $f(x)=\sum_k a_k x_k$, so
$$
f(e_n)=a_n\xrightarrow[n\to\infty]{}0,
$$
because $\sum_k|a_k|^2<\infty$ forces $a_n\to 0$. Hence $f(e_n)\to 0=f(0)$ for every $f\in(\ell^2)^*$, i.e. $e_n\rightharpoonup 0$ weakly. But
$$
\|e_n-0\|=\|e_n\|=1\not\to 0,
$$
so $(e_n)$ does **not** converge strongly (and cannot converge strongly to any other limit, since by part (a)–(b) the only candidate is the weak limit $0$). Thus weak convergence does not imply strong convergence. $\qquad\checkmark$

*(Equivalently, in $L^2[0,1]$ the sequence $\sin(n\pi x)\rightharpoonup 0$ by the Riemann–Lebesgue lemma while $\|\sin(n\pi x)\|_{L^2}=\tfrac1{\sqrt2}\not\to0$.)*

### Part (d): in finite dimensions, weak convergence implies strong convergence

By part (b) it remains to prove weak $\Rightarrow$ strong when $\dim X=d<\infty$. Fix a basis $b_1,\dots,b_d$ of $X$, with associated coordinate functionals $f_1,\dots,f_d$ determined by $f_i(b_j)=\delta_{ij}$. On a finite-dimensional space *every* linear functional is continuous, so each $f_i\in X^*$.

Suppose $x_n\rightharpoonup x$. Applying the definition to each $f_i$ gives convergence of coordinates:
$$
f_i(x_n)\to f_i(x)\qquad(i=1,\dots,d).
$$
Writing $x_n=\sum_{i=1}^d f_i(x_n)\,b_i$ and $x=\sum_{i=1}^d f_i(x)\,b_i$,
$$
\|x_n-x\|=\Big\|\sum_{i=1}^d\big(f_i(x_n)-f_i(x)\big)b_i\Big\|\le\sum_{i=1}^d |f_i(x_n)-f_i(x)|\,\|b_i\|\xrightarrow[n\to\infty]{}0,
$$
a finite sum of terms each tending to $0$. Hence $x_n\to x$ strongly. Combined with part (b), **weak and strong convergence coincide** in finite dimensions. $\qquad\blacksquare$

### Remark — what really distinguishes the two notions

The structural picture: strong convergence is convergence in the metric of $X$; weak convergence is convergence in the *initial topology* generated by $X^*$ (the coarsest making every $f\in X^*$ continuous). Hahn–Banach is what makes this topology Hausdorff (points separated), giving unique limits, and the trivial estimate $|f(x_n)-f(x)|\le\|f\|\,\|x_n-x\|$ makes it coarser than the norm topology — hence strong $\Rightarrow$ weak, never the reverse in general. The reverse holds precisely when $X$ is finite-dimensional: there the weak topology equals the norm topology (only finitely many coordinate functionals to test), and equivalently the closed unit ball is norm-compact. In infinite dimensions the ball is never norm-compact, and the basis sequence $e_n\rightharpoonup 0$, $\|e_n\|=1$ is the canonical witness — the gap between weak and strong convergence is, at bottom, the failure of compactness of the unit ball (Riesz's theorem). This is why weak convergence is indispensable in infinite-dimensional analysis: bounded sequences need not have strongly convergent subsequences, but in reflexive spaces they always have *weakly* convergent ones.
