<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99A05: Weak versus strong convergence — counterexample, implications, finite-dimensional collapse, boundedness, and uniqueness

## Why It's Hard

Five short parts, each isolating a *different* cornerstone of functional analysis, and the trap in every one is to forget that "weak" means **tested against all of $X^*$** while "strong" means **norm**:

- **(a)** demands an honest counterexample — one must name a space, a sequence, and verify *both* $f(u_n)\to f(u)$ for every functional *and* $\|u_n-u\|\not\to0$. The standard orthonormal-basis example works only because square-summability forces coordinates to vanish.
- **(b)** is the one-line easy direction, but it pins down *why*: continuity of each $f$.
- **(c)** the finite-dimensional collapse needs **equivalence of norms** / coordinate functionals — weak convergence of coordinates upgrades to norm convergence only because the dimension is finite.
- **(d)** boundedness from weak convergence is the **Uniform Boundedness Principle** in disguise, and the subtle point is *where completeness is used*: not on $X$ (which may be incomplete) but on $X^*$, which is **always** a Banach space — that is what licenses Banach–Steinhaus, via the canonical isometric embedding $X\hookrightarrow X^{**}$.
- **(e)** uniqueness of weak limits is exactly the statement that $X^*$ **separates points**, i.e. the **Hahn–Banach** theorem.

The difficulty is not depth in any one part but breadth: the problem is a checklist of the five facts that make the weak topology usable.

## The Key Insight

Recall: $u_n\rightharpoonup u$ (weak) means $f(u_n)\to f(u)$ for **every** $f\in X^*$; $u_n\to u$ (strong) means $\|u_n-u\|\to0$. The five parts are five different uses of the duality $X\leftrightarrow X^*$:

- **(a)** In $\ell^2$, the basis $e_n\rightharpoonup0$ (each coordinate $\to0$) but $\|e_n\|=1$: weak $\ne$ strong.
- **(b)** $|f(u_n)-f(u)|\le\|f\|\,\|u_n-u\|\to0$: continuity gives strong $\Rightarrow$ weak.
- **(c)** In finite dimensions, weak convergence = coordinatewise convergence, and (all norms equivalent) that *is* norm convergence.
- **(d)** Each $f(u_n)$ converges, hence is bounded in $n$; the family $\{u_n\}\subset X^{**}$ is pointwise bounded on the **Banach** space $X^*$, so **UBP** bounds $\sup_n\|u_n\|$.
- **(e)** If $f(u)=f(v)$ for all $f\in X^*$, then **Hahn–Banach** ($\exists f$ with $f(u-v)=\|u-v\|$) forces $u=v$.

## Complete Proof

Notation: $X^*$ is the dual (bounded linear functionals on $X$), itself a Banach space under the operator norm; $u_n\rightharpoonup u$ denotes weak convergence and $u_n\to u$ strong (norm) convergence.

### Part (a): weak $\not\Rightarrow$ strong (counterexample)

Take $X=\ell^2$ and let $u_n=e_n=(0,\dots,0,1,0,\dots)$ (the $1$ in slot $n$). The dual of $\ell^2$ is $\ell^2$ itself: every $f\in X^*$ is $f(x)=\sum_k f_k x_k$ for some $(f_k)\in\ell^2$. Then
$$
f(e_n)=f_n\xrightarrow[n\to\infty]{}0,
$$
because $\sum_k|f_k|^2<\infty$ forces $f_n\to0$. Thus $f(e_n)\to0=f(0)$ for every $f\in X^*$, i.e. $e_n\rightharpoonup0$. But
$$
\|e_n-0\|=\|e_n\|=1\not\to0,
$$
indeed $\|e_n-e_m\|=\sqrt2$ for $n\ne m$, so $(e_n)$ is not even Cauchy. Hence $e_n\rightharpoonup0$ while $e_n\not\to0$ strongly: weak convergence does not imply strong. $\qquad\checkmark$

### Part (b): strong $\Rightarrow$ weak

Suppose $u_n\to u$, i.e. $\|u_n-u\|\to0$. For any $f\in X^*$, boundedness of $f$ gives
$$
|f(u_n)-f(u)|=|f(u_n-u)|\le\|f\|\,\|u_n-u\|\xrightarrow[n\to\infty]{}0 .
$$
So $f(u_n)\to f(u)$ for every $f\in X^*$, which is precisely $u_n\rightharpoonup u$. $\qquad\checkmark$

### Part (c): in finite dimensions, weak $\iff$ strong

Strong $\Rightarrow$ weak holds always (part (b)); we prove the converse when $d:=\dim X<\infty$. Fix a basis $\{b_1,\dots,b_d\}$ of $X$ and let $f_1,\dots,f_d\in X^*$ be the associated **coordinate functionals**, i.e. $x=\sum_{i=1}^d f_i(x)\,b_i$ for all $x$ (these are linear, and continuous since every linear functional on a finite-dimensional space is bounded). Assume $u_n\rightharpoonup u$. Applying weak convergence to each $f_i$,
$$
f_i(u_n)\xrightarrow[n\to\infty]{}f_i(u)\qquad(i=1,\dots,d).
$$
Therefore
$$
\|u_n-u\|=\Big\|\sum_{i=1}^d\big(f_i(u_n)-f_i(u)\big)b_i\Big\|\le\sum_{i=1}^d|f_i(u_n)-f_i(u)|\,\|b_i\|\xrightarrow[n\to\infty]{}0 ,
$$
so $u_n\to u$ strongly. (Equivalently: weak convergence is convergence of each coordinate, and on a finite-dimensional space all norms are equivalent, so coordinatewise convergence is norm convergence.) Hence in finite dimensions the two notions coincide. $\qquad\checkmark$

### Part (d): a weakly convergent sequence is norm-bounded

Assume $u_n\rightharpoonup u$. Embed $X$ into its bidual via the canonical map $J:X\to X^{**}$, $J(x)(f)=f(x)$; this is a **linear isometry**, $\|J(x)\|_{X^{**}}=\|x\|_X$ (a consequence of Hahn–Banach). Regard each $u_n$ as the functional $J(u_n)$ on $X^*$.

**Pointwise boundedness.** For each fixed $f\in X^*$, the scalar sequence $\big(f(u_n)\big)_n=\big(J(u_n)(f)\big)_n$ converges (to $f(u)$), and a convergent sequence of scalars is bounded:
$$
\sup_n\big|J(u_n)(f)\big|=\sup_n|f(u_n)|<\infty\qquad\text{for every }f\in X^* .
$$
So the family $\{J(u_n)\}_n$ of bounded linear functionals on $X^*$ is **pointwise bounded**.

**Apply Banach–Steinhaus.** The domain $X^*$ is a **Banach space** (the dual of any normed space is complete), so the **Uniform Boundedness Principle** applies to the family $\{J(u_n)\}\subseteq X^{**}=\mathcal B(X^*,\mathbb{F})$ and yields
$$
\sup_n\|J(u_n)\|_{X^{**}}<\infty .
$$
Since $J$ is isometric, $\|J(u_n)\|_{X^{**}}=\|u_n\|_X$, whence
$$
\sup_n\|u_n\|_X<\infty .
$$
Thus $\|u_n\|$ is bounded independently of $n$. (Note completeness was needed only on $X^*$, which holds regardless of whether $X$ itself is complete.) $\qquad\checkmark$

### Part (e): weak limits are unique

Suppose $u_n\rightharpoonup u$ and $u_n\rightharpoonup v$. Then for every $f\in X^*$,
$$
f(u)=\lim_n f(u_n)=f(v),\qquad\text{so}\qquad f(u-v)=0\ \ \text{for all }f\in X^* .
$$
By a corollary of the **Hahn–Banach theorem**, for any nonzero $w\in X$ there exists $f\in X^*$ with $\|f\|=1$ and $f(w)=\|w\|>0$. If $u-v\ne0$, taking $w=u-v$ would give some $f$ with $f(u-v)=\|u-v\|\ne0$, a contradiction. Hence $u-v=0$, i.e. $u=v$: the weak limit is unique. $\qquad\blacksquare$

### Remark — the five facts that make the weak topology work

Each part is a use of the pairing between $X$ and $X^*$, and together they justify treating "$\rightharpoonup$" as a genuine convergence:

- **(b)+(e)** say the weak topology is coarser than the norm topology yet still **Hausdorff** (limits unique) — the latter is exactly that $X^*$ **separates points** (Hahn–Banach).
- **(a)+(c)** locate the difference precisely: weak and strong agree **iff** $\dim X<\infty$; the orthonormal basis is the canonical witness that in infinite dimensions the weak topology is strictly coarser (and the closed unit ball, weakly compact in reflexive spaces, is never norm-compact).
- **(d)** is the structural backbone: weak convergence cannot blow up, by Banach–Steinhaus. It is what makes weak limits well-behaved and underlies the **Banach–Alaoglu / weak sequential compactness** results — every bounded sequence in a reflexive space has a weakly convergent subsequence, the workhorse of the direct method in the calculus of variations and PDE.
