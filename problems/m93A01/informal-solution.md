<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93A01: Compact Sobolev embeddings on the circle via Fourier series, and bounded-vs-compact for four operators

## Why It's Hard

The problem looks like four disconnected facts about Sobolev spaces, but they are really one principle examined from four angles. The challenge is to find the single lens through which all of them become transparent:

- **(a)** "Show *in detail*" that $H^1(S^1)\hookrightarrow L^2(S^1)$ is compact — this is the Rellich–Kondrachov theorem in its simplest incarnation, and the grader wants the mechanism, not a citation. On the circle the mechanism is completely explicit: **Fourier series diagonalize everything**, and compactness becomes a statement about decay of a sequence of multipliers.
- **(b)** then probes the boundaries of part (a) by changing *one ingredient at a time*:
  - **(i)** keeps the embedding but swaps the **compact** domain $S^1$ for the **non-compact** $\mathbb{R}$ — and compactness fails, because mass can escape to infinity (translation invariance). This is the subtle one: the *same* inclusion that is compact on the circle is only bounded on the line.
  - **(ii)** keeps the circle but swaps the inclusion for the **derivative** $H^1\to L^2$ — bounded but not compact, because differentiation does **not** gain smoothing relative to the available regularity; high frequencies are not compressed.
  - **(iii)** gives the derivative *one more derivative to spend*, $H^2\to L^2$ — now compact, because there is a genuine **gain of one derivative**, which is exactly the compact embedding of (a) in disguise.

The trap throughout is to conflate **bounded** with **compact**. Every one of the four maps is bounded; the content is which are compact, and the Fourier picture makes the dividing line a one-line decay condition.

## The Key Insight

Identify $S^1=\mathbb{R}/2\pi\mathbb{Z}$ and use the orthonormal basis $e_n(x)=e^{inx}/\sqrt{2\pi}$, $n\in\mathbb{Z}$, of $L^2(S^1)$. Writing $f=\sum_n a_n e_n$ with $a_n=\langle f,e_n\rangle$, Parseval gives $\|f\|_{L^2}^2=\sum_n|a_n|^2$, and (integrating by parts, periodic boundary terms vanishing) the weak derivative has Fourier coefficients $\widehat{f'}(n)=in\,a_n$, so
$$
\|f'\|_{L^2}^2=\sum_n n^2|a_n|^2,\qquad \|f\|_{H^k}^2\asymp\sum_n(1+n^2)^k|a_n|^2 .
$$
Thus **every operator in the problem is a Fourier multiplier** $T:e_n\mapsto\lambda_n e_n$ between weighted $\ell^2$ spaces, and the governing principle is:

> A multiplier from $\{(1+n^2)^{s}\text{-weighted }\ell^2\}$ to $\{(1+n^2)^{t}\text{-weighted }\ell^2\}$ with symbol $\lambda_n$ is **bounded** iff $\sup_n\dfrac{|\lambda_n|\,(1+n^2)^{t/2}}{(1+n^2)^{s/2}}<\infty$, and **compact** iff that ratio $\to0$ as $|n|\to\infty$ — *provided* the domain is a genuine $\ell^2$ over a discrete spectrum, i.e. the underlying manifold is **compact**.

Reading off the four ratios:

| map | weight ratio at frequency $n$ | $|n|\to\infty$ | verdict |
|---|---|---|---|
| (a) $\iota:H^1(S^1)\to L^2$ | $1/\sqrt{1+n^2}$ | $\to 0$ | **compact** |
| (i) $\iota:H^1(\mathbb{R})\to L^2$ | $1/\sqrt{1+\xi^2}$, $\xi\in\mathbb{R}$ *continuous* | $\to0$ but spectrum continuous | bounded, **not** compact |
| (ii) $D:H^1(S^1)\to L^2$ | $|n|/\sqrt{1+n^2}$ | $\to 1$ | bounded, **not** compact |
| (iii) $D:H^2(S^1)\to L^2$ | $|n|/(1+n^2)$ | $\to 0$ | **compact** |

The continuous spectrum of $\mathbb{R}$ is exactly why (i) escapes the "ratio $\to0\Rightarrow$ compact" rule: there is no smallest nonzero frequency gap, and translation produces a bounded sequence with no convergent subsequence.

## Complete Proof

**Fourier setup.** $\{e_n\}_{n\in\mathbb{Z}}$, $e_n(x)=e^{inx}/\sqrt{2\pi}$, is an orthonormal basis of $L^2(S^1)$. For $f\in L^2$ with $f=\sum_n a_n e_n$ ($a_n=\langle f,e_n\rangle$), Parseval gives $\|f\|_{L^2}^2=\sum_n|a_n|^2$. If $f\in H^1$ (weak derivative $f'\in L^2$), then for each $n$, integrating by parts on $S^1$,
$$
\langle f',e_n\rangle=\int_0^{2\pi}f'\,\overline{e_n}\,dx=-\int_0^{2\pi}f\,\overline{e_n}{}'\,dx=in\int_0^{2\pi}f\,\overline{e_n}\,dx=in\,a_n,
$$
the boundary term vanishing by periodicity. Hence $\|f'\|_{L^2}^2=\sum_n n^2|a_n|^2$, and
$$
\|f\|_{H^1}^2=\|f\|_{L^2}^2+\|f'\|_{L^2}^2=\sum_n(1+n^2)|a_n|^2,\qquad
\|f\|_{H^2}^2\asymp\sum_n(1+n^2)^2|a_n|^2 .
$$
(The stated norm $\sum_{i=0}^k\|D^if\|_{L^2}^2=\sum_n(\sum_{i=0}^k n^{2i})|a_n|^2$ is equivalent to $\sum_n(1+n^2)^k|a_n|^2$, the constants being harmless.) In particular $H^k(S^1)=\{f\in L^2:\sum_n(1+n^2)^k|a_n|^2<\infty\}$.

### Part (a): $\iota:H^1(S^1)\to L^2(S^1)$ is compact

Let $\iota$ be the inclusion. We exhibit $\iota$ as a **norm limit of finite-rank operators**, which is the cleanest "in detail" route to compactness.

For $N\ge0$ define the truncation $P_N:H^1\to L^2$,
$$
P_N f=\sum_{|n|\le N}a_n e_n .
$$
The range of $P_N$ is contained in $\operatorname{span}\{e_n:|n|\le N\}$, a space of dimension $2N+1$, so $P_N$ is a **bounded finite-rank operator**, hence compact.

Now estimate $\|\iota-P_N\|_{H^1\to L^2}$. For $f\in H^1$ with $\|f\|_{H^1}\le1$,
$$
\|\iota f-P_N f\|_{L^2}^2=\Big\|\sum_{|n|>N}a_ne_n\Big\|_{L^2}^2=\sum_{|n|>N}|a_n|^2
=\sum_{|n|>N}\frac{1}{1+n^2}\,(1+n^2)|a_n|^2 .
$$
For $|n|>N$ we have $\dfrac{1}{1+n^2}\le\dfrac{1}{1+N^2}$, so
$$
\|\iota f-P_N f\|_{L^2}^2\le\frac{1}{1+N^2}\sum_{|n|>N}(1+n^2)|a_n|^2\le\frac{1}{1+N^2}\,\|f\|_{H^1}^2\le\frac{1}{1+N^2}.
$$
Taking the supremum over the unit ball,
$$
\|\iota-P_N\|_{H^1\to L^2}\le\frac{1}{\sqrt{1+N^2}}\xrightarrow[N\to\infty]{}0 .
$$
Thus $\iota$ is the operator-norm limit of the compact operators $P_N$. Since the compact operators form a closed subspace of the bounded operators (a norm limit of compact operators is compact), $\iota$ is **compact**. $\qquad\checkmark$

*(Equivalent sequential phrasing, for concreteness.) Let $\|f_m\|_{H^1}\le C$. Each coordinate is bounded, $|a_n^{(m)}|\le\|f_m\|_{L^2}\le C$, so by a diagonal argument pass to a subsequence with $a_n^{(m)}\to a_n$ for every $n$. The tails are uniformly small: $\sum_{|n|>N}|a_n^{(m)}|^2\le\frac{1}{1+N^2}\|f_m\|_{H^1}^2\le\frac{C^2}{1+N^2}$ for all $m$. Given $\varepsilon$, choose $N$ to kill the tail $<\varepsilon$ uniformly, then the finitely many coordinates $|n|\le N$ converge, so $(f_m)$ is Cauchy in $L^2$. Hence bounded sequences have $L^2$-convergent subsequences — compactness.*

### Part (b)

#### (i) $\iota:H^1(\mathbb{R})\to L^2(\mathbb{R})$ — bounded, **not** compact

**Bounded.** Directly from the definition $\|f\|_{H^1(\mathbb{R})}^2=\|f\|_{L^2}^2+\|f'\|_{L^2}^2$,
$$
\|\iota f\|_{L^2}=\|f\|_{L^2}\le\|f\|_{H^1},
$$
so $\|\iota\|\le1$.

**Not compact.** Compactness fails because $\mathbb{R}$ is not compact and mass can run off to infinity. Fix $0\ne\varphi\in C_c^\infty(\mathbb{R})$ and set
$$
f_k(x)=\varphi(x-k),\qquad k\in\mathbb{N}.
$$
Translation preserves all $L^2$ norms of $f$ and $f'$, so $\|f_k\|_{H^1}=\|\varphi\|_{H^1}$ for all $k$: the sequence is **bounded** in $H^1$. But choose $k\ne j$ with $|k-j|>\operatorname{diam}(\operatorname{supp}\varphi)$; then $f_k$ and $f_j$ have disjoint supports, so
$$
\|f_k-f_j\|_{L^2}^2=\|f_k\|_{L^2}^2+\|f_j\|_{L^2}^2=2\|\varphi\|_{L^2}^2>0 .
$$
Hence $(f_k)$ has no $L^2$-Cauchy subsequence, so $(\iota f_k)$ has no convergent subsequence. The image of the unit ball is not precompact: $\iota$ is **not compact**. $\qquad\checkmark$

#### (ii) $D:H^1(S^1)\to L^2(S^1)$ — bounded, **not** compact

**Bounded.** $\|Df\|_{L^2}=\|f'\|_{L^2}\le\big(\|f\|_{L^2}^2+\|f'\|_{L^2}^2\big)^{1/2}=\|f\|_{H^1}$, so $\|D\|\le1$.

**Not compact.** In Fourier terms $D$ is the multiplier $e_n\mapsto in\,e_n$. Normalize the basis vectors for the $H^1$ norm:
$$
g_n=\frac{e_n}{\sqrt{1+n^2}},\qquad \|g_n\|_{H^1}=1\ (n\ge1),
$$
a **bounded** sequence in $H^1$. Their images are
$$
Dg_n=\frac{in}{\sqrt{1+n^2}}\,e_n,\qquad \|Dg_n\|_{L^2}=\frac{|n|}{\sqrt{1+n^2}}\xrightarrow[n\to\infty]{}1 .
$$
Because the $e_n$ are orthogonal, for $n\ne m$,
$$
\|Dg_n-Dg_m\|_{L^2}^2=\frac{n^2}{1+n^2}+\frac{m^2}{1+m^2}\xrightarrow[n,m\to\infty]{}2 .
$$
So $(Dg_n)$ is not $L^2$-Cauchy and has no convergent subsequence: $D$ maps a bounded set to a non-precompact one, hence is **not compact**. (Mechanism: the symbol ratio $|n|/\sqrt{1+n^2}\to1$ does not decay — differentiation exactly consumes the one derivative of regularity that $H^1$ provides, leaving nothing to smooth the high frequencies.) $\qquad\checkmark$

#### (iii) $D:H^2(S^1)\to L^2(S^1)$ — bounded **and** compact

**Bounded.** $\|Df\|_{L^2}=\|f'\|_{L^2}\le\big(\|f\|_{L^2}^2+\|f'\|_{L^2}^2+\|f''\|_{L^2}^2\big)^{1/2}\asymp\|f\|_{H^2}$, so $\|D\|<\infty$.

**Compact — by factoring through part (a).** Differentiation raises into $H^1$ with one derivative to spare: if $f\in H^2$ then $f'\in H^1$ and
$$
\|f'\|_{H^1}^2=\|f'\|_{L^2}^2+\|f''\|_{L^2}^2\le\|f\|_{H^2}^2,
$$
so $\tilde D:H^2\to H^1$, $\tilde D f=f'$, is **bounded**. Then
$$
D=\big(H^2\xrightarrow{\ \tilde D\ }H^1\xrightarrow{\ \iota\ }L^2\big),
$$
the composition of the bounded operator $\tilde D$ with the **compact** inclusion $\iota$ from part (a). A composition with a compact operator is compact, so $D:H^2\to L^2$ is **compact**. $\qquad\blacksquare$

*(Direct check of the decay, matching the table.) $D$ is the multiplier $e_n\mapsto in\,e_n$, and normalizing in $H^2$ gives $h_n=e_n/\|e_n\|_{H^2}$ with $\|e_n\|_{H^2}^2\asymp(1+n^2)^2$, so $\|Dh_n\|_{L^2}=|n|/\|e_n\|_{H^2}\asymp |n|/(1+n^2)\to0$. The truncations $P_N\circ D$ then approximate $D$ in operator norm exactly as in part (a), with bound $\sim 1/N\to0$.)*

### Remark — one principle, four readings

All four maps are bounded; compactness is governed entirely by whether the Fourier-multiplier symbol decays relative to the domain's weight **and** whether the spectrum is discrete:

- **(a)** and **(iii)** are compact because each *gains a derivative*: the ratio $1/\sqrt{1+n^2}$ (resp. $|n|/(1+n^2)$) $\to0$. They are in fact the *same* theorem — (iii) is (a) precomposed with the derivative.
- **(ii)** fails because the derivative on $H^1(S^1)$ gains nothing (ratio $\to1$): it is bounded but not better.
- **(i)** fails for a different reason — the embedding *would* be "compact by decay" frequency-by-frequency, but the spectrum of $-d^2/dx^2$ on $\mathbb{R}$ is continuous, so there is no discrete tail to truncate; concretely, translation manufactures a bounded non-precompact sequence. The compactness of the underlying manifold ($S^1$ vs $\mathbb{R}$) is indispensable — this is precisely the hypothesis of Rellich–Kondrachov.
