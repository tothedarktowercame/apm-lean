<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m01J04: Weak×strong pairings and compensated compactness up to the div–curl lemma

## Why It's Hard

The governing fact of the subject is a *negative* one: **products of weakly convergent sequences do not converge**. If $a_n\rightharpoonup a$ and $b_n\rightharpoonup b$ weakly, the product $a_nb_n$ generally fails to converge to $ab$ (think $\sin(nx)\cdot\sin(nx)\rightharpoonup \tfrac12\ne 0$). So the entire art of these three parts is *finding the compensation* that rescues a specific bilinear quantity — and each part supplies the rescue differently:

- **(a)** is the basic principle — a pairing of a *weakly* convergent factor against a *strongly* convergent one does pass to the limit. The subtlety is needing boundedness of the weak sequence (from the Uniform Boundedness Principle).
- **(b)** rescues $u_n\nabla u_n$ — a product of two $H^1$-bounded factors — by upgrading $u_n\to u$ to *strong* $L^2$ convergence via the **Rellich–Kondrachov compact embedding**, while the gradients converge only weakly.
- **(c)** is the genuinely hard **div–curl lemma**: $\mathbf v_n$ and $\nabla f_n$ both converge *only weakly* in $L^2$, so no naive rescue exists. The compensation is *structural* — $\nabla\cdot\mathbf v_n$ converges strongly in $H^{-1}$ and $\nabla f_n$ is a gradient — and unlocking it requires an integration-by-parts/Leibniz manipulation that converts the product into pairings where one factor is, after all, strong.

## The Key Insight

Weak convergence is preserved under pairing **against a strongly convergent factor**. So the strategy throughout is: *manufacture a strong factor.*

- **(a)** $\langle f_n,g_n\rangle-\langle f,g\rangle=\langle f_n,g_n-g\rangle+\langle f_n-f,g\rangle$; the first term is $\le\|f_n\|\,\|g_n-g\|\to 0$ (bounded × strong), the second $\to0$ by weak convergence.
- **(b)** Rellich gives $u_{n_k}\to u$ strongly in $L^2$, so $u_{n_k}\psi\to u\psi$ *strongly* in $(L^2)^d$, while $\nabla u_{n_k}\rightharpoonup\nabla u$ weakly; pairing them via (a) gives $\int u_{n_k}\nabla u_{n_k}\cdot\psi=\int\nabla u_{n_k}\cdot(u_{n_k}\psi)\to\int\nabla u\cdot(u\psi)$.
- **(c)** Write $\varphi\nabla f_n=\nabla(f_n\varphi)-f_n\nabla\varphi$. Then
$$
\int\mathbf v_n\!\cdot\!\nabla f_n\,\varphi=-\langle\nabla\!\cdot\!\mathbf v_n,\,f_n\varphi\rangle_{H^{-1},H^1_0}-\int\mathbf v_n\!\cdot\!(f_n\nabla\varphi),
$$
and **both** terms are now weak×strong: $\nabla\cdot\mathbf v_n$ is strong in $H^{-1}$ (hypothesis) against $f_n\varphi\rightharpoonup f\varphi$ in $H^1_0$, and $f_n\nabla\varphi\to f\nabla\varphi$ strong in $L^2$ (Rellich) against $\mathbf v_n\rightharpoonup\mathbf v$.

## Complete Proof

Throughout $\langle f,g\rangle=g(f)$ denotes the duality pairing $X\times X^*$, and (for parts b,c) $\Omega\subset\mathbb R^d$ is a bounded domain with Lipschitz boundary, so the Rellich–Kondrachov theorem gives the compact embedding $H^1(\Omega)\hookrightarrow\hookrightarrow L^2(\Omega)$.

### Part (a): weak × strong $\Rightarrow$ convergence of the pairing

Let $f_n\rightharpoonup f$ weakly in $X$ and $g_n\to g$ strongly in $X^*$. Since weakly convergent sequences are bounded (Uniform Boundedness Principle applied to $\{f_n\}$ viewed as functionals on $X^*$), there is $M$ with $\|f_n\|\le M$. Decompose
$$
\langle f_n,g_n\rangle-\langle f,g\rangle=\underbrace{\langle f_n,\,g_n-g\rangle}_{(\mathrm I)}+\underbrace{\langle f_n-f,\,g\rangle}_{(\mathrm{II})} .
$$
For (I), $|\langle f_n,g_n-g\rangle|=|(g_n-g)(f_n)|\le\|g_n-g\|_{X^*}\,\|f_n\|_X\le M\,\|g_n-g\|_{X^*}\to 0$. For (II), $\langle f_n-f,g\rangle=g(f_n)-g(f)\to 0$ since $f_n\rightharpoonup f$ means $g(f_n)\to g(f)$ for every fixed $g\in X^*$. Hence $\langle f_n,g_n\rangle\to\langle f,g\rangle$. $\qquad\checkmark$

### Part (b): $u_{n_k}\nabla u_{n_k}\rightharpoonup u\nabla u$ tested against $(L^\infty)^d$

Let $\{u_n\}$ be bounded in $H^1(\Omega)$. Since $H^1$ is a Hilbert space (reflexive), bounded sequences have weakly convergent subsequences: pass to $u_{n_k}\rightharpoonup u$ in $H^1(\Omega)$ for some $u\in H^1(\Omega)$. Two consequences:

- $\nabla u_{n_k}\rightharpoonup\nabla u$ weakly in $(L^2(\Omega))^d$ (the gradient is a bounded linear map $H^1\to(L^2)^d$, hence weak–weak continuous).
- By **Rellich–Kondrachov**, the embedding $H^1\hookrightarrow L^2$ is compact, so (passing to a further subsequence, still denoted $u_{n_k}$) $u_{n_k}\to u$ **strongly** in $L^2(\Omega)$.

Fix $\psi\in(L^\infty(\Omega))^d$. Then $u_{n_k}\psi\to u\psi$ strongly in $(L^2(\Omega))^d$, because
$$
\|u_{n_k}\psi-u\psi\|_{L^2}=\|(u_{n_k}-u)\psi\|_{L^2}\le\|\psi\|_{L^\infty}\,\|u_{n_k}-u\|_{L^2}\to 0 .
$$
Now write the quantity as a pairing in the Hilbert space $(L^2)^d$ (self-dual):
$$
\int_\Omega u_{n_k}\nabla u_{n_k}\cdot\psi\,dx=\int_\Omega \nabla u_{n_k}\cdot(u_{n_k}\psi)\,dx=\big\langle\,\nabla u_{n_k}\,,\,u_{n_k}\psi\,\big\rangle_{(L^2)^d}.
$$
This pairs the weakly convergent $\nabla u_{n_k}\rightharpoonup\nabla u$ against the strongly convergent $u_{n_k}\psi\to u\psi$, so by part (a),
$$
\int_\Omega u_{n_k}\nabla u_{n_k}\cdot\psi\,dx\ \longrightarrow\ \int_\Omega \nabla u\cdot(u\psi)\,dx=\int_\Omega u\,\nabla u\cdot\psi\,dx. \qquad\checkmark
$$

### Part (c): the div–curl lemma

Assume $f_n\rightharpoonup f$ weakly in $H^1(\Omega)$, $\mathbf v_n\rightharpoonup\mathbf v$ weakly in $(L^2(\Omega))^d$, and $\nabla\cdot\mathbf v_n$ converges strongly in $H^{-1}(\Omega)$. First identify the strong limit: $\mathbf v_n\rightharpoonup\mathbf v$ implies $\nabla\cdot\mathbf v_n\rightharpoonup\nabla\cdot\mathbf v$ in $H^{-1}$ (divergence is bounded $(L^2)^d\to H^{-1}$, weak–weak continuous), and a strong limit equals the weak limit, so
$$
\nabla\cdot\mathbf v_n\ \longrightarrow\ \nabla\cdot\mathbf v\quad\text{strongly in }H^{-1}(\Omega).
$$
Also, since $f_n\rightharpoonup f$ in $H^1$ (bounded), Rellich gives $f_n\to f$ strongly in $L^2(\Omega)$ (the whole sequence, since every subsequence has a sub-subsequence converging strongly to the weak limit $f$).

Fix $\varphi\in C_0^\infty(\Omega)$. Using the Leibniz rule $\nabla(f_n\varphi)=\varphi\,\nabla f_n+f_n\,\nabla\varphi$, i.e. $\varphi\,\nabla f_n=\nabla(f_n\varphi)-f_n\,\nabla\varphi$,
$$
\int_\Omega \mathbf v_n\cdot\nabla f_n\,\varphi\,dx=\underbrace{\int_\Omega \mathbf v_n\cdot\nabla(f_n\varphi)\,dx}_{(\mathrm I)}-\underbrace{\int_\Omega \mathbf v_n\cdot(f_n\nabla\varphi)\,dx}_{(\mathrm{II})} .
$$

**Term (II).** Since $f_n\to f$ strongly in $L^2$ and $\nabla\varphi\in (C_0^\infty)^d\subset (L^\infty)^d$, we have $f_n\nabla\varphi\to f\nabla\varphi$ strongly in $(L^2)^d$. Pairing against the weakly convergent $\mathbf v_n\rightharpoonup\mathbf v$, part (a) gives
$$
(\mathrm{II})=\big\langle\mathbf v_n,\,f_n\nabla\varphi\big\rangle_{(L^2)^d}\ \longrightarrow\ \int_\Omega \mathbf v\cdot(f\nabla\varphi)\,dx .
$$

**Term (I).** Since $\varphi$ has compact support and $f_n\in H^1$, the product $f_n\varphi\in H^1_0(\Omega)$, and integration by parts gives
$$
(\mathrm I)=\int_\Omega \mathbf v_n\cdot\nabla(f_n\varphi)\,dx=-\big\langle\,\nabla\cdot\mathbf v_n,\ f_n\varphi\,\big\rangle_{H^{-1},\,H^1_0}.
$$
Now $f_n\varphi\rightharpoonup f\varphi$ weakly in $H^1_0$ (multiplication by $\varphi\in C_0^\infty$ is a bounded operator $H^1\to H^1_0$, hence weak–weak continuous), while $\nabla\cdot\mathbf v_n\to\nabla\cdot\mathbf v$ strongly in $H^{-1}=(H^1_0)^*$. Applying part (a) with $X=H^1_0$, $X^*=H^{-1}$,
$$
\big\langle\nabla\cdot\mathbf v_n,\ f_n\varphi\big\rangle\ \longrightarrow\ \big\langle\nabla\cdot\mathbf v,\ f\varphi\big\rangle,\qquad\text{so}\qquad (\mathrm I)\ \longrightarrow\ -\big\langle\nabla\cdot\mathbf v,\ f\varphi\big\rangle=\int_\Omega \mathbf v\cdot\nabla(f\varphi)\,dx .
$$

**Combine.** Therefore
$$
\int_\Omega \mathbf v_n\cdot\nabla f_n\,\varphi\,dx\ \longrightarrow\ \int_\Omega \mathbf v\cdot\nabla(f\varphi)\,dx-\int_\Omega \mathbf v\cdot(f\nabla\varphi)\,dx=\int_\Omega \mathbf v\cdot\big[\nabla(f\varphi)-f\nabla\varphi\big]\,dx,
$$
and $\nabla(f\varphi)-f\nabla\varphi=\varphi\,\nabla f$, so the limit is
$$
\int_\Omega \mathbf v\cdot\nabla f\,\varphi\,dx. \qquad\blacksquare
$$

### Remark — compensated compactness

These three parts are a graded tour of **compensated compactness**, the theory of which nonlinear (bilinear) quantities are continuous under weak convergence. The master principle (a) is that the duality pairing is *separately* continuous when one variable converges strongly. Part (b) is the easy case where one factor is genuinely compact ($H^1\hookrightarrow\hookrightarrow L^2$ supplies a strong factor for free). Part (c) is the **div–curl lemma** of Murat–Tartar: the product $\mathbf v_n\cdot\nabla f_n$ of two merely-weakly-convergent $L^2$ fields *does* converge in the sense of distributions, provided the divergence of one and the curl of the other (here $\nabla f_n$ is curl-free, being a gradient) are controlled — precisely the structural compensation that integration by parts exposes as two weak×strong pairings. This lemma is the analytic engine behind passing to the limit in nonlinear PDEs (homogenization, conservation laws, compensated-compactness existence proofs), where one must justify exactly such products of weak limits.
