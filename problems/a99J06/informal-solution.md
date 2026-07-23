<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J06: Existence of a holomorphic logarithm on a simply connected domain

## Why It's Hard

The conclusion $f = e^{g}$ says exactly that $g$ is a holomorphic **logarithm** of $f$, so the obvious move is to "just take $g=\log f$." That move is illegitimate: the complex logarithm has **no global single-valued holomorphic branch** on $\mathbb{C}\setminus\{0\}$. Following $\log$ continuously around a loop encircling the origin returns you shifted by $2\pi i$ — the *monodromy* of the logarithm. Since $f$ is merely nonvanishing, its image can wind around $0$, and there is no a priori reason a branch of $\log f$ can be selected holomorphically and consistently across all of $\Omega$.

So the real content is **topological**: the only obstruction to building a global logarithm is the possibility of nontrivial loops, and *simple connectivity is precisely the hypothesis that kills that obstruction.* The difficulty is recognizing that one should not attempt to construct $\log f$ directly at all — the values are the wrong object to chase. The right object is the **derivative** a logarithm would have to possess, which is single-valued and free of all branch ambiguity. The entire subtlety of multivaluedness then collapses into one clean theorem: *holomorphic functions have primitives on simply connected domains.*

## The Key Insight

If $f=e^{g}$ held, then differentiating forces
$$g'=\frac{f'}{f},$$
the **logarithmic derivative** of $f$. This expression is honestly holomorphic and single-valued on $\Omega$ (numerator and denominator are holomorphic and $f$ never vanishes) — it carries none of the multivaluedness of $\log$ itself. So instead of constructing $g$ from values, construct it from its derivative: let $g_0$ be a **primitive** of $f'/f$, which exists because $\Omega$ is simply connected. Then verify $f e^{-g_0}$ is constant (its derivative is identically $0$), and absorb that nonzero constant into an additive shift of $g_0$. The multivalued logarithm is never invoked; it is replaced wholesale by "antiderivatives exist."

## Complete Proof

Let $\Omega\subset\mathbb{C}$ be open, simply connected, and nonempty (in particular connected), and let $f:\Omega\to\mathbb{C}$ be holomorphic with $f(z)\ne 0$ for all $z\in\Omega$. Fix a base point $z_0\in\Omega$.

### Step 1 — The logarithmic derivative is holomorphic

Since $f$ is holomorphic, so is $f'$; and since $f$ has no zeros in $\Omega$, the quotient
$$
\varphi := \frac{f'}{f}
$$
is holomorphic on $\Omega$ (a ratio of holomorphic functions with nonvanishing denominator). No branch choices are involved: $\varphi$ is a genuine, single-valued holomorphic function.

### Step 2 — Simple connectivity gives a primitive

**Claim.** Every holomorphic function on a simply connected open set $\Omega$ has a holomorphic primitive.

*Justification.* Define
$$
g_0(z):=\int_{\gamma_z}\varphi(\zeta)\,d\zeta,
$$
where $\gamma_z$ is any path in $\Omega$ from $z_0$ to $z$. This is **well-defined (path-independent)**: if $\gamma,\tilde\gamma$ are two such paths, then $\gamma$ followed by $\tilde\gamma$ reversed is a closed loop in $\Omega$, and by the **Cauchy theorem for simply connected domains** the integral of the holomorphic $\varphi$ around any closed loop vanishes, so the two path-integrals agree. To see $g_0$ is holomorphic with $g_0'=\varphi$: for $z$ and nearby $w$, choosing the straight segment from $z$ to $w$,
$$
\frac{g_0(w)-g_0(z)}{w-z}=\frac{1}{w-z}\int_{[z,w]}\varphi(\zeta)\,d\zeta\;\xrightarrow[w\to z]{}\;\varphi(z),
$$
because $\varphi$ is continuous (the average of $\varphi$ over a shrinking segment tends to $\varphi(z)$). Hence $g_0$ is complex-differentiable with $g_0'=\varphi$, proving the claim.

Applying this to $\varphi=f'/f$, we obtain a holomorphic $g_0:\Omega\to\mathbb{C}$ with
$$
g_0' = \frac{f'}{f}\qquad\text{on }\Omega. \tag{1}
$$

### Step 3 — $f\,e^{-g_0}$ is a nonzero constant

Consider the holomorphic function $\phi(z):=f(z)\,e^{-g_0(z)}$. By the product and chain rules together with $(1)$,
$$
\phi'(z)=f'(z)e^{-g_0(z)} + f(z)\big(-g_0'(z)\big)e^{-g_0(z)}
= e^{-g_0(z)}\Big(f'(z) - f(z)\cdot\tfrac{f'(z)}{f(z)}\Big)
= e^{-g_0(z)}\big(f'-f'\big)=0.
$$
Since $\Omega$ is connected and $\phi'\equiv 0$, the function $\phi$ is **constant**: $\phi\equiv c$ for some $c\in\mathbb{C}$. Moreover $c\ne 0$, because $\phi=f\,e^{-g_0}$ is a product of two nowhere-zero functions ($f$ is nonvanishing by hypothesis and the exponential is never $0$). Evaluating at the base point, $c=\phi(z_0)=f(z_0)e^{-g_0(z_0)}$.

### Step 4 — Absorb the constant

Since $c\ne 0$, choose any complex number $k$ with $e^{k}=c$ (every nonzero complex number is an exponential — pick $k=\ln|c|+i\arg c$ for any choice of argument). From $f\,e^{-g_0}=c=e^{k}$ we get, for every $z\in\Omega$,
$$
f(z)=c\,e^{g_0(z)}=e^{k}\,e^{g_0(z)}=e^{\,g_0(z)+k}.
$$
Define
$$
\boxed{\,g(z):=g_0(z)+k.\,}
$$
Then $g$ is holomorphic on $\Omega$ (a holomorphic function plus a constant) and satisfies
$$
f(z)=\exp\{g(z)\}\qquad\text{for every } z\in\Omega. \qquad\blacksquare
$$

### Remark — what each hypothesis does, and what $g$ is

The proof uses **nonvanishing of $f$** twice — to make $f'/f$ holomorphic (Step 1) and to make the constant $c$ nonzero (Step 3) — and uses **simple connectivity** exactly once, but decisively, to produce the primitive in Step 2. That single use is irreplaceable: on the punctured plane $\Omega=\mathbb{C}\setminus\{0\}$ (open and connected but *not* simply connected), the nonvanishing holomorphic function $f(z)=z$ has $f'/f=1/z$, whose loop integral around $0$ is $2\pi i\ne 0$ — so no primitive exists and there is no global holomorphic logarithm of $z$. The function $g$ produced here is a **holomorphic branch of $\log f$**; it is unique up to adding an integer multiple of $2\pi i$, corresponding to the freedom in choosing $k$ in Step 4.
