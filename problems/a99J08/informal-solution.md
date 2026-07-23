<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J08: A $\sqrt{z}$ corner bound — $|g(z)|\le C|z|^{1/2}$ on the half-disk from mixed boundary data

*(Reading the domain: "$D=\{|z|<1\}$ and $\Im(z)=y>0$" specifies the **open upper half-disk** $D=\{z:|z|<1,\ \Im z>0\}$. Its boundary is the diameter $(-1,1)$ together with the upper semicircle, and the conditions $\Re g=0$ on $(0,1)$, $\Im g=0$ on $(-1,0)$ are boundary data on the two halves of the diameter, meeting at the corner $z=0$.)*

## Why It's Hard

The two boundary conditions are of **different types** — the real part is pinned on the positive radius, the imaginary part on the negative radius — and they collide at the corner $z=0$. Mixed boundary data at a corner is exactly the situation that produces fractional-power (branch-point) behavior, and the target exponent $\tfrac12$ is the tell: it says $g$ behaves like $\sqrt z$ near $0$. The difficulty is that $g$ is *not* holomorphic across the diameter (the data lives on the boundary of the half-disk, not an interior chord), so you cannot just expand $g$ in a power series at $0$. Estimating $|g|$ directly from two real-linear conditions is awkward. The unlock is to find a single holomorphic quantity that **merges** the two conditions into one symmetric condition the Schwarz reflection principle can act on — and the natural candidate is $g^2$, because squaring turns "purely imaginary" and "purely real" both into "real."

## The Key Insight

**Square $g$.** On the positive radius $g$ is purely imaginary, so $g^2$ is real (indeed $\le 0$); on the negative radius $g$ is purely real, so $g^2$ is real ($\ge 0$). Hence
$$\Im\big(g(x)^2\big)=0 \quad\text{for all } x\in(-1,1),$$
a *single* condition on the *entire* diameter. Now $H:=g^2$ is holomorphic on the upper half-disk, continuous up to the diameter, and **real** there — exactly the hypotheses of the **Schwarz reflection principle**, which extends $H$ to a function holomorphic on the *full* disk $\{|z|<1\}$. In particular $H$ is analytic at the corner $0$.

Continuity forces $g(0)=0$ (approaching along the positive radius makes $g(0)$ imaginary; along the negative radius makes it real), so $H(0)=g(0)^2=0$. An analytic function vanishing at $0$ satisfies $|H(z)|\le M|z|$ near $0$; therefore
$$|g(z)|^2=|H(z)|\le M|z| \quad\Longrightarrow\quad |g(z)|\le \sqrt M\,|z|^{1/2}.$$
The square root is what converts $H$'s honest first-order zero into $g$'s half-order rate — the $\tfrac12$ is intrinsic, not slack.

## Complete Proof

Let $D=\{z:|z|<1,\ \Im z>0\}$, with $g:\bar D\to\mathbb{C}$ continuous and holomorphic on $D$, satisfying $\Re g=0$ on $(0,1)$ and $\Im g=0$ on $(-1,0)$.

**Step 1: $g(0)=0$.** Both radii lie in $\bar D$ and $g$ is continuous there. Letting $x\to 0^+$ along $(0,1)$: $\Re g(x)=0$ for all such $x$, so $\Re g(0)=\lim_{x\to0^+}\Re g(x)=0$. Letting $x\to0^-$ along $(-1,0)$: $\Im g(x)=0$, so $\Im g(0)=0$. Thus $g(0)$ is both purely imaginary and purely real, whence $g(0)=0$.

**Step 2: $H:=g^2$ is real on the diameter.** For $x\in(0,1)$, $\Re g(x)=0$ means $g(x)=i\beta$ with $\beta\in\mathbb{R}$, so $H(x)=g(x)^2=-\beta^2\in\mathbb{R}$. For $x\in(-1,0)$, $\Im g(x)=0$ means $g(x)=\alpha\in\mathbb{R}$, so $H(x)=\alpha^2\in\mathbb{R}$. And $H(0)=0\in\mathbb{R}$. Hence $\Im H(x)=0$ for every $x\in(-1,1)$. Moreover $H=g^2$ is holomorphic on $D$ and continuous on $\bar D$.

**Step 3: Schwarz reflection extends $H$ to the full disk.** $H$ is holomorphic on the upper half-disk, continuous up to the open segment $(-1,1)$, and real-valued there. By the **Schwarz reflection principle**, the formula
$$\widetilde H(z)=\begin{cases} H(z), & \Im z\ge 0,\ |z|<1,\\[2pt] \overline{H(\bar z)}, & \Im z<0,\ |z|<1,\end{cases}$$
defines a single holomorphic function on the whole disk $\{|z|<1\}$ agreeing with $H$ on $\bar D$. (The two pieces match continuously on $(-1,1)$ because $H$ is real there, and Morera/the reflection theorem upgrade the match to holomorphy across the segment.) In particular $\widetilde H$ is analytic in a neighborhood of the corner $z=0$.

**Step 4: rate at the corner.** By Step 1, $\widetilde H(0)=H(0)=g(0)^2=0$. An analytic function vanishing at $0$ has a power series $\widetilde H(z)=\sum_{k\ge1}c_k z^k=z\sum_{k\ge1}c_k z^{k-1}$, so $\widetilde H(z)/z$ is analytic near $0$ and hence bounded: there are $M<\infty$ and $r\in(0,1)$ with
$$|H(z)|=|\widetilde H(z)|\le M|z|\qquad (|z|\le r).$$
Therefore, for $z\in\bar D$ with $0<|z|\le r$,
$$\frac{|g(z)|}{|z|^{1/2}}=\frac{|H(z)|^{1/2}}{|z|^{1/2}}\le \frac{(M|z|)^{1/2}}{|z|^{1/2}}=\sqrt M,$$
using $|g(z)|^2=|g(z)^2|=|H(z)|$.

**Step 5: away from the corner (compactness).** On $K=\{z\in\bar D:|z|\ge r\}$, which is compact, $g$ is continuous, so $|g|\le \|g\|_{\infty,\bar D}<\infty$, while $|z|^{1/2}\ge r^{1/2}>0$. Hence
$$\frac{|g(z)|}{|z|^{1/2}}\le \frac{\|g\|_{\infty,\bar D}}{r^{1/2}}\qquad (z\in K).$$

**Conclusion.** Combining Steps 4 and 5, for all $z\in\bar D\setminus\{0\}$,
$$\frac{|g(z)|}{|z|^{1/2}}\le \max\!\left(\sqrt M,\ \frac{\|g\|_{\infty,\bar D}}{r^{1/2}}\right)<\infty,$$
so $z\mapsto |g(z)|/|z|^{1/2}$ is bounded on $\bar D$ (its limit at $0$ is in fact $\le\sqrt M$, so it extends boundedly across $0$). $\qquad\blacksquare$

**Sharpness.** The exponent $\tfrac12$ cannot be improved. Take $g(z)=i\,z^{1/2}$ with the principal branch (well-defined and holomorphic on the upper half-disk, continuous up to $\bar D$). Writing $z=re^{i\theta}$, $\theta\in[0,\pi]$: on the positive radius ($\theta=0$) $g=i\sqrt r$ is purely imaginary ($\Re g=0$ ✓); on the negative radius ($\theta=\pi$) $g=i\cdot i\sqrt r=-\sqrt r$ is purely real ($\Im g=0$ ✓). Here $|g(z)|/|z|^{1/2}\equiv 1$, so the ratio is bounded but does **not** tend to $0$ — the half-power is exactly the right scale.

## What Connects

**Within complex analysis.** This is a model case of **corner/edge regularity under mixed (Dirichlet–Neumann-type) boundary conditions**: where two boundary conditions of different type meet, solutions of elliptic problems acquire fractional-power singularities, and the exponent is set by the corner angle and the boundary-condition pattern (here, a $\pi$-angle straight edge with a real/imaginary switch gives exponent $\tfrac12$). The technique — **reflect to remove the boundary** — is the Schwarz reflection principle, the holomorphic analogue of even/odd extension for harmonic functions; the trick of taking $g^2$ to symmetrize incompatible boundary data is the same device used to linearize free-boundary and Signorini-type conditions. It also rhymes with a99A03/a98J02 in this set: the recurring move is to find the *right* auxiliary object (there $f'$ via FTC; here $g^2$) on which a clean structural theorem (FTC + Cauchy–Schwarz; Schwarz reflection) does the heavy lifting, after which the desired estimate falls out by reading off a single vanishing order.
