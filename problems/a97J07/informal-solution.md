<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J07: Geometric-mean bound at the disk center via reflection + maximum modulus

## Why It's Hard

The value $f(0)$ is an **interior** value, while the hypotheses bound $|f|$ only on the **boundary** circle — and the two boundary bounds are **asymmetric**: $a$ on the upper semicircle, $b$ on the lower. The maximum modulus principle applied to $f$ directly gives only

$$|f(0)| \leq \max_{|z|=1} |f(z)| \leq \max(a, b),$$

which is weaker than the claimed geometric mean $\sqrt{ab}$ (and equals it only when $a = b$). To get the geometric mean you must combine the two arcs **multiplicatively**, so that every boundary point feels *both* constants at once rather than just the larger one. The hint — consider $f(z)$ together with $f(-z)$ — is the whole trick: reflection through the origin swaps the upper and lower semicircles.

## The Key Insight

Form the symmetrized product

$$g(z) = f(z)\, f(-z).$$

Reflection $z \mapsto -z$ maps the unit circle to itself and **swaps** the upper and lower semicircles. So for any boundary point $z$, the antipodal pair $\{z, -z\}$ has one point in the (closed) upper arc — where $|f| \leq a$ — and one in the (closed) lower arc — where $|f| \leq b$. Hence

$$|g(z)| = |f(z)|\,|f(-z)| \leq ab \qquad \text{for all } |z| = 1,$$

*uniformly*, with no leftover $\max(a,b)$. Now $g$ is continuous on the closed disk and analytic inside, so maximum modulus pushes this boundary bound to the center: $|g(0)| \leq ab$. Finally $g(0) = f(0)f(-0) = f(0)^{2}$, so $|f(0)|^{2} \leq ab$. The square is exactly what turns the product bound $ab$ into the geometric mean $\sqrt{ab}$.

## Complete Proof

**The auxiliary function.** Define $g : \overline{\Delta} \to \mathbb{C}$ by $g(z) = f(z) f(-z)$. Since the closed disk is symmetric under $z \mapsto -z$, the map $z \mapsto f(-z)$ is continuous on $\overline{\Delta}$ and analytic on $\Delta$ (it is $f$ precomposed with the analytic automorphism $z \mapsto -z$, which sends $\Delta$ to $\Delta$ and $\overline{\Delta}$ to $\overline{\Delta}$). A product of two such functions is again continuous on $\overline{\Delta}$ and analytic on $\Delta$. So **$g$ is continuous on $\overline{\Delta}$ and analytic on $\Delta$**.

**Extending the boundary bounds to the closed arcs.** By hypothesis $|f(z)| \leq a$ on the open upper arc $\{|z| = 1, \operatorname{Im} z > 0\}$ and $|f(z)| \leq b$ on the open lower arc $\{|z| = 1, \operatorname{Im} z < 0\}$. Because $f$ is continuous on $\overline{\Delta}$, these inequalities pass to the closures of the arcs: taking limits along the upper arc gives

$$|f(z)| \leq a \quad \text{on} \quad \Gamma_+ = \{|z| = 1,\ \operatorname{Im} z \geq 0\},$$

and likewise

$$|f(z)| \leq b \quad \text{on} \quad \Gamma_- = \{|z| = 1,\ \operatorname{Im} z \leq 0\}.$$

(The two real boundary points $z = \pm 1$ lie in both closed arcs, so there both $|f| \leq a$ and $|f| \leq b$ hold — consistent, and harmless below.)

**Bounding $g$ on the whole circle.** Fix any $z$ with $|z| = 1$; then $|-z| = 1$ and $\operatorname{Im}(-z) = -\operatorname{Im}(z)$.

- If $\operatorname{Im} z \geq 0$, then $z \in \Gamma_{+}$ so $|f(z)| \leq a$, while $-z \in \Gamma_{-}$ so $|f(-z)| \leq b$.
- If $\operatorname{Im} z \leq 0$, then $z \in \Gamma_{-}$ so $|f(z)| \leq b$, while $-z \in \Gamma_{+}$ so $|f(-z)| \leq a$.

In either case

$$|g(z)| = |f(z)|\,|f(-z)| \leq ab. \tag{$\ast$}$$

So ($\ast$) holds for **every** point of the boundary circle $\partial\Delta = \{|z| = 1\}$.

**Maximum modulus.** $g$ is continuous on the compact set $\overline{\Delta}$ and analytic on its interior $\Delta$. By the maximum modulus principle, the maximum of $|g|$ over $\overline{\Delta}$ is attained on the boundary $\partial\Delta$. In particular, for the interior point 0,

$$|g(0)| \leq \max_{|z| = 1} |g(z)| \leq ab,$$

the last inequality by ($\ast$).

**Conclusion.** Evaluate $g$ at the center:

$$g(0) = f(0)\, f(-0) = f(0)\, f(0) = f(0)^2,$$

so $|f(0)|^{2} = |g(0)| \leq ab$. Taking nonnegative square roots,

$$|f(0)| \leq (ab)^{1/2}. \qquad \blacksquare$$

## What Connects

**Within analysis**: This is the disk version of the **two-constants theorem** / a baby **Phragmén–Lindelöf**: a multiplicatively-combined bound on a boundary split into pieces yields a geometric-mean bound at an interior point. The appearance of $\sqrt{ab}$ is the fingerprint of a logarithmic/multiplicative interpolation ($\log|f|$ is subharmonic), and the squaring $g(0) = f(0)^{2}$ is what realizes the exponent $\tfrac{1}{2}$.

**The reusable trick**: symmetrizing an asymmetric boundary condition by multiplying $f$ by a transported copy (here $f(-z)$; elsewhere $\overline{f(\bar{z})}$ or $\overline{f(1/\bar{z})}$, or rotations) so that maximum modulus "sees" all the boundary data at once. The same device proves Hadamard's three-lines and three-circles theorems.
