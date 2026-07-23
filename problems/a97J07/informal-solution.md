<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J07: Geometric-mean bound at the disk center via reflection + maximum modulus

## Why It's Hard

The value f(0) is an **interior** value, while the hypotheses bound |f| only on the **boundary** circle — and the two boundary bounds are **asymmetric**: a on the upper semicircle, b on the lower. The maximum modulus principle applied to f directly gives only

$$|f(0)| \leq \max_{|z|=1} |f(z)| \leq \max(a, b),$$

which is weaker than the claimed geometric mean √(ab) (and equals it only when a = b). To get the geometric mean you must combine the two arcs **multiplicatively**, so that every boundary point feels *both* constants at once rather than just the larger one. The hint — consider f(z) together with f(−z) — is the whole trick: reflection through the origin swaps the upper and lower semicircles.

## The Key Insight

Form the symmetrized product

$$g(z) = f(z)\, f(-z).$$

Reflection z ↦ −z maps the unit circle to itself and **swaps** the upper and lower semicircles. So for any boundary point z, the antipodal pair {z, −z} has one point in the (closed) upper arc — where |f| ≤ a — and one in the (closed) lower arc — where |f| ≤ b. Hence

$$|g(z)| = |f(z)|\,|f(-z)| \leq ab \qquad \text{for all } |z| = 1,$$

*uniformly*, with no leftover max(a,b). Now g is continuous on the closed disk and analytic inside, so maximum modulus pushes this boundary bound to the center: |g(0)| ≤ ab. Finally g(0) = f(0)f(−0) = f(0)², so |f(0)|² ≤ ab. The square is exactly what turns the product bound ab into the geometric mean √(ab).

## Complete Proof

**The auxiliary function.** Define g : Δ̄ → ℂ by g(z) = f(z) f(−z). Since the closed disk is symmetric under z ↦ −z, the map z ↦ f(−z) is continuous on Δ̄ and analytic on Δ (it is f precomposed with the analytic automorphism z ↦ −z, which sends Δ to Δ and Δ̄ to Δ̄). A product of two such functions is again continuous on Δ̄ and analytic on Δ. So **g is continuous on Δ̄ and analytic on Δ**.

**Extending the boundary bounds to the closed arcs.** By hypothesis |f(z)| ≤ a on the open upper arc {|z| = 1, Im z > 0} and |f(z)| ≤ b on the open lower arc {|z| = 1, Im z < 0}. Because f is continuous on Δ̄, these inequalities pass to the closures of the arcs: taking limits along the upper arc gives

$$|f(z)| \leq a \quad \text{on} \quad \Gamma_+ = \{|z| = 1,\ \operatorname{Im} z \geq 0\},$$

and likewise

$$|f(z)| \leq b \quad \text{on} \quad \Gamma_- = \{|z| = 1,\ \operatorname{Im} z \leq 0\}.$$

(The two real boundary points z = ±1 lie in both closed arcs, so there both |f| ≤ a and |f| ≤ b hold — consistent, and harmless below.)

**Bounding g on the whole circle.** Fix any z with |z| = 1; then |−z| = 1 and Im(−z) = −Im(z).

- If Im z ≥ 0, then z ∈ Γ₊ so |f(z)| ≤ a, while −z ∈ Γ₋ so |f(−z)| ≤ b.
- If Im z ≤ 0, then z ∈ Γ₋ so |f(z)| ≤ b, while −z ∈ Γ₊ so |f(−z)| ≤ a.

In either case

$$|g(z)| = |f(z)|\,|f(-z)| \leq ab. \tag{$\ast$}$$

So ($\ast$) holds for **every** point of the boundary circle ∂Δ = {|z| = 1}.

**Maximum modulus.** g is continuous on the compact set Δ̄ and analytic on its interior Δ. By the maximum modulus principle, the maximum of |g| over Δ̄ is attained on the boundary ∂Δ. In particular, for the interior point 0,

$$|g(0)| \leq \max_{|z| = 1} |g(z)| \leq ab,$$

the last inequality by ($\ast$).

**Conclusion.** Evaluate g at the center:

$$g(0) = f(0)\, f(-0) = f(0)\, f(0) = f(0)^2,$$

so |f(0)|² = |g(0)| ≤ ab. Taking nonnegative square roots,

$$|f(0)| \leq (ab)^{1/2}. \qquad \blacksquare$$

## What Connects

**Within analysis**: This is the disk version of the **two-constants theorem** / a baby **Phragmén–Lindelöf**: a multiplicatively-combined bound on a boundary split into pieces yields a geometric-mean bound at an interior point. The appearance of √(ab) is the fingerprint of a logarithmic/multiplicative interpolation (log|f| is subharmonic), and the squaring g(0) = f(0)² is what realizes the exponent ½.

**The reusable trick**: symmetrizing an asymmetric boundary condition by multiplying f by a transported copy (here f(−z); elsewhere f(z̄)‾ or f(1/z̄)‾, or rotations) so that maximum modulus "sees" all the boundary data at once. The same device proves Hadamard's three-lines and three-circles theorems.
