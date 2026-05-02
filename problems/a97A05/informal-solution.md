
**Why it's hard:** The hypothesis is one-sided (Re(f) bounded above and below) but f itself need not be bounded — Im(f) can be arbitrarily large. We need to manufacture two bounded analytic functions whose ratio is f, and there's no obvious choice without exploiting a conformal map of a half-plane to a disk.

**The key insight:** Shift f horizontally so that Re(f) lies in the right half-plane {Re(w) > 0}, then apply the Cayley-type Möbius transformation w ↦ (w - 1)/(w + 1), which maps the right half-plane onto the open unit disk. This produces a bounded analytic function φ ∘ f on H, and inverting the relation gives f as a ratio of two bounded analytic functions.

**Proof:**

By hypothesis, there exists M > 0 such that |Re(f(z))| ≤ M for all z ∈ H. Set f₁(z) = f(z) + (M + 1). Then Re(f₁(z)) = Re(f(z)) + M + 1 ≥ -M + M + 1 = 1 > 0 for all z ∈ H, so f₁ maps H into the right half-plane R = {w ∈ ℂ : Re(w) > 0}. Note f₁ is analytic on H (translate of f).

Consider the Möbius transformation φ(w) = (w - 1)/(w + 1), which maps R onto the open unit disk Δ = {|ζ| < 1}. (Standard: |w - 1|² = |w|² - 2Re(w) + 1 < |w|² + 2Re(w) + 1 = |w + 1|² when Re(w) > 0.) Since Re(f₁(z)) ≥ 1 > 0, the denominator f₁(z) + 1 never vanishes on H, so

$$\psi(z) := \varphi(f_1(z)) = \frac{f_1(z) - 1}{f_1(z) + 1}$$

is analytic on H, and |ψ(z)| < 1 for all z ∈ H. So ψ is analytic and bounded on H.

Now solve for f. From ψ = (f₁ - 1)/(f₁ + 1):
$$\psi(f_1 + 1) = f_1 - 1 \implies f_1(\psi - 1) = -\psi - 1 \implies f_1 = \frac{1 + \psi}{1 - \psi}$$

(The denominator 1 - ψ is nonzero since |ψ| < 1.) Therefore:
$$f = f_1 - (M + 1) = \frac{1 + \psi}{1 - \psi} - (M + 1) = \frac{(1 + \psi) - (M+1)(1 - \psi)}{1 - \psi} = \frac{(M + 2)\psi - M}{1 - \psi}$$

Define:
- g(z) = (M + 2)ψ(z) - M
- h(z) = 1 - ψ(z)

Both g and h are analytic on H (linear combinations of ψ and constants).

**Boundedness of g:** |g(z)| = |(M+2)ψ(z) - M| ≤ (M+2)|ψ(z)| + M < (M+2) + M = 2M + 2.

**Boundedness of h:** |h(z)| = |1 - ψ(z)| ≤ 1 + |ψ(z)| < 2.

So both g and h are bounded analytic functions on H, and f(z) = g(z)/h(z). ∎

**What connects:** This is the standard one-sided-bound trick in complex analysis: a one-sided bound on Re(f) (or on log|f|, etc.) is upgraded to a two-sided bound on a Möbius-transformed quantity, producing membership in a "nice" function class. The same construction shows that any analytic function on H with positive real part is the Cayley pullback of a Schur function (analytic and bounded by 1 on Δ via the conformal map between H and Δ), which underlies the Herglotz-Riesz integral representation of analytic functions with positive real part. The decomposition f = g/h with g, h ∈ H^∞(H) is a baby case of the inner-outer factorization in the theory of the Hardy space H^p.

