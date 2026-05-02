
**Why it's hard:** The integrand depends on z both via p(z) and via the denominator ζ - z, and at z = ζ the factor (p(ζ) - p(z))/(ζ - z) appears to be 0/0. We need to check that this is a genuine polynomial in z (not just a rational function), and then verify the interpolation property at the n given nodes via residue theory.

**The key insight:** The expression (p(ζ) - p(z))/(ζ - z) is the *divided difference quotient* — it's a polynomial in z (and ζ) of degree n-1 in z, because p(ζ) - p(z) vanishes when z = ζ, so (ζ - z) divides it as polynomials. When we integrate over ζ, the result is a polynomial in z of degree at most n - 1. Setting z = z_k makes p(z_k) = 0, so the integrand simplifies and the residue theorem gives P(z_k) = f(z_k).

**Proof:**

**Step 1: Algebraic reduction.**

Write p(ζ) - p(z) as a polynomial in two variables. Since p(z) = ∏(z - z_k):
$$p(\zeta) - p(z) = \zeta^n + a_{n-1}\zeta^{n-1} + \cdots - z^n - a_{n-1}z^{n-1} - \cdots = \sum_{j=0}^{n} a_j(\zeta^j - z^j)$$
where a_n = 1 and a_0, ..., a_{n-1} are the elementary symmetric functions of the z_k (up to sign). Each ζ^j - z^j factors as (ζ - z)(ζ^{j-1} + ζ^{j-2}z + ... + z^{j-1}). Therefore:
$$\frac{p(\zeta) - p(z)}{\zeta - z} = \sum_{j=1}^{n} a_j \sum_{i=0}^{j-1} \zeta^{j-1-i} z^i = \sum_{i=0}^{n-1} q_i(\zeta) z^i$$
where each q_i(ζ) = ∑_{j=i+1}^{n} a_j ζ^{j-1-i} is a polynomial in ζ. So:
$$Q(\zeta, z) := \frac{p(\zeta) - p(z)}{\zeta - z} = \sum_{i=0}^{n-1} q_i(\zeta) \cdot z^i$$
is a polynomial of degree exactly n - 1 in z (the leading coefficient is q_{n-1}(ζ) = 1, since a_n = 1).

**Step 2: P is a polynomial of degree n - 1 in z.**

Substituting into the definition of P:
$$P(z) = \frac{1}{2\pi i}\int_\gamma \frac{f(\zeta)}{p(\zeta)} \sum_{i=0}^{n-1} q_i(\zeta) z^i \,d\zeta = \sum_{i=0}^{n-1} \left(\frac{1}{2\pi i}\int_\gamma \frac{f(\zeta)\, q_i(\zeta)}{p(\zeta)}\,d\zeta\right) z^i$$

Each coefficient
$$c_i := \frac{1}{2\pi i}\int_\gamma \frac{f(\zeta)\, q_i(\zeta)}{p(\zeta)}\,d\zeta$$
is a constant (a complex number), since it's an integral over the fixed contour γ. So P(z) = c_0 + c_1 z + ... + c_{n-1}z^{n-1} is a polynomial of degree at most n - 1.

To see the degree is exactly n - 1, note c_{n-1} = (1/(2πi)) ∫_γ f(ζ)/p(ζ) dζ. By the residue theorem, since z_1, ..., z_n are simple poles of f(ζ)/p(ζ) inside γ:
$$c_{n-1} = \sum_{k=1}^n \text{Res}_{\zeta = z_k}\left(\frac{f(\zeta)}{p(\zeta)}\right) = \sum_{k=1}^n \frac{f(z_k)}{p'(z_k)}$$

This is generically nonzero. (If c_{n-1} happens to vanish, the degree is strictly less than n-1; the problem statement implicitly assumes generic data, or "degree n-1" means "of polynomial type up to degree n-1.")

**Step 3: Interpolation property P(z_k) = f(z_k).**

Fix k ∈ {1, ..., n}. Since p(z_k) = 0:
$$P(z_k) = \frac{1}{2\pi i}\int_\gamma \frac{f(\zeta)}{p(\zeta)} \cdot \frac{p(\zeta) - 0}{\zeta - z_k}\,d\zeta = \frac{1}{2\pi i}\int_\gamma \frac{f(\zeta)}{\zeta - z_k}\,d\zeta$$

By Cauchy's integral formula (since z_k is inside γ and f is analytic on and inside γ):
$$P(z_k) = f(z_k)$$

This holds for every k = 1, ..., n. ∎

**What connects:** P is the **Hermite/Lagrange interpolating polynomial** of f at the nodes z_1, ..., z_n, written via a contour-integral formula due to Hermite. The Lagrange form $\sum_k f(z_k) \prod_{j \neq k} (z - z_j)/(z_k - z_j)$ can be derived from this by computing residues: P(z) = ∑_k Res_{ζ = z_k}((f(ζ)/p(ζ)) · (p(ζ) - p(z))/(ζ - z)) = ∑_k f(z_k) · (p(z_k) - p(z))/((z_k - z) · p'(z_k)) = ∑_k f(z_k) (p(z) - 0)/((z - z_k) p'(z_k)) (using p(z_k) = 0), which is exactly the Lagrange form once we recognize p(z)/((z - z_k) p'(z_k)) = ∏_{j ≠ k} (z - z_j)/(z_k - z_j). The contour integral form generalizes naturally to Hermite interpolation with multiplicities (replace simple zeros of p by higher-order zeros) and to the Cauchy-Hermite formula in approximation theory.

