
**Why it's hard:** Direct root-finding for z⁵ + 15z + 1 = 0 is intractable. The classical approach is Rouché's theorem, but choosing the right "dominant" term on each circle (|z| = 2 vs |z| = 3/2) requires a careful comparison of |z⁵| vs |15z + 1|, which crosses over somewhere between these radii.

**The key insight:** On the circle |z| = 2, the term z⁵ dominates (|z⁵| = 32 > |15z + 1| ≤ 31), so f has the same number of roots as z⁵ inside |z| < 2 — that's 5 roots. On the circle |z| = 3/2, the term 15z dominates (|15z| = 22.5 > |z⁵ + 1| ≤ (3/2)⁵ + 1 = 243/32 + 1 ≈ 8.59), so f has the same number of roots as 15z inside |z| < 3/2 — that's 1 root. Subtracting gives 4 roots in the annulus.

**Proof:**

We use Rouché's theorem: if g, h are analytic on a closed disk D̄_r, and |g(z) - h(z)| < |h(z)| (or equivalently |h - g| < |g| + |h|, the "symmetric Rouché") on the boundary |z| = r, then g and h have the same number of zeros inside |z| < r.

**Step 1: Roots inside |z| < 2.**

On |z| = 2: take h(z) = z⁵ and the "perturbation" g(z) - h(z) = 15z + 1.
- |z⁵| = |z|⁵ = 32
- |15z + 1| ≤ 15|z| + 1 = 30 + 1 = 31

Since 31 < 32, the hypothesis of Rouché's theorem is satisfied: |f(z) - z⁵| = |15z + 1| < |z⁵| on |z| = 2. By Rouché, f and z⁵ have the same number of zeros (counted with multiplicity) in |z| < 2. The function z⁵ has a single zero at z = 0 of multiplicity 5, so f has exactly **5 zeros** in |z| < 2.

**Step 2: Roots inside |z| < 3/2.**

On |z| = 3/2: take h(z) = 15z and the "perturbation" g(z) - h(z) = z⁵ + 1.
- |15z| = 15 · 3/2 = 45/2 = 22.5
- |z⁵ + 1| ≤ |z|⁵ + 1 = (3/2)⁵ + 1 = 243/32 + 1 = 275/32 ≈ 8.59

Since 275/32 < 45/2 (equivalently 275 < 720), Rouché applies: |f(z) - 15z| = |z⁵ + 1| < |15z| on |z| = 3/2. So f and 15z have the same number of zeros in |z| < 3/2. The function 15z has a single zero at z = 0 of multiplicity 1, so f has exactly **1 zero** in |z| < 3/2.

**Step 3: Roots in the annulus 3/2 < |z| < 2.**

We must check that f has no zeros on the circle |z| = 3/2 (it doesn't, by the strict inequality in Step 2: if f(z) = 0 then |15z| = |z⁵ + 1|, contradicting |15z| > |z⁵ + 1| on |z| = 3/2).

So the number of roots in the open annulus 3/2 < |z| < 2 equals (roots in |z| < 2) − (roots in |z| ≤ 3/2) = (roots in |z| < 2) − (roots in |z| < 3/2) = 5 − 1 = **4 roots**.

(Strictly, we should verify there are no roots on |z| = 3/2 itself; we just did. Similarly, f has no roots on |z| = 2 by the strict inequality in Step 1.)

**Conclusion:** f has 5 roots in {|z| < 2} and 4 roots in the annulus {3/2 < |z| < 2}. ∎

**What connects:** This is a textbook Rouché problem, and the choice of dominant term encodes a basic principle in perturbation theory: for the polynomial z^n + lower-order terms, on a circle of radius r, the term that dominates is whichever has the largest magnitude at radius r. Here z⁵ wins for r = 2 (we're in the "tail" regime), 15z wins for r = 3/2 (we're in the "linear" regime). The crossover happens roughly where r⁵ = 15r, i.e., r⁴ = 15, r ≈ 1.97 — just below |z| = 2, which is why the inequalities are tight (32 vs 31 — only one unit of slack). This kind of analysis underlies the localization of zeros in numerical algebra and the asymptotic count of zeros in regions for entire functions of finite order.

