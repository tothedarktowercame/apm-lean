
**Why it's hard:** Convergence is a quantifier-heavy statement (∀ε ∃N ∀n,m...), so the convergence set E is built from a countable intersection of countable unions of countable intersections of measurable sets — but we have to verify each layer is measurable. The boundedness hypothesis is what makes pointwise convergence equivalent to the Cauchy criterion (which is what gives a measurable expression).

**The key insight:** A bounded real sequence converges iff it is Cauchy iff limsup = liminf. Both characterizations express E using only countable Boolean operations on sets of the form {x : f_n(x) - f_m(x) < ε} or {x : limsup f_n(x) - liminf f_n(x) < ε}, all of which are measurable because the f_n are measurable and limsup/liminf of measurable functions are measurable.

**Proof:**

Since each f_n is measurable, for any rational ε > 0 and any n, m ∈ ℕ, the set
$$\{x \in X : |f_n(x) - f_m(x)| < \varepsilon\}$$
is in Σ (it's the preimage of (−∞, ε) under the measurable function |f_n - f_m|).

By the Cauchy criterion for convergence in ℝ (which applies because each sequence (f_n(x)) is bounded, hence convergence is equivalent to the Cauchy property — and even without boundedness, convergence in ℝ is equivalent to Cauchy):

$$E = \{x \in X : (f_n(x)) \text{ converges}\} = \bigcap_{k=1}^{\infty} \bigcup_{N=1}^{\infty} \bigcap_{n,m \geq N} \left\{x : |f_n(x) - f_m(x)| < \frac{1}{k}\right\}$$

Each innermost set is in Σ, so the countable intersection over n, m ≥ N is in Σ, the countable union over N is in Σ, and the countable intersection over k is in Σ. Hence E ∈ Σ.

*Alternative via limsup/liminf.* Define
$$g(x) = \limsup_{n \to \infty} f_n(x), \quad h(x) = \liminf_{n \to \infty} f_n(x)$$

Both g and h are measurable (extended-real-valued), since limsup and liminf of countably many measurable functions are measurable:
$$g(x) = \inf_{N} \sup_{n \geq N} f_n(x), \quad h(x) = \sup_N \inf_{n \geq N} f_n(x)$$

For x where (f_n(x)) is bounded (which is all of X by hypothesis), the sequence converges iff g(x) = h(x). So:
$$E = \{x \in X : g(x) = h(x)\} = \{x \in X : g(x) - h(x) = 0\}$$

Since g and h are measurable and pointwise finite (by boundedness), g - h is measurable, and {g - h = 0} is the preimage of the measurable singleton {0}, which is in Σ. ∎

**What connects:** This is one of the foundational results showing that the Borel σ-algebra has enough closure properties to handle the standard analytic operations. The same proof technique shows that the set where a sequence of measurable functions has any specific asymptotic behavior — converges to a fixed value, has a Cesàro mean, oscillates within bounds, etc. — is measurable, as long as the property can be expressed via countable Boolean combinations of measurable sets. This underlies Egorov's theorem (where measurability of the convergence set is crucial) and the proof that pointwise limits of measurable functions are measurable. The boundedness hypothesis is actually unnecessary in ℝ — convergence and Cauchy are equivalent without it — but in ℂ or ℝ^n the same argument works directly via the Cauchy criterion.

