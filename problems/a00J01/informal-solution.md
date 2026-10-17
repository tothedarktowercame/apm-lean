# Informal Solution: a00J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Definition.** $\|f\|_\infty = \inf\{M \geq 0 : m(\{x : |f(x)| > M\}) = 0\}$, the essential supremum of $|f|$. Equivalently, the smallest $M$ such that $|f| \leq M$ almost everywhere.

**Claim.** For $f \in L^\infty([0,1])$, $\lim_{p\to\infty} \|f\|_p = \|f\|_\infty$.

**Upper bound: $\limsup \|f\|_p \leq \|f\|_\infty$.**

For a.e. $x$, $|f(x)| \leq \|f\|_\infty$. So $\|f\|_p^p = \int|f|^p \leq \|f\|_\infty^p \cdot m([0,1]) = \|f\|_\infty^p$. Taking $p$-th roots: $\|f\|_p \leq \|f\|_\infty$ for all $p \geq 1$.

(This is routine — finite measure $m([0,1]) = 1$ makes it clean.)

**Lower bound: $\liminf \|f\|_p \geq \|f\|_\infty$.**

Fix $\alpha < \|f\|_\infty$. The set $E_\alpha = \{x : |f(x)| > \alpha\}$ has $m(E_\alpha) > 0$ by definition of ess sup. Then $\|f\|_p^p \geq \int_{E_\alpha} |f|^p \geq \alpha^p \cdot m(E_\alpha)$. Taking $p$-th roots: $\|f\|_p \geq \alpha \cdot m(E_\alpha)^{1/p} \to \alpha$ as $p \to \infty$ (since $m(E_\alpha)^{1/p} \to 1$ for $m(E_\alpha) > 0$).

So $\liminf \|f\|_p \geq \alpha$ for every $\alpha < \|f\|_\infty$, hence $\liminf \|f\|_p \geq \|f\|_\infty$.

(The crux: $E_\alpha$ has POSITIVE measure because $\alpha <$ ess sup, and $t^{1/p} \to 1$ for $t > 0$.)

**Combine.** $\|f\|_\infty \leq \liminf \|f\|_p \leq \limsup \|f\|_p \leq \|f\|_\infty$. ∎

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. **Upper bound** ($\|f\|_p \leq \|f\|_\infty$ on finite measure): `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` in Mathlib gives $\|f\|_p \leq \|f\|_q \cdot \mu(univ)^{1/p-1/q}$. With $q=\top$ and $\mu(univ)=1$ this gives $\|f\|_p \leq \|f\|_\infty$. **Critical path: YES.**
2. **Level set positive measure**: for $\alpha < \|f\|_\infty$, $\mu(\{\|f\| > \alpha\}) > 0$. From the definition of essSup: if $\mu(\{\|f\| > \alpha\}) = 0$ then $\alpha \geq \|f\|_\infty$, contradicting $\alpha < \|f\|_\infty$. **Custom, straightforward.**
3. **$t^{1/p} \to 1$**: For $t > 0$, $t^{1/p} \to 1$ as $p \to \infty$. Mathlib: `ENNReal.rpow_natCast` + `tendsto_rpow_nhds_zero_of_norm_lt_one` or similar. **Fragmented in Mathlib.**
4. **Squeeze theorem**: $\liminf \geq L$ and $\limsup \leq L$ implies limit $= L$. Mathlib: `tendsto_of_tendsto_of_tendsto_of_le_of_le`. **Available.**

**Stage 3 — LEAN FORMALIZATION**

The upper bound should close from a single Mathlib comparison lemma. The lower bound needs the level-set argument with $t^{1/p} \to 1$. See Main.lean.

Status: upper bound closeable; lower bound needs ~10 lines of $\varepsilon$-argument.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The upper bound is genuinely easy — both on paper and in Lean. The Mathlib comparison $\|f\|_p \leq \|f\|_\infty \cdot \mu(univ)^{1/p}$ is a single lemma, and on $[0,1]$ the factor $1^{1/p} = 1$ kills the correction.

The lower bound is the hard direction. On paper: pick $\alpha$, bound below on $E_\alpha$, take $p$-th root, send $\alpha \to \|f\|_\infty$. In Lean: the $\varepsilon$-argument with $m(E_\alpha)^{1/p} \to 1$ needs rpow limit lemmas that are scattered. Conceptual difficulty zero; formalization difficulty moderate.
