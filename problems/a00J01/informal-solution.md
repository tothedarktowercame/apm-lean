# Informal Solution: a00J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Definition.** ‖f‖_∞ = inf{M ≥ 0 : m({x : |f(x)| > M}) = 0}, the essential supremum of |f|. Equivalently, the smallest M such that |f| ≤ M almost everywhere.

**Claim.** For f ∈ L^∞([0,1]), lim_{p→∞} ‖f‖_p = ‖f‖_∞.

**Upper bound: lim sup ‖f‖_p ≤ ‖f‖_∞.**

For a.e. x, |f(x)| ≤ ‖f‖_∞. So ‖f‖_p^p = ∫|f|^p ≤ ‖f‖_∞^p · m([0,1]) = ‖f‖_∞^p. Taking p-th roots: ‖f‖_p ≤ ‖f‖_∞ for all p ≥ 1.

(This is routine — finite measure m([0,1]) = 1 makes it clean.)

**Lower bound: lim inf ‖f‖_p ≥ ‖f‖_∞.**

Fix α < ‖f‖_∞. The set E_α = {x : |f(x)| > α} has m(E_α) > 0 by definition of ess sup. Then ‖f‖_p^p ≥ ∫_{E_α} |f|^p ≥ α^p · m(E_α). Taking p-th roots: ‖f‖_p ≥ α · m(E_α)^{1/p} → α as p → ∞ (since m(E_α)^{1/p} → 1 for m(E_α) > 0).

So lim inf ‖f‖_p ≥ α for every α < ‖f‖_∞, hence lim inf ‖f‖_p ≥ ‖f‖_∞.

(The crux: E_α has POSITIVE measure because α < ess sup, and t^{1/p} → 1 for t > 0.)

**Combine.** ‖f‖_∞ ≤ lim inf ‖f‖_p ≤ lim sup ‖f‖_p ≤ ‖f‖_∞. ∎

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. **Upper bound** (‖f‖_p ≤ ‖f‖_∞ on finite measure): `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` in Mathlib gives ‖f‖_p ≤ ‖f‖_q · μ(univ)^{1/p-1/q}. With q=⊤ and μ(univ)=1 this gives ‖f‖_p ≤ ‖f‖_∞. **Critical path: YES.**
2. **Level set positive measure**: for α < ‖f‖_∞, μ({‖f‖ > α}) > 0. From the definition of essSup: if μ({‖f‖ > α}) = 0 then α ≥ ‖f‖_∞, contradicting α < ‖f‖_∞. **Custom, straightforward.**
3. **t^{1/p} → 1**: For t > 0, t^{1/p} → 1 as p → ∞. Mathlib: `ENNReal.rpow_natCast` + `tendsto_rpow_nhds_zero_of_norm_lt_one` or similar. **Fragmented in Mathlib.**
4. **Squeeze theorem**: lim inf ≥ L and lim sup ≤ L implies limit = L. Mathlib: `tendsto_of_tendsto_of_tendsto_of_le_of_le`. **Available.**

**Stage 3 — LEAN FORMALIZATION**

The upper bound should close from a single Mathlib comparison lemma. The lower bound needs the level-set argument with t^{1/p} → 1. See Main.lean.

Status: upper bound closeable; lower bound needs ~10 lines of ε-argument.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The upper bound is genuinely easy — both on paper and in Lean. The Mathlib comparison ‖f‖_p ≤ ‖f‖_∞ · μ(univ)^{1/p} is a single lemma, and on [0,1] the factor 1^{1/p} = 1 kills the correction.

The lower bound is the hard direction. On paper: pick α, bound below on E_α, take p-th root, send α → ‖f‖_∞. In Lean: the ε-argument with m(E_α)^{1/p} → 1 needs rpow limit lemmas that are scattered. Conceptual difficulty zero; formalization difficulty moderate.
