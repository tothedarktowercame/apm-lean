# Informal Solution: a96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

For each `n ≥ 1` choose the disjoint interval `I_n = [2^{-(n+1)}, 2^{-n}] ⊂ (0,1]`. Let `m_n` be its midpoint and `r_n` half its length. Define a “tent”
```
φ_n(x) = max(0, 1 - |x - m_n| / r_n)
```
and set `f_n(x) = φ_n(x)/n`. Each `f_n` is continuous, non-negative, supported in the interior of `I_n`, and satisfies `‖f_n‖_∞ = 1/n` (the peak occurs at `m_n`). Because the supports are disjoint and `φ_n` vanishes at the interval endpoints, at most one `f_n` is non-zero at any `x`. Consequently, if `S_N(x) = ∑_{n=1}^N f_n(x)` and `S(x) = lim_N S_N(x)`, then `S` is continuous, `S_N → S` uniformly, and
```
|S(x) - S_N(x)| = ∑_{n>N} f_n(x) ≤ sup_{n>N} ‖f_n‖_∞ = 1/(N+1).
```
Finally `∑_{n=1}^∞ ‖f_n‖_∞ = ∑_{n=1}^∞ 1/n = +∞`, so the series of sup norms diverges even though the functions converge uniformly.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Tent continuity/nonnegativity.** Uses that compositions of continuous functions and `max` stay continuous, and that the tent formula is ≥ 0.
- **Disjoint support.** From the dyadic intervals `I_n`: if both `φ_n(x)`, `φ_m(x)` are positive then the point lies in the intersection, which can only happen at shared endpoints where the tents vanish, so at most one summand contributes.
- **Uniform tail bound.** Disjoint support implies `∑_{n>N} f_n(x) ≤ sup_{n>N} 1/n = 1/(N+1)` uniformly in `x`, giving uniform convergence.
- **Divergent sup norms.** Harmonic series diverges, so `∑ ‖f_n‖_∞ = ∑ 1/n = ∞`.

**Stage 3 — LEAN FORMALIZATION**

Plan: encode the tent explicitly via
```
f n x = (Nat.succ n)⁻¹ * max 0 (1 - |x - mid n| / rad n)
```
where `mid n` and `rad n` describe the dyadic geometry. Needed ingredients: continuity of the tent, a lemma stating that tents on our dyadic family have pairwise disjoint supports, and a tail estimate `∀ x, ∑_{k≥N} f k x ≤ 1/(N+1)`. Once those are available we can conclude uniform convergence via the Cauchy criterion and note `¬ Summable (fun n => 1/(n+1))`. At the moment Mathlib lacks a prepackaged “triangular bump” API, so all these support/continuity calculations must be written manually; this is the blocker that prevented finishing the Lean proof in this pass.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal solution already matches the planned Lean construction: both rely on dyadic tents. Once the tent lemmas are formalized, cite the resulting Lean theorem (the target is `tent_sequence_exists` described in Stage 3) in Stage 1, and note explicitly that the harmonic-series divergence uses `Mathlib.Analysis.PSeries.not_summable_one_div_natCast`.
