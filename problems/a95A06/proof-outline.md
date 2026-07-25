# Proof Outline: a95A06

## Problem

f(z) = Σ z^{n!}/n! on the closed unit disk.
(a) f is continuous on Δ̄ and analytic on Δ.
(b) The unit circle is a natural boundary (no analytic continuation).

## Proof approach

### Part (a): Continuity — COMPLETE ✓

By the Weierstrass M-test (Mathlib's `continuousOn_tsum`):
- Each term z^{n!}/n! is continuous.
- ‖z^{n!}/n!‖ ≤ 1/n! on |z| ≤ 1 (proved in `lacunary_term_bound`).
- Σ 1/n! converges (proved in `lacunary_majorant_summable`).

### Part (a): Analyticity — PARTIAL (1 sorry)

Each term z^{n!}/n! is analytic (`lacunaryTerm_differentiableOn` proved).
The series of analytic functions converges uniformly on compact subsets of Δ,
giving analyticity of the sum. The sorry is for the final assembly step
(combining termwise differentiability with uniform convergence).

### Part (b): Natural boundary — SORRY (1 sorry)

Requires showing |f'(re^{2πiθ})| → ∞ for rational θ = p/q.
Key ingredient: `factorial_dvd_of_le` (q ∣ n! when n ≥ q) is proved.
The full divergence argument (Hadamard gap theorem) is not in Mathlib.

## Proved lemmas (zero sorry)

- `lacunary_term_bound`: ‖z^{n!}/n!‖ ≤ 1/n! on the closed disk
- `lacunary_majorant_summable`: Σ 1/n! converges
- `lacunaryTerm_continuousOn`: each term continuous on Δ̄
- `lacunarySeries_continuousOn`: **part (a) continuity** via M-test
- `lacunaryTerm_differentiableOn`: each term analytic on Δ
- `factorial_dvd_of_le`: q ∣ n! when q ≤ n (for the boundary blowup)

## Checked Lean state

- `lake env lean problems/a95A06/lean/Main.lean`: exit 0
- Sorry count: 2
- Classification: partial
