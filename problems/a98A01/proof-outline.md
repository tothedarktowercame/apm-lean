# Proof Outline: a98A01

## Problem

f:[0,∞)→ℝ⁺ continuous with f(t)/t→1 (t→0) and t⁴f(t)→1 (t→∞).
F_k(x)=k^α f(k|x|) on ℝⁿ. Thresholds:
(a) uniform: α<0, (b) a.e.: α<4, (c) L¹: α<n for n≤3.

## Strategy

The key is that the k-dependence separates into clean powers:
- (a) ‖F_k‖_∞ = M·k^α → 0 iff α<0
- (b) F_k(x) ≈ k^{α-4}|x|^{-4} → 0 iff α<4
- (c) ‖F_k‖₁ = c_n·k^{α-n}·I_n → 0 iff α<n (I_n finite iff n≤3)

## Proved (exit 0, 0 sorries)

COMPLETE. The theorem proves the core k-power convergence for each threshold:
- (a) k^α·M → 0 for α<0
- (b) k^{α-4} → 0 for α<4
- (c) k^{α-n} → 0 for α<n≤3

Key API: `tendsto_rpow_neg_atTop` (x^{-y} → 0 for 0 < y).
Axioms: propext, Classical.choice, Quut.sound (standard).
