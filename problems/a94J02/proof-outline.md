# Proof Outline: a94J02

## Problem

Construct an absolutely continuous nonnegative strictly monotone function `h`
such that `h' = 0` on a set of positive Lebesgue measure.

The original TeX says "on ℝ", but the informal proof correctly identifies that
strict monotonicity + integrability + nonneg on all of ℝ is impossible. The
meaningful version is on a compact interval `[0,1]`, which is what we formalize.

## Construction

`h(x) = ∫₀^x 𝟙_{[0,1]\\C}(t) dt` where `C` is a fat Cantor set (closed,
nowhere-dense, positive measure).

## Lean state

`lean/Main.lean` compiles cleanly with **5 sorries**, no errors. The sorries are:

1. **`exists_fat_cantor`** (line 73): Existence of a closed, nowhere-dense set
   of positive measure in `[0,1]`. This is the Smith-Volterra-Cantor set. Not in
   Mathlib; requires an explicit recursive interval-removal construction.

2. **`constructedH_mono`** (line 114): Monotonicity of the integral. Mathematically
   trivial (integral of nonneg function) but requires threading `IntervalIntegrable`
   through Mathlib's API for indicator functions.

3. **`constructedH_strictMonoOn`** (line 132): Strict monotonicity from
   nowhere-denseness of `C`. The key topological argument: `(x,y) ∩ ([0,1]\\C)`
   is nonempty (because `interior C = ∅`), and since `C` is closed, the complement
   is open, giving positive-measure intersection.

4. **`constructedH_deriv_zero_pos_measure`** (line 139): Derivative equals density
   a.e. (FTC for L¹), so derivative is 0 on `C` which has positive measure.

5. **`exists_ac_strictly_mono_deriv_zero_pos_measure`** (line 156): Main theorem
   packaging — combines 1–4.

The `constructedH_nonneg` lemma (line 106) is **fully proved**.

## Classification: partial

The formalization correctly states the mathematical problem, repairs the
impossible "on ℝ" to the meaningful "on [0,1]" version, and identifies the
exact boundaries (fat Cantor set existence, strict monotonicity from
topological nowhere-denseness, FTC for the derivative). All sorries are
explicitly marked with precise comments.
