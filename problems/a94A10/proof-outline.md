# Proof Outline: a94A10

## Problem

Suppose `f` is an entire function with the property that `f(z)` is real if and
only if `z` is real. Verify that `f'(z) = 0` cannot be true for any real `z`.

## Statement Repair

1. The `RealIffReal` definition is correct as proposed.
2. The informal proof's helper lemmas used `iteratedDeriv`; we use `analyticOrderAt`
   from `Mathlib.Analysis.Analytic.Order` for the local factorization, which is
   more natural and directly supported.
3. The proof requires Rouché's theorem or the argument principle for the core step
   (finding non-real preimages of real values at a critical point). Neither is in
   Mathlib as of 2026.

## Proof Strategy

By contradiction: assume `f'(x₀) = 0` for real `x₀`.

1. **f is non-constant** (proved): a constant `f` maps non-real `z` to real values,
   violating the hypothesis.
2. **Order ≥ 2** (proved): `f - f(x₀)` vanishes to order `n ≥ 2` at `x₀`, via
   `analyticOrderAt_deriv_add_one` from Mathlib.
3. **Local factorization** (proved): `f(z) - f(x₀) = (z-x₀)^n · g(z)` with
   `g(x₀) ≠ 0`, via `analyticOrderAt_eq_natCast`.
4. **Order ≠ ⊤** (proved): otherwise `f` is locally constant, hence globally
   constant by the identity theorem, contradicting step 1.
5. **Non-real preimage of real value** (SORRY): the local n-to-1 structure at a
   critical point of order `n ≥ 2` produces non-real preimages of real values.
   This requires Rouché's theorem, the argument principle, or a delicate IVT
   argument on `Im(f(x₀ + r·e^{iα}))` — none of which are readily available.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 1 (on `exists_nonreal_preimage_of_real`)
- **Classification**: partial
- **Proved lemmas**:
  - `nonconstant_of_realIffReal`: f is non-constant
  - `order_ge_two_of_deriv_zero`: order ≥ 2 when f'(x₀) = 0
  - `exists_factorization_of_order_ge_two`: local factorization extraction
  - `deriv_ne_zero_on_reals`: main theorem (modulo the sorry)
- **Blocker**: The core step requires showing that a holomorphic function with
  a critical point of order `n ≥ 2` at a real point maps some non-real point
  near it to a real value. This needs Rouché's theorem, the argument principle,
  or a careful IVT argument — not currently in Mathlib.
