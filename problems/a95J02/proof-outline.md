# Proof Outline: a95J02

## Problem

λ > 0, f entire, f(1) = 1, |f(z)| ≥ |z|^λ for all z.
Determine f. Answer: f(z) = z^n where n = λ (λ is a positive integer).

## Proof approach

1. f has no zeros for z ≠ 0. ✓ PROVED.
2. f(0) = 0: if not, 1/f is entire bounded (→0), Liouville → constant 0, contradiction.
3. Factor f(z) = z^n · g(z), g entire, g(0) ≠ 0.
4. |g(z)| ≥ |z|^{λ-n}: forces λ = n, then |g| ≥ 1, Liouville → g = 1.
5. f(z) = z^n.

## Proved lemma

- `zero_only_at_origin`: f(z) ≠ 0 for z ≠ 0 (from |f(z)| ≥ |z|^λ > 0).

## Theory boundaries (2 sorries)

1. `f_zero_eq_zero`: Liouville on 1/f requires boundedness setup.
2. `entire_lower_bound_is_monomial`: main theorem (inherits from above).

## Checked Lean state

- `lake env lean problems/a95J02/lean/Main.lean`: exit 0
- Sorry count: 2
- Classification: partial
