# Proof Outline: a97J07

## Problem

f continuous on {|z|≤1}, analytic on {|z|<1}. ‖f(z)‖≤a on upper semicircle,
‖f(z)‖≤b on lower semicircle. Prove ‖f(0)‖≤√(ab).

## Strategy (from informal-solution.md)

Reflection trick: g(z)=f(z)·f(-z) satisfies ‖g‖≤ab on whole circle.
Maximum modulus: ‖g(0)‖≤ab. Since g(0)=f(0)², ‖f(0)‖²≤ab, so ‖f(0)‖≤√(ab).

## Proved (exit 0, 0 sorries)

COMPLETE PROOF. Key Mathlib API: `Complex.norm_le_of_forall_mem_frontier_norm_le`
(maximum modulus principle in `Analysis/Complex/AbsMax.lean`).

Steps:
1. g(z)=f(z)·f(-z) is DiffContOnCl on ball 0 1 (DifferentiableOn.mul + comp with neg)
2. ‖g(z)‖≤ab on frontier: reflection swaps upper/lower arcs
3. Maximum modulus: ‖g(0)‖≤ab
4. g(0)=f(0)², so ‖f(0)‖²≤ab, hence ‖f(0)‖≤√(ab) via Real.le_sqrt

## Axioms
propext, Classical.choice, Quot.sound (standard).
