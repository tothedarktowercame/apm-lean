# Proof Outline: m96J02

This bundle currently has a harvested informal solution but no imported
Lean proof attempt in this problem root.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J02.md`

## Follow-up Needed

- extract a formalization-oriented proof outline from the informal solution
- add or select the canonical Lean attempt for this problem

## Hop 4 statement review: defective

The frozen theorem is false because it combines relative smoothness on
`Icc 0 T` with global two-sided derivatives at the endpoint `0`.

For every proposed `T > 0`, take `g := fun _ _ => 0`, `α = β = 0`,
`x := fun t => |t|`, and `y := fun _ => 0`. On `Icc 0 T`, `x` agrees with the
identity and is therefore `ContDiffOn ℝ 2`; Mathlib's totalized `deriv` gives
`deriv x 0 = 0` and `deriv (deriv x) t = 0` throughout the interval. The zero
function satisfies the Volterra equation, but at `t = T` one has
`x T = T ≠ 0 = y T`.

No true bridge lemma can prove the frozen conclusion. A corrected statement
must require two-sided smoothness near zero or consistently use within-
derivatives at the endpoint.
