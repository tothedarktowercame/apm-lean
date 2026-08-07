# Proof Outline: t96J07

The frozen theorem is false because of implication precedence in its first
conjunct. This is now formally verified by
`apm_t96j07_not_fixed_axis_clause` in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t96J07.md`

## Frozen-statement defect

The clause parses as

```text
∀ x, (x ≠ 0 → projectivelyEq x (A x)) ↔ ∃ i, projectivelyEq x (axis i).
```

At `x = 0`, the left side is vacuously true. The right side would make an axis
vector equal to a scalar multiple of zero; evaluating at the axis coordinate
gives `1 = 0`.

The intended theorem must instead place the entire equivalence under the
`x ≠ 0` implication. The statement is frozen, so this repair was not made.
