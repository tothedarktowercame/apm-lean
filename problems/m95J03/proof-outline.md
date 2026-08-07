# Proof Outline: m95J03

The frozen Lean theorem is present in `lean/Main.lean`. The first complete
conjunct has been factored into a compiled helper:

- the left-inverse solvability criterion and uniqueness statement;

The exponential-series conjunct matches
`NormedSpace.exp_series_hasSum_exp'`; its direct arbitrary-matrix
specialization currently exceeds the elaboration heartbeat budget.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J03.md`

## Remaining boundary

- prove entrywise continuity of `B` and convergence of `diagonalJordan`;
- discharge the explicit nilpotence and nonvanishing calculations at zero;
- construct and verify an invertible conjugating matrix for nonzero `ρ`;
- identify the truncated exponential with `flow 1`;
- prove the initial-value and derivative formulas coordinatewise.

The compiled helper uses `Matrix.mulVec_mulVec`. Mathlib already supplies the
needed exponential convergence theorem, so no custom convergence theory is
needed once its matrix specialization is made tractable.
