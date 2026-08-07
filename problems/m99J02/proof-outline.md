# Proof Outline: m99J02

The canonical Lean attempt is `lean/Main.lean`. It proves continuity of the
glued kernel, cancellation of the regular differential expression away from
the gluing point, and constancy of the Wronskian.

- `apm_m99j02_g_continuous` proves the two branches agree continuously at `y`,
  excluding a delta-prime contribution.
- `hregular_cancel` proves `g'' + qg = 0` away from `y`.
- `apm_m99j02_wronskian_eq_zero` proves Abel's identity for the raw derivative
  encoding.

## Remaining Boundary

- Split the compactly supported whole-line integral at finite bounds around
  the test function's support and at `y`.
- Apply interval integration by parts twice on each branch.
- Cancel value boundary terms using kernel continuity and identify the first
  derivative jump with the Wronskian.
