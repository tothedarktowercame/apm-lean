# Proof Outline: t92J07

The canonical Lean attempt is `lean/Main.lean`. The smooth-fiber conclusion is
now reduced definitionally to common regular-value regularity.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t92J07.md`

## Compiled progress

- `apm_t92J07_isSmoothRegularFiber_preimage_iff` removes the redundant
  preimage equality from every desired fiber certificate.

## Remaining boundary

- Prove manifold Sard: the critical values of each smooth `f i` are null.
- Implement it chartwise from Mathlib's vector-space Sard theorem, including a
  countable atlas and `mfderiv`/chart-derivative compatibility.
- Avoid the countable union of critical-value sets and apply the compiled
  fiber equivalence.
