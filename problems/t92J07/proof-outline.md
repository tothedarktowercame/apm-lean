# Proof Outline: t92J07

The canonical Lean attempt is `lean/Main.lean`. The smooth-fiber conclusion is
now reduced definitionally to common regular-value regularity.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t92J07.md`

## Compiled progress

- `apm_t92J07_isSmoothRegularFiber_preimage_iff` removes the redundant
  preimage equality from every desired fiber certificate.
- `apm_t92J07_criticalValues` names the exact exceptional set.
- `apm_t92J07_exists_common_regularValue_of_null` proves the complete
  countable-union avoidance step, uniformly including a zero-dimensional
  target.

## Remaining boundary

- Prove manifold Sard: the critical values of each smooth `f i` are null.
- Implement manifold Sard chartwise from Mathlib's vector-space theorem. This
  still requires a countable chart cover, `mfderiv`/chart-derivative
  compatibility, and extending chart representatives to the whole model
  space in the form expected by the available Sard theorem.
- Feed those nullity results directly to the compiled common-regular-value
  lemma, then apply the compiled fiber equivalence.
