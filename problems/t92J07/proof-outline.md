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
- `apm_t92J07_isRegularValue_fin_zero` proves every value is regular for a
  zero-dimensional target, using the canonical tangent-space identification.
- `apm_t92J07_criticalValues_fin_zero` proves the exceptional set is empty,
  and the main theorem now closes the entire `m = 0` branch.

## Remaining boundary

- For positive-dimensional targets, prove manifold Sard: the critical values
  of each smooth `f i` are null.
- Implement manifold Sard chartwise from Mathlib's vector-space theorem. This
  still requires a countable chart cover, `mfderiv`/chart-derivative
  compatibility, and extending chart representatives to the whole model
  space in the form expected by the available Sard theorem.
- Feed those nullity results directly to the compiled common-regular-value
  lemma, then apply the compiled fiber equivalence.

## Hop 4: stated Sard bridge

`apm_t92J07_bridge_1` states the missing theorem at the exact abstraction
boundary used here: a smooth map from a second-countable finite-dimensional
manifold to positive-dimensional Euclidean space has a null set of critical
values, where criticality is defined by failure of surjectivity of `mfderiv`.
It can be applied pointwise to the family and fed directly to
`apm_t92J07_exists_common_regularValue_of_null`.
