# Proof Outline: m01J04

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m01J04.md`

## Closer hop 1 progress

- The abstract weak×strong pairing conjunct is complete. Banach–Steinhaus
  bounds the weakly convergent sequence, after which a direct epsilon argument
  controls the varying-functional term by the operator norm.
- One sorry remains for both custom Sobolev clauses. Rellich supplies the
  subsequence abstractly, but the frozen predicates still require measurable
  Hölder estimates, a Leibniz construction inside `apm_m01J04_H1`, preservation
  of `apm_m01J04_isH1Zero`, and the corresponding integration-by-parts identity.
- Searches of the lemma index, fully closed artifacts, construction libraries,
  and Mathlib found no packaged bridge for this custom record.

## Closer hop 2 research

- Mathlib supplies the raw Hölder tools `MemLp.mul'`,
  `eLpNorm_smul_le_mul_eLpNorm`, and `L2.integrable_inner`; the integrability
  and bounded-multiplier estimates are therefore available.
- The remaining work is specific to the frozen encoding: construct the product
  `H1` record, prove its weak-gradient Leibniz identity, preserve `isH1Zero` by
  multiplying approximants, and connect the divergence pairing to the target
  integral. No packaged record-level bridge was found.

## Closer hop 3 progress

- Both remaining clauses are now proved for `d = 0`. In this case
  `EuclideanSpace ℝ (Fin 0)` is a subsingleton, so every gradient-valued field
  and every displayed inner product vanish; the required limits are constant
  zero limits.
- One sorry remains, confined to `d ≠ 0`. Closing it requires the custom
  positive-dimensional `H1` product record, its weak-gradient Leibniz rule,
  preservation of `apm_m01J04_isH1Zero`, and the resulting divergence-test
  identity. The raw Mathlib integrability estimates do not supply these
  record-level constructions.
