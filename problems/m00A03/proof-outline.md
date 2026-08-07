# Proof Outline: m00A03

The canonical Lean attempt completely proves the Riesz-lemma conjunct. One
sorry remains for the compact-operator spectral conclusions.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A03.md`

## Formal progress

- `riesz_lemma_of_lt_one` proves the requested separation estimate.
- `apm_m00A03_finite_norm_ge_of_finite_norm_gt` converts the statement's
  strict spectral cutoff into the closed annulus used by the standard proof.
- `apm_m00A03_derivedSet_subset_zero_of_annular_finite` proves the complete
  topological consequence: finite positive-norm annuli force every derived-set
  point to be zero, using `accPt_iff_nhds` and a finite-point-exclusion
  neighborhood.
- `IsCompactOperator.hasEigenvalue_iff_mem_spectrum` identifies every nonzero
  spectral value as an eigenvalue.

## Remaining bridge

Mathlib's proof of `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`
provides the compact-image/subsequence contradiction machinery for a fixed
spectral parameter. The remaining work is the genuinely new multi-eigenvalue
assembly: enumerate distinct annular spectral points, obtain eigenvectors,
build their strict invariant finite-span flag and shift identity, then apply
Riesz's lemma to produce the separated sequence. This annular-finiteness claim
is now the only proposition behind the remaining `sorry`; the derived-set
conclusion is compiled from it.
