# Proof Outline: m99J06

The canonical partial formalization is `lean/Main.lean`, with one documented
boundary remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m99J06.md`

## Compiled progress

- `apm_m99J06_galerkin_energy`: testing the discrete equation with its
  solution gives the exact energy identity.
- Weak solutions are unique by extensionality of the Hilbert inner product.
- `apm_m99J06_galerkin_unique`: two Galerkin solutions coincide, since their
  difference has zero inner product with itself. This proves the coercivity
  half of finite-dimensional solvability.
- `apm_m99J06_exists_unique_inner_eq`: Riesz representation gives a unique
  vector representing any continuous real-linear functional on a complete
  real Hilbert space. Applied to a finite-dimensional Galerkin subspace (after
  installing its completeness), this closes the abstract duality step.
- `apm_m99J06_model_ext`: equality of both the value representative and weak
  derivative representative implies equality of the ambient Hilbert-space
  elements. This supplies the descent step after representative-level linear
  combinations have been constructed.

## Follow-up needed

- Derive from `M.inner_eq` that the representative-level right-hand side is a
  continuous linear functional. The model does not expose `M.val` as a linear
  map, so this requires an `L²` equality argument before the compiled Riesz
  helper applies.
- Prove closure of `apm_m99J06_isH01Pair` under linear combinations and the
  product-integrability identities needed to distribute `M.inner_eq`; then use
  `apm_m99J06_model_ext` to transport those identities back to `H`.
- Establish the custom one-dimensional Sobolev integration-by-parts and
  regularity bridge needed for weak/strong equivalence.
- Obtain a weakly convergent subsequence from the bounded sequence and pass
  the Galerkin equations to its limit using density.
