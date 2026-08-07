# Proof Outline: m99J04

The canonical Lean attempt is `lean/Main.lean`. It proves compactness and
self-adjointness of the congruence and all algebraic transport identities
needed after selecting an eigenbasis.

- Compact operators are stable under bounded composition, so `A†TA` is compact.
- Adjoint composition identities prove `A†TA` is self-adjoint.
- `apm_m99j04_weight_inner` proves weighted normalization and orthogonality
  transport through `A`.
- `apm_m99j04_generalized_eigenvector` converts an eigenvector of `A†TA` into
  a generalized eigenvector of `(T,P)`.
- `apm_m99j04_orthonormal_map_of_adjoint_comp` proves that `A†A = id` sends
  every Hilbert basis to an orthonormal family, closing one direction of the
  final equivalence.

## Remaining Boundary

- Turn the spectral theorem's dense orthogonal sum of eigenspaces into one
  `HilbertBasis` whose vectors retain their eigenspace labels.
- Apply the existing transport lemmas pointwise to that basis.
- Prove the converse orthonormality implication using density of the Hilbert
  basis span.
