# Proof Outline: m95A02

The canonical Lean attempt is `lean/Main.lean`. It proves the Hilbert-basis
clause and basic facts about the custom Fourier evaluation and maximum-distance
encoding.

- `HilbertBasis.ofRepr` supplies the canonical coordinate basis.
- `m95A02Value_single` identifies evaluation of `lp.single 2 n 1` with the
  normalized Fourier mode.
- `m95A02Value_zero` and `m95A02MaxDist_self` establish the zero and diagonal
  behavior of the custom encodings.
- Mathlib's `lp.inner_single_right` identifies Fourier coordinates with inner
  products, supplying the algebraic bridge from weak convergence to individual
  coordinate convergence.

## Remaining Boundary

- Formalize the sharp Fourier-kernel estimate needed for the Hölder bound.
- Apply the weak-space filter criterion to `lp.inner_single_right`.
- Prove uniform control of the bilateral Fourier tail from the summable
  weights and translate it through the custom `sSup` distance.
