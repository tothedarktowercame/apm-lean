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
- Closer hop 2 compiles that bridge completely as
  `m95A02_tendsto_coord_of_weak`, using the weak-space evaluation criterion,
  the Riesz functional of `lp.single`, and `lp.inner_single_left`.

## Remaining Boundary

- Formalize the sharp Fourier-kernel estimate needed for the Hölder bound.
- Prove uniform control of the bilateral Fourier tail from the summable
  weights and translate it through the custom `sSup` distance.
