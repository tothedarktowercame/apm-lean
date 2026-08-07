# Proof Outline: m94J02

The canonical Lean attempt is `lean/Main.lean`. It proves that dilation
preserves the weighted coefficient space and establishes the eigenvalue
inclusion in the statement's custom spectrum.

- `apm_m94J02_T` preserves summability because every diagonal multiplier
  `‖2⁻ⁿ‖` is at most one.
- For each coordinate vector `e_j`, `(T - 2⁻ʲ I)e_j = 0`. A hypothetical
  left inverse would therefore send zero to both `e_j` and zero, a
  contradiction. Thus every displayed eigenvalue belongs to the custom
  spectrum.
- Closer hop 2 proves `apm_m94J02_norm_T_le`: dilation is a contraction in
  the frozen weighted norm. The proof uses `Summable.tsum_le_tsum` and the
  pointwise estimate `‖2⁻ⁿ‖ ≤ 1`. This is reusable in the compactness tail
  estimate and in the spectrum's bounded-inverse arguments.

## Closer hop 3 progress

- `apm_m94J02_diagonal_range_subset_spectrum` packages the individual
  coordinate-eigenvector contradictions into the set inclusion
  `range (n ↦ 2⁻ⁿ) ⊆ spectrum`.
- For the remaining forward inclusion at zero, a hypothetical bounded inverse
  must send the `n`th coordinate vector to `2ⁿ` times that vector, contradicting
  its fixed operator bound as `n → ∞`. This quantitative argument is not
  packaged for the file's custom unbundled inverse encoding.

## Remaining Boundary

- Weighted-`ℓ¹` completeness and closed-disk continuity.
- The Cauchy-product summability and sharp `5/4` norm estimate.
- The spectral-radius power limit via subadditivity.
- Sequential compactness via diagonal extraction and tail control.
- The reverse spectrum inclusion and the proof that zero is spectral.
