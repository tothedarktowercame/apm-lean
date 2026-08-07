# Proof Outline: m93J07

The canonical Lean attempt is in `lean/Main.lean`.  It currently closes the
finite-measure monotonicity clause and records a compiled analytic core for
the explicit power-function counterexamples.

- The impossibility of an `L⁴` but not `L²` function on `[0,1]` follows from
  `MemLp.mono_exponent` and finiteness of the restricted measure.
- On `(0,1)`, the square of `x^(-1/3)` is integrable while its fourth power
  is not, by `intervalIntegral.integrableOn_Ioo_rpow_iff`.
- On `(1,∞)`, the fourth power of `x^(-1/3)` is integrable while its square
  is not, by `integrableOn_Ioi_rpow_iff`.
- These four scalar integrability facts are proved as local helper lemmas.

## Closer hop 2 progress

- `apm_m93J07_localWitness` is the indicator of `x ^ (-1/3)` on `(0,1)`.
- Its strong measurability and exact memberships `MemLp ... 2 volume` and
  `¬ MemLp ... 4 volume` now compile, using the scalar integral helpers,
  `memLp_two_iff_integrable_sq`, and `MemLp.integrable_norm_rpow`.
- The same indicator conversion can be reused for the restricted-measure and
  tail witnesses. The dominant remaining work is still the Banach-space
  example bundle and the dense-proper operator on the frozen `Lp` type.

## Closer hop 3 progress

- The theorem now uses `apm_m93J07_localWitness` directly to discharge the
  global `L²(volume) \ L⁴(volume)` conjunct. That conjunct has been removed
  from the aggregate proposition guarded by the sole `sorry`.
- The remaining aggregate contains the six Banach-space assertions, the two
  dense-proper endomorphisms of the restricted `Lp` space, the tail
  `L⁴ \ L²` witness, and the restricted-measure `L² \ L⁴` witness.

## Remaining Boundary

- Package the tail and restricted power functions with indicators and bridge
  their scalar integrability results to the exact `MemLp` goals.
- Formalize the Banach-space examples and the implication that a separable
  strong dual forces separability of the original space.
- Construct dense, nonsurjective linear and continuous-linear endomorphisms
  of the specified `Lp` space.  No corpus helper currently packages this
  construction for the frozen subtype and measure conventions.
