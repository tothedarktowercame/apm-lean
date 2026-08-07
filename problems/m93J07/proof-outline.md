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

## Remaining Boundary

- Package the power functions with indicators and bridge the scalar
  integrability results to the exact `MemLp` goals.
- Formalize the Banach-space examples and the implication that a separable
  strong dual forces separability of the original space.
- Construct dense, nonsurjective linear and continuous-linear endomorphisms
  of the specified `Lp` space.  No corpus helper currently packages this
  construction for the frozen subtype and measure conventions.
