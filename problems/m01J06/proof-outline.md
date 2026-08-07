# Proof Outline: m01J06

The Lean artifact is partial. Positivity facts and the full construction of
the explicit critical sine modes are compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m01J06.md`

## Formalized

- The zero configuration is admissible.
- Every critical frequency and critical load is positive.
- For `s ↦ sin (w s)`, the first derivative is `w cos (w s)` and the
  second derivative is `-w² sin (w s)`.
- The second derivative formula is transported to
  `iteratedDerivWithin 2` on `Icc 0 1`.
- For every `m`, the sine at frequency `(2m+1)π/2` is a nontrivial linear mode
  at the stated critical load. Thus the reverse implication from a listed
  critical load to existence of a mode is complete.
- `apm_m01J06_derivWithin_smul_variation` proves that scalar variations commute
  with `derivWithin` on the frozen interval, including its endpoints.

## Remaining Boundaries

- Differentiate the set integral and prove the Euler–Lagrange/natural boundary
  equations; the zero-stationarity clause needs the same integral bridge.
- Prove only the converse ODE classification: every nontrivial custom linear
  mode has one of the listed frequencies.
- Establish the genuine local nonlinear bifurcation theorem near every
  critical load.

Closer hop 3 identifies
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` as the direct first-
variation API. The remaining prerequisite is a uniform integrable majorant
deduced from compact-interval `ContDiffOn`; after that, set/interval-integral
conversion and a locally developed fundamental lemma are still needed.
