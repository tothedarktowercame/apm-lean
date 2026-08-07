# Proof Outline: m99A01

The canonical Lean attempt is `lean/Main.lean`. It verifies the displayed
candidate's ODE and endpoint conditions and formalizes the family used to show
unboundedness above.

- `apm_m99A01_extremal_ode` proves `y'' - y = 1` for the candidate.
- The theorem proves the candidate is globally `C¹` with both required endpoint
  values.
- `apm_m99A01_sine_family_admissible` proves every `n sin(2t)` is admissible.
- `apm_m99A01_deriv_sine_family` computes its derivative as
  `2n cos(2t)`.
- The three `apm_m99A01_integral_*_two_mul` lemmas evaluate the scaled sine and
  cosine integrals exactly.
- `apm_m99A01_functional_sine_family` proves
  `J(n sin(2t)) = (5π/4)n² + 2n`, and `apm_m99A01_no_maximum` uses this to
  close the nonexistence-of-a-maximum clause.

## Remaining Boundary

- Convert stationarity to the Euler–Lagrange ODE and prove uniqueness of the
  inhomogeneous Dirichlet problem.
- Expand the quadratic functional around the candidate to prove minimality.
The unboundedness and no-maximum portion is now closed. Global minimality still
needs the quadratic expansion and integration-by-parts cancellation of its
cross term.
