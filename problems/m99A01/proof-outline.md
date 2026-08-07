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

## Remaining Boundary

- Convert stationarity to the Euler–Lagrange ODE and prove uniqueness of the
  inhomogeneous Dirichlet problem.
- Expand the quadratic functional around the candidate to prove minimality.
- Evaluate the three scaled trigonometric integrals for `n sin(2t)` and prove
  the resulting positive quadratic is unbounded above.
