# Refutation of `apm_m98a02`

The final conjunct omits `[Nontrivial X]`.  Let `X := Fin 0 → ℝ` and let
`A = 0`.  This is a complete real normed space and `‖A‖ < 1`.  Every continuous
linear endomorphism `B` of `X` equals zero, so `‖B‖ = 0`.  The demanded lower
bound becomes

`1 / (1 + ‖A‖) ≤ ‖B‖`, hence `1 ≤ 0`, a contradiction.

`Refutation.lean` states the frozen conjunction at universe zero and proves
its negation using this example.  It compiles with the pinned dependencies and
contains no proof placeholders.
