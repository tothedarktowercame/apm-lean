/-
  C3 — UT Austin Prelim b03J02 (Algebra)

  Let R be an integral domain, a ∈ R nonzero and noninvertible.
  (a) The ideal (a, x) ⊂ R[x] is not principal.
  (b) If K is a field then K[x,y] is not a PID.
-/
import Mathlib

open Polynomial Ideal

/-- K[X][Y] is not a PID, because K[X] is a PID but not a field. -/
theorem kxy_not_pid (K : Type*) [Field K] [DecidableEq K] :
    ¬ IsPrincipalIdealRing (Polynomial (Polynomial K)) := by
  intro h
  -- If K[X][Y] were a PID, then K[X] would be a field.
  have hfield : IsField K[X] := IsField.of_isPrincipalIdealRing_polynomial (R := K[X])
  -- But K[X] is not a field (X is not a unit).
  exact polynomial_not_isField hfield
