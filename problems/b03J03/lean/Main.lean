import Mathlib

open Polynomial

noncomputable section

/-!
# APM b03J03

## Statement repairs

None. Part (b) explicitly asks for proof or disproof; it is formalized by the
square-free counterexample `D = ℤ`, `a = 5`.

## Encoding notes

The quadratic order is the genuine quotient `ℤ[x]/(x²-5)`. Saying it is not
`IsIntegrallyClosed` means it is not integrally closed in its fraction field,
canonically identified with `ℚ[x]/(x²-5)` as in the source.
-/

def apmQuadraticIdeal : Ideal ℤ[X] :=
  Ideal.span {X ^ 2 - C (5 : ℤ)}

theorem apm_b03j03 :
    (∀ (D K : Type*)
      [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
      [Field K] [Algebra D K] [IsFractionRing D K],
      IsIntegrallyClosedIn D K) ∧
    (Squarefree (5 : ℤ) ∧
      ¬IsIntegrallyClosed (ℤ[X] ⧸ apmQuadraticIdeal)) := by
  sorry
