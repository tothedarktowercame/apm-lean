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
  refine ⟨?_, ?_, ?_⟩
  · intro D K _ _ _ _ _ _
    exact (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  · norm_num
  · -- Boundary (pass-1 Codex, sustained attempt): searched
    -- `AdjoinRoot.isDomain_of_prime`, `AdjoinRoot.modByMonicHom`,
    -- `isIntegrallyClosed_iff`, Eisenstein, quotient, and fraction-ring APIs;
    -- also all closed sibling artifacts, `ConstructionTargets/`, and
    -- `YoungL2.lean`. The first two conjuncts are complete.
    -- Earlier searches included `isIntegrallyClosed_iff_isIntegrallyClosedIn`,
    -- `IsIntegral`, quotient-lift APIs, and polynomial quotient/fraction-ring
    -- equivalences.  The intended witness is `(1 + X) / 2` in the fraction
    -- field of `ℤ[X] ⧸ (X^2 - 5)`, satisfying `T^2 - T - 1`; completing this
    -- requires an explicit identification of Mathlib's abstract fraction field
    -- with `ℚ[X] ⧸ (X^2 - 5)` and a coefficient argument showing the witness is
    -- not in the image of the integer quotient. The audit found the latter
    -- coordinate tool, but the remaining blocker is constructing the
    -- fraction-field presentation, transporting the monic relation, and
    -- clearing `2` to obtain the impossible equations `2*a = 1`, `2*b = 1`.
    -- No searched library or closed artifact packages this bridge.
    sorry
