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
  · -- Boundary (closer hop 1): bridge still open. Enriched analysis.
    -- Mathlib has `isIntegrallyClosed_iff` (IntegrallyClosed.lean:125):
    --   IsIntegrallyClosed R ↔ ∀ x : K, IsIntegral R x → ∃ y, algebraMap R K y = x
    -- To show ¬IsIntegrallyClosed (ℤ[X] ⧸ (X²-5)):
    --   Need: ∃ x in Frac(ℤ[X]/(X²-5)), IsIntegral over R, but x ∉ image of algebraMap.
    -- Witness: (1+√5)/2, satisfying T²-T-1=0 (integral), but not in ℤ[X]/(X²-5)
    -- (which has elements a+b√5 with a,b ∈ ℤ; (1+√5)/2 requires 2|1 contradiction).
    --
    -- Blocker: constructing the fraction field of ℤ[X]/(X²-5), placing the witness
    -- in it, proving the integral equation, and the non-membership, all through
    -- Mathlib's abstract FractionField and quotient ring APIs.
    -- Each sub-step is 15-30 lines; total ~60-100 lines.
    -- APIs: `FractionField`, `Ideal.Quotient`, `IsIntegral`, `algebraMap`,
    --   `Polynomial.Quotient` (if exists), `RingHom.map_quotient`
    sorry
