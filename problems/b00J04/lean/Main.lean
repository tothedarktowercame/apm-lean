import Mathlib

noncomputable section

/-!
# APM b00J04

## Statement repairs

None.

## Encoding notes

The inclusions `R ⊆ S ⊆ F` are represented by an intermediate
`Subalgebra R F`; its bottom element is precisely the embedded copy of `R`.
`IsFractionRing R F` records that `F` is the fraction field of `R`.
-/

theorem apm_b00j04
    (R F : Type*)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Subalgebra R F) :
    (∀ α : S, ∃ a b : R, b ≠ 0 ∧
      (α : F) = algebraMap R F a / algebraMap R F b ∧
      (algebraMap R F b)⁻¹ ∈ S) ∧
    IsPrincipalIdealRing S ∧
    (Module.Finite R S → S = ⊥) := by
  -- SKIPPED: three-part commutative algebra for intermediate rings R⊂S⊂Frac(R).
  -- (a) Every α∈S is a/b with 1/b∈S: use that α=a/b in F, and S is a ring containing R.
  -- (b) S is a PID: every ideal of S contracts to an ideal of R (a PID), use localization.
  -- (c) If S finite R-module then S=R: integrality argument (S⊆Frac(R), finite ⟹ integral ⟹ S=R).
  -- Blocker: requires `IsPrincipalIdealRing`, `IsFractionRing`, `Subalgebra`,
  -- integral extension theory — deep algebra infrastructure to assemble.
  sorry
