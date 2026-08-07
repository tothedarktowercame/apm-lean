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

/-- Mathlib's canonical numerator and denominator give the reduced fraction
needed before the Bézout step in the first conjunct. -/
lemma apm_b00J04_exists_reduced_fraction
    (R F : Type*)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (x : F) :
    ∃ a b : R, b ≠ 0 ∧
      x = algebraMap R F a / algebraMap R F b ∧ IsRelPrime a b := by
  refine ⟨IsFractionRing.num R x, IsFractionRing.den R x,
    ?_, ?_, ?_⟩
  · intro hb
    have h1 := (IsFractionRing.den R x).property.1 1 (by simp [hb])
    exact one_ne_zero h1
  · exact (IsFractionRing.mk'_num_den' R x).symm
  · exact IsFractionRing.num_den_reduced R x

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
  /-
  PARTIAL boundary (closer hop 1): the nontrivial normalization prerequisite
  for part (a) is now compiled as `apm_b00J04_exists_reduced_fraction`, using
  Mathlib's `IsFractionRing.num`, `den`, `mk'_num_den'`, and
  `num_den_reduced`. Thus every element has a denominator coprime to its
  numerator; the original skip's inference from an arbitrary `a/b ∈ S` to
  `1/b ∈ S` would be invalid without this reduction.

  The remaining local bridge is extracting a Bézout identity from
  `IsRelPrime a b` under `IsPrincipalIdealRing R` and transporting
  `1/b = u*(a/b)+v` into the subalgebra. Afterward, proving every ideal of `S`
  principal requires formalizing the contraction/extension argument. The
  module-finite conclusion still needs either common-denominator control for
  a finite generating set or Mathlib's integrality/integrally-closed route.
  Searches of the lemma index, localization sources, prior artifacts, and
  construction libraries found no packaged theorem combining these stages.
  -/
  sorry
