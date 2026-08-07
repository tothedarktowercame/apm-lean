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

lemma apm_b00J04_inv_den_mem
    (R F : Type*)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Subalgebra R F) (alpha : S) (a b : R)
    (hb : b ≠ 0)
    (halpha : (alpha : F) = algebraMap R F a / algebraMap R F b)
    (hab : IsRelPrime a b) :
    (algebraMap R F b)⁻¹ ∈ S := by
  rcases hab.isCoprime with ⟨u, v, huv⟩
  have hmem :
      algebraMap R F u * (alpha : F) + algebraMap R F v ∈ S :=
    S.add_mem (S.mul_mem (S.algebraMap_mem u) alpha.property)
      (S.algebraMap_mem v)
  rw [show (algebraMap R F b)⁻¹ =
      algebraMap R F u * (alpha : F) + algebraMap R F v by
    rw [halpha]
    have hbF : algebraMap R F b ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R F)).mpr hb
    field_simp
    symm
    simpa only [map_add, map_mul, map_one, mul_comm] using
      congrArg (algebraMap R F) huv]
  exact hmem

lemma apm_b00J04_first_conjunct
    (R F : Type*)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Subalgebra R F) :
    ∀ alpha : S, ∃ a b : R, b ≠ 0 ∧
      (alpha : F) = algebraMap R F a / algebraMap R F b ∧
      (algebraMap R F b)⁻¹ ∈ S := by
  intro alpha
  obtain ⟨a, b, hb, halpha, hab⟩ :=
    apm_b00J04_exists_reduced_fraction R F (alpha : F)
  exact ⟨a, b, hb, halpha,
    apm_b00J04_inv_den_mem R F S alpha a b hb halpha hab⟩

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
  refine ⟨apm_b00J04_first_conjunct R F S, ?_⟩
  /-
  PARTIAL boundary (closer hop 2). The Bézout bridge and the entire first
  conjunct are now compiled. `IsRelPrime.isCoprime` exposes coefficients
  `u,v` with `u*a + v*b = 1`; `apm_b00J04_inv_den_mem` maps this identity into
  `F`, rewrites `1/b = u*(a/b)+v`, and closes membership using the subalgebra
  operations. `apm_b00J04_first_conjunct` combines this with the canonical
  reduced fraction from hop 1. Consequently the remaining `sorry` covers only
  `IsPrincipalIdealRing S` and the module-finite implication.

  Prior hop 1: the nontrivial normalization prerequisite
  for part (a) is now compiled as `apm_b00J04_exists_reduced_fraction`, using
  Mathlib's `IsFractionRing.num`, `den`, `mk'_num_den'`, and
  `num_den_reduced`. Thus every element has a denominator coprime to its
  numerator; the original skip's inference from an arbitrary `a/b ∈ S` to
  `1/b ∈ S` would be invalid without this reduction.

  Proving every ideal of `S`
  principal still requires formalizing the contraction/extension argument. The
  module-finite conclusion still needs either common-denominator control for
  a finite generating set or Mathlib's integrality/integrally-closed route.
  Searches of the lemma index, localization sources, prior artifacts, and
  construction libraries found no packaged theorem combining these stages.
  -/
  sorry
