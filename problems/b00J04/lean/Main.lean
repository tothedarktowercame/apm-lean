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

/-- A finitely generated submodule of the fraction field admits one common
nonzero denominator. Adapted from the compiled sibling `b96A04`. -/
lemma apm_b00J04_common_denom_of_fg_submodule
    (R F : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    (M : Submodule R F) (hfg : M.FG) :
    ∃ r : R, r ≠ 0 ∧
      ∀ m ∈ M, r • m ∈ Set.range (algebraMap R F) := by
  rw [Submodule.fg_def] at hfg
  obtain ⟨s, hsfin, hs⟩ := hfg
  let t : Finset F := hsfin.toFinset
  let r0 : nonZeroDivisors R :=
    IsLocalization.commonDenomOfFinset (nonZeroDivisors R) t
  refine ⟨r0, nonZeroDivisors.coe_ne_zero r0, ?_⟩
  intro m hm
  have hmspan : m ∈ Submodule.span R (t : Set F) := by
    simpa [t, hs] using hm
  have hclear : r0 • m ∈ LinearMap.range (Algebra.linearMap R F) := by
    refine Submodule.span_induction (p := fun z _ =>
      r0 • z ∈ LinearMap.range (Algebra.linearMap R F)) ?_ ?_ ?_ ?_ hmspan
    · intro x hx
      let ix : t := ⟨x, hx⟩
      refine ⟨IsLocalization.integerMultiple (nonZeroDivisors R) t id ix, ?_⟩
      change algebraMap R F _ = _
      rw [IsLocalization.map_integerMultiple]
      rfl
    · simp
    · intro x y _ _ hx hy
      simpa [smul_add] using
        (LinearMap.range (Algebra.linearMap R F)).add_mem hx hy
    · intro a x _ hx
      rw [smul_comm]
      exact (LinearMap.range (Algebra.linearMap R F)).smul_mem a hx
  simpa [LinearMap.mem_range] using hclear

/-- A module-finite intermediate algebra therefore has one denominator that
clears every one of its elements after embedding into the fraction field. -/
lemma apm_b00J04_common_denom_of_finite_subalgebra
    (R F : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    (S : Subalgebra R F) (hfinite : Module.Finite R S) :
    ∃ r : R, r ≠ 0 ∧
      ∀ s : S, r • (s : F) ∈ Set.range (algebraMap R F) := by
  letI : Module.Finite R S := hfinite
  let ι : S →ₗ[R] F := (Subalgebra.val S).toLinearMap
  have hfg : (LinearMap.range ι).FG := by
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map ι
  obtain ⟨r, hr, hclear⟩ :=
    apm_b00J04_common_denom_of_fg_submodule R F (LinearMap.range ι) hfg
  refine ⟨r, hr, fun s => ?_⟩
  exact hclear (s : F) ⟨s, rfl⟩

def apm_b00J04_denomSubmonoid
    (R F : Type*) [CommRing R] [Field F] [Algebra R F]
    (S : Subalgebra R F) : Submonoid R :=
  (IsUnit.submonoid S).comap (algebraMap R S).toMonoidHom

/-- Every intermediate algebra in a fraction field is the localization at
the base elements which become units in that intermediate algebra. -/
lemma apm_b00J04_isLocalization_denomSubmonoid
    (R F : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Subalgebra R F) :
    IsLocalization (apm_b00J04_denomSubmonoid R F S) S := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact y.property
  · intro z
    obtain ⟨a, b, hb, hz, hbinv⟩ := apm_b00J04_first_conjunct R F S z
    let binv : S := ⟨(algebraMap R F b)⁻¹, hbinv⟩
    have hbunit : IsUnit (algebraMap R S b) := by
      rw [isUnit_iff_exists_inv]
      refine ⟨binv, ?_⟩
      apply Subtype.ext
      change algebraMap R F b * (algebraMap R F b)⁻¹ = 1
      exact mul_inv_cancel₀ ((map_ne_zero_iff _
        (FaithfulSMul.algebraMap_injective R F)).mpr hb)
    let bm : apm_b00J04_denomSubmonoid R F S := ⟨b, hbunit⟩
    refine ⟨(a, bm), ?_⟩
    apply Subtype.ext
    change (z : F) * algebraMap R F b = algebraMap R F a
    rw [hz]
    exact div_mul_cancel₀ _ ((map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective R F)).mpr hb)
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, one_mul]
    apply (FaithfulSMul.algebraMap_injective R F)
    exact congrArg Subtype.val hxy

lemma apm_b00J04_subalgebra_isPrincipalIdealRing
    (R F : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Subalgebra R F) : IsPrincipalIdealRing S := by
  letI : IsLocalization (apm_b00J04_denomSubmonoid R F S) S :=
    apm_b00J04_isLocalization_denomSubmonoid R F S
  constructor
  intro J
  rw [← IsLocalization.map_comap (apm_b00J04_denomSubmonoid R F S) S J]
  infer_instance

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
  PARTIAL boundary (closer hop 3). The Bézout bridge and the entire first
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

  CLOSER HOP 3: solved sibling `b96A04` contains the missing common-denominator
  construction. It is adapted here as
  `apm_b00J04_common_denom_of_fg_submodule`, using
  `IsLocalization.commonDenomOfFinset` and span induction. The specialization
  `apm_b00J04_common_denom_of_finite_subalgebra` maps the finite top submodule
  of `S` into `F` and proves that one nonzero `r : R` clears every element of
  `S`. Thus the finite-generation/common-denominator stage is compiled. What
  remains for the third conjunct is to apply this to the inverse powers forced
  by the first conjunct and deduce that every inverted denominator is a unit,
  hence `S = ⊥`. The independent PID conjunct still requires presenting `S`
  as the corresponding localization or proving ideal map-comap directly; no
  packaged intermediate-subalgebra localization instance was found.

  HOP 4 supplies that missing instance locally. The denominator submonoid is
  the preimage of the units of `S`; the reduced-fraction theorem proves every
  element of `S` has a numerator and a denominator in this submonoid, while
  injectivity follows through `F`. `IsLocalization.map_comap` then writes
  every ideal of `S` as the extension of its contraction, and Mathlib's
  principal-ideal map instance proves it principal. The finite-module clause
  is routed through `IsIntegral.of_finite` and `isIntegrallyClosed_iff`, since
  a PID is integrally closed in its fraction field.
  -/
  refine ⟨apm_b00J04_subalgebra_isPrincipalIdealRing R F S, ?_⟩
  intro hfinite
  letI : Module.Finite R S := hfinite
  apply le_antisymm
  · intro s hs
    change (s : F) ∈ (algebraMap R F).range
    let ss : S := ⟨s, hs⟩
    have hsint : IsIntegral R ss := IsIntegral.of_finite R ss
    have hint : IsIntegral R (s : F) := by
      simpa [ss] using IsIntegral.map (Subalgebra.val S) hsint
    exact (isIntegrallyClosed_iff (R := R) (K := F)).mp inferInstance hint
  · exact bot_le
