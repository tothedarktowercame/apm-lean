import Mathlib

/-!
# APM b96A04: Module-theoretic rigidity of a fraction field

## Statement repairs

Part (a) is false when `y = 0`, since then `d * y ∣ y` for every `d`.
We add the intended hypothesis `y ≠ 0`, which is also used by the supplied
informal solution.

## Encoding questions

None. The equality `R = K` is represented invariantly by surjectivity of
`algebraMap R K`, since `R` and its fraction field may be distinct Lean types.
-/

open scoped Pointwise

noncomputable section

private theorem fraction_surjective_of_free_embedding
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F]
    (i : K →ₗ[R] F) (hi : Function.Injective i) :
    Function.Surjective (algebraMap R K) := by
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
  have hbK : algebraMap R K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hbu : IsUnit b := by
    let B := Module.Free.chooseBasis R F
    have hi_one : i (1 : K) ≠ 0 := fun h => one_ne_zero (hi (by simpa using h))
    have hrepr : B.repr (i (1 : K)) ≠ 0 := by
      simpa using B.repr.injective.ne hi_one
    obtain ⟨j, hj⟩ : ∃ j, B.repr (i (1 : K)) j ≠ 0 := by
      by_contra h
      push_neg at h
      apply hrepr
      ext k
      exact h k
    rw [isUnit_iff_exists_inv]
    refine ⟨B.repr (i ((algebraMap R K (b * B.repr (i 1) j))⁻¹)) j, ?_⟩
    apply mul_right_cancel₀ hj
    have hjK : algebraMap R K (B.repr (i 1) j) ≠ 0 := by
      intro h
      apply hj
      exact IsFractionRing.injective R K (by simpa using h)
    have hbaK : algebraMap R K (b * B.repr (i 1) j) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hbK hjK
    have hy : (b * B.repr (i 1) j) •
        i ((algebraMap R K (b * B.repr (i 1) j))⁻¹) = i (1 : K) := by
      rw [← i.map_smul]
      congr 1
      rw [Algebra.smul_def]
      exact mul_inv_cancel₀ hbaK
    have hcoord := congrArg (fun q => B.repr q j) hy
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcoord
  rw [isUnit_iff_exists_inv] at hbu
  obtain ⟨c, hc⟩ := hbu
  refine ⟨a * c, ?_⟩
  have hcK : algebraMap R K b * algebraMap R K c = 1 := by
    simpa [map_mul] using congrArg (algebraMap R K) hc
  rw [map_mul, div_eq_mul_inv, (inv_eq_of_mul_eq_one_right hcK).symm]

private theorem common_denom_of_fg_submodule
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (M : Submodule R K) (hfg : M.FG) :
    ∃ r : R, r ≠ 0 ∧
      ∀ m ∈ M, r • m ∈ Set.range (algebraMap R K) := by
  rw [Submodule.fg_def] at hfg
  obtain ⟨s, hsfin, hs⟩ := hfg
  let t : Finset K := hsfin.toFinset
  let r0 : nonZeroDivisors R :=
    IsLocalization.commonDenomOfFinset (nonZeroDivisors R) t
  refine ⟨r0, nonZeroDivisors.coe_ne_zero r0, ?_⟩
  intro m hm
  have hmspan : m ∈ Submodule.span R (t : Set K) := by
    simpa [t, hs] using hm
  have hclear : r0 • m ∈ LinearMap.range (Algebra.linearMap R K) := by
    refine Submodule.span_induction (p := fun z _ =>
      r0 • z ∈ LinearMap.range (Algebra.linearMap R K)) ?_ ?_ ?_ ?_ hmspan
    · intro x hx
      let ix : t := ⟨x, hx⟩
      refine ⟨IsLocalization.integerMultiple (nonZeroDivisors R) t id ix, ?_⟩
      change algebraMap R K _ = _
      rw [IsLocalization.map_integerMultiple]
      rfl
    · simp
    · intro x y _ _ hx hy
      simpa [smul_add] using
        (LinearMap.range (Algebra.linearMap R K)).add_mem hx hy
    · intro a x _ hx
      rw [smul_comm]
      exact (LinearMap.range (Algebra.linearMap R K)).smul_mem a hx
  simpa [LinearMap.mem_range] using hclear

theorem apm_b96a04
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (∀ y d : R, y ≠ 0 → d * y ∣ y → IsUnit d) ∧
    (∀ (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F],
      (∀ (m : F) (r : R), m ≠ 0 → r • m = 0 → r = 0) ∧
      ∀ (m : F), m ≠ 0 → ∀ d : R, d ≠ 0 → ¬IsUnit d →
        ∃ x : R, x ≠ 0 ∧ ¬∃ y : F, (d * x) • y = m) ∧
    (∀ (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F],
      (∃ i : K →ₗ[R] F, Function.Injective i) →
        Function.Surjective (algebraMap R K)) ∧
    (Module.Projective R K → Function.Surjective (algebraMap R K)) ∧
    (∀ I : Ideal R, I ≠ ⊤ → Module.Projective R (R ⧸ I) → I = ⊥) ∧
    (∀ M : Submodule R K,
      (∀ a : R, algebraMap R K a ∈ M) → M.FG →
        ∃ r : R, r ≠ 0 ∧
          ∀ m ∈ M, r • m ∈ Set.range (algebraMap R K)) ∧
    (Module.Finite R K → Function.Surjective (algebraMap R K)) := by
  constructor
  · intro y d hy hd
    obtain ⟨c, hc⟩ := hd
    rw [isUnit_iff_exists_inv]
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ hy
    simpa [mul_assoc, mul_left_comm] using hc.symm
  constructor
  · intro F _ _ _
    constructor
    · intro m r hm hr
      exact (smul_eq_zero.mp hr).resolve_right hm
    · intro m hm d hd hdu
      let b := Module.Free.chooseBasis R F
      have hrepr : b.repr m ≠ 0 := by
        simpa using b.repr.injective.ne hm
      obtain ⟨j, hj⟩ : ∃ j, b.repr m j ≠ 0 := by
        by_contra h
        push_neg at h
        apply hrepr
        ext i
        exact h i
      refine ⟨b.repr m j, hj, ?_⟩
      rintro ⟨y, hy⟩
      apply hdu
      rw [isUnit_iff_exists_inv]
      refine ⟨b.repr y j, ?_⟩
      apply mul_left_cancel₀ hj
      have hcoord := congrArg (fun q => b.repr q j) hy
      simpa [mul_assoc, mul_left_comm] using hcoord
  constructor
  · rintro F _ _ _ ⟨i, hi⟩
    exact fraction_surjective_of_free_embedding R K F i hi
  constructor
  · intro hK
    obtain ⟨F, _, _, _, i, s, his⟩ := Module.Projective.iff_split.mp hK
    letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
    apply fraction_surjective_of_free_embedding R K F i
    exact LinearMap.injective_of_comp_eq_id i s his
  constructor
  · intro I hI hP
    letI : Module.Projective R (R ⧸ I) := hP
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    -- Mathlib's projective lifting API splits the canonical quotient map
    -- directly; no transport from an abstract free-module splitting is needed.
    obtain ⟨s, hs⟩ :=
      LinearMap.exists_rightInverse_of_surjective I.mkQ
        (LinearMap.range_eq_top.mpr I.mkQ_surjective)
    let e : R := s (1 : R ⧸ I)
    have he : e ≠ 0 := by
      intro he0
      have := LinearMap.congr_fun hs (1 : R ⧸ I)
      simp [e, he0] at this
    apply le_antisymm
    · intro x hx
      change x = 0
      have hqx : I.mkQ x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      have hse : x * e = 0 := by
        have hmap := congrArg s hqx
        have hqsmul : I.mkQ x = x • (1 : R ⧸ I) := by
          simp [Algebra.smul_def]
        rw [hqsmul, s.map_smul] at hmap
        simpa [e, smul_eq_mul] using hmap
      exact (mul_eq_zero.mp hse).resolve_right he
    · exact bot_le
  constructor
  · intro M _ hfg
    exact common_denom_of_fg_submodule R K M hfg
  · intro hfinite
    letI : Module.Finite R K := hfinite
    obtain ⟨r, hr, hclear⟩ :=
      common_denom_of_fg_submodule R K (⊤ : Submodule R K) Module.Finite.fg_top
    intro z
    obtain ⟨a, ha⟩ := hclear ((algebraMap R K r)⁻¹ * z) (by simp)
    refine ⟨a, ?_⟩
    have hrK : algebraMap R K r ≠ 0 := by
      simpa using (IsFractionRing.injective R K).ne hr
    simpa [Algebra.smul_def, hrK] using ha
