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

private abbrev apmB03Poly : ℤ[X] := X ^ 2 - C (5 : ℤ)

private def apmB03ToZ : AdjoinRoot apmB03Poly →+* Zsqrtd 5 :=
  AdjoinRoot.lift (Int.castRingHom _) Zsqrtd.sqrtd (by
    simp only [apmB03Poly, eval₂_sub, eval₂_pow, eval₂_X, map_ofNat]
    rw [show Zsqrtd.sqrtd ^ 2 = (5 : Zsqrtd 5) by
      simpa [pow_two] using Zsqrtd.dmuld (d := 5)]
    norm_num)

private def apmB03FromZ : Zsqrtd 5 →+* AdjoinRoot apmB03Poly :=
  Zsqrtd.lift ⟨AdjoinRoot.root apmB03Poly, by
    have h := AdjoinRoot.eval₂_root apmB03Poly
    change eval₂ (AdjoinRoot.of apmB03Poly) (AdjoinRoot.root apmB03Poly)
      (X ^ 2 - C 5) = 0 at h
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_ofNat, map_ofNat] at h
    simpa [pow_two] using (sub_eq_zero.mp h)⟩

private theorem apmB03RootSq :
    AdjoinRoot.root apmB03Poly * AdjoinRoot.root apmB03Poly = 5 := by
  have h := AdjoinRoot.eval₂_root apmB03Poly
  change eval₂ (AdjoinRoot.of apmB03Poly) (AdjoinRoot.root apmB03Poly)
    (X ^ 2 - C 5) = 0 at h
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_ofNat, map_ofNat] at h
  simpa [pow_two] using (sub_eq_zero.mp h)

private def apmB03Equiv : AdjoinRoot apmB03Poly ≃+* Zsqrtd 5 :=
  RingEquiv.ofRingHom apmB03ToZ apmB03FromZ
    (by apply Zsqrtd.hom_ext; simp [apmB03ToZ, apmB03FromZ])
    (by
      apply AdjoinRoot.ringHom_ext
      · ext z
        simp [apmB03ToZ, apmB03FromZ]
      · simp [apmB03ToZ, apmB03FromZ])

-- Uses the Mathlib `Zsqrtd` normal form: the real coordinate makes the final
-- non-membership assertion the parity contradiction `2 * y.re = 1`.
private theorem apmB03NotIntegrallyClosed :
    ¬ IsIntegrallyClosed (AdjoinRoot apmB03Poly) := by
  letI : Zsqrtd.Nonsquare 5 := ⟨by
    intro n hn
    have hn' : (n : ℤ) * n = 5 := by exact_mod_cast hn.symm
    have hle : n ≤ 2 := by nlinarith
    interval_cases n <;> norm_num at hn⟩
  letI : Nontrivial (AdjoinRoot apmB03Poly) := ⟨0, 1, by
    intro h
    have := congrArg apmB03Equiv h
    simpa using this⟩
  letI : NoZeroDivisors (AdjoinRoot apmB03Poly) :=
    ⟨fun {a b} hab ↦ by
      have hz : apmB03Equiv a * apmB03Equiv b = 0 := by
        simpa using congrArg apmB03Equiv hab
      rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero hz with ha | hb
      · exact Or.inl (apmB03Equiv.injective (by simpa using ha))
      · exact Or.inr (apmB03Equiv.injective (by simpa using hb))⟩
  letI : IsDomain (AdjoinRoot apmB03Poly) := NoZeroDivisors.to_isDomain _
  letI : CharZero (AdjoinRoot apmB03Poly) :=
    charZero_of_injective_ringHom
      (f := apmB03Equiv.symm.toRingHom) apmB03Equiv.symm.injective
  intro hclosed
  let K := FractionRing (AdjoinRoot apmB03Poly)
  let r : AdjoinRoot apmB03Poly := AdjoinRoot.root apmB03Poly
  let x : K := algebraMap _ K (1 + r) / (2 : K)
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hr : r * r = 5 := apmB03RootSq
  have hxpoly : x ^ 2 - x - 1 = 0 := by
    dsimp [x]
    dsimp [K] at htwo ⊢
    field_simp [htwo]
    have hrK :
        (algebraMap (AdjoinRoot apmB03Poly)
          (FractionRing (AdjoinRoot apmB03Poly)) r) ^ 2 = 5 := by
      rw [pow_two, ← map_mul, hr]
      simp only [map_ofNat]
    simp only [map_add, map_one]
    linear_combination hrK
  have hxint : IsIntegral (AdjoinRoot apmB03Poly) x := by
    let q : (AdjoinRoot apmB03Poly)[X] := X ^ 2 - X - 1
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      convert
        (monic_X_pow_add (R := AdjoinRoot apmB03Poly) (n := 2) (p := -X - 1)
          (by compute_degree <;> norm_num)) using 1 <;> ring
    · simpa [q, aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_ofNat] using hxpoly
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp hclosed hxint
  have hclear : (2 : AdjoinRoot apmB03Poly) * y = 1 + r := by
    apply IsFractionRing.injective (AdjoinRoot apmB03Poly) K
    rw [map_mul, map_ofNat, hy]
    dsimp [x]
    dsimp [K] at htwo ⊢
    field_simp
  have hz := congrArg apmB03Equiv hclear
  have hmap2 : apmB03Equiv (2 : AdjoinRoot apmB03Poly) = (2 : Zsqrtd 5) := by
    change apmB03ToZ ((AdjoinRoot.of apmB03Poly) 2) = 2
    exact DFunLike.congr_fun (AdjoinRoot.lift_comp_of (h := apmB03ToZ._proof_1)) 2
  have hmaproot : apmB03Equiv r = Zsqrtd.sqrtd := by
    change apmB03ToZ (AdjoinRoot.root apmB03Poly) = Zsqrtd.sqrtd
    exact AdjoinRoot.lift_root apmB03ToZ._proof_1
  have hz' : (2 : Zsqrtd 5) * apmB03Equiv y = 1 + Zsqrtd.sqrtd := by
    simpa only [map_mul, map_add, map_one, hmap2, hmaproot] using hz
  have hre := congrArg Zsqrtd.re hz'
  norm_num at hre
  omega

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
    exact apmB03NotIntegrallyClosed
