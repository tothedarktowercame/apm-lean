import Mathlib

/-!
# APM b90A02: Free, projective, and flat modules

## Statement repairs

The source permits a noncommutative unital ring and defines flatness for right
modules. Mathlib's `Module.Flat` and its tensor product currently support this
criterion only over commutative semirings (the library records noncommutative
flatness as a TODO). We therefore impose commutativity on `R`; in that setting
left and right module formulations agree.

## Encoding questions

None beyond the declared commutativity repair. Flatness is represented by
Mathlib's tensor-product-based `Module.Flat`, not by a weaker surrogate.
-/

noncomputable section

lemma apm_b90a02_rat_to_int_eq_zero (f : ℚ →ₗ[ℤ] ℤ) (q : ℚ) : f q = 0 := by
  let n : ℕ := (f q).natAbs + 1
  have hn : (n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (f q).natAbs)
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hq : (n : ℤ) • (q / n) = q := by
    change (n : ℚ) * (q / n) = q
    field_simp [hnQ]
  have hdvd : (n : ℤ) ∣ f q := by
    refine ⟨f (q / n), ?_⟩
    calc
      f q = f ((n : ℤ) • (q / n)) := congrArg f hq.symm
      _ = (n : ℤ) • f (q / n) := f.map_smul _ _
      _ = (n : ℤ) * f (q / n) := rfl
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  change (f q).natAbs < n
  simp [n]

theorem apm_b90a02
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    (Module.Free R M → Module.Flat R M) ∧
    (Module.Projective R M → Module.Flat R M) ∧
    Module.Flat ℤ ℚ ∧
    ¬Module.Projective ℤ ℚ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro
    infer_instance
  · intro
    infer_instance
  · infer_instance
  · intro hproj
    letI : Module.Projective ℤ ℚ := hproj
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective ℤ ℚ).out
    have hs0 : s = 0 := by
      ext q i
      exact apm_b90a02_rat_to_int_eq_zero ((Finsupp.lapply i).comp s) q
    have hone := hs (1 : ℚ)
    rw [hs0] at hone
    simpa using hone
