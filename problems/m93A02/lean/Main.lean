import Mathlib

/-!
# APM m93A02: a quadratic equation in Banach spaces

## Statement repairs

* In part (a), `L(H) + Q(h,h) = k` is ill-typed because `L(H)` denotes the
  range of `L`; it is minimally repaired to `L h + Q(h,h) = k`.
* The printed strict estimate `‖h‖ < B ‖k‖` cannot hold at `k = 0`.
  It is minimally repaired to `‖h‖ ≤ B ‖k‖`, preserving the requested
  neighbourhood of zero and its quantitative linear bound.

## Encoding questions

None. Part (b) is stated through the explicit counterexample
`L h = (h,0)`, `Q(h₁,h₂) = (0,h₁h₂)` rather than as a false universal claim.
-/

noncomputable section

theorem apm_m93a02
    (H K : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (L : H →ₗ[ℝ] K) (Q : H →ₗ[ℝ] H →ₗ[ℝ] K)
    (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hL_surj : Function.Surjective L)
    (hL_lower : ∀ h : H, δ * ‖h‖ ≤ ‖L h‖)
    (hQ : ∀ h₁ h₂ : H, ‖Q h₁ h₂‖ ≤ M * ‖h₁‖ * ‖h₂‖) :
    (∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ k : K, ‖k‖ < ε →
        ∃ h : H, L h + Q h h = k ∧ ‖h‖ ≤ B * ‖k‖) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ k : ℝ × ℝ, ‖k‖ < ε ∧
        ¬ ∃ h : ℝ, (h, 0) + (0, h * h) = k) := by
  constructor
  · have hL_inj : Function.Injective L := by
      intro x y hxy
      have hz : L (x - y) = 0 := by simpa using sub_eq_zero.mpr hxy
      have hb := hL_lower (x - y)
      rw [hz, norm_zero] at hb
      have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    let e : H ≃ₗ[ℝ] K := LinearEquiv.ofBijective L ⟨hL_inj, hL_surj⟩
    have he_apply (x : H) : e x = L x := rfl
    have he_symm_bound (k : K) : ‖e.symm k‖ ≤ δ⁻¹ * ‖k‖ := by
      have hb := hL_lower (e.symm k)
      rw [← he_apply, e.apply_symm_apply] at hb
      calc
        ‖e.symm k‖ ≤ ‖k‖ / δ := (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hb)
        _ = δ⁻¹ * ‖k‖ := by field_simp
    /-
    Boundary (closer hop 1) for the quantitative contraction argument. The
    plain map `L` is now upgraded to the explicit linear equivalence `e`, and
    `he_symm_bound` compiles the sharp inverse estimate
    `‖e.symm k‖ ≤ δ⁻¹ ‖k‖`. It remains to apply `ContractingWith` on a closed ball
    of radius `2 * ‖k‖ / δ`. The self-map and contraction estimates must handle
    the separate case `M = 0` (the informal constant `δ² / (4M)` is undefined
    there) and package completeness of the ball subtype. Mathlib supplies the
    abstract fixed-point theorem, but no compiled sibling combines it with an
    inverse constructed from a bounded-below plain `LinearMap` in these exact
    conventions.
    -/
    sorry
  · intro ε hε
    refine ⟨(0, ε / 2), ?_, ?_⟩
    · simp [Real.norm_eq_abs, abs_of_pos hε, hε]
    · rintro ⟨h, hh⟩
      have hfirst : h = 0 := by
        simpa using congrArg Prod.fst hh
      have hsecond : h * h = ε / 2 := by
        simpa using congrArg Prod.snd hh
      rw [hfirst] at hsecond
      linarith
