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

private lemma apm_m93a02_quadratic_sub_bound
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Q : H →ₗ[ℝ] H →ₗ[ℝ] K) (M : ℝ)
    (hQ : ∀ h₁ h₂ : H, ‖Q h₁ h₂‖ ≤ M * ‖h₁‖ * ‖h₂‖)
    (x y : H) :
    ‖Q x x - Q y y‖ ≤ M * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hid : Q x x - Q y y = Q (x - y) x + Q y (x - y) := by
    simp
  rw [hid]
  calc
    ‖Q (x - y) x + Q y (x - y)‖ ≤
        ‖Q (x - y) x‖ + ‖Q y (x - y)‖ := norm_add_le _ _
    _ ≤ M * ‖x - y‖ * ‖x‖ + M * ‖y‖ * ‖x - y‖ :=
      add_le_add (hQ _ _) (hQ _ _)
    _ = M * (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

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
    by_cases hM0 : M = 0
    · have hQzero : ∀ x y : H, Q x y = 0 := by
        intro x y
        have hb := hQ x y
        rw [hM0] at hb
        simp only [zero_mul] at hb
        exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
      refine ⟨1, δ⁻¹, by norm_num, inv_pos.mpr hδ, ?_⟩
      intro k hk
      refine ⟨e.symm k, ?_, he_symm_bound k⟩
      rw [hQzero]
      rw [add_zero, ← he_apply, e.apply_symm_apply]
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
      /-
      Boundary (closer hop 2), now restricted to `0 < M`.  The degenerate
      case `M = 0` is completely proved above by taking `h = e.symm k`.
      In addition, `apm_m93a02_quadratic_sub_bound` compiles the exact
      Lipschitz estimate
      `‖Q x x - Q y y‖ ≤ M (‖x‖ + ‖y‖) ‖x-y‖` needed on the ball.

      The remaining assembly is to choose `ε = δ^2/(8*M)` and
      `r = 2*‖k‖/δ`, define `F x = e.symm (k - Q x x)`, prove `F` maps
      `Metric.closedBall 0 r` to itself, and use the displayed estimate plus
      `he_symm_bound` to obtain contraction constant at most `1/2`.
      Mathlib source confirms `Metric.isClosed_closedBall.isComplete` and
      `ContractingWith.exists_fixedPoint'`; siblings `t91A04` and `m96J06`
      demonstrate the abstract API, but neither packages these parameterized
      ball inequalities or the plain-`LinearEquiv` inverse bound.
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
