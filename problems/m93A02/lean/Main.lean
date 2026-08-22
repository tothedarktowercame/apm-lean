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

/-- The numerical estimates behind the invariant ball and its contraction
constant.  Here `q` will be `‖k‖` and `2*q/δ` the ball radius. -/
private lemma apm_m93a02_contraction_constants
    {δ M q : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hq : 0 ≤ q)
    (hqsmall : q < δ ^ 2 / (8 * M)) :
    δ⁻¹ * (q + M * (2 * q / δ) ^ 2) ≤ 2 * q / δ ∧
      δ⁻¹ * M * (2 * (2 * q / δ)) < 1 / 2 := by
  constructor
  · rw [inv_mul_le_iff₀ hδ]
    have hMq : 8 * M * q < δ ^ 2 := by
      rw [lt_div_iff₀ (by positivity : 0 < 8 * M)] at hqsmall
      nlinarith
    have hδ0 : δ ≠ 0 := ne_of_gt hδ
    field_simp [hδ0]
    nlinarith
  · rw [show δ⁻¹ * M * (2 * (2 * q / δ)) =
        δ⁻¹ * (M * (2 * (2 * q / δ))) by ring]
    rw [inv_mul_lt_iff₀ hδ]
    have hMq : 8 * M * q < δ ^ 2 := by
      rw [lt_div_iff₀ (by positivity : 0 < 8 * M)] at hqsmall
      nlinarith
    have hδ0 : δ ≠ 0 := ne_of_gt hδ
    field_simp [hδ0]
    nlinarith

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
      refine ⟨δ ^ 2 / (8 * M), 2 * δ⁻¹, ?_, by positivity, ?_⟩
      · positivity
      intro k hk
      let r : ℝ := 2 * ‖k‖ / δ
      let F : H → H := fun x => e.symm (k - Q x x)
      have hc := apm_m93a02_contraction_constants hδ hMpos (norm_nonneg k) hk
      have hmaps : Set.MapsTo F (Metric.closedBall 0 r) (Metric.closedBall 0 r) := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
        calc
          ‖F x‖ ≤ δ⁻¹ * ‖k - Q x x‖ := he_symm_bound _
          _ ≤ δ⁻¹ * (‖k‖ + ‖Q x x‖) := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ δ⁻¹ * (‖k‖ + M * r ^ 2) := by
            gcongr
            calc
              ‖Q x x‖ ≤ M * ‖x‖ * ‖x‖ := hQ _ _
              _ ≤ M * r * r := by gcongr
              _ = M * r ^ 2 := by ring
          _ ≤ r := by simpa [r] using hc.1
      have hcontract : ContractingWith (1 / 2 : NNReal)
          (Set.MapsTo.restrict F (Metric.closedBall 0 r) (Metric.closedBall 0 r) hmaps) := by
        constructor
        · norm_num
        · rw [lipschitzWith_iff_dist_le_mul]
          intro x y
          change dist (F x) (F y) ≤ (1 / 2 : ℝ) * dist (x : H) y
          rw [dist_eq_norm]
          have hxy := apm_m93a02_quadratic_sub_bound Q M hQ x y
          have hx : ‖(x : H)‖ ≤ r := by
            simpa only [dist_zero_right] using (Metric.mem_closedBall.mp x.property)
          have hy : ‖(y : H)‖ ≤ r := by
            simpa only [dist_zero_right] using (Metric.mem_closedBall.mp y.property)
          have hcoef : δ⁻¹ * M * (‖(x : H)‖ + ‖(y : H)‖) ≤ 1 / 2 := by
            apply le_of_lt
            calc
              δ⁻¹ * M * (‖(x : H)‖ + ‖(y : H)‖) ≤ δ⁻¹ * M * (r + r) := by gcongr
              _ = δ⁻¹ * M * (2 * r) := by ring
              _ < 1 / 2 := by simpa only [r] using hc.2
          have hnorm : ‖(k - Q x x) - (k - Q y y)‖ = ‖Q x x - Q y y‖ := by
            calc
              ‖(k - Q x x) - (k - Q y y)‖ = ‖-(Q x x - Q y y)‖ := by
                congr 1
                abel
              _ = ‖Q x x - Q y y‖ := norm_neg _
          calc
            ‖F x - F y‖ ≤ δ⁻¹ * ‖(k - Q x x) - (k - Q y y)‖ := by
              simpa [F, ← map_sub] using he_symm_bound ((k - Q x x) - (k - Q y y))
            _ = δ⁻¹ * ‖Q x x - Q y y‖ := by rw [hnorm]
            _ ≤ δ⁻¹ * (M * (‖(x : H)‖ + ‖(y : H)‖) * ‖(x : H) - y‖) := by gcongr
            _ ≤ (1 / 2 : ℝ) * ‖(x : H) - y‖ := by
              simpa only [mul_assoc] using
                mul_le_mul_of_nonneg_right hcoef (norm_nonneg ((x : H) - y))
            _ = (1 / 2 : NNReal) * dist (x : H) y := by
              simp [dist_eq_norm]
      have hzero : (0 : H) ∈ Metric.closedBall 0 r := by
        rw [Metric.mem_closedBall, dist_self]
        dsimp [r]
        positivity
      obtain ⟨h, hhmem, hhfix, -⟩ :=
        hcontract.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps hzero (by simp)
      refine ⟨h, ?_, ?_⟩
      · have hh : e.symm (k - Q h h) = h := hhfix
        symm at hh
        have := congrArg e hh
        simp only [e.apply_symm_apply] at this
        rw [he_apply] at this
        exact (eq_sub_iff_add_eq).mp this
      · have hh : ‖h‖ ≤ r := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hhmem
        simpa [r, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
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
