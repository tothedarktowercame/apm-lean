import Mathlib

/-! # APM m95A01: the Newton--Schulz inverse iteration

## Statement repairs

None.
-/

noncomputable section

open Filter

def m95A01Iterates {𝕜 X : Type*}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A B₀ : X →L[𝕜] X) : ℕ → X →L[𝕜] X
  | 0 => B₀
  | n + 1 => 2 • m95A01Iterates A B₀ n -
      m95A01Iterates A B₀ n * A * m95A01Iterates A B₀ n

lemma m95A01_left_residual {𝕜 X : Type*}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A B₀ : X →L[𝕜] X) (n : ℕ) :
    1 - A * m95A01Iterates A B₀ n = (1 - A * B₀) ^ (2 ^ n) := by
  induction n with
  | zero => simp [m95A01Iterates]
  | succ n ih =>
      rw [m95A01Iterates, pow_succ]
      simp only [two_smul]
      have hstep :
          1 - A * (m95A01Iterates A B₀ n + m95A01Iterates A B₀ n -
            m95A01Iterates A B₀ n * A * m95A01Iterates A B₀ n) =
            (1 - A * m95A01Iterates A B₀ n) ^ 2 := by noncomm_ring
      rw [hstep, ih]
      rw [pow_two, ← pow_add]
      congr 1
      omega

lemma m95A01_right_residual {𝕜 X : Type*}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A B₀ : X →L[𝕜] X) (n : ℕ) :
    1 - m95A01Iterates A B₀ n * A = (1 - B₀ * A) ^ (2 ^ n) := by
  induction n with
  | zero => simp [m95A01Iterates]
  | succ n ih =>
      rw [m95A01Iterates, pow_succ]
      simp only [two_smul]
      have hstep :
          1 - (m95A01Iterates A B₀ n + m95A01Iterates A B₀ n -
            m95A01Iterates A B₀ n * A * m95A01Iterates A B₀ n) * A =
            (1 - m95A01Iterates A B₀ n * A) ^ 2 := by noncomm_ring
      rw [hstep, ih]
      rw [pow_two, ← pow_add]
      congr 1
      omega

theorem apm_m95a01
    (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (A B₀ : X →L[𝕜] X)
    (hAB : ‖A * B₀ - 1‖ < 1) (hBA : ‖B₀ * A - 1‖ < 1) :
    (Tendsto (fun n => A * m95A01Iterates A B₀ n) atTop (nhds 1) ∧
      Tendsto (fun n => m95A01Iterates A B₀ n * A) atTop (nhds 1)) ∧
    (Function.Surjective A →
      ∃ K : ℝ, ∀ n : ℕ, ‖m95A01Iterates A B₀ n‖ < K) ∧
    (Function.Surjective A →
      ∃ Ainv : X →L[𝕜] X,
        A * Ainv = 1 ∧ Ainv * A = 1 ∧
        ∀ x : X,
          Tendsto (fun n => m95A01Iterates A B₀ n x) atTop (nhds (Ainv x))) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hleft0 : ‖1 - A * B₀‖ < 1 := by
    rw [← norm_neg (1 - A * B₀)]
    simpa using hAB
  have hright0 : ‖1 - B₀ * A‖ < 1 := by
    rw [← norm_neg (1 - B₀ * A)]
    simpa using hBA
  have hleft_res : Tendsto (fun n : ℕ => (1 - A * B₀) ^ (2 ^ n)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hleft0).comp hpow
  have hright_res : Tendsto (fun n : ℕ => (1 - B₀ * A) ^ (2 ^ n)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hright0).comp hpow
  have hleft : Tendsto (fun n => A * m95A01Iterates A B₀ n) atTop (nhds 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : X →L[𝕜] X)) atTop (nhds 1) :=
      tendsto_const_nhds
    have := hc.sub hleft_res
    simpa only [sub_zero] using this.congr' (by
      filter_upwards [] with n
      rw [← m95A01_left_residual A B₀ n]
      abel)
  have hright : Tendsto (fun n => m95A01Iterates A B₀ n * A) atTop (nhds 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : X →L[𝕜] X)) atTop (nhds 1) :=
      tendsto_const_nhds
    have := hc.sub hright_res
    simpa only [sub_zero] using this.congr' (by
      filter_upwards [] with n
      rw [← m95A01_right_residual A B₀ n]
      abel)
  have huAB : IsUnit (A * B₀) := by
    simpa [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hleft0
  have huBA : IsUnit (B₀ * A) := by
    simpa [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hright0
  have hA_surj : Function.Surjective A := by
    have hp := (ContinuousLinearMap.isUnit_iff_bijective.mp huAB).2
    intro y
    obtain ⟨x, hx⟩ := hp y
    exact ⟨B₀ x, by simpa using hx⟩
  have hA_inj : Function.Injective A := by
    have hp := (ContinuousLinearMap.isUnit_iff_bijective.mp huBA).1
    intro x y hxy
    apply hp
    simpa using congrArg B₀ hxy
  have huA : IsUnit A :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hA_inj, hA_surj⟩
  obtain ⟨Ainv, hAAinv, hAinvA⟩ := isUnit_iff_exists.mp huA
  have hiter : Tendsto (m95A01Iterates A B₀) atTop (nhds Ainv) := by
    have hc : Tendsto (fun _ : ℕ => Ainv) atTop (nhds Ainv) := tendsto_const_nhds
    have hm := hc.mul hleft
    convert hm using 1
    funext n
    rw [← mul_assoc, hAinvA, one_mul]
  refine ⟨⟨hleft, hright⟩, ?_, ?_⟩
  · intro _
    obtain ⟨K, hK⟩ := (Metric.isBounded_range_of_tendsto _ hiter).exists_norm_le
    refine ⟨K + 1, fun n => (hK _ ⟨n, rfl⟩).trans_lt ?_⟩
    linarith
  · intro _
    refine ⟨Ainv, hAAinv, hAinvA, ?_⟩
    intro x
    exact (ContinuousLinearMap.apply 𝕜 X x).continuous.continuousAt.tendsto.comp hiter
