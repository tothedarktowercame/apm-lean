import Mathlib

open Filter MeasureTheory Set

noncomputable section

/-!
# APM a01A01

## Statement repairs

None.

## Encoding notes

`apmLimsupInfinite u` is the cofinal quantified characterization of
`limsup u = +∞`: every real height is exceeded arbitrarily far out in the
sequence. The higher-dimensional domain is the genuine Euclidean space
`EuclideanSpace ℝ (Fin d)`, with its Lebesgue measure.
-/

def apmLimsupInfinite (u : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ u k

/-! ## The 1D typewriter sequence with growing height

For index `k`, decode `(a, b) = Nat.unpair k`, set `n = a + b + 1`, `j = b`.
Then `j < n` always. The function is `√n · 𝟙_{[j/n, (j+1)/n]}`.
-/

/-- The stage: `n = (Nat.unpair k).1 + (Nat.unpair k).2 + 1`. -/
def twStage (k : ℕ) : ℕ :=
  (Nat.unpair k).1 + (Nat.unpair k).2 + 1

/-- The position within the stage: `j = (Nat.unpair k).2`. -/
def twPos (k : ℕ) : ℕ :=
  (Nat.unpair k).2

/-- The 1D typewriter function. -/
def typewriter1d (k : ℕ) : ℝ → ℝ := fun x =>
  Real.sqrt (twStage k) *
    Set.indicator (Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k))
      (fun _ => (1 : ℝ)) x

/-- The position is always less than the stage. -/
lemma twPos_lt_twStage (k : ℕ) : twPos k < twStage k := by
  show (Nat.unpair k).2 < (Nat.unpair k).1 + (Nat.unpair k).2 + 1
  omega

/-- The stage goes to infinity as k → ∞. -/
lemma twStage_tendsto_atTop : Tendsto twStage atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro n₀
  refine ⟨max (n₀^2) 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  have hsq : k < twStage k ^ 2 := twStage_sq_gt k hk1
  have hn0sq : n₀^2 ≤ max (n₀^2) 1 := le_max_left _ _
  have hk_ge : n₀^2 ≤ k := hn0sq.trans hk
  nlinarith [sq_nonneg (twStage k), sq_nonneg n₀]

/-- Key bound: `twStage k` squared exceeds `k`. -/
lemma twStage_sq_gt (k : ℕ) (hk : 1 ≤ k) : k < twStage k ^ 2 := by
  have key : ∀ a b : ℕ, Nat.pair a b < ((Nat.unpair (Nat.pair a b)).1 + (Nat.unpair (Nat.pair a b)).2 + 1)^2 := by
    intro a b
    have h := Nat.unpair_pair a b
    rw [h]
    unfold Nat.pair
    split_ifs with h
    · nlinarith [sq_nonneg a, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_nonneg b]
  have := key (Nat.unpair k).1 (Nat.unpair k).2
  rwa [Nat.pair_unpair] at this

/-- Integrability of each typewriter function. -/
lemma typewriter1d_integrable (k : ℕ) :
    IntegrableOn (typewriter1d k) (Icc (0 : ℝ) 1) volume := by
  -- typewriter1d k is nonneg, measurable, and bounded by √n on [0,1] which has measure 1
  have hsm : AEStronglyMeasurable (typewriter1d k) (volume.restrict (Icc (0 : ℝ) 1)) := by
    unfold typewriter1d twStage twPos
    exact (StronglyMeasurable.const_mul
      (StronglyMeasurable.indicator stronglyMeasurable_const measurableSet_Icc) _).aestronglyMeasurable
  have hnn : ∀ x, 0 ≤ typewriter1d k x := typewriter1d_nonneg k
  -- Bound: typewriter1d k x ≤ √n for all x
  have hle : ∀ x, typewriter1d k x ≤ Real.sqrt (twStage k) := by
    intro x
    show Real.sqrt (twStage k) *
        Set.indicator (Icc ((twPos k : ℝ) / twStage k)
          (((twPos k + 1 : ℕ) : ℝ) / twStage k)) (fun _ => (1 : ℝ)) x ≤
      Real.sqrt (twStage k)
    rw [Set.indicator_apply]
    split_ifs
    · simp [Real.sqrt_nonneg]
    · exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (by norm_num)
  refine ⟨hsm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (h := Filter.Eventually.of_forall hnn)]
  calc ∫⁻ x, ENNReal.ofReal (typewriter1d k x) ∂(volume.restrict (Icc (0 : ℝ) 1))
      ≤ ∫⁻ x, ENNReal.ofReal (Real.sqrt (twStage k)) ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal (hle x)
    _ = ENNReal.ofReal (Real.sqrt (twStage k)) * (volume (Icc (0 : ℝ) 1)).toReal := by
        rw [lintegral_const_toReal_eq]
    _ < ⊤ := by
        rw [Real.volume_Icc]
        simp [ENNReal.ofReal_lt_top]

/-- Nonnegativity. -/
lemma typewriter1d_nonneg (k : ℕ) (x : ℝ) : 0 ≤ typewriter1d k x := by
  show 0 ≤ Real.sqrt (twStage k) *
    Set.indicator (Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k))
      (fun _ => (1 : ℝ)) x
  rw [Set.indicator_apply]
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) zero_le_one
  · exact mul_nonneg (Real.sqrt_nonneg _) le_rfl

/-- Integral equals `√n / n` where `n = twStage k`. -/
lemma integral_typewriter1d (k : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, typewriter1d k x ∂volume
      = Real.sqrt (twStage k) / twStage k := by
  have hn : 0 < twStage k := by
    show 0 < (Nat.unpair k).1 + (Nat.unpair k).2 + 1; omega
  have hj : twPos k < twStage k := twPos_lt_twStage k
  have hn' : (0 : ℝ) < twStage k := by exact_mod_cast hn
  have hj0 : (0 : ℝ) ≤ (twPos k : ℝ) / twStage k :=
    div_nonneg (by exact_mod_cast (Nat.zero_le _)) hn'.le
  have hj1 : ((twPos k + 1 : ℕ) : ℝ) / twStage k ≤ (1 : ℝ) :=
    (div_le_one hn').mpr (by exact_mod_cast hj)
  have heq : ∀ x, Real.sqrt (twStage k) *
      Set.indicator (Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k))
        (fun _ => (1:ℝ)) x =
      Set.indicator (Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k))
        (fun _ => Real.sqrt (twStage k)) x := by
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> ring
  -- typewriter1d k = Real.sqrt (twStage k) * indicator(...)
  -- which is definitionally equal after unfolding twStage/twPos
  show ∫ x in Icc (0 : ℝ) 1,
    Real.sqrt (twStage k) *
      (Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k)).indicator
        (fun _ => 1) x ∂volume
    = Real.sqrt (twStage k) / twStage k
  simp only [heq]
  rw [setIntegral_indicator
      (t := Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k))
      measurableSet_Icc]
  have hsub : Icc (0 : ℝ) 1 ∩
      Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k)
      = Icc ((twPos k : ℝ) / twStage k) (((twPos k + 1 : ℕ) : ℝ) / twStage k) := by
    apply Set.inter_eq_right.mpr
    rintro x ⟨hx1, hx2⟩
    exact ⟨hj0.trans hx1, hx2.trans hj1⟩
  rw [hsub, setIntegral_const, Measure.real, Real.volume_Icc]
  have hdiff : 0 ≤ (((twPos k + 1 : ℕ) : ℝ) / twStage k) - ((twPos k : ℝ) / twStage k) := by
    have hcast : ((twPos k + 1 : ℕ) : ℝ) = (twPos k : ℝ) + 1 := by exact_mod_cast rfl
    rw [hcast, div_sub_div_same]
    exact div_nonneg (by norm_num) hn'.le
  rw [ENNReal.toReal_ofReal hdiff, smul_eq_mul]
  rw [show ((twPos k + 1 : ℕ) : ℝ) = (twPos k : ℝ) + 1 from by exact_mod_cast rfl]
  push_cast
  field_simp
  ring

/-- The integrals tend to zero. -/
lemma tendsto_typewriter1d :
    Tendsto (fun k => ∫ x in Icc (0 : ℝ) 1, typewriter1d k x ∂volume)
      atTop (nhds 0) := by
  -- twStage k → ∞
  have hstage_tendsto : Tendsto twStage atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro n₀
    refine ⟨max (n₀^2) 1, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := le_of_max_le_right hk
    have hsq : k < twStage k ^ 2 := twStage_sq_gt k hk1
    have hn0sq : n₀^2 ≤ max (n₀^2) 1 := le_max_left _ _
    have hk_ge : n₀^2 ≤ k := hn0sq.trans hk
    nlinarith [sq_nonneg (twStage k), sq_nonneg n₀]
  -- integral = √(twStage k) / twStage k = 1/√(twStage k) for twStage k ≥ 1
  -- Use squeeze: 0 ≤ integral ≤ 1, and the bound 1/√(twStage k) → 0
  -- Actually simplest: just show the integral is 0 ≤ g k where g → 0.
  -- We have √n/n ≤ 1/√1 = 1 trivially, but we need a bound that → 0.
  -- √n/n = 1/√n ≤ 1/√(twStage k). And twStage k → ∞ so 1/√(twStage k) → 0.
  -- Use squeeze with 0 ≤ f ≤ g, g → 0.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
  · -- Tendsto (fun k => 1 / √(twStage k)) atTop (nhds 0)
    have hsqrt : Tendsto (fun k => Real.sqrt (twStage k)) atTop atTop := by
      have hcast : Tendsto (fun k => (twStage k : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop : Tendsto Nat.cast atTop atTop).comp hstage_tendsto
      exact Real.tendsto_sqrt_atTop.comp hcast
    exact tendsto_inv_atTop_zero.comp hsqrt
  · -- 0 ≤ integral
    intro k
    show 0 ≤ ∫ x in Icc (0 : ℝ) 1, typewriter1d k x ∂volume
    rw [integral_typewriter1d]
    exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
  · -- integral ≤ (√(twStage k))⁻¹
    intro k
    show ∫ x in Icc (0 : ℝ) 1, typewriter1d k x ∂volume ≤ (Real.sqrt (twStage k))⁻¹
    rw [integral_typewriter1d]
    have hkpos : (0 : ℝ) < twStage k := by
      have : 0 < (Nat.unpair k).1 + (Nat.unpair k).2 + 1 := by omega
      exact_mod_cast this
    have hsq : Real.sqrt (twStage k) * Real.sqrt (twStage k) = twStage k :=
      Real.mul_self_sqrt (le_trans (by norm_num) hkpos)
    -- Goal: √n / n ≤ (√n)⁻¹
    -- √n / n = √n / (√n * √n) = 1/√n = (√n)⁻¹
    rw [div_eq_inv_mul, ← hsq, mul_comm (Real.sqrt (twStage k)), inv_mul_cancel_right₀]
    · exact le_refl _
    · exact ne_of_gt (Real.sqrt_pos.mpr hkpos)

/-- The limsup at every point of `[0,1]` is infinite. -/
lemma limsup_typewriter1d (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    apmLimsupInfinite (fun k => typewriter1d k x) := by
  intro M N
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  -- Choose n₀ large enough: √n₀ ≥ max 0 M and ((n₀-1)/2)² ≥ N
  set mM : ℕ := Nat.ceil (max 0 M)
  set n₀ : ℕ := max (max (mM^2 + 1) (2 * N + 3)) 3
  have hn₀_pos : 0 < n₀ := by omega
  have hn₀_ge_mM : mM^2 + 1 ≤ n₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn₀_ge_N : 2 * N + 3 ≤ n₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  -- j = min(⌊x * n₀⌋₊, n₀ - 1) so j < n₀ always
  set j : ℕ := min (Nat.floor (x * n₀)) (n₀ - 1)
  have hj_le_floor : j ≤ Nat.floor (x * n₀) := Nat.min_le_left _ _
  have hj_le_pred : j ≤ n₀ - 1 := Nat.min_le_right _ _
  have hj_lt : j < n₀ := by omega
  set a : ℕ := n₀ - 1 - j
  have ha_j : a + j = n₀ - 1 := by omega
  set k : ℕ := Nat.pair a j
  have hunpair : Nat.unpair k = (a, j) := Nat.unpair_pair a j
  have hstage : twStage k = n₀ := by
    show (Nat.unpair k).1 + (Nat.unpair k).2 + 1 = n₀
    rw [hunpair]; omega
  have hpos_k : twPos k = j := by
    show (Nat.unpair k).2 = j; rw [hunpair]
  use k
  constructor
  · -- k ≥ N: since a + j = n₀-1, one of them ≥ (n₀-1)/2 ≥ N+1
    -- k = if a < j then j² + a else a² + a + j
    -- In either case k ≥ ((n₀-1)/2)² ≥ (N+1)² ≥ N
    have hhalf : (n₀ - 1) / 2 ≥ N + 1 := by omega
    have hk_ge : k ≥ ((n₀ - 1) / 2)^2 := by
      unfold_let k Nat.pair
      split_ifs with hlt
      · -- a < j: k = j² + a; j ≥ (n₀-1)/2
        have : j ≥ (n₀ - 1) / 2 := by omega
        omega
      · -- a ≥ j: k = a² + a + j; a ≥ (n₀-1)/2
        have : a ≥ (n₀ - 1) / 2 := by omega
        omega
    calc N ≤ (N + 1)^2 := by omega
      _ ≤ ((n₀ - 1) / 2)^2 := Nat.pow_le_pow_of_le_left hhalf 2
      _ ≤ k := hk_ge
  · -- M ≤ typewriter1d k x = √n₀ (since x ∈ Icc(j/n₀, (j+1)/n₀))
    -- Lower bound: j/n₀ ≤ x
    have hj_div_le : (j : ℝ) / n₀ ≤ x := by
      have hj_real : (j : ℝ) ≤ Nat.floor (x * n₀) := by exact_mod_cast hj_le_floor
      have hfloor_le : (Nat.floor (x * n₀) : ℝ) ≤ x * n₀ := by
        exact Nat.floor_le (by positivity)
      have hle : (j : ℝ) ≤ x * n₀ := hj_real.trans hfloor_le
      have : (j : ℝ) / n₀ ≤ x * n₀ / n₀ := div_le_div_right hle (by exact_mod_cast hn₀_pos)
      rwa [mul_div_assoc, div_self (by exact_mod_cast hn₀_pos.ne')] at this
    -- Upper bound: x ≤ (j+1)/n₀
    have hx_div_le : x ≤ ((j + 1 : ℕ) : ℝ) / n₀ := by
      by_cases hj_eq_pred : j = n₀ - 1
      · -- j = n₀ - 1: (j+1)/n₀ = n₀/n₀ = 1 ≥ x
        rw [hj_eq_pred]
        have h01 : ((n₀ - 1 + 1 : ℕ) : ℝ) / n₀ = (1 : ℝ) := by
          rw [show n₀ - 1 + 1 = n₀ from by omega]
          push_cast [div_self (by exact_mod_cast hn₀_pos.ne')]
        rw [h01]; exact hx1
      · -- j < n₀ - 1, so min gives j = Nat.floor (x * n₀)
        have hj_floor : j = Nat.floor (x * n₀) := by
          unfold_let j
          rcases Nat.min_eq_or (Nat.floor (x * n₀)) (n₀ - 1) with h | h
          · exact h
          · exfalso; apply hj_eq_pred
            unfold_let j at *
            rw [h]
        -- x * n₀ < Nat.floor(x*n₀) + 1 = j + 1
        have hlt : x * n₀ < ((j + 1 : ℕ) : ℝ) := by
          rw [← hj_floor]
          exact_mod_cast (Nat.lt_floor_add_one (by positivity))
        have : x ≤ ((j + 1 : ℕ) : ℝ) / n₀ := by
          rw [div_le_iff_right (by exact_mod_cast hn₀_pos)]
          exact_mod_cast (le_of_lt hlt)
        exact this
    -- x ∈ Icc(j/n₀, (j+1)/n₀), so typewriter1d k x = √n₀
    have hmem : x ∈ Icc ((j : ℝ) / n₀) (((j + 1 : ℕ) : ℝ) / n₀) :=
      ⟨hj_div_le, hx_div_le⟩
    have hval : typewriter1d k x = Real.sqrt n₀ := by
      show Real.sqrt (twStage k) *
          Set.indicator (Icc ((twPos k : ℝ) / twStage k)
            (((twPos k + 1 : ℕ) : ℝ) / twStage k)) (fun _ => (1 : ℝ)) x = Real.sqrt n₀
      rw [hstage, hpos_k, Set.indicator_of_mem hmem, mul_one]
    rw [hval]
    -- √n₀ ≥ M: since n₀ ≥ mM² + 1 and mM ≥ max 0 M
    by_cases hM : 0 ≤ M
    · -- M ≤ mM (ceil), so M² ≤ mM² ≤ n₀
      have hM_le_mM : M ≤ mM := by
        have : max 0 M = M := max_eq_right hM
        rw [show mM = Nat.ceil M from by rw [this]]
        exact Nat.le_ceil M
      have hM_sq : M^2 ≤ (mM : ℝ)^2 := pow_le_pow_two hM_le_mM
      have hmM_sq : (mM : ℝ)^2 ≤ n₀ := by
        have : (mM^2 : ℝ) ≤ ((mM^2 + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ _)
        exact this.trans (by exact_mod_cast hn₀_ge_mM)
      have hM_sq_le : M^2 ≤ n₀ := hM_sq.trans hmM_sq
      exact Real.le_sqrt_of_sq_le (by exact_mod_cast hM_sq_le)
    · -- M < 0: √n₀ ≥ 0 > M
      exact le_trans (Real.sqrt_nonneg _) (le_of_lt hM)

theorem apm_a01a01 :
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, IntegrableOn (f k) (Icc (0 : ℝ) 1) volume) ∧
      (∀ k x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f k x) ∧
      (∀ x, x ∈ Icc (0 : ℝ) 1 → apmLimsupInfinite (fun k ↦ f k x)) ∧
      Tendsto (fun k ↦ ∫ x in Icc (0 : ℝ) 1, f k x ∂volume)
        atTop (nhds 0)) ∧
    (∀ d : ℕ, 0 < d →
      ∃ f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ k, Integrable (f k) volume) ∧
        (∀ k x, 0 ≤ f k x) ∧
        (∀ x, apmLimsupInfinite (fun k ↦ f k x)) ∧
        Tendsto (fun k ↦ ∫ x, f k x ∂volume) atTop (nhds 0)) := by
  sorry
