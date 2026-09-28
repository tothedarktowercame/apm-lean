import Mathlib

open Filter MeasureTheory Set

noncomputable section

/-!
# APM a01A01

## Statement repairs

None.

## Encoding notes

The condition `∀ M N, ∃ k ≥ N, M ≤ f k x` is the cofinal quantified
characterization of `limsup (fun k ↦ f k x) = +∞`. The higher-dimensional
domain is the genuine Euclidean space `EuclideanSpace ℝ (Fin d)` with its
Lebesgue measure.
-/

/-- Stage number for the diagonal enumeration of pairs of naturals. -/
def apm_a01A01_stage (k : ℕ) : ℕ :=
  (Nat.unpair k).1 + (Nat.unpair k).2 + 1

/-- Position inside a diagonally enumerated stage. -/
def apm_a01A01_position (k : ℕ) : ℕ :=
  (Nat.unpair k).2

lemma apm_a01A01_position_lt_stage (k : ℕ) :
    apm_a01A01_position k < apm_a01A01_stage k := by
  show (Nat.unpair k).2 < (Nat.unpair k).1 + (Nat.unpair k).2 + 1
  omega

lemma apm_a01A01_index_lt_stage_sq (k : ℕ) (_hk : 1 ≤ k) :
    k < apm_a01A01_stage k ^ 2 := by
  have key : ∀ a b : ℕ,
      Nat.pair a b <
        ((Nat.unpair (Nat.pair a b)).1 + (Nat.unpair (Nat.pair a b)).2 + 1) ^ 2 := by
    intro a b
    rw [Nat.unpair_pair]
    unfold Nat.pair
    split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b]
  have h := key (Nat.unpair k).1 (Nat.unpair k).2
  rwa [Nat.pair_unpair] at h

lemma apm_a01A01_stage_tendsto_atTop :
    Tendsto apm_a01A01_stage atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro n₀
  refine ⟨max (n₀ ^ 2) 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  have hsq : k < apm_a01A01_stage k ^ 2 :=
    apm_a01A01_index_lt_stage_sq k hk1
  have hk_ge : n₀ ^ 2 ≤ k := (le_max_left _ _).trans hk
  nlinarith [sq_nonneg (apm_a01A01_stage k), sq_nonneg n₀]

/-- The one-dimensional typewriter cell attached to a global index. -/
def apm_a01A01_typewriter1d (k : ℕ) : ℝ → ℝ := fun x =>
  Real.sqrt (apm_a01A01_stage k) *
    Set.indicator
      (Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) / apm_a01A01_stage k))
      (fun _ => (1 : ℝ)) x

lemma apm_a01A01_typewriter1d_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ apm_a01A01_typewriter1d k x := by
  unfold apm_a01A01_typewriter1d
  rw [Set.indicator_apply]
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) zero_le_one
  · simp

lemma apm_a01A01_typewriter1d_integrableOn (k : ℕ) :
    IntegrableOn (apm_a01A01_typewriter1d k) (Icc (0 : ℝ) 1) volume := by
  let C := Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
    (((apm_a01A01_position k + 1 : ℕ) : ℝ) / apm_a01A01_stage k)
  have hC : MeasurableSet C := measurableSet_Icc
  have hCfin : volume C ≠ ⊤ := measure_Icc_lt_top.ne
  have hi : Integrable (C.indicator
      (fun _ : ℝ => Real.sqrt (apm_a01A01_stage k))) volume :=
    (integrableOn_const hCfin).integrable_indicator hC
  apply hi.integrableOn.congr_fun _ measurableSet_Icc
  intro x _
  unfold apm_a01A01_typewriter1d
  dsimp [C]
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> ring

lemma apm_a01A01_integral_typewriter1d (k : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume =
      Real.sqrt (apm_a01A01_stage k) / apm_a01A01_stage k := by
  have hn : 0 < apm_a01A01_stage k := by
    unfold apm_a01A01_stage
    omega
  have hn' : (0 : ℝ) < apm_a01A01_stage k := by exact_mod_cast hn
  have hj := apm_a01A01_position_lt_stage k
  have hj0 : (0 : ℝ) ≤ (apm_a01A01_position k : ℝ) / apm_a01A01_stage k :=
    div_nonneg (by positivity) hn'.le
  have hj1 : (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
      apm_a01A01_stage k) ≤ 1 :=
    (div_le_one hn').mpr (by exact_mod_cast hj)
  unfold apm_a01A01_typewriter1d
  rw [show (fun x : ℝ => Real.sqrt (apm_a01A01_stage k) *
      (Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k)).indicator (fun _ => 1) x) =
      (Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k)).indicator
        (fun _ => Real.sqrt (apm_a01A01_stage k)) by
      funext x
      rw [Set.indicator_apply, Set.indicator_apply]
      split_ifs <;> ring]
  rw [setIntegral_indicator measurableSet_Icc]
  have hsub : Icc (0 : ℝ) 1 ∩
      Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k) =
      Icc ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k)
        (((apm_a01A01_position k + 1 : ℕ) : ℝ) /
          apm_a01A01_stage k) := by
    apply Set.inter_eq_right.mpr
    rintro x ⟨hx1, hx2⟩
    exact ⟨hj0.trans hx1, hx2.trans hj1⟩
  rw [hsub, setIntegral_const, Measure.real, Real.volume_Icc]
  have hdiff : 0 ≤
      (((apm_a01A01_position k + 1 : ℕ) : ℝ) / apm_a01A01_stage k) -
        ((apm_a01A01_position k : ℝ) / apm_a01A01_stage k) := by
    rw [show ((apm_a01A01_position k + 1 : ℕ) : ℝ) =
      (apm_a01A01_position k : ℝ) + 1 by exact_mod_cast rfl,
      div_sub_div_same]
    exact div_nonneg (by norm_num) hn'.le
  rw [ENNReal.toReal_ofReal hdiff, smul_eq_mul]
  rw [show ((apm_a01A01_position k + 1 : ℕ) : ℝ) =
    (apm_a01A01_position k : ℝ) + 1 by exact_mod_cast rfl]
  field_simp
  ring

lemma apm_a01A01_integral_typewriter1d_tendsto :
    Tendsto (fun k => ∫ x in Icc (0 : ℝ) 1,
      apm_a01A01_typewriter1d k x ∂volume) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun k => Real.sqrt (apm_a01A01_stage k)) atTop atTop := by
    have hcast : Tendsto (fun k => (apm_a01A01_stage k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto Nat.cast atTop atTop).comp
        apm_a01A01_stage_tendsto_atTop
    exact Real.tendsto_sqrt_atTop.comp hcast
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_inv_atTop_zero.comp hsqrt)
  · intro k
    change 0 ≤ ∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume
    rw [apm_a01A01_integral_typewriter1d]
    positivity
  · intro k
    change (∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume) ≤
      (Real.sqrt (apm_a01A01_stage k))⁻¹
    rw [apm_a01A01_integral_typewriter1d]
    have hkpos : (0 : ℝ) < apm_a01A01_stage k := by
      unfold apm_a01A01_stage
      positivity
    have hsq : Real.sqrt (apm_a01A01_stage k) *
        Real.sqrt (apm_a01A01_stage k) = apm_a01A01_stage k :=
      Real.mul_self_sqrt hkpos.le
    have hspos : 0 < Real.sqrt (apm_a01A01_stage k) := Real.sqrt_pos.mpr hkpos
    apply le_of_eq
    field_simp [hspos.ne', hkpos.ne']
    simpa [pow_two] using hsq

lemma apm_a01A01_add_le_pair (a b : ℕ) : a + b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b]

lemma apm_a01A01_typewriter1d_cofinal
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (M : ℝ) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ M ≤ apm_a01A01_typewriter1d k x := by
  obtain ⟨s, hs⟩ := exists_nat_ge (max ((max M 0) ^ 2) (N + 1 : ℝ))
  have hsNreal : (N + 1 : ℝ) ≤ s := (le_max_right _ _).trans hs
  have hsN : N + 1 ≤ s := by exact_mod_cast hsNreal
  have hspos : 0 < s := by omega
  have hsposR : (0 : ℝ) < s := by exact_mod_cast hspos
  let j : ℕ := if x = 1 then s - 1 else ⌊(s : ℝ) * x⌋₊
  have hjlt : j < s := by
    dsimp [j]
    split_ifs with hxeq
    · omega
    · apply (Nat.floor_lt (mul_nonneg hsposR.le hx.1)).mpr
      have hxlt : x < 1 := hx.2.lt_of_ne hxeq
      nlinarith
  let k := Nat.pair (s - 1 - j) j
  have hstage : apm_a01A01_stage k = s := by
    simp [k, apm_a01A01_stage]
    omega
  have hpos : apm_a01A01_position k = j := by
    simp [k, apm_a01A01_position]
  refine ⟨k, ?_, ?_⟩
  · have hsum : s - 1 - j + j = s - 1 := by omega
    have hpair := apm_a01A01_add_le_pair (s - 1 - j) j
    dsimp [k]
    omega
  · have hcell : x ∈ Icc ((j : ℝ) / s) (((j + 1 : ℕ) : ℝ) / s) := by
      constructor
      · rw [div_le_iff₀ hsposR]
        dsimp [j]
        split_ifs with hxeq
        · subst x
          norm_num
        · simpa [mul_comm] using Nat.floor_le (mul_nonneg hsposR.le hx.1)
      · rw [le_div_iff₀ hsposR]
        dsimp [j]
        split_ifs with hxeq
        · subst x
          norm_num [Nat.sub_add_cancel hspos]
        · simpa [Nat.cast_add_one, mul_comm] using
            (Nat.lt_floor_add_one ((s : ℝ) * x)).le
    have hM : M ≤ Real.sqrt s := by
      have hsq : (max M 0) ^ 2 ≤ (s : ℝ) := (le_max_left _ _).trans hs
      have hm0 : 0 ≤ max M 0 := le_max_right _ _
      exact le_trans (le_max_left _ _) ((Real.le_sqrt hm0 hsposR.le).2 hsq)
    unfold apm_a01A01_typewriter1d
    rw [hstage, hpos, Set.indicator_of_mem hcell, mul_one]
    exact hM

/-! A sparse whole-line scheduler.  At resolution `n`, valid codes encode
an integer interval and one of its `n` equal cells.  Invalid codes are zero. -/

def apm_a01A01_lineResolution (k : ℕ) : ℕ := (Nat.unpair k).1 + 1

def apm_a01A01_lineCode (k : ℕ) : ℕ := (Nat.unpair k).2

def apm_a01A01_lineValid (k : ℕ) : Prop :=
  apm_a01A01_lineCode k < apm_a01A01_lineResolution k ^ 2

instance apm_a01A01_lineValid_decidable (k : ℕ) :
    Decidable (apm_a01A01_lineValid k) := Classical.propDecidable _

def apm_a01A01_intDecode (q : ℕ) : ℤ :=
  if Even q then Int.ofNat (q / 2) else Int.negSucc (q / 2)

def apm_a01A01_lineLeft (k : ℕ) : ℝ :=
  let n := apm_a01A01_lineResolution k
  let q := apm_a01A01_lineCode k / n
  let j := apm_a01A01_lineCode k % n
  (apm_a01A01_intDecode q : ℝ) + (j : ℝ) / n

def apm_a01A01_typewriterLine (k : ℕ) : ℝ → ℝ := by
  classical
  exact fun x =>
    if apm_a01A01_lineValid k then
      Real.sqrt (apm_a01A01_lineResolution k) *
        Set.indicator
          (Icc (apm_a01A01_lineLeft k)
            (apm_a01A01_lineLeft k + 1 / apm_a01A01_lineResolution k))
          (fun _ => (1 : ℝ)) x
    else 0

lemma apm_a01A01_lineResolution_pos (k : ℕ) :
    0 < apm_a01A01_lineResolution k := by
  simp [apm_a01A01_lineResolution]

lemma apm_a01A01_typewriterLine_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ apm_a01A01_typewriterLine k x := by
  classical
  simp only [apm_a01A01_typewriterLine]
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  · exact le_rfl

/-- Non-vacuity check for the sparse scheduler. -/
lemma apm_a01A01_typewriterLine_zero_zero :
    apm_a01A01_typewriterLine 0 0 = 1 := by
  norm_num [apm_a01A01_typewriterLine, apm_a01A01_lineValid,
    apm_a01A01_lineCode, apm_a01A01_lineResolution,
    apm_a01A01_lineLeft, apm_a01A01_intDecode, Nat.unpair]

lemma apm_a01A01_typewriterLine_integrable (k : ℕ) :
    Integrable (apm_a01A01_typewriterLine k) volume := by
  classical
  unfold apm_a01A01_typewriterLine
  split_ifs
  · let C := Icc (apm_a01A01_lineLeft k)
        (apm_a01A01_lineLeft k + 1 / apm_a01A01_lineResolution k)
    have hC : MeasurableSet C := measurableSet_Icc
    have hfin : volume C ≠ ⊤ := measure_Icc_lt_top.ne
    have hi : Integrable (C.indicator
        (fun _ : ℝ => Real.sqrt (apm_a01A01_lineResolution k))) volume :=
      (integrableOn_const hfin).integrable_indicator hC
    apply hi.congr
    filter_upwards with x
    dsimp [C]
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> ring
  · exact integrable_zero ℝ ℝ volume

lemma apm_a01A01_integral_typewriterLine (k : ℕ) :
    ∫ x, apm_a01A01_typewriterLine k x ∂volume =
      if apm_a01A01_lineValid k then
        Real.sqrt (apm_a01A01_lineResolution k) /
          apm_a01A01_lineResolution k
      else 0 := by
  classical
  unfold apm_a01A01_typewriterLine
  split_ifs with hk
  · rw [show (fun x : ℝ => Real.sqrt (apm_a01A01_lineResolution k) *
        (Icc (apm_a01A01_lineLeft k)
          (apm_a01A01_lineLeft k + 1 / apm_a01A01_lineResolution k)).indicator
          (fun _ => (1 : ℝ)) x) =
        (Icc (apm_a01A01_lineLeft k)
          (apm_a01A01_lineLeft k + 1 / apm_a01A01_lineResolution k)).indicator
          (fun _ => Real.sqrt (apm_a01A01_lineResolution k)) by
        funext x
        rw [Set.indicator_apply, Set.indicator_apply]
        split_ifs <;> ring]
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Measure.real, Real.volume_Icc]
    have hn : (0 : ℝ) < apm_a01A01_lineResolution k := by
      exact_mod_cast apm_a01A01_lineResolution_pos k
    rw [ENNReal.toReal_ofReal]
    · simp only [smul_eq_mul]
      field_simp [hn.ne']
      ring
    · simpa using (one_div_pos.mpr hn).le
  · simp

lemma apm_a01A01_pair_lt_sum_sq (a b : ℕ) :
    Nat.pair a b < (a + b + 1) ^ 2 := by
  unfold Nat.pair
  split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b]

lemma apm_a01A01_valid_bounded_resolution
    (B k : ℕ) (hk : apm_a01A01_lineValid k)
    (hres : apm_a01A01_lineResolution k < B) :
    k < (B + B ^ 2 + 1) ^ 2 := by
  have hcode : apm_a01A01_lineCode k < B ^ 2 := by
    exact lt_of_lt_of_le hk (Nat.pow_le_pow_left hres.le 2)
  have ha : (Nat.unpair k).1 < B := by
    simp only [apm_a01A01_lineResolution] at hres
    omega
  have hp := apm_a01A01_pair_lt_sum_sq (Nat.unpair k).1 (Nat.unpair k).2
  rw [Nat.pair_unpair] at hp
  have hb : (Nat.unpair k).2 < B ^ 2 := by
    simpa [apm_a01A01_lineCode] using hcode
  nlinarith

lemma apm_a01A01_integral_typewriterLine_tendsto :
    Tendsto (fun k ↦ ∫ x, apm_a01A01_typewriterLine k x ∂volume)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (nhds 0) := by
    have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hcast)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB⟩ := (Metric.tendsto_atTop.mp hbase) ε hε
  refine ⟨(B + B ^ 2 + 1) ^ 2, fun k hk ↦ ?_⟩
  rw [apm_a01A01_integral_typewriterLine]
  by_cases hv : apm_a01A01_lineValid k
  · rw [if_pos hv]
    have hres : B ≤ apm_a01A01_lineResolution k := by
      by_contra hn
      have hlt : apm_a01A01_lineResolution k < B := Nat.lt_of_not_ge hn
      exact (not_lt_of_ge hk) (apm_a01A01_valid_bounded_resolution B k hv hlt)
    have hdist := hB (apm_a01A01_lineResolution k) hres
    have hn : (0 : ℝ) < apm_a01A01_lineResolution k := by
      exact_mod_cast apm_a01A01_lineResolution_pos k
    have heq : Real.sqrt (apm_a01A01_lineResolution k) /
        apm_a01A01_lineResolution k =
        (Real.sqrt (apm_a01A01_lineResolution k))⁻¹ := by
      have hs := Real.mul_self_sqrt hn.le
      field_simp [hn.ne', (Real.sqrt_pos.mpr hn).ne']
      simpa [pow_two] using hs
    rw [heq]
    simpa using hdist
  · rw [if_neg hv]
    simpa using hε

lemma apm_a01A01_intDecode_surjective :
    Function.Surjective apm_a01A01_intDecode := by
  intro z
  cases z with
  | ofNat m =>
      refine ⟨2 * m, ?_⟩
      simp [apm_a01A01_intDecode, even_iff_two_dvd]
  | negSucc m =>
      refine ⟨2 * m + 1, ?_⟩
      have hodd : ¬ Even (2 * m + 1) := by
        rintro ⟨c, hc⟩
        omega
      simp only [apm_a01A01_intDecode, if_neg hodd]
      congr 1
      omega

lemma apm_a01A01_typewriterLine_cofinal (x M : ℝ) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ M ≤ apm_a01A01_typewriterLine k x := by
  let z : ℤ := ⌊x⌋
  obtain ⟨q, hq⟩ := apm_a01A01_intDecode_surjective z
  obtain ⟨n, hn⟩ := exists_nat_ge
    (max (max ((max M 0) ^ 2) (N + 1 : ℝ)) (q + 1 : ℝ))
  have hnN : N + 1 ≤ n := by
    exact_mod_cast (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))
  have hnq : q + 1 ≤ n := by
    exact_mod_cast (le_trans (le_max_right _ _) hn)
  have hnpos : 0 < n := by omega
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let y : ℝ := x - z
  have hy0 : 0 ≤ y := by
    dsimp [y, z]
    exact sub_nonneg.mpr (Int.floor_le x)
  have hy1 : y < 1 := by
    dsimp [y, z]
    exact Int.fract_lt_one x
  let j : ℕ := ⌊(n : ℝ) * y⌋₊
  have hjlt : j < n := by
    dsimp [j]
    apply (Nat.floor_lt (mul_nonneg hnposR.le hy0)).mpr
    nlinarith
  let code := q * n + j
  let k := Nat.pair (n - 1) code
  have hres : apm_a01A01_lineResolution k = n := by
    simp [k, apm_a01A01_lineResolution]
    omega
  have hcode : apm_a01A01_lineCode k = code := by
    simp [k, apm_a01A01_lineCode]
  have hvalid : apm_a01A01_lineValid k := by
    rw [apm_a01A01_lineValid, hres, hcode]
    dsimp [code]
    nlinarith
  have hqdiv : code / n = q := by
    dsimp [code]
    rw [mul_comm q n]
    rw [Nat.mul_add_div hnpos]
    rw [Nat.div_eq_of_lt hjlt, add_zero]
  have hjmod : code % n = j := by
    dsimp [code]
    rw [mul_comm q n]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hjlt
  have hleft : apm_a01A01_lineLeft k = (z : ℝ) + (j : ℝ) / n := by
    simp only [apm_a01A01_lineLeft, hres, hcode, hqdiv, hjmod, hq]
  refine ⟨k, ?_, ?_⟩
  · have hp := apm_a01A01_add_le_pair (n - 1) code
    dsimp [k]
    omega
  · have hjle : (j : ℝ) ≤ (n : ℝ) * y := by
      dsimp [j]
      exact Nat.floor_le (mul_nonneg hnposR.le hy0)
    have hyj : (n : ℝ) * y < j + 1 := by
      dsimp [j]
      exact_mod_cast Nat.lt_floor_add_one ((n : ℝ) * y)
    have hxcell : x ∈ Icc (apm_a01A01_lineLeft k)
        (apm_a01A01_lineLeft k + 1 / apm_a01A01_lineResolution k) := by
      rw [hleft, hres]
      constructor
      · calc
          (z : ℝ) + (j : ℝ) / n ≤ (z : ℝ) + y := by
            gcongr
            exact (div_le_iff₀ hnposR).2 (by simpa [mul_comm] using hjle)
          _ = x := by dsimp [y]; ring
      · calc
          x = (z : ℝ) + y := by dsimp [y]; ring
          _ ≤ (z : ℝ) + ((j : ℝ) + 1) / n := by
            gcongr
            exact (le_div_iff₀ hnposR).2 (by simpa [mul_comm] using hyj.le)
          _ = (z : ℝ) + (j : ℝ) / n + 1 / n := by ring
    have hM : M ≤ Real.sqrt n := by
      have hsq : (max M 0) ^ 2 ≤ (n : ℝ) :=
        (le_max_left _ _).trans ((le_max_left _ _).trans hn)
      exact le_trans (le_max_left _ _)
        ((Real.le_sqrt (le_max_right _ _) hnposR.le).2 hsq)
    unfold apm_a01A01_typewriterLine
    rw [if_pos hvalid, hres]
    rw [Set.indicator_of_mem (by simpa [hres] using hxcell), mul_one]
    exact hM

def apm_a01A01_factor {d : ℕ} (k : ℕ) (i : Fin (d + 1)) (t : ℝ) : ℝ :=
  if i = 0 then apm_a01A01_typewriterLine k t else Real.exp (-t ^ 2)

def apm_a01A01_typewriterPi (d k : ℕ) (x : Fin (d + 1) → ℝ) : ℝ :=
  ∏ i, apm_a01A01_factor k i (x i)

/-- Non-vacuity of the finite-product construction. -/
lemma apm_a01A01_typewriterPi_zero_zero :
    apm_a01A01_typewriterPi 0 0 (0 : Fin 1 → ℝ) = 1 := by
  simp [apm_a01A01_typewriterPi, apm_a01A01_factor,
    apm_a01A01_typewriterLine_zero_zero]

lemma apm_a01A01_factor_integrable {d : ℕ} (k : ℕ) (i : Fin (d + 1)) :
    Integrable (apm_a01A01_factor k i) volume := by
  unfold apm_a01A01_factor
  split_ifs
  · exact apm_a01A01_typewriterLine_integrable k
  · simpa [one_mul] using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one)

lemma apm_a01A01_typewriterPi_integrable (d k : ℕ) :
    Integrable (apm_a01A01_typewriterPi d k) volume := by
  unfold apm_a01A01_typewriterPi
  simpa only [volume_pi_pi] using
    (Integrable.fintype_prod (fun i : Fin (d + 1) ↦
      apm_a01A01_factor_integrable k i))

lemma apm_a01A01_typewriterPi_nonneg (d k : ℕ) (x : Fin (d + 1) → ℝ) :
    0 ≤ apm_a01A01_typewriterPi d k x := by
  apply Finset.prod_nonneg
  intro i _
  unfold apm_a01A01_factor
  split_ifs
  · exact apm_a01A01_typewriterLine_nonneg k _
  · positivity

lemma apm_a01A01_integral_typewriterPi (d k : ℕ) :
    ∫ x, apm_a01A01_typewriterPi d k x ∂volume =
      (∫ t, apm_a01A01_typewriterLine k t ∂volume) *
        (Real.sqrt Real.pi) ^ d := by
  unfold apm_a01A01_typewriterPi
  rw [integral_fintype_prod_volume_eq_prod, Fin.prod_univ_succ]
  simp only [apm_a01A01_factor, if_pos, Fin.succ_ne_zero, if_false]
  have hg : (∫ x : ℝ, Real.exp (-x ^ 2) ∂volume) = Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  rw [hg, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma apm_a01A01_integral_typewriterPi_tendsto (d : ℕ) :
    Tendsto (fun k ↦ ∫ x, apm_a01A01_typewriterPi d k x ∂volume)
      atTop (nhds 0) := by
  simp_rw [apm_a01A01_integral_typewriterPi]
  simpa using apm_a01A01_integral_typewriterLine_tendsto.mul_const
    ((Real.sqrt Real.pi) ^ d)

lemma apm_a01A01_typewriterPi_cofinal
    (d : ℕ) (x : Fin (d + 1) → ℝ) (M : ℝ) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ M ≤ apm_a01A01_typewriterPi d k x := by
  let C : ℝ := ∏ j : Fin d, Real.exp (-(x j.succ) ^ 2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  obtain ⟨k, hkN, hk⟩ :=
    apm_a01A01_typewriterLine_cofinal (x 0) (M / C) N
  refine ⟨k, hkN, ?_⟩
  have hform : apm_a01A01_typewriterPi d k x =
      apm_a01A01_typewriterLine k (x 0) * C := by
    rw [apm_a01A01_typewriterPi, Fin.prod_univ_succ]
    simp only [apm_a01A01_factor, if_pos, Fin.succ_ne_zero, if_false]
    rfl
  rw [hform]
  exact (div_le_iff₀ hC).mp hk

def apm_a01A01_typewriterEuclidean (d k : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) → ℝ := fun x ↦
  apm_a01A01_typewriterPi d k (WithLp.ofLp x)

/-- Non-vacuity after transport to Euclidean space. -/
lemma apm_a01A01_typewriterEuclidean_zero_zero :
    apm_a01A01_typewriterEuclidean 0 0 0 = 1 := by
  simp [apm_a01A01_typewriterEuclidean,
    apm_a01A01_typewriterPi_zero_zero]

lemma apm_a01A01_typewriterEuclidean_integrable (d k : ℕ) :
    Integrable (apm_a01A01_typewriterEuclidean d k) volume := by
  let mp := PiLp.volume_preserving_ofLp (Fin (d + 1))
  have hemb : MeasurableEmbedding
      (@WithLp.ofLp 2 (Fin (d + 1) → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.measurableEmbedding
  exact (mp.integrable_comp_emb hemb).2
    (apm_a01A01_typewriterPi_integrable d k)

lemma apm_a01A01_typewriterEuclidean_nonneg
    (d k : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    0 ≤ apm_a01A01_typewriterEuclidean d k x :=
  apm_a01A01_typewriterPi_nonneg d k (WithLp.ofLp x)

lemma apm_a01A01_integral_typewriterEuclidean (d k : ℕ) :
    ∫ x, apm_a01A01_typewriterEuclidean d k x ∂volume =
      ∫ x, apm_a01A01_typewriterPi d k x ∂volume := by
  exact (PiLp.volume_preserving_ofLp (Fin (d + 1))).integral_comp
    ((MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm.measurableEmbedding)
    (apm_a01A01_typewriterPi d k)

lemma apm_a01A01_integral_typewriterEuclidean_tendsto (d : ℕ) :
    Tendsto (fun k ↦ ∫ x, apm_a01A01_typewriterEuclidean d k x ∂volume)
      atTop (nhds 0) := by
  simpa only [apm_a01A01_integral_typewriterEuclidean] using
    apm_a01A01_integral_typewriterPi_tendsto d

lemma apm_a01A01_typewriterEuclidean_cofinal
    (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) (M : ℝ) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ M ≤ apm_a01A01_typewriterEuclidean d k x :=
  apm_a01A01_typewriterPi_cofinal d (WithLp.ofLp x) M N

theorem apm_a01a01 :
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, IntegrableOn (f k) (Icc (0 : ℝ) 1) volume) ∧
      (∀ k x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f k x) ∧
      (∀ x, x ∈ Icc (0 : ℝ) 1 →
        ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ f k x) ∧
      Tendsto (fun k ↦ ∫ x in Icc (0 : ℝ) 1, f k x ∂volume)
        atTop (nhds 0)) ∧
    (∀ d : ℕ, 0 < d →
      ∃ f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ k, Integrable (f k) volume) ∧
        (∀ k x, 0 ≤ f k x) ∧
        (∀ x, ∀ M : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ M ≤ f k x) ∧
        Tendsto (fun k ↦ ∫ x, f k x ∂volume) atTop (nhds 0)) := by
  constructor
  · refine ⟨apm_a01A01_typewriter1d, ?_, ?_, ?_,
      apm_a01A01_integral_typewriter1d_tendsto⟩
    · exact apm_a01A01_typewriter1d_integrableOn
    · intro k x _
      exact apm_a01A01_typewriter1d_nonneg k x
    · exact apm_a01A01_typewriter1d_cofinal
  · intro d hd
    cases d with
    | zero => omega
    | succ n =>
        refine ⟨apm_a01A01_typewriterEuclidean n, ?_, ?_, ?_, ?_⟩
        · exact apm_a01A01_typewriterEuclidean_integrable n
        · exact apm_a01A01_typewriterEuclidean_nonneg n
        · exact apm_a01A01_typewriterEuclidean_cofinal n
        · exact apm_a01A01_integral_typewriterEuclidean_tendsto n
