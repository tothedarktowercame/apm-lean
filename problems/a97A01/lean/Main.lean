import Mathlib

/-!
# APM a97A01 — weak convergence of the Rademacher functions

## Statement repairs

The source says `f_n(t) = 1` on both the odd and even dyadic intervals. This
would make the sequence constant almost everywhere and the claimed limit
false. Following the supplied solution, the value on even intervals is
repaired to `-1`; these are the Rademacher functions.

## Encoding questions

None. `f ∈ L∞([0,1])` is represented by `MemLp f ∞` for Lebesgue measure
restricted to `Icc 0 1`, so representatives and almost-everywhere behavior
are retained explicitly.
-/

open Filter MeasureTheory Set

noncomputable section

def apm_a97A01_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The source's dyadic sign function, including its specified endpoint
value. -/
def apm_a97A01_rademacher (n : ℕ) (t : ℝ) : ℝ := by
  classical
  exact if n = 1 then 1
    else if t = 1 then -1
    else if ∃ k : ℕ,
        1 ≤ k ∧ k ≤ 2 ^ n ∧ Odd k ∧
        t ∈ Set.Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
          ((k : ℝ) / (2 ^ n : ℕ))
      then 1 else -1

/-- Every encoded Rademacher function has pointwise absolute value one. -/
lemma apm_a97A01_abs_rademacher (n : ℕ) (t : ℝ) :
    |apm_a97A01_rademacher n t| = 1 := by
  unfold apm_a97A01_rademacher
  split_ifs <;> simp

/-- In particular, every point explicitly lying in an admissible odd cell
has positive sign.  This is the cellwise input to the cancellation proof. -/
lemma apm_a97A01_rademacher_eq_one_of_mem_odd_cell
    {n k : ℕ} {t : ℝ} (hn : n ≠ 1) (ht : t ≠ 1)
    (hk₀ : 1 ≤ k) (hk₁ : k ≤ 2 ^ n) (hkodd : Odd k)
    (htk : t ∈ Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
      ((k : ℝ) / (2 ^ n : ℕ))) :
    apm_a97A01_rademacher n t = 1 := by
  unfold apm_a97A01_rademacher
  simp only [hn, ht, ↓reduceIte]
  rw [if_pos ⟨k, hk₀, hk₁, hkodd, htk⟩]

/-- The dyadic sign functions in the frozen encoding are measurable. -/
lemma apm_a97A01_rademacher_measurable (n : ℕ) :
    Measurable (apm_a97A01_rademacher n) := by
  unfold apm_a97A01_rademacher
  by_cases hn : n = 1
  · simp [hn]
  simp only [hn, ↓reduceIte]
  have hdyadic : MeasurableSet {t : ℝ | ∃ k : ℕ,
      1 ≤ k ∧ k ≤ 2 ^ n ∧ Odd k ∧
      t ∈ Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
        ((k : ℝ) / (2 ^ n : ℕ))} := by
    rw [show {t : ℝ | ∃ k : ℕ,
        1 ≤ k ∧ k ≤ 2 ^ n ∧ Odd k ∧
        t ∈ Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
          ((k : ℝ) / (2 ^ n : ℕ))} =
        ⋃ k : ℕ, if 1 ≤ k ∧ k ≤ 2 ^ n ∧ Odd k then
          Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
            ((k : ℝ) / (2 ^ n : ℕ)) else ∅ by
      ext t
      simp only [mem_setOf_eq, mem_iUnion, mem_ite_empty_right, mem_Ico]
      aesop]
    exact MeasurableSet.iUnion fun k ↦ by
      split_ifs
      · exact measurableSet_Ico
      · exact MeasurableSet.empty
  exact Measurable.ite (measurableSet_singleton 1) measurable_const
    (Measurable.ite hdyadic measurable_const measurable_const)

/-- Pairing an `L∞` function with any encoded Rademacher function is
integrable on the restricted interval.  This packages the domination step
needed after dyadic cancellation. -/
lemma apm_a97A01_integrable_mul_rademacher
    (f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure) (n : ℕ) :
    Integrable (fun t ↦ f t * apm_a97A01_rademacher n t)
      apm_a97A01_measure := by
  letI : IsFiniteMeasure apm_a97A01_measure := by
    unfold apm_a97A01_measure
    infer_instance
  apply (hf.integrable (by simp)).mul_bdd
    (c := 1) (apm_a97A01_rademacher_measurable n).aestronglyMeasurable
  filter_upwards with t
  simp [Real.norm_eq_abs, apm_a97A01_abs_rademacher]

/-- The unit pointwise modulus gives the exact uniform `L¹` domination used
to pass from dyadic step functions to arbitrary test functions. -/
lemma apm_a97A01_norm_integral_mul_rademacher_le
    (g : ℝ → ℝ) (n : ℕ) :
    ‖∫ t, g t * apm_a97A01_rademacher n t ∂apm_a97A01_measure‖ ≤
      ∫ t, |g t| ∂apm_a97A01_measure := by
  calc
    ‖∫ t, g t * apm_a97A01_rademacher n t ∂apm_a97A01_measure‖ ≤
        ∫ t, ‖g t * apm_a97A01_rademacher n t‖ ∂apm_a97A01_measure :=
      norm_integral_le_integral_norm _
    _ = ∫ t, |g t| ∂apm_a97A01_measure := by
      apply integral_congr_ae
      filter_upwards with t
      simp [Real.norm_eq_abs, apm_a97A01_abs_rademacher]

/-- Why this unblocks `apm_a97a01`: same-level half-open dyadic cells with
the casted natural endpoints are disjoint, so membership in an admissible even
cell excludes every odd-cell witness in the frozen existential encoding. -/
theorem apm_a97A01_bridge_1
    {n k : ℕ} {t : ℝ} (hn : n ≠ 1) (ht : t ≠ 1)
    (hk₀ : 1 ≤ k) (_hk₁ : k ≤ 2 ^ n) (hkeven : Even k)
    (htk : t ∈ Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
      ((k : ℝ) / (2 ^ n : ℕ))) :
    apm_a97A01_rademacher n t = -1 := by
  unfold apm_a97A01_rademacher
  simp only [hn, ht, ↓reduceIte]
  rw [if_neg]
  rintro ⟨l, hl₀, hl₁, hlodd, htl⟩
  have hpow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h₁ : ((l - 1 : ℕ) : ℝ) < k := by
    have := lt_of_le_of_lt htl.1 htk.2
    exact (div_lt_div_iff_of_pos_right hpow).mp this
  have h₂ : ((k - 1 : ℕ) : ℝ) < l := by
    have := lt_of_le_of_lt htk.1 htl.2
    exact (div_lt_div_iff_of_pos_right hpow).mp this
  have h₁' : l - 1 < k := by exact_mod_cast h₁
  have h₂' : k - 1 < l := by exact_mod_cast h₂
  have hlk : l ≤ k := by omega
  have hkl : k ≤ l := by omega
  have hEq : l = k := Nat.le_antisymm hlk hkl
  subst l
  exact (Nat.not_even_iff_odd.mpr hlodd) hkeven

/-- On each admissible level-`n` cell the frozen function is pointwise
constant, apart from the separately encoded endpoint which cannot belong to
the half-open cell. -/
lemma apm_a97A01_rademacher_eq_parity_of_mem_cell
    {n k : ℕ} {t : ℝ} (hn : n ≠ 1) (hk₀ : 1 ≤ k) (hk₁ : k ≤ 2 ^ n)
    (htk : t ∈ Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
      ((k : ℝ) / (2 ^ n : ℕ))) :
    apm_a97A01_rademacher n t = if Odd k then 1 else -1 := by
  have ht : t ≠ 1 := by
    intro h
    subst t
    have hpow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    have hkcast : (k : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast hk₁
    have hle : (k : ℝ) / (2 ^ n : ℕ) ≤ 1 := (div_le_one hpow).2 hkcast
    linarith [htk.2]
  by_cases hodd : Odd k
  · rw [if_pos hodd]
    exact apm_a97A01_rademacher_eq_one_of_mem_odd_cell hn ht hk₀ hk₁ hodd htk
  · rw [if_neg hodd]
    exact apm_a97A01_bridge_1 hn ht hk₀ hk₁
      (Nat.not_odd_iff_even.mp hodd) htk

/-- Exact integral on one fine dyadic cell, expressed using the restricted
measure so that later cancellation can pair equal-measure adjacent cells. -/
lemma apm_a97A01_integral_one_cell
    {n k : ℕ} (hn : n ≠ 1) (hk₀ : 1 ≤ k) (hk₁ : k ≤ 2 ^ n) :
    ∫ t, (Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
        ((k : ℝ) / (2 ^ n : ℕ))).indicator (fun _ : ℝ => (1 : ℝ)) t *
      apm_a97A01_rademacher n t ∂apm_a97A01_measure =
      (if Odd k then (1 : ℝ) else -1) *
        (apm_a97A01_measure (Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
          ((k : ℝ) / (2 ^ n : ℕ)))).toReal := by
  let A : Set ℝ := Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
    ((k : ℝ) / (2 ^ n : ℕ))
  have hfun : (fun t ↦ A.indicator (fun _ : ℝ ↦ (1 : ℝ)) t *
      apm_a97A01_rademacher n t) =
      A.indicator (fun _ : ℝ ↦ if Odd k then (1 : ℝ) else -1) := by
    funext t
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht, one_mul]
      exact apm_a97A01_rademacher_eq_parity_of_mem_cell hn hk₀ hk₁ ht
    · simp [ht]
  rw [show Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
      ((k : ℝ) / (2 ^ n : ℕ)) = A from rfl, hfun,
    integral_indicator measurableSet_Ico]
  simp [A, integral_const, Measure.real]

/-- All admissible cells at a fixed level have the same restricted Lebesgue
measure. -/
lemma apm_a97A01_measure_cell
    {n k : ℕ} (hk₀ : 1 ≤ k) (hk₁ : k ≤ 2 ^ n) :
    (apm_a97A01_measure (Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
      ((k : ℝ) / (2 ^ n : ℕ)))).toReal = 1 / (2 ^ n : ℕ) := by
  let a : ℝ := ((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ)
  let b : ℝ := (k : ℝ) / (2 ^ n : ℕ)
  have hpow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hkcast : (k : ℝ) ≤ (2 ^ n : ℕ) := by exact_mod_cast hk₁
  have ha0 : 0 ≤ a := by positivity
  have hb1 : b ≤ 1 := (div_le_one hpow).2 hkcast
  have hsub : Ico a b ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨le_trans ha0 ht.1, le_trans (le_of_lt ht.2) hb1⟩
  unfold apm_a97A01_measure
  rw [Measure.restrict_apply measurableSet_Ico]
  change (volume (Ico a b ∩ Icc 0 1)).toReal = _
  rw [inter_eq_left.mpr hsub, Real.volume_Ico, ENNReal.toReal_ofReal]
  · dsimp [a, b]
    rw [Nat.cast_sub hk₀]
    field_simp
    ring
  · dsimp [a, b]
    rw [Nat.cast_sub hk₀]
    exact sub_nonneg.mpr (div_le_div_of_nonneg_right (by norm_num) hpow.le)

/-- Arithmetic form of the one-cell integral used by the finite pairing
argument. -/
lemma apm_a97A01_integral_one_cell_eq_inv
    {n k : ℕ} (hn : n ≠ 1) (hk₀ : 1 ≤ k) (hk₁ : k ≤ 2 ^ n) :
    ∫ t, (Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
        ((k : ℝ) / (2 ^ n : ℕ))).indicator (fun _ : ℝ => (1 : ℝ)) t *
      apm_a97A01_rademacher n t ∂apm_a97A01_measure =
      if Odd k then (1 : ℝ) / (2 ^ n : ℕ)
      else -((1 : ℝ) / (2 ^ n : ℕ)) := by
  rw [apm_a97A01_integral_one_cell hn hk₀ hk₁,
    apm_a97A01_measure_cell hk₀ hk₁]
  split_ifs <;> ring

/-- An alternating sign block of even length cancels when its zero-based
starting index is even.  The `+ 1` converts offsets to the one-based cell
indices used by the source encoding. -/
lemma apm_a97A01_sum_parity_block
    (a q : ℕ) (ha : Even a) (x : ℝ) :
    ∑ r ∈ Finset.range (2 * q),
      (if Odd (a + r + 1) then x else -x) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have he : Even (a + 2 * q) := ha.add (even_two_mul q)
      have ho : Odd (a + 2 * q + 1) := he.add_one
      have he' : Even (a + (2 * q + 1) + 1) := ho.add_one
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [if_pos ho, if_neg (Nat.not_odd_iff_even.mpr he')]
      ring

/-- Power-of-two specialization matching a strict dyadic refinement. -/
lemma apm_a97A01_sum_parity_two_pow
    (a d : ℕ) (ha : Even a) (hd : 0 < d) (x : ℝ) :
    ∑ r ∈ Finset.range (2 ^ d),
      (if Odd (a + r + 1) then x else -x) = 0 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  rw [pow_succ, mul_comm]
  exact apm_a97A01_sum_parity_block a (2 ^ e) ha x

/-- The first zero-based fine-cell index inside a coarse dyadic cell is even
at every strict refinement. -/
lemma apm_a97A01_even_refinement_start
    (m j n : ℕ) (hmn : m < n) : Even (j * 2 ^ (n - m)) := by
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - m ≠ 0)
  rw [he, pow_succ]
  exact (even_two.mul_left (2 ^ e)).mul_left j

/-- A finite monotone grid partitions its half-open endpoint interval into
its consecutive half-open cells. -/
lemma apm_a97A01_Ico_eq_biUnion_grid
    {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) (ha : Monotone a) :
    Ico (a 0) (a N) =
      ⋃ i ∈ Finset.range N, Ico (a i) (a (i + 1)) := by
  apply Subset.antisymm (Ico_subset_biUnion_Ico N a)
  intro x hx
  simp only [mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  have hiN : i < N := Finset.mem_range.mp hi
  exact ⟨le_trans (ha (Nat.zero_le i)) hxi.1,
    lt_of_lt_of_le hxi.2 (ha (by omega))⟩

/-- The level-`n` affine grid across one level-`m` cell has the expected
coarse endpoints. -/
lemma apm_a97A01_refinement_endpoints
    (m j n : ℕ) (hmn : m ≤ n) :
    let L := 2 ^ (n - m)
    let a := j * L
    (((a : ℕ) : ℝ) / (2 ^ n : ℕ) = (j : ℝ) / (2 ^ m : ℕ)) ∧
      ((((a + L : ℕ) : ℝ) / (2 ^ n : ℕ)) =
        ((j + 1 : ℕ) : ℝ) / (2 ^ m : ℕ)) := by
  dsimp
  have hp : 2 ^ n = 2 ^ m * 2 ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  constructor <;> rw [hp] <;> push_cast
  · field_simp
  · field_simp

/-- Set-level dyadic refinement identity in the exact casted endpoint syntax
used by the frozen problem. -/
lemma apm_a97A01_refinement_partition
    (m j n : ℕ) (hmn : m ≤ n) :
    Ico ((j : ℝ) / (2 ^ m : ℕ))
        (((j + 1 : ℕ) : ℝ) / (2 ^ m : ℕ)) =
      ⋃ r ∈ Finset.range (2 ^ (n - m)),
        Ico ((((j * 2 ^ (n - m) + r : ℕ) : ℝ)) / (2 ^ n : ℕ))
          ((((j * 2 ^ (n - m) + r + 1 : ℕ) : ℝ)) / (2 ^ n : ℕ)) := by
  let L := 2 ^ (n - m)
  let a := j * L
  let grid : ℕ → ℝ := fun r ↦ ((a + r : ℕ) : ℝ) / (2 ^ n : ℕ)
  have hgrid : Monotone grid := by
    intro r s hrs
    dsimp [grid]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.add_le_add_left hrs a)
      (by positivity)
  have hpart := apm_a97A01_Ico_eq_biUnion_grid L grid hgrid
  obtain ⟨hleft, hright⟩ := apm_a97A01_refinement_endpoints m j n hmn
  dsimp [grid, L, a] at hpart
  rw [hleft, hright] at hpart
  simpa [L, a, grid, Nat.add_assoc] using hpart

/-- Function-level form of dyadic refinement: because the fine half-open
cells are disjoint, the coarse-cell indicator is their finite sum. -/
lemma apm_a97A01_indicator_refinement
    (m j n : ℕ) (hmn : m ≤ n) :
    (fun t ↦ (Ico ((j : ℝ) / (2 ^ m : ℕ))
        (((j + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
        (fun _ : ℝ ↦ (1 : ℝ)) t) =
      fun t ↦ ∑ r ∈ Finset.range (2 ^ (n - m)),
        (Ico ((((j * 2 ^ (n - m) + r : ℕ) : ℝ)) / (2 ^ n : ℕ))
          ((((j * 2 ^ (n - m) + r + 1 : ℕ) : ℝ)) / (2 ^ n : ℕ))).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) t := by
  funext t
  let L := 2 ^ (n - m)
  let a := j * L
  let C : ℕ → Set ℝ := fun r ↦
    Ico (((a + r : ℕ) : ℝ) / (2 ^ n : ℕ))
      (((a + r + 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
  have hpart := apm_a97A01_refinement_partition m j n hmn
  change (Ico ((j : ℝ) / (2 ^ m : ℕ))
    (((j + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator (fun _ ↦ (1 : ℝ)) t =
      ∑ r ∈ Finset.range L, (C r).indicator (fun _ ↦ (1 : ℝ)) t
  by_cases ht : t ∈ Ico ((j : ℝ) / (2 ^ m : ℕ))
      (((j + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))
  · have htU : t ∈ ⋃ r ∈ Finset.range L, C r := by
      simpa [L, a, C] using (show t ∈ (⋃ r ∈ Finset.range (2 ^ (n - m)),
        Ico ((((j * 2 ^ (n - m) + r : ℕ) : ℝ)) / (2 ^ n : ℕ))
          ((((j * 2 ^ (n - m) + r + 1 : ℕ) : ℝ)) / (2 ^ n : ℕ))) by
        rw [← hpart]; exact ht)
    simp only [mem_iUnion] at htU
    obtain ⟨r, hr, htr⟩ := htU
    rw [Set.indicator_of_mem ht]
    rw [Finset.sum_eq_single r]
    · simp [htr]
    · intro s hs hsr
      have hts : t ∉ C s := by
        intro hts
        have hpow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
        have hsr₁ : ((a + s : ℕ) : ℝ) < ((a + r + 1 : ℕ) : ℝ) := by
          exact (div_lt_div_iff_of_pos_right hpow).mp (lt_of_le_of_lt hts.1 htr.2)
        have hrs₁ : ((a + r : ℕ) : ℝ) < ((a + s + 1 : ℕ) : ℝ) := by
          exact (div_lt_div_iff_of_pos_right hpow).mp (lt_of_le_of_lt htr.1 hts.2)
        have hsr' : a + s < a + r + 1 := by exact_mod_cast hsr₁
        have hrs' : a + r < a + s + 1 := by exact_mod_cast hrs₁
        have : s = r := by omega
        exact hsr this
      simp [hts]
    · intro hnr
      exact (hnr hr).elim
  · simp only [Set.indicator, ht, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have htr : t ∉ C r := by
      intro hmem
      apply ht
      rw [hpart]
      simp only [mem_iUnion]
      exact ⟨r, by simpa [L] using hr, by simpa [L, a, C] using hmem⟩
    simp [htr]

/-- Why this unblocks `apm_a97a01`: refining a level-`m` dyadic cell to any
strictly finer nonexceptional level pairs equal-length odd and even cells, so
the encoded Rademacher function has exactly zero integral on the coarse cell. -/
theorem apm_a97A01_bridge_2
    (m j n : ℕ) (hj : j < 2 ^ m) (hmn : m < n) (hn : 1 < n) :
    ∫ t,
      (Ico ((j : ℝ) / (2 ^ m : ℕ))
          (((j + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
          (fun _ : ℝ => (1 : ℝ)) t *
      apm_a97A01_rademacher n t ∂apm_a97A01_measure = 0 := by
  let L := 2 ^ (n - m)
  let a := j * L
  have hmn' : m ≤ n := hmn.le
  have hd : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hn1 : n ≠ 1 := by omega
  have hp : 2 ^ n = 2 ^ m * L := by
    dsimp [L]
    rw [← pow_add, Nat.add_sub_of_le hmn']
  have ha : Even a := by
    simpa [a, L] using apm_a97A01_even_refinement_start m j n hmn
  have hfun := apm_a97A01_indicator_refinement m j n hmn'
  have hterm (r : ℕ) : Integrable (fun t ↦
      (Ico (((a + r : ℕ) : ℝ) / (2 ^ n : ℕ))
        (((a + r + 1 : ℕ) : ℝ) / (2 ^ n : ℕ))).indicator
        (fun _ : ℝ => (1 : ℝ)) t * apm_a97A01_rademacher n t)
        apm_a97A01_measure := by
    let A : Set ℝ := Ico (((a + r : ℕ) : ℝ) / (2 ^ n : ℕ))
      (((a + r + 1 : ℕ) : ℝ) / (2 ^ n : ℕ))
    have hconst : Integrable (fun _ : ℝ ↦ (1 : ℝ)) apm_a97A01_measure := by
      letI : IsFiniteMeasure apm_a97A01_measure := by
        unfold apm_a97A01_measure
        infer_instance
      exact integrable_const (1 : ℝ)
    have hind : Integrable (A.indicator (fun _ : ℝ ↦ (1 : ℝ)))
        apm_a97A01_measure := hconst.indicator measurableSet_Ico
    apply hind.mul_bdd (c := 1)
      (apm_a97A01_rademacher_measurable n).aestronglyMeasurable
    filter_upwards with t
    simp [Real.norm_eq_abs, apm_a97A01_abs_rademacher]
  have hi : (∫ t, (Ico ((j : ℝ) / (2 ^ m : ℕ))
        (((j + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
        (fun _ : ℝ => (1 : ℝ)) t * apm_a97A01_rademacher n t
        ∂apm_a97A01_measure) =
      ∫ t, (∑ r ∈ Finset.range (2 ^ (n - m)),
        (Ico ((((j * 2 ^ (n - m) + r : ℕ) : ℝ)) / (2 ^ n : ℕ))
          ((((j * 2 ^ (n - m) + r + 1 : ℕ) : ℝ)) / (2 ^ n : ℕ))).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) t) * apm_a97A01_rademacher n t
        ∂apm_a97A01_measure := by
    apply integral_congr_ae
    filter_upwards with t
    rw [congrFun hfun t]
  rw [hi]
  simp only [Finset.sum_mul]
  rw [integral_finset_sum _ (fun r _ ↦ by simpa [a, L] using hterm r)]
  have hk (r : ℕ) (hr : r ∈ Finset.range L) :
      1 ≤ a + r + 1 ∧ a + r + 1 ≤ 2 ^ n := by
    have hrL : r < L := Finset.mem_range.mp hr
    have hj' : j + 1 ≤ 2 ^ m := by omega
    have htop : a + L ≤ 2 ^ n := by
      rw [hp]
      dsimp [a]
      nlinarith
    exact ⟨by omega, by omega⟩
  calc
    _ = ∑ r ∈ Finset.range L,
        (if Odd (a + r + 1) then (1 : ℝ) / (2 ^ n : ℕ)
          else -((1 : ℝ) / (2 ^ n : ℕ))) := by
      apply Finset.sum_congr rfl
      intro r hr
      simpa [a, L] using apm_a97A01_integral_one_cell_eq_inv
        (k := a + r + 1) hn1 (hk r hr).1 (hk r hr).2
    _ = 0 := by
      simpa [L] using apm_a97A01_sum_parity_two_pow a (n - m) ha hd
        ((1 : ℝ) / (2 ^ n : ℕ))

/-- First half of dyadic density: an `L∞` representative on the finite
restricted interval admits a bounded continuous `L¹` approximation. -/
lemma apm_a97A01_exists_continuous_L1_approx
    (f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : BoundedContinuousFunction ℝ ℝ, Continuous g ∧
      ∫ t, |f t - g t| ∂apm_a97A01_measure < ε := by
  letI : IsFiniteMeasure apm_a97A01_measure := by
    unfold apm_a97A01_measure
    infer_instance
  have hfi : Integrable f apm_a97A01_measure := hf.integrable (by simp)
  obtain ⟨g, hg, hgi⟩ :=
    hfi.exists_boundedContinuous_integral_sub_le (half_pos hε)
  refine ⟨g, g.continuous, ?_⟩
  have hlt : (∫ t, ‖f t - g t‖ ∂apm_a97A01_measure) < ε :=
    lt_of_le_of_lt hg (by linarith)
  simpa [Real.norm_eq_abs] using hlt

/-- A continuous function has an oscillation smaller than `ε` on every cell
of some uniform dyadic mesh of `[0,1]`. -/
lemma apm_a97A01_exists_dyadic_modulus
    (g : ℝ → ℝ) (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |x - y| ≤ (1 : ℝ) / (2 ^ m : ℕ) → |g x - g y| < ε := by
  have hu : UniformContinuousOn g (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hu) ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 : ℝ) / 2 < 1)
  refine ⟨m, fun x hx y hy hxy ↦ ?_⟩
  apply hmod x hx y hy
  rw [Real.dist_eq]
  have hmesh : (1 : ℝ) / (2 ^ m : ℕ) = ((1 : ℝ) / 2) ^ m := by
    rw [div_pow]
    norm_num
  exact lt_of_le_of_lt hxy (by simpa [hmesh] using hm)

/-- Sampling a continuous function at the left endpoints of a sufficiently
fine dyadic partition gives a pointwise approximation on `[0,1)`. -/
lemma apm_a97A01_exists_dyadic_step_pointwise
    (g : ℝ → ℝ) (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin (2 ^ m) → ℝ), ∀ t ∈ Ico (0 : ℝ) 1,
      |g t - ∑ j : Fin (2 ^ m), c j *
        (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
          ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) t| < ε := by
  obtain ⟨m, hm⟩ := apm_a97A01_exists_dyadic_modulus g hg hε
  let c : Fin (2 ^ m) → ℝ := fun j ↦ g ((j : ℕ) / (2 ^ m : ℕ))
  refine ⟨m, c, fun t ht ↦ ?_⟩
  have hpart := apm_a97A01_refinement_partition 0 0 m (Nat.zero_le m)
  have htU : t ∈ ⋃ r ∈ Finset.range (2 ^ m),
      Ico ((r : ℝ) / (2 ^ m : ℕ))
        (((r + 1 : ℕ) : ℝ) / (2 ^ m : ℕ)) := by
    have hpart' : Ico (0 : ℝ) 1 = ⋃ r ∈ Finset.range (2 ^ m),
        Ico ((r : ℝ) / (2 ^ m : ℕ))
          (((r + 1 : ℕ) : ℝ) / (2 ^ m : ℕ)) := by simpa using hpart
    rw [← hpart']
    exact ht
  simp only [mem_iUnion] at htU
  obtain ⟨r, hr, htr⟩ := htU
  let rfin : Fin (2 ^ m) := ⟨r, Finset.mem_range.mp hr⟩
  have hsum : (∑ j : Fin (2 ^ m), c j *
      (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
        ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
        (fun _ : ℝ ↦ (1 : ℝ)) t) = c rfin := by
    rw [Finset.sum_eq_single rfin]
    · rw [Set.indicator_of_mem htr]
      ring
    · intro s hs hsr
      have hts : t ∉ Ico (((s : ℕ) : ℝ) / (2 ^ m : ℕ))
          ((((s : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ)) := by
        intro hts
        have hpow : (0 : ℝ) < (2 ^ m : ℕ) := by positivity
        have h₁ : (s : ℝ) < ((r + 1 : ℕ) : ℝ) :=
          (div_lt_div_iff_of_pos_right hpow).mp (lt_of_le_of_lt hts.1 htr.2)
        have h₂ : (r : ℝ) < (((s : ℕ) + 1 : ℕ) : ℝ) :=
          (div_lt_div_iff_of_pos_right hpow).mp (lt_of_le_of_lt htr.1 hts.2)
        have h₁' : (s : ℕ) < r + 1 := by exact_mod_cast h₁
        have h₂' : r < (s : ℕ) + 1 := by exact_mod_cast h₂
        have heq : (s : ℕ) = r := by omega
        apply hsr
        exact Fin.ext heq
      change c s * _ = 0
      simp only [Set.indicator, hts, ↓reduceIte, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ rfin)).elim
  rw [hsum]
  have hr0 : (0 : ℝ) ≤ r / (2 ^ m : ℕ) := by positivity
  have hr1 : (r : ℝ) / (2 ^ m : ℕ) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    exact_mod_cast (le_of_lt rfin.isLt)
  apply hm t ⟨ht.1, le_of_lt ht.2⟩ _ ⟨hr0, hr1⟩
  rw [abs_of_nonneg (sub_nonneg.mpr htr.1)]
  have hw : (((r + 1 : ℕ) : ℝ) / (2 ^ m : ℕ) - (r : ℝ) / (2 ^ m : ℕ)) =
      (1 : ℝ) / (2 ^ m : ℕ) := by push_cast; ring
  linarith [htr.2]

/-- The pointwise dyadic sampling estimate integrates with no loss on the
unit restricted measure; the missing endpoint is null. -/
lemma apm_a97A01_exists_dyadic_step_L1
    (g : BoundedContinuousFunction ℝ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin (2 ^ m) → ℝ),
      ∫ t, |g t - ∑ j : Fin (2 ^ m), c j *
        (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
          ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) t| ∂apm_a97A01_measure < ε := by
  obtain ⟨m, c, hc⟩ :=
    apm_a97A01_exists_dyadic_step_pointwise g g.continuous (half_pos hε)
  refine ⟨m, c, ?_⟩
  letI : IsFiniteMeasure apm_a97A01_measure := by
    unfold apm_a97A01_measure
    infer_instance
  let s : ℝ → ℝ := fun t ↦ ∑ j : Fin (2 ^ m), c j *
    (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
      ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
      (fun _ : ℝ ↦ (1 : ℝ)) t
  have hs : Integrable s apm_a97A01_measure := by
    apply integrable_finset_sum
    intro j hj
    have hi : Integrable ((Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
        ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
        (fun _ : ℝ ↦ (1 : ℝ))) apm_a97A01_measure :=
      (integrable_const (μ := apm_a97A01_measure) (1 : ℝ)).indicator measurableSet_Ico
    simpa [mul_assoc] using hi.const_mul (c j)
  have hgint : Integrable (g : ℝ → ℝ) apm_a97A01_measure := by
    exact g.integrable apm_a97A01_measure
  have hleft : Integrable (fun t ↦ |g t - s t|) apm_a97A01_measure :=
    (hgint.sub hs).abs
  have hconst : Integrable (fun _ : ℝ ↦ ε / 2) apm_a97A01_measure := integrable_const _
  have hmem : ∀ᵐ t ∂apm_a97A01_measure, t ∈ Icc (0 : ℝ) 1 := by
    unfold apm_a97A01_measure
    exact ae_restrict_mem measurableSet_Icc
  have hne : ∀ᵐ t ∂apm_a97A01_measure, t ≠ 1 := by
    rw [ae_iff]
    simp [apm_a97A01_measure]
  have hae : ∀ᵐ t ∂apm_a97A01_measure, |g t - s t| ≤ ε / 2 := by
    filter_upwards [hmem, hne] with t ht ht1
    exact le_of_lt (hc t ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩)
  have hle := integral_mono_ae hleft hconst hae
  have hmeasure : apm_a97A01_measure.real univ = 1 := by
    simp [apm_a97A01_measure, Measure.real, Real.volume_Icc]
  rw [integral_const, hmeasure, one_smul] at hle
  have hehalf : ε / 2 < ε := by linarith
  simpa [s] using lt_of_le_of_lt hle hehalf

/-- Why this unblocks `apm_a97a01`: finite linear combinations of the casted
half-open dyadic cells are dense in `L¹[0,1]`.  Together with coarse-cell
cancellation and the compiled uniform integral bound, this transfers exact
cancellation to an arbitrary frozen `L∞` test function. -/
theorem apm_a97A01_bridge_3
    (f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin (2 ^ m) → ℝ),
      ∫ t,
        |f t - ∑ j : Fin (2 ^ m),
          c j *
            (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
              ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
              (fun _ : ℝ => (1 : ℝ)) t| ∂apm_a97A01_measure < ε := by
  letI : IsFiniteMeasure apm_a97A01_measure := by
    unfold apm_a97A01_measure
    infer_instance
  obtain ⟨g, hgcont, hfg⟩ :=
    apm_a97A01_exists_continuous_L1_approx f hf (half_pos hε)
  obtain ⟨m, c, hgs⟩ := apm_a97A01_exists_dyadic_step_L1 g (half_pos hε)
  refine ⟨m, c, ?_⟩
  let s : ℝ → ℝ := fun t ↦ ∑ j : Fin (2 ^ m),
    c j * (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
      ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
      (fun _ : ℝ ↦ (1 : ℝ)) t
  have hfint : Integrable f apm_a97A01_measure := hf.integrable (by simp)
  have hgint : Integrable (g : ℝ → ℝ) apm_a97A01_measure :=
    g.integrable apm_a97A01_measure
  have hsint : Integrable s apm_a97A01_measure := by
    apply integrable_finset_sum
    intro j hj
    have hi : Integrable ((Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
        ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
        (fun _ : ℝ ↦ (1 : ℝ))) apm_a97A01_measure :=
      (integrable_const (μ := apm_a97A01_measure) (1 : ℝ)).indicator measurableSet_Ico
    simpa [mul_assoc] using hi.const_mul (c j)
  have hleft : Integrable (fun t ↦ |f t - s t|) apm_a97A01_measure :=
    (hfint.sub hsint).abs
  have hright : Integrable (fun t ↦ |f t - g t| + |g t - s t|)
      apm_a97A01_measure := (hfint.sub hgint).abs.add (hgint.sub hsint).abs
  have htri : (∫ t, |f t - s t| ∂apm_a97A01_measure) ≤
      ∫ t, |f t - g t| + |g t - s t| ∂apm_a97A01_measure := by
    apply integral_mono_ae hleft hright
    filter_upwards with t
    exact abs_sub_le _ _ _
  have hadd : (∫ t, |f t - g t| + |g t - s t| ∂apm_a97A01_measure) =
      (∫ t, |f t - g t| ∂apm_a97A01_measure) +
        ∫ t, |g t - s t| ∂apm_a97A01_measure := by
    exact integral_add (hfint.sub hgint).abs (hgint.sub hsint).abs
  rw [hadd] at htri
  have hsum : (∫ t, |f t - g t| ∂apm_a97A01_measure) +
      ∫ t, |g t - s t| ∂apm_a97A01_measure < ε := by
    have hgs' : (∫ t, |g t - s t| ∂apm_a97A01_measure) < ε / 2 := by
      simpa [s] using hgs
    linarith
  simpa [s] using lt_of_le_of_lt htri hsum

theorem apm_a97a01
    (f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure) :
    Tendsto
      (fun n : ℕ ↦ ∫ t,
        f t * apm_a97A01_rademacher n t ∂apm_a97A01_measure)
      atTop (nhds 0) := by
  letI : IsFiniteMeasure apm_a97A01_measure := by
    unfold apm_a97A01_measure
    infer_instance
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, c, hc⟩ := apm_a97A01_bridge_3 f hf (half_pos hε)
  let s : ℝ → ℝ := fun t ↦ ∑ j : Fin (2 ^ m),
    c j * (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
      ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
      (fun _ : ℝ => (1 : ℝ)) t
  refine ⟨max (m + 1) 2, fun n hn ↦ ?_⟩
  have hmn : m < n := lt_of_lt_of_le (Nat.lt_succ_self m)
    (le_trans (Nat.le_max_left _ _) hn)
  have hn₂ : 1 < n := lt_of_lt_of_le (by omega)
    (le_trans (Nat.le_max_right _ _) hn)
  have hterm (j : Fin (2 ^ m)) : Integrable (fun t ↦
      c j * (Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
        ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))).indicator
        (fun _ : ℝ => (1 : ℝ)) t * apm_a97A01_rademacher n t)
        apm_a97A01_measure := by
    let A : Set ℝ := Ico (((j : ℕ) : ℝ) / (2 ^ m : ℕ))
      ((((j : ℕ) + 1 : ℕ) : ℝ) / (2 ^ m : ℕ))
    have hconst : Integrable (fun _ : ℝ ↦ (1 : ℝ)) apm_a97A01_measure :=
      integrable_const (1 : ℝ)
    have hind : Integrable (A.indicator (fun _ : ℝ ↦ (1 : ℝ)))
        apm_a97A01_measure := hconst.indicator measurableSet_Ico
    have hi := hind.mul_bdd (c := 1)
      (apm_a97A01_rademacher_measurable n).aestronglyMeasurable
      (by filter_upwards with t; simp [Real.norm_eq_abs, apm_a97A01_abs_rademacher])
    simpa [A, mul_assoc] using hi.const_mul (c j)
  have hs_int : Integrable (fun t ↦ s t * apm_a97A01_rademacher n t)
      apm_a97A01_measure := by
    simp only [s, Finset.sum_mul]
    exact integrable_finset_sum _ (fun j _ ↦ hterm j)
  have hs_cancel : ∫ t, s t * apm_a97A01_rademacher n t
      ∂apm_a97A01_measure = 0 := by
    simp only [s, Finset.sum_mul]
    rw [integral_finset_sum _ (fun j _ ↦ hterm j)]
    apply Finset.sum_eq_zero
    intro j hj
    simp_rw [mul_assoc]
    rw [integral_const_mul, apm_a97A01_bridge_2 m j n j.isLt hmn hn₂, mul_zero]
  have hf_int := apm_a97A01_integrable_mul_rademacher f hf n
  have hsplit : (∫ t, (f t - s t) * apm_a97A01_rademacher n t
      ∂apm_a97A01_measure) =
      ∫ t, f t * apm_a97A01_rademacher n t ∂apm_a97A01_measure := by
    have hfun : (fun t ↦ (f t - s t) * apm_a97A01_rademacher n t) =
        (fun t ↦ f t * apm_a97A01_rademacher n t -
          s t * apm_a97A01_rademacher n t) := by funext t; ring
    rw [hfun, integral_sub hf_int hs_int, hs_cancel, sub_zero]
  have hbound := apm_a97A01_norm_integral_mul_rademacher_le (fun t ↦ f t - s t) n
  rw [hsplit] at hbound
  rw [Real.dist_eq, sub_zero]
  have hhalf : ‖∫ t, f t * apm_a97A01_rademacher n t ∂apm_a97A01_measure‖ < ε / 2 :=
    by simpa [s] using lt_of_le_of_lt hbound hc
  have hehalf : ε / 2 < ε := by linarith
  simpa [Real.norm_eq_abs] using lt_trans hhalf hehalf
  /-
  CLOSER HOP 2 (2026-08-08): two analytic consequences that hop 1 only
  described now compile. `apm_a97A01_integrable_mul_rademacher` proves every
  frozen pairing is Bochner-integrable, and
  `apm_a97A01_norm_integral_mul_rademacher_le` proves the exact uniform error
  estimate

      ‖∫ g(t) r_n(t)‖ ≤ ∫ |g(t)|.

  Thus, once cancellation is known on an `L¹`-dense dyadic class, passage to
  arbitrary `f` is reduced to a standard epsilon argument with no remaining
  domination or integrability obligations.

  Going beyond hop 1, Mathlib's Hilbert-space orthonormal/Bessel APIs were
  also inspected as an alternate route. They would imply weak convergence
  after the encoded functions are bundled as an orthonormal sequence in
  `Lp ℝ 2`, but proving orthogonality requires the same exact dyadic
  cancellation. The existing `weak_convergence_of_ae_tendsto_L2_bounded`
  sibling lemma is inapplicable because Rademacher functions have no a.e.
  pointwise limit. No searched repository or Mathlib theorem identifies this
  custom existential interval encoding with a standard Rademacher system.

  The honest remaining bridge is therefore purely the exact cancellation on
  coarser dyadic intervals plus `L¹` density of their finite step functions.
  The exceptional `n = 1` branch must be excluded in cancellation. The frozen
  statement is unchanged and no unproved helper was introduced.

  CLOSER HOP 3 (2026-08-08): the positive half of the cellwise sign
  calculation now compiles as
  `apm_a97A01_rademacher_eq_one_of_mem_odd_cell`.  It unfolds the custom
  existential encoding and explicitly discharges the exceptional `n = 1`
  and endpoint `t = 1` branches, so future cancellation code can consume an
  odd-cell membership witness directly.  Attempts to strengthen this to an
  iff exposed the genuinely missing complementary fact: half-open dyadic
  cells of the same level are disjoint, hence a point in an even cell cannot
  satisfy the odd-cell existential.  Mathlib/repository searches supplied
  interval-disjointness ingredients but no theorem specialized to the
  casted `Nat` endpoints used here.  The remaining bridge is that uniqueness/
  even-cell lemma, finite paired-interval integration, and `L¹` density of
  dyadic step functions.  The frozen statement remains unchanged.
  -/
