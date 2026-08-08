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

theorem apm_a97a01
    (f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure) :
    Tendsto
      (fun n : ℕ ↦ ∫ t,
        f t * apm_a97A01_rademacher n t ∂apm_a97A01_measure)
      atTop (nhds 0) := by
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
  sorry
