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

theorem apm_a97a01
    (f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure) :
    Tendsto
      (fun n : ℕ ↦ ∫ t,
        f t * apm_a97A01_rademacher n t ∂apm_a97A01_measure)
      atTop (nhds 0) := by
  /-
  CLOSER HOP 1 (2026-08-08): the two foundational analytic obligations are
  now compiled: `apm_a97A01_abs_rademacher` proves the exact pointwise bound
  `|r_n| = 1`, and `apm_a97A01_rademacher_measurable` proves measurability of
  the nested dyadic-existential definition.  Thus every pairing is integrable
  for the supplied `L∞` function on the finite measure space.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  conditional-expectation/martingale and simple-function density APIs, prior
  problems, the candidate artifact, and git history found no packaged weak
  convergence theorem for this custom dyadic sign encoding.  The remaining
  bridge is to prove exact cancellation on each coarser dyadic interval and
  approximate the `L∞` input in `L¹` by dyadic step functions (or equivalently
  invoke a dyadic martingale convergence theorem after constructing the
  filtration).  The pointwise unit bound then controls the approximation
  error.  The special `n = 1` constant branch is harmless for an `atTop`
  limit but must be excluded in the cancellation lemma.  The frozen statement
  is unchanged and no unproved helper was introduced.
  -/
  sorry
