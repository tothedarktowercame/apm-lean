import Mathlib

/-!
# APM a98A04

## Statement repairs

None.  The source's informal equation `sup = ∞` is represented by its
well-typed real-valued meaning: every real height is exceeded.

## Encoding questions

None.
-/

open MeasureTheory Set

/-- The singular spike `f_{a,b}` defined in the problem. -/
noncomputable def apm_a98a04_spike (a b x : ℝ) : ℝ :=
  if a < x ∧ x < b then 1 / Real.sqrt ((b - a) * (x - a)) else 0

lemma apm_a98a04_spike_nonneg (a b x : ℝ) :
    0 ≤ apm_a98a04_spike a b x := by
  unfold apm_a98a04_spike
  split_ifs
  · positivity
  · exact le_rfl

lemma apm_a98a04_spike_eq_zero_of_not_mem
    {a b x : ℝ} (hx : x ∉ Ioo a b) :
    apm_a98a04_spike a b x = 0 := by
  rw [apm_a98a04_spike, if_neg]
  exact fun h => hx h

theorem apm_a98a04 :
    (∀ a b : ℝ, a < b →
      Integrable (apm_a98a04_spike a b) volume ∧
      ∫ x : ℝ, apm_a98a04_spike a b x ∂volume = 2) ∧
    (∃ f : ℝ → ℝ,
      Integrable f volume ∧
      ∀ (g : ℝ → ℝ), g =ᵐ[volume] f →
        ∀ α β : ℝ, α < β →
          ∀ M : ℝ, ∃ x ∈ Ioo α β, M < g x) := by
  /-
  PARTIAL boundary (closer hop 1).

  The local spike is now proved nonnegative and exactly supported in `(a,b)`
  by `apm_a98a04_spike_nonneg` and
  `apm_a98a04_spike_eq_zero_of_not_mem`. Mathlib also provides
  `intervalIntegral.integrableOn_Ioo_rpow_iff`, which confirms integrability
  of the model singularity `x ^ (-1/2)` on `(0,t)`.

  Closing the first conjunct still requires transporting that result through
  `x ↦ x-a`, rewriting inverse square root as real `rpow (-1/2)`, extracting
  the positive factor `(b-a)⁻¹/²`, and evaluating the translated set integral
  as exactly `2`. The second conjunct then requires enumerating rational
  subintervals, constructing a pointwise finite real-valued sum of weighted
  spikes (rather than an `ℝ≥0∞` sum), proving integrability by summable L¹
  norms/monotone convergence, and showing every a.e.-equal representative
  exceeds each height on a positive-measure subinterval.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, closed artifacts,
  Mathlib's `rpow` integrability, integral substitution, simple-function,
  tsum-integral, and monotone-convergence APIs found the individual power and
  convergence ingredients but no packaged translated spike integral or
  everywhere-essentially-unbounded construction. Git history has no later
  attempt. No statement defect was found.
  -/
  sorry
