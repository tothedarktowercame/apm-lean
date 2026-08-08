import Mathlib

/-!
# APM a01J06 — summability of zeros of an entire function of exponential type

## Statement repairs

The nonzero hypothesis `f ≠ 0` is made explicit. The identically zero function
satisfies the stated growth estimate but does not have a discrete sequence of
zeros with finite multiplicities, so the source's phrase “zeros listed with
appropriate multiplicity” implicitly excludes it.

The zero sequence is tied to `f` by requiring the finite fiber over every
point to have cardinality equal to Mathlib's analytic order of vanishing.
Thus neither the zero set nor its multiplicities are fabricated.
-/

open Complex

noncomputable section

def apm_a01J06_ExpTypeBound (f : ℂ → ℂ) (A B : ℝ) : Prop :=
  ∀ z : ℂ, ‖f z‖ ≤ B * Real.exp (A * ‖z‖)

def apm_a01J06_EnumeratesZeros (f : ℂ → ℂ) (ω : ℕ → ℂ) : Prop :=
  ∀ z : ℂ,
    Finite {n : ℕ // ω n = z} ∧
      Nat.card {n : ℕ // ω n = z} = analyticOrderNatAt f z

/-- The repaired fiber-cardinality encoding really does enumerate only zeros.
This is the first transport step needed to compare `ω` with the divisor in
Mathlib's Jensen formula. -/
lemma apm_a01J06_apply_eq_zero_of_enumeratesZeros
    {f : ℂ → ℂ} {ω : ℕ → ℂ}
    (hω : apm_a01J06_EnumeratesZeros f ω) (n : ℕ) :
    f (ω n) = 0 := by
  have hfinite := (hω (ω n)).1
  let i : {m : ℕ // ω m = ω n} := ⟨n, rfl⟩
  have hcard : 0 < Nat.card {m : ℕ // ω m = ω n} := by
    letI := Fintype.ofFinite {m : ℕ // ω m = ω n}
    letI : Nonempty {m : ℕ // ω m = ω n} := ⟨i⟩
    exact Nat.card_pos
  apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
  rw [← (hω (ω n)).2]
  exact Nat.ne_of_gt hcard

theorem apm_a01j06 (f : ℂ → ℂ) (ω : ℕ → ℂ) (A B : ℝ)
    (hf_entire : Differentiable ℂ f)
    (hf_nonzero : f ≠ 0)
    (hA : 0 < A)
    (hB : 0 < B)
    (hf_bound : apm_a01J06_ExpTypeBound f A B)
    (hω : apm_a01J06_EnumeratesZeros f ω) :
    ∀ α : ℝ, 1 < α →
      Summable (fun n : ℕ => Real.rpow (1 + ‖ω n‖) (-α)) := by
  /-
  CLOSER HOP 2: Mathlib now contains Jensen's formula as
  `MeromorphicOn.circleAverage_log_norm` and its divisor/log-counting
  reformulation
  `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`.
  The prior repository artifact at commit `a8f8752` cannot be reused: its
  `zeroCount` is definitionally zero and is not related to its `zeros`; the
  artifact itself proves a counterexample to precisely that missing link.

  The compiled lemma `apm_a01J06_apply_eq_zero_of_enumeratesZeros` above goes
  beyond that artifact and proves the repaired fiber-cardinality hypothesis
  sends every `ω n` to an actual zero.  The remaining bridge is quantitative:
  derive a linear ordinary zero-count bound from the logarithmic Jensen
  identity and the exponential bound, identify the finite divisor mass in a
  disk with the sum of the finite fiber cardinalities supplied by `hω`, and
  formalize the dyadic-shell comparison with the `α > 1` geometric series.
  No statement defect was found.
  -/
  sorry
