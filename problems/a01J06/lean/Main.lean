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

theorem apm_a01j06 (f : ℂ → ℂ) (ω : ℕ → ℂ) (A B : ℝ)
    (hf_entire : Differentiable ℂ f)
    (hf_nonzero : f ≠ 0)
    (hA : 0 < A)
    (hB : 0 < B)
    (hf_bound : apm_a01J06_ExpTypeBound f A B)
    (hω : apm_a01J06_EnumeratesZeros f ω) :
    ∀ α : ℝ, 1 < α →
      Summable (fun n : ℕ => Real.rpow (1 + ‖ω n‖) (-α)) := by
  sorry
