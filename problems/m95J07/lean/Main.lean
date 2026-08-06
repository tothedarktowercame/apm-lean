import Mathlib

/-!
# APM m95J07 — category and automatic continuity

## Statement repairs

None. “Second category” is read in its standard sense of “not meagre.”

## Encoding note

A function in `C[-1,1]` is differentiable at the interior point zero exactly
when its restriction has an ambient extension differentiable at zero; this
avoids replacing the sup-norm continuous-function space by all functions.
-/

abbrev apm_m95j07_C := ContinuousMap (Set.Icc (-1 : ℝ) 1) ℝ

def apm_m95j07_DifferentiableAtZero (f : apm_m95j07_C) : Prop :=
  ∃ F : ℝ → ℝ,
    (∀ t (ht : t ∈ Set.Icc (-1 : ℝ) 1), F t = f ⟨t, ht⟩) ∧
    DifferentiableAt ℝ F 0

theorem apm_m95j07 :
    (¬ IsMeagre {f : apm_m95j07_C | ¬ apm_m95j07_DifferentiableAtZero f}) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (T : X →ₗ[ℝ] X) (A : X →L[ℝ] X),
      Function.Injective A → Continuous (fun x => A (T x)) → Continuous T) := by
  -- SKIPPED: two-part functional analysis problem.
  -- (a) Nowhere-differentiable functions in C[-1,1] form a non-meagre set (second category).
  --     Classic Baire category theorem application.
  -- (b) Automatic continuity: if A∘T is continuous and A injective, then T continuous.
  --     Requires closed graph theorem or open mapping theorem.
  -- Blocker: (a) needs Baire category theorem application (meagre/non-meagre argument);
  -- (b) needs closed graph / open mapping theorem (may partially exist in Mathlib).
  -- APIs: `IsMeagre`, `ContinuousMap`, `ContinuousLinearMap`, `CompleteSpace`
  sorry
