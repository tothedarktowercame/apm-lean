import Mathlib

/-!
# APM t96A04 — the unit-interval function space is not compact

`C` is represented by bundled continuous maps and carries the uniform metric.
-/

noncomputable section

local notation "I" => Set.Icc (0 : ℝ) 1
local notation "C" => ContinuousMap I I

theorem apm_t96a04 : ¬ IsCompact (Set.univ : Set C) := by
  sorry
