import Mathlib

/-!
# APM a99J07 — polynomial growth from the unit-disk sup norm

The unit-disk norm is the real supremum of the norms attained by `p` on the
actual closed unit disk.  The degree parameter `N` is explicitly pinned to
`p.natDegree`, and the conclusion is precisely the source's global growth
bound.

## Statement repairs

None.

## Encoding questions

None. Complex absolute values use the current norm notation.
-/

open Set

noncomputable section

def a99J07SupNormUnitDisk (p : Polynomial ℂ) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, ‖z‖ ≤ 1 ∧ r = ‖p.eval z‖}

theorem apm_a99j07
    (p : Polynomial ℂ) (N : ℕ)
    (hN : 1 ≤ N) (hdegree : p.natDegree = N) :
    ∀ w : ℂ,
      ‖p.eval w‖ ≤
        a99J07SupNormUnitDisk p * (max (1 : ℝ) ‖w‖) ^ N := by
  sorry
