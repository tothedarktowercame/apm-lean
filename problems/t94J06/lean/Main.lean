import Mathlib
import ConstructionTargets.Rouche

/-!
# APM t94J06

## Statement repairs

None.

## Encoding questions

None.  The equation is stated directly over `ℂ`; its non-holomorphic real
term `cos ‖z‖` is explicitly coerced into `ℂ`.
-/

/-- The continuous, non-holomorphic function appearing in the problem. -/
noncomputable def apm_t94J06_function (z : ℂ) : ℂ :=
  z ^ 4 + 5 * z ^ 3 + Complex.I * z ^ 3 + ((Real.cos ‖z‖ : ℝ) : ℂ)

/-- On the circle of radius seven, the lower-order (including
non-holomorphic) part is strictly dominated by `z ^ 4`. -/
lemma apm_t94J06_boundary_domination {z : ℂ} (hz : ‖z‖ = 7) :
    ‖apm_t94J06_function z - z ^ 4‖ < ‖z ^ 4‖ := by
  have hcos : ‖((Real.cos ‖z‖ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one ‖z‖
  calc
    ‖apm_t94J06_function z - z ^ 4‖ =
        ‖5 * z ^ 3 + Complex.I * z ^ 3 + ((Real.cos ‖z‖ : ℝ) : ℂ)‖ := by
          simp only [apm_t94J06_function]
          ring_nf
    _ ≤ ‖5 * z ^ 3‖ + ‖Complex.I * z ^ 3‖ +
          ‖((Real.cos ‖z‖ : ℝ) : ℂ)‖ := by
            exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 5 * ‖z‖ ^ 3 + ‖z‖ ^ 3 + 1 := by
      gcongr <;> simp
    _ = 2059 := by rw [hz]; norm_num
    _ < 2401 := by norm_num
    _ = ‖z ^ 4‖ := by rw [norm_pow, hz]; norm_num

/-- The straight-line boundary homotopy from `z⁴` to the given function is
zero-free. This is the topological part of Rouché's estimate and does not use
holomorphicity. -/
lemma apm_t94J06_boundary_homotopy_ne_zero :
    ∀ t : Set.Icc (0 : ℝ) 1,
      ∀ z ∈ Metric.sphere (0 : ℂ) 7,
        z ^ 4 + (t.1 : ℂ) * (apm_t94J06_function z - z ^ 4) ≠ 0 := by
  apply ConstructionTargets.Rouche.rouche_homotopy_ne_zero_on_sphere
  intro z hz
  apply apm_t94J06_boundary_domination
  simpa [Metric.mem_sphere, dist_zero_right] using hz

theorem apm_t94j06 :
    ∃ z : ℂ, apm_t94J06_function z = 0 := by
  /-
  Boundary (closer hop 1, still open): the function is not holomorphic because of
  `Real.cos ‖z‖`, so Rouché's theorem and the argument principle cannot be
  applied. The intended route proves domination by `z ^ 4` on a large circle,
  constructs a nonvanishing straight-line boundary homotopy, computes winding
  number four, and invokes the topological fact that a nonzero boundary degree
  forces a zero in the disk. I searched Mathlib's winding number, loop degree,
  Brouwer/topological degree, punctured-plane homotopy, boundary-extension,
  Rouché, and argument-principle APIs. No winding-number or Brouwer-degree
  infrastructure is available to express the decisive step for a merely
  continuous map. The closer search additionally checked `LEMMA-INDEX.md`,
  `ConstructionTargets.Rouche`, all closed artifacts, winding-number siblings
  `t97J08` and `a95J03`, no-retraction/Brouwer searches, and git history. The
  reusable Rouché module supplies the elementary straight-line nonvanishing
  homotopy lemma without analyticity, but its zero-count transfer is analytic
  and therefore cannot apply here. The local lemma
  `apm_t94J06_boundary_domination` now proves the strict estimate on the
  radius-seven circle, and `apm_t94J06_boundary_homotopy_ne_zero` packages the
  resulting zero-free straight-line homotopy. What remains is exactly the topological degree theorem
  turning that boundary homotopy into an interior zero; the frozen existential
  conclusion exposes no further smaller proposition.
  -/
  sorry
