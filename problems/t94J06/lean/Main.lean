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

/-- The map is continuous despite its explicitly non-holomorphic radial term. -/
lemma apm_t94J06_continuous : Continuous apm_t94J06_function := by
  unfold apm_t94J06_function
  fun_prop

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

/-- The compiled straight-line expression as an actual boundary homotopy. -/
noncomputable def apm_t94J06_boundaryHomotopy
    (p : Set.Icc (0 : ℝ) 1 × Metric.sphere (0 : ℂ) 7) : ℂ :=
  p.2.1 ^ 4 + (p.1.1 : ℂ) *
    (apm_t94J06_function p.2.1 - p.2.1 ^ 4)

/-- Continuity of the boundary homotopy, packaged for a future degree or
winding-number theorem. -/
lemma apm_t94J06_boundaryHomotopy_continuous :
    Continuous apm_t94J06_boundaryHomotopy := by
  unfold apm_t94J06_boundaryHomotopy
  have hf : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
      Metric.sphere (0 : ℂ) 7 => apm_t94J06_function p.2.1) :=
    apm_t94J06_continuous.comp (continuous_subtype_val.comp continuous_snd)
  fun_prop

/-- The bundled boundary homotopy takes values in the punctured plane. -/
lemma apm_t94J06_boundaryHomotopy_ne_zero
    (p : Set.Icc (0 : ℝ) 1 × Metric.sphere (0 : ℂ) 7) :
    apm_t94J06_boundaryHomotopy p ≠ 0 := by
  exact apm_t94J06_boundary_homotopy_ne_zero p.1 p.2.1 p.2.2

/-- In particular, the given function itself has no zero on the radius-seven
boundary; this is the `t = 1` endpoint of the compiled homotopy. -/
lemma apm_t94J06_boundary_ne_zero :
    ∀ z ∈ Metric.sphere (0 : ℂ) 7, apm_t94J06_function z ≠ 0 := by
  intro z hz
  have h := apm_t94J06_boundary_homotopy_ne_zero
    ⟨1, by constructor <;> norm_num⟩ z hz
  simpa using h

theorem apm_t94j06 :
    ∃ z : ℂ, apm_t94J06_function z = 0 := by
  /-
  Boundary (closer hop 2, still open): the function is not holomorphic because of
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
  resulting zero-free straight-line homotopy. This hop additionally proves
  `apm_t94J06_continuous` for the full non-holomorphic map and extracts
  `apm_t94J06_boundary_ne_zero` as the `t = 1` endpoint of that homotopy.
  What remains is exactly the topological degree theorem
  turning that boundary homotopy into an interior zero; the frozen existential
  conclusion exposes no further smaller proposition.

  Closer hop 3 packages the pointwise expression as the genuine map
  `apm_t94J06_boundaryHomotopy` on `[0,1] × sphere 0 7`, proves its continuity
  in `apm_t94J06_boundaryHomotopy_continuous`, and proves globally that it
  lands in the punctured plane via
  `apm_t94J06_boundaryHomotopy_ne_zero`. Thus a future degree/winding API can
  consume an actual continuous zero-free homotopy without reconstructing any
  analytic or subtype-continuity facts. A direct search for a real- or
  imaginary-axis root was also discarded: the imaginary equation forces the
  axis coordinate to zero, where the remaining real value is one. Renewed
  searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's homotopy,
  degree, Brouwer, punctured-plane, and fundamental-group sources, and related
  no-retraction artifacts found no theorem converting this bundled homotopy
  into an interior zero. The sole bridge remains that topological-degree step.
  -/
  sorry
