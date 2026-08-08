import Mathlib

/-!
# APM t94A09 — vector fields on two spheres and a torus

## Statement repairs

None.

## Encoding note

A smooth tangent field on an embedded sphere is represented by a smooth
ambient extension whose restriction is orthogonal to the radius.  For the
product torus `S¹ × S¹`, the two components are likewise tangent to their
circle factors.  Thus the actual vector fields, tangency, smoothness, and zero
sets are retained explicitly.
-/

open InnerProductSpace
open scoped ContDiff

noncomputable section

abbrev apm_t94a09_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t94a09_E4 := EuclideanSpace ℝ (Fin 4)
abbrev apm_t94a09_S2 := Metric.sphere (0 : apm_t94a09_E3) 1
abbrev apm_t94a09_S3 := Metric.sphere (0 : apm_t94a09_E4) 1
abbrev apm_t94a09_Torus := Circle × Circle

def apm_t94a09_SmoothSphereField
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Metric.sphere (0 : E) 1 → E) : Prop :=
  ∃ Vext : E → E, ContDiff ℝ ∞ Vext ∧
    ∀ p : Metric.sphere (0 : E) 1,
      Vext p = V p ∧ ⟪V p, (p : E)⟫_ℝ = 0

def apm_t94a09_SmoothTorusField
    (V : apm_t94a09_Torus → ℂ × ℂ) : Prop :=
  ∃ Vext : (ℂ × ℂ) → (ℂ × ℂ), ContDiff ℝ ∞ Vext ∧
    ∀ p : apm_t94a09_Torus,
      Vext (p.1, p.2) = V p ∧
      Complex.re (V p).1 * Complex.re p.1 +
          Complex.im (V p).1 * Complex.im p.1 = 0 ∧
      Complex.re (V p).2 * Complex.re p.2 +
          Complex.im (V p).2 * Complex.im p.2 = 0

lemma apm_t94a09_smoothSphereField_restrict
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Vext : E → E) (hV : ContDiff ℝ ∞ Vext)
    (horth : ∀ p : Metric.sphere (0 : E) 1, ⟪Vext p, (p : E)⟫_ℝ = 0) :
    apm_t94a09_SmoothSphereField (fun p ↦ Vext p) := by
  exact ⟨Vext, hV, fun p ↦ ⟨rfl, horth p⟩⟩

lemma apm_t94a09_smoothTorusField_restrict
    (Vext : (ℂ × ℂ) → (ℂ × ℂ)) (hV : ContDiff ℝ ∞ Vext)
    (horth : ∀ p : apm_t94a09_Torus,
      Complex.re (Vext (p.1, p.2)).1 * Complex.re p.1 +
          Complex.im (Vext (p.1, p.2)).1 * Complex.im p.1 = 0 ∧
      Complex.re (Vext (p.1, p.2)).2 * Complex.re p.2 +
          Complex.im (Vext (p.1, p.2)).2 * Complex.im p.2 = 0) :
    apm_t94a09_SmoothTorusField (fun p ↦ Vext (p.1, p.2)) := by
  exact ⟨Vext, hV, fun p ↦ ⟨rfl, horth p⟩⟩

/-- The standard complex-structure rotation on `ℝ⁴`, written in coordinates. -/
def apm_t94a09_J (x : apm_t94a09_E4) : apm_t94a09_E4 :=
  WithLp.toLp 2 fun i =>
    match i with
    | 0 => -x 1
    | 1 => x 0
    | 2 => -x 3
    | 3 => x 2

lemma apm_t94a09_contDiff_J : ContDiff ℝ ∞ apm_t94a09_J := by
  unfold apm_t94a09_J
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> fun_prop

lemma apm_t94a09_inner_J (x : apm_t94a09_E4) :
    ⟪apm_t94a09_J x, x⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  rw [Fin.sum_univ_four]
  simp [apm_t94a09_J]
  rw [real_inner_comm (x 1) (x 0), real_inner_comm (x 3) (x 2)]
  ring

lemma apm_t94a09_J_ne_zero_of_ne_zero {x : apm_t94a09_E4} (hx : x ≠ 0) :
    apm_t94a09_J x ≠ 0 := by
  intro hJ
  apply hx
  ext i
  fin_cases i
  · have h := congrArg (fun y : apm_t94a09_E4 => y 1) hJ
    simpa [apm_t94a09_J] using h
  · have h := congrArg (fun y : apm_t94a09_E4 => y 0) hJ
    simpa [apm_t94a09_J] using h
  · have h := congrArg (fun y : apm_t94a09_E4 => y 3) hJ
    simpa [apm_t94a09_J] using h
  · have h := congrArg (fun y : apm_t94a09_E4 => y 2) hJ
    simpa [apm_t94a09_J] using h

lemma apm_t94a09_exists_smoothSphereField_S3 :
    ∃ V : apm_t94a09_S3 → apm_t94a09_E4,
      apm_t94a09_SmoothSphereField V ∧ ∀ p, V p ≠ 0 := by
  refine ⟨fun p => apm_t94a09_J p,
    apm_t94a09_smoothSphereField_restrict apm_t94a09_J
      apm_t94a09_contDiff_J (fun p => apm_t94a09_inner_J p), ?_⟩
  intro p
  apply apm_t94a09_J_ne_zero_of_ne_zero
  intro hp
  have := p.property
  simp [hp] at this

theorem apm_t94a09 :
    (¬∃ V : apm_t94a09_S2 → apm_t94a09_E3,
      apm_t94a09_SmoothSphereField V ∧ ∀ p, V p ≠ 0) ∧
    (∃ V : apm_t94a09_S3 → apm_t94a09_E4,
      apm_t94a09_SmoothSphereField V ∧ ∀ p, V p ≠ 0) ∧
    (∃ V : apm_t94a09_Torus → ℂ × ℂ,
      apm_t94a09_SmoothTorusField V ∧ ∃! p, V p = 0) := by
  /-
  Boundary (closer hop 1): the two restriction lemmas above remove the
  ambient-extension packaging for explicit fields.  The `S³` conjunct can use
  the linear complex-structure field `x ↦ (-x₁,x₀,-x₃,x₂)`, whose norm
  equals `‖x‖` and whose inner product with `x` vanishes.  The torus conjunct
  can use a fixed tangent direction multiplied by the nonnegative polynomial
  `‖z-1‖²+‖w-1‖²`, which vanishes at exactly `(1,1)`.

  Searches of `ConstructionTargets/`, `LEMMA-INDEX.md`, all closed sphere and
  vector-field artifacts, git history, and Mathlib's sphere, tangent-bundle,
  Euler-characteristic, degree, Poincaré--Hopf, and homotopy APIs found no
  hairy-ball theorem or equivalent obstruction for `S²`.  Thus the two
  existence clauses reduce to explicit finite-dimensional algebra and
  smoothness, while the first conjunct still requires a new hairy-ball proof
  (e.g. via degree or Poincaré--Hopf), which is the principal open bridge.

  CLOSER HOP 2: the `S³` existence clause is now completely compiled in
  `apm_t94a09_exists_smoothSphereField_S3`.  The explicit ambient rotation
  `apm_t94a09_J` is proved `C∞`, orthogonal to every radius, and injective at
  zero; restriction to the unit sphere is therefore a smooth nowhere-zero
  tangent field.  This closes all smoothness and coordinate algebra for the
  middle frozen conjunct rather than merely recording its candidate.

  A direct torus implementation was also investigated. Its tangency and
  unique-zero algebra reduce as expected to the nonnegative sum of two
  complex norm-squares, but Mathlib's smoothness automation does not recognize
  `Complex.normSq` or the real-to-complex inclusion as smooth without manually
  expanding both into real and imaginary coordinate polynomials. That finite
  packaging remains open alongside the substantially deeper first conjunct.
  Renewed inspection of the sphere-degree, antipodal-map, Euler-class, and
  vector-bundle sources still found no obstruction capable of proving the
  `S²` nonexistence clause. The frozen statement is unchanged.
  -/
  sorry
