import Mathlib

/-!
# APM m02J06

## Statement repairs

The printed condition `|x| = 0 ⇒ f(x) = 0` only constrains one point and makes
the compactness conclusion false by translations. Following the intended
Kolmogorov–Riesz argument, it is repaired to the uniform support condition
`|x| ≥ 1 ⇒ f(x) = 0`. The translation estimate is quantified over `h > 0`.
The usual nonnegativity condition for a mollifier is made explicit; it is
needed for the stated constant-one approximation estimate.

## Encoding questions

Compactness is asserted after mapping the actual measurable representatives
into Mathlib's `L¹` space, so it is compactness in the `L¹` norm and not a
pointwise-function topology.
-/

open MeasureTheory Set

/-- The class `K` from the problem, with its intended common support. -/
def apm_m02J06_K : Set (ℝ → ℝ) :=
  {f | Integrable f volume ∧
    ∫ x, |f x| ∂volume ≤ 1 ∧
    (∀ h : ℝ, 0 < h → ∫ x, |f (x + h) - f x| ∂volume ≤ Real.sqrt h) ∧
    (∀ x : ℝ, 1 ≤ |x| → f x = 0)}

/-- The standard rescaling of a mollifier. -/
noncomputable def apm_m02J06_mollifier (φ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ε⁻¹ * φ (x / ε)

/-- Convolution of two scalar functions on `ℝ`. -/
noncomputable def apm_m02J06_convolution (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t, f (x - t) * g t ∂volume

/-- The canonical class of an integrable function in `L¹(ℝ)`. -/
noncomputable def apm_m02J06_toL1 (f : ℝ → ℝ) (hf : Integrable f volume) :
    Lp ℝ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.2 hf).toLp f

/-- `K` regarded as a subset of the normed space `L¹(ℝ)`. -/
def apm_m02J06_KL1 : Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  {u | ∃ (f : ℝ → ℝ) (hf : Integrable f volume),
    f ∈ apm_m02J06_K ∧ u = apm_m02J06_toL1 f hf}

/-- The defining one-sided translation estimate for `apm_m02J06_K` extends
to arbitrary shifts.  The negative case uses Mathlib's
`integral_add_right_eq_self`; compare the translated-integral helper
`integral_translate_norm` in the solved artifact `a95J08`. -/
lemma apm_m02J06_translation_estimate
    {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) (h : ℝ) :
    ∫ x, |f (x + h) - f x| ∂volume ≤ Real.sqrt |h| := by
  rcases hf with ⟨_, _, htrans, _⟩
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have hk : 0 < -h := neg_pos.mpr hh
    have heq :
        (∫ x, |f (x + h) - f x| ∂volume) =
          ∫ x, |f (x + (-h)) - f x| ∂volume := by
      rw [← integral_add_right_eq_self
        (fun x : ℝ ↦ |f (x + h) - f x|) (-h)]
      congr 1
      funext x
      rw [add_assoc, neg_add_cancel, add_zero, abs_sub_comm]
    rw [heq, abs_of_neg hh]
    exact htrans (-h) hk
  · simp
  · rw [abs_of_pos hh]
    exact htrans h hh

theorem apm_m02j06 :
    ∀ (φ : ℝ → ℝ) (M : ℝ),
      ContDiff ℝ ⊤ φ →
      (∀ x, 0 ≤ φ x) →
      ∫ x, φ x ∂volume = 1 →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (∀ x, |φ x| ≤ M) →
      (∃ x, |φ x| = M) →
      (∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K,
        ∫ x, |f x - apm_m02J06_convolution f
          (apm_m02J06_mollifier φ ε) x| ∂volume ≤ Real.sqrt ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K, ∀ x y : ℝ,
        |apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x -
          apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) y| ≤
            (M / ε) * Real.sqrt |x - y|) ∧
      IsCompact apm_m02J06_KL1 := by
  /-
  SKIPPED (Kolmogorov–Riesz/L¹ quotient bridge). Mathlib searches found the
  general convolution integral API (`integral_convolution`) and abstract
  Arzelà–Ascoli theorems, but no Kolmogorov–Riesz compactness criterion for
  `Lp`, nor a compiled theorem transferring a uniformly supported,
  equicontinuous family of mollified representatives into total boundedness of
  their `L¹` equivalence classes.

  Closer hop 1 closes the first item in that list:
  `apm_m02J06_translation_estimate` extends the one-sided estimate to every
  real shift, using `integral_add_right_eq_self` (and the same translation
  principle as `integral_translate_norm` from solved artifact `a95J08`).
  `ConstructionTargets.YoungConvolution` supplies `convolution_memLp` and
  Young's inequality, but neither gives compactness.  A renewed search found
  `BoundedContinuousFunction.arzela_ascoli` and
  `isCompact_iff_totallyBounded_isComplete`; these can provide the abstract
  compactness step only after the mollified functions have been bundled with
  a common compact domain/range and their sup-norm nets transported to `Lp`.

  The remaining bridge is therefore to justify the Tonelli interchanges and
  rescaled-mollifier normalization/support bounds, build those bounded
  continuous maps, transfer their finite sup-norm nets to `L¹`, and prove
  `apm_m02J06_KL1` closed under changes of representatives modulo a.e.
  equality. `a96J02` contains convolution identities but no compactness route;
  `a96J03` only records an unfinished translation-continuity plan. The frozen
  statement was left unchanged.
  -/
  sorry
