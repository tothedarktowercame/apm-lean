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

/-- The chosen `L¹` class is independent of the integrable representative. -/
lemma apm_m02J06_toL1_congr_ae
    {f g : ℝ → ℝ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hfg : f =ᵐ[volume] g) :
    apm_m02J06_toL1 f hf = apm_m02J06_toL1 g hg := by
  exact MemLp.toLp_congr (memLp_one_iff_integrable.2 hf)
    (memLp_one_iff_integrable.2 hg) hfg

/-- Positive rescaling preserves nonnegativity of the mollifier. -/
lemma apm_m02J06_mollifier_nonneg
    {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ apm_m02J06_mollifier φ ε x := by
  exact mul_nonneg (inv_nonneg.mpr hε.le) (hφ (x / ε))

/-- A mollifier supported in the unit interval rescales to support radius
`ε`. -/
lemma apm_m02J06_mollifier_eq_zero
    {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ |x| → φ x = 0)
    {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ |x|) :
    apm_m02J06_mollifier φ ε x = 0 := by
  rw [apm_m02J06_mollifier, hφ (x / ε)]
  · simp
  · rw [abs_div, abs_of_pos hε]
    exact (le_div_iff₀ hε).2 (by simpa using hx)

/-- The positive rescaling preserves total mass one. -/
lemma apm_m02J06_mollifier_integral_one
    {φ : ℝ → ℝ} (hφ : ∫ x, φ x ∂volume = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ x, apm_m02J06_mollifier φ ε x ∂volume = 1 := by
  have hscale := Measure.integral_comp_mul_left φ ε⁻¹
  simp only [inv_inv, abs_of_pos hε] at hscale
  have hscale' : (∫ x, φ (ε⁻¹ * x) ∂volume) = ε := by
    simpa [hφ, smul_eq_mul] using hscale
  change (∫ x, ε⁻¹ * φ (x / ε) ∂volume) = 1
  simp_rw [div_eq_inv_mul]
  rw [integral_const_mul, hscale']
  field_simp

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

/-- Convolution with the rescaled mollifier has a common compact support:
the support radius is the sum of the radii of `f` and the mollifier. -/
lemma apm_m02J06_convolution_eq_zero
    {φ f : ℝ → ℝ} (hφ : ∀ x, 1 ≤ |x| → φ x = 0)
    {ε : ℝ} (hε : 0 < ε) (hf : f ∈ apm_m02J06_K)
    {x : ℝ} (hx : 1 + ε ≤ |x|) :
    apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x = 0 := by
  unfold apm_m02J06_convolution
  have hz : (fun t : ℝ ↦
      f (x - t) * apm_m02J06_mollifier φ ε t) = 0 := by
    funext t
    by_cases ht : ε ≤ |t|
    · simp [apm_m02J06_mollifier_eq_zero hφ hε ht]
    · have ht' : |t| < ε := lt_of_not_ge ht
      have htri : |x| ≤ |x - t| + |t| := by
        calc
          |x| = |(x - t) + t| := by ring_nf
          _ ≤ |x - t| + |t| := abs_add_le _ _
      have hxt : 1 ≤ |x - t| := by linarith
      simp [hf.2.2.2 (x - t) hxt]
  simp [hz]

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

  CLOSER HOP 2: the rescaling and representative prerequisites are now closed.
  `apm_m02J06_toL1_congr_ae` proves independence of the integrable
  representative. `apm_m02J06_mollifier_nonneg` and
  `apm_m02J06_mollifier_eq_zero` prove nonnegativity and support radius `ε`.
  `apm_m02J06_mollifier_integral_one` applies
  `Measure.integral_comp_mul_left` to prove exact normalization.

  Searches beyond hop 1 covered `ConstructionTargets.LpRepresentative`, Haar
  scaling, `LpSpace.Basic`, and convolution/Tonelli sources. They supplied the
  compiled quotient and scaling lemmas above, but no packaged route builds the
  equicontinuous compact-domain family or transfers Arzelà--Ascoli nets into
  `L¹`. The remaining bridge is the Tonelli estimates, bounded-continuous-map
  packaging, finite-net transfer, and final compactness argument. The frozen
  statement remains unchanged.

  CLOSER HOP 3 goes beyond the prior quotient/scaling work by proving
  `apm_m02J06_convolution_eq_zero`: every mollified representative vanishes
  outside radius `1 + ε`. The proof splits on whether the convolution variable
  lies outside the mollifier radius and otherwise uses the triangle inequality
  to put `x - t` outside the common support of `f`. Thus the common compact
  domain required by Arzelà--Ascoli is now compiled, rather than merely listed
  as a packaging obligation.

  Renewed searches covered Mathlib's general and bounded-continuous-function
  Arzelà--Ascoli theorems, total-boundedness/compactness criteria, convolution
  decay siblings (`a03J03`, `a97J03`), and the entire reusable module set. No
  Fréchet--Kolmogorov theorem or finite-net transfer into `Lp` was found. The
  remaining bridge is narrower: prove the two Tonelli convolution estimates,
  bundle the now uniformly supported mollifications as an equicontinuous
  bounded-continuous family, transport its sup-norm nets into `L¹`, and prove
  closedness of `apm_m02J06_KL1`. The frozen statement remains unchanged.
  -/
  sorry
