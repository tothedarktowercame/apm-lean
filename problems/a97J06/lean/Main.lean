import Mathlib

/-!
# APM a97J06: A cosine transform

## Statement repairs

None.

## Encoding questions

None. The improper integral over `[0, ∞)` is represented by the Lebesgue set
integral over `Set.Ioi 0`; the omitted endpoint is a null set.
-/

open MeasureTheory Set
open scoped NNReal

noncomputable section

/-- The integrand `cos(tx) / (x² + 4)`. -/
def apm_a97J06_integrand (t x : ℝ) : ℝ :=
  Real.cos (t * x) / (x ^ 2 + 4)

/-- The exact zero-frequency normalization. -/
lemma apm_a97J06_integral_zero :
    ∫ x in Ioi (0 : ℝ), apm_a97J06_integrand 0 x ∂volume = Real.pi / 4 := by
  let γ : ℝ≥0 := ⟨2, by norm_num⟩
  have hγ : γ ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num [γ] at hv
  have hfull := ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 hγ
  have hwhole : (∫ x : ℝ, (x ^ 2 + 4)⁻¹) = Real.pi / 2 := by
    simp only [ProbabilityTheory.cauchyPDFReal_def, sub_zero] at hfull
    norm_num [γ] at hfull
    rw [MeasureTheory.integral_const_mul] at hfull
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hpi] at hfull ⊢
    exact hfull
  have heven := integral_comp_abs (f := fun x : ℝ => (x ^ 2 + 4)⁻¹)
  have hhalf : (∫ x in Ioi (0 : ℝ), (x ^ 2 + 4)⁻¹) = Real.pi / 4 := by
    rw [show (fun x : ℝ => (|x| ^ 2 + 4)⁻¹) = fun x => (x ^ 2 + 4)⁻¹ by
      funext x
      rw [sq_abs]] at heven
    rw [hwhole] at heven
    linarith
  simpa [apm_a97J06_integrand] using hhalf

/-- The half-line transform is even in its frequency parameter. -/
lemma apm_a97J06_integral_neg (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), apm_a97J06_integrand (-t) x ∂volume) =
      ∫ x in Ioi (0 : ℝ), apm_a97J06_integrand t x ∂volume := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp [apm_a97J06_integrand]

/-- The oscillatory kernel is absolutely integrable for every frequency. -/
lemma apm_a97J06_integrable (t : ℝ) :
    Integrable (apm_a97J06_integrand t) volume := by
  have hbase : Integrable (fun x : ℝ => (x ^ 2 + 4)⁻¹) volume := by
    have h := (integrable_inv_one_add_sq.const_mul (1 / 4 : ℝ)).comp_mul_left'
      (by norm_num : (1 / 2 : ℝ) ≠ 0)
    convert h using 1
    funext x
    field_simp
    ring
  apply hbase.mono'
  · apply Continuous.aestronglyMeasurable
    unfold apm_a97J06_integrand
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).div
      ((continuous_id.pow 2).add continuous_const) (fun x => by positivity)
  · filter_upwards with x
    unfold apm_a97J06_integrand
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < x ^ 2 + 4),
      inv_eq_one_div]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)

/-- Scaling `x = 2u` reduces this problem exactly to the standard Cauchy
kernel `1 / (1 + u²)` at frequency `2t`. -/
lemma apm_a97J06_integral_eq_half_standard (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), apm_a97J06_integrand t x ∂volume) =
      (1 / 2 : ℝ) *
        ∫ u in Ioi (0 : ℝ), Real.cos (u * (2 * t)) / (1 + u ^ 2) ∂volume := by
  have hscale := integral_comp_mul_left_Ioi (apm_a97J06_integrand t) 0
    (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero] at hscale
  have hpoint : (fun u : ℝ => apm_a97J06_integrand t (2 * u)) =
      fun u => (1 / 4 : ℝ) * (Real.cos (u * (2 * t)) / (1 + u ^ 2)) := by
    funext u
    rw [apm_a97J06_integrand]
    have hu : 1 + u ^ 2 ≠ 0 := by positivity
    field_simp [hu]
    ring
  rw [hpoint, integral_const_mul] at hscale
  change (1 / 4 : ℝ) *
      (∫ u in Ioi (0 : ℝ), Real.cos (u * (2 * t)) / (1 + u ^ 2) ∂volume) =
      (2 : ℝ)⁻¹ * (∫ x in Ioi (0 : ℝ), apm_a97J06_integrand t x ∂volume)
    at hscale
  norm_num at hscale ⊢
  linarith

/-- Why this unblocks `apm_a97j06`: this is the shared scale-one Cauchy
cosine-transform evaluation left open here and in `a03J05`.  It is the exact
positive-frequency consequence of the semicircle contour/residue argument;
the zero-frequency and negative-frequency reductions are already proved. -/
theorem apm_a97J06_bridge_1 (s : ℝ) (hs : 0 < s) :
    ∫ x in Ioi (0 : ℝ), Real.cos (x * s) / (1 + x ^ 2) ∂volume =
      (Real.pi / 2) * Real.exp (-s) := by
  sorry

theorem apm_a97j06 (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), apm_a97J06_integrand t x ∂volume =
      (Real.pi / 4) * Real.exp (-2 * |t|) := by
  -- BOUNDARY: This integral evaluates to (π/4)e^{-2|t|} via contour integration.
  -- The informal proof uses the residue theorem on e^{itz}/(z²+4) over a semicircular
  -- contour in the upper half-plane, enclosing the pole at z = 2i.
  --
  -- Routes assessed:
  -- 1. CONTOUR INTEGRATION (informal route): Mathlib has `circleIntegral` and the
  --    Cauchy integral formula (`Mathlib.Analysis.Complex.CauchyIntegral`), but NO
  --    machinery for semicircular contours, arc-vanishing estimates (ML-estimate),
  --    or a general residue theorem. Building the contour from scratch would require
  --    parametrizing the semicircular arc, proving the arc integral vanishes as R→∞
  --    (using |e^{itz}| ≤ 1 in the upper half-plane for t≥0), and connecting to the
  --    real integral — a major formalization effort.
  --
  -- 2. ODE APPROACH (alternative): I(t) = ∫₀^∞ cos(tx)/(x²+4) dx satisfies I'' = 4I
  --    for t ≠ 0 (after differentiating under the integral), giving I = Ce^{-2|t|}.
  --    The constant C = I(0) = π/4 is computable from `integral_Ioi_inv_one_add_sq`.
  --    Blocker: justifying differentiation under the integral requires dominated
  --    convergence for ∂²/∂t² of cos(tx)/(x²+4) = -x²cos(tx)/(x²+4), and the ODE
  --    argument I'' = 4I requires rewriting x²/(x²+4) = 1 - 4/(x²+4), where the
  --    ∫cos(tx) term is a distributional delta — not available as a Bochner integral.
  --
  -- 3. FOURIER TRANSFORM APPROACH: The integral is the Fourier cosine transform of
  --    the Poisson kernel 1/(x²+4). Mathlib has Fourier transform machinery
  --    (`Mathlib.Analysis/FourierTransform/`) but the specific transform of 1/(x²+a²)
  --    is not pre-computed and would require substantial setup.
  --
  -- APIs searched:
  -- - `circleIntegral`, `CauchyIntegral`: available but insufficient (no contour deformation)
  -- - `integral_Ioi_inv_one_add_sq`: gives ∫₀^∞ 1/(1+x²) dx = π/2 (useful for t=0 only)
  -- - `integral_Ioi_cpow_of_lt`, `integrableOn_Ioi_rpow_of_lt`: for power-type integrands
  -- - No `residue`, no `semicircle`, no `contour_integral_over_arc`
  --
  -- Specific blocker: No Mathlib API for semicircular contour integration or the
  -- residue theorem applied to real integrals. The ODE alternative hits a
  -- distributional delta (∫cos(tx) dx) that has no Bochner integral representation.
  -- This problem requires either new Mathlib infrastructure or an ad hoc proof
  -- spanning 100+ lines of careful complex analysis formalization.
  --
  -- CLOSER HOP 1: Git history contained compiled normalization and symmetry
  -- lemmas from an earlier branch that were absent at the frozen target commit.
  -- They are restored above, adapted to the present `Ioi` statement, as
  -- `apm_a97J06_integral_zero` and `apm_a97J06_integral_neg`. Consequently the
  -- live bridge is now only the evaluation for `0 < t`. A renewed search of
  -- `LEMMA-INDEX.md`, `ConstructionTargets.Sinc`, Mathlib's Cauchy-distribution,
  -- Fourier, Laplace, Cauchy-integral, and parametric-integral sources, plus
  -- closed artifacts, found no Cauchy characteristic-function theorem, justified
  -- Laplace inversion for this oscillatory kernel, residue theorem, or packaged
  -- semicircle/Jordan-lemma limit. `a03J05` has the same remaining transform at
  -- scale one; its new zero-frequency lemma does not close positive frequency.
  --
  -- CLOSER HOP 2: `apm_a97J06_integral_eq_half_standard` now compiles the
  -- exact change of variables `x = 2u`. It proves that this theorem is exactly
  -- one half of the scale-one Cauchy cosine transform at frequency `2t`,
  -- eliminating every denominator- and normalization-specific obligation.
  -- Sibling `a03J05` still has one sorry at that positive-frequency identity,
  -- so it cannot be reused to close this frozen theorem. The remaining bridge
  -- is now shared verbatim by the two artifacts.
  --
  -- CLOSER HOP 3: `apm_a97J06_integrable` now proves absolute integrability
  -- of the exact oscillatory kernel for every `t`. It scales Mathlib's
  -- `integrable_inv_one_add_sq` to `(x²+4)⁻¹` and applies `Real.abs_cos_le_one`
  -- through `Integrable.mono'`. This goes beyond the prior algebraic scaling
  -- reduction by discharging the principal domination prerequisite for any
  -- future Fourier/Fubini argument. The new sorry-free `a03J05` helper proves
  -- the same fact at scale one, but its positive-frequency evaluation remains
  -- sorry-backed. Renewed inspection therefore leaves precisely the same
  -- characteristic-function / contour-limit bridge open.
  sorry
