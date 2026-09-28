import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open SchwartzMap MeasureTheory
open scoped SchwartzMap LineDeriv

noncomputable section

private noncomputable def lineMapCLM : ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).prod (-(ContinuousLinearMap.id ℝ ℝ))

private def lineMap : ℝ → ℝ × ℝ := fun s => (s, -s)

private lemma lineMap_temperate : lineMap.HasTemperateGrowth := by
  simpa [lineMap, lineMapCLM] using lineMapCLM.hasTemperateGrowth

private lemma lineMap_antilipschitz : AntilipschitzWith 1 lineMap := by
  intro x y
  simp only [edist_dist, ENNReal.coe_one, one_mul]
  apply ENNReal.ofReal_le_ofReal
  rw [dist_eq_norm, dist_eq_norm]
  exact le_max_left _ _

private noncomputable def restrictLine :
    𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  compCLMOfAntilipschitz ℂ lineMap_temperate lineMap_antilipschitz

private noncomputable def lineIntegralCLM : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] ℂ :=
  (integralCLM ℂ (volume : Measure ℝ)).comp restrictLine

private noncomputable def lineDistribution : 𝓢'(ℝ × ℝ, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ lineIntegralCLM

private lemma lineDistribution_apply (φ : 𝓢(ℝ × ℝ, ℂ)) :
    lineDistribution φ = ∫ s : ℝ, φ (s, -s) := by
  rfl

private lemma integral_tangent_deriv_eq_zero (φ : 𝓢(ℝ × ℝ, ℂ)) :
    ∫ s : ℝ, ((∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s) -
      (∂_{((0, 1) : ℝ × ℝ)} φ) (s, -s)) = 0 := by
  let g : 𝓢(ℝ, ℂ) := restrictLine φ
  have hg (s : ℝ) :
      deriv g s = (∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s) -
        (∂_{((0, 1) : ℝ × ℝ)} φ) (s, -s) := by
    have hl : HasDerivAt (fun t : ℝ ↦ (t, -t)) (1, -1) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_id s).neg
    have h := (φ.hasFDerivAt (s, -s)).comp_hasDerivAt s hl
    change deriv (fun t : ℝ ↦ φ (t, -t)) s = _
    rw [show deriv (fun t : ℝ ↦ φ (t, -t)) s =
      fderiv ℝ φ (s, -s) (1, -1) by
        simpa only [Function.comp_apply] using h.deriv]
    rw [show ((1, -1) : ℝ × ℝ) = (1, 0) - (0, 1) by ext <;> norm_num,
      map_sub]
    rfl
  rw [← MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hg)]
  exact MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s ↦ g.hasDerivAt s) (derivCLM ℝ ℂ g).integrable g.integrable

private lemma lineDeriv_comm (φ : 𝓢(ℝ × ℝ, ℂ)) :
    ∂_{((1, 0) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} φ) =
      ∂_{((0, 1) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} φ) := by
  ext z
  change ∂^{![((1, 0) : ℝ × ℝ), ((0, 1) : ℝ × ℝ)]} φ z =
    ∂^{![((0, 1) : ℝ × ℝ), ((1, 0) : ℝ × ℝ)]} φ z
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact ((φ.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

private lemma tempered_lineDeriv_comm (T : 𝓢'(ℝ × ℝ, ℂ)) :
    ∂_{((1, 0) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} T) =
      ∂_{((0, 1) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} T) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    LineDeriv.lineDerivOp_neg, neg_neg]
  rw [lineDeriv_comm]

private lemma lineDistribution_deriv_eq :
    ∂_{((1, 0) : ℝ × ℝ)} lineDistribution =
      ∂_{((0, 1) : ℝ × ℝ)} lineDistribution := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply]
  rw [lineDistribution_apply, lineDistribution_apply]
  have hz := integral_tangent_deriv_eq_zero φ
  have hix : Integrable (fun s : ℝ ↦
      (∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s)) := by
    simpa [restrictLine, lineMap] using
      (restrictLine (∂_{((1, 0) : ℝ × ℝ)} φ)).integrable
  have hiy : Integrable (fun s : ℝ ↦
      (∂_{((0, 1) : ℝ × ℝ)} φ) (s, -s)) := by
    simpa [restrictLine, lineMap] using
      (restrictLine (∂_{((0, 1) : ℝ × ℝ)} φ)).integrable
  rw [integral_sub hix hiy] at hz
  have heq := sub_eq_zero.mp hz
  change ∫ s : ℝ, -(∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s) =
    ∫ s : ℝ, -(∂_{((0, 1) : ℝ × ℝ)} φ) (s, -s)
  simpa only [integral_neg] using congrArg Neg.neg heq

theorem apm_m97a05 :
    ∃ T : 𝓢'(ℝ × ℝ, ℂ),
      (∀ φ : 𝓢(ℝ × ℝ, ℂ), T φ = ∫ s : ℝ, φ (s, -s)) ∧
      ∂_{((1, 0) : ℝ × ℝ)} T = ∂_{((0, 1) : ℝ × ℝ)} T ∧
      ∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} T) =
        ∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} T) := by
  refine ⟨lineDistribution, lineDistribution_apply, lineDistribution_deriv_eq, ?_⟩
  calc
    ∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} lineDistribution) =
        ∂_{((1, 0) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} lineDistribution) :=
      congrArg (∂_{((1, 0) : ℝ × ℝ)} ·) lineDistribution_deriv_eq
    _ = ∂_{((0, 1) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} lineDistribution) :=
      tempered_lineDeriv_comm lineDistribution
    _ = ∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} lineDistribution) :=
      congrArg (∂_{((0, 1) : ℝ × ℝ)} ·) lineDistribution_deriv_eq
