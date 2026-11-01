import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open SchwartzMap MeasureTheory Real Complex
open Topology
open scoped SchwartzMap LineDeriv FourierTransform RealInnerProductSpace

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

/-! ### The Fourier transform of `T`, stated on `EuclideanSpace ℝ (Fin 2)`

`ℝ × ℝ` carries no `InnerProductSpace ℝ` structure, so Mathlib's Fourier transform of
tempered distributions is only available on `EuclideanSpace ℝ (Fin 2)`; we transport `T`
there along the canonical identification.  Under Mathlib's convention
`𝓕 f v = ∫ w, 𝐞 (-⟪w, v⟫) • f w` the Fourier transform of the line measure `T` is the
measure on the diagonal, i.e. `(𝓕 T) ψ = ∫ t, ψ (t, t)`. -/

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

private def toE2 (q : ℝ × ℝ) : E2 := WithLp.toLp 2 ![q.1, q.2]

private def line2 (s : ℝ) : E2 := WithLp.toLp 2 ![s, -s]

private lemma toE2_norm_sq (x y : ℝ) : ‖toE2 (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  simp only [toE2, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one, sq_abs]
  rw [Real.sq_sqrt (by positivity)]

/-- The covector `p ↦ ⟪(1,-1), p⟫`. -/
private def δline : E2 →ₗ[ℝ] ℝ := (innerₗ E2) (line2 1)

private lemma δline_apply (p : E2) : δline p = ⟪line2 1, p⟫ := rfl

private lemma line2_smul (s : ℝ) : line2 s = s • line2 1 := by
  ext i
  fin_cases i <;> simp [line2]

private lemma inner_line2 (s : ℝ) (p : E2) : ⟪line2 s, p⟫ = s * δline p := by
  rw [line2_smul, real_inner_smul_left, δline_apply]

/-- The canonical linear equivalence `E2 ≃ₗ[ℝ] ℝ × ℝ`. -/
private def toE2L : E2 ≃ₗ[ℝ] ℝ × ℝ where
  toFun p := ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)) p 0,
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)) p 1)
  invFun q := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm ![q.1, q.2]
  map_add' := by intro p p'; ext i <;> simp
  map_smul' := by intro r p; ext i <;> simp
  left_inv := by intro p; ext i; fin_cases i <;> simp
  right_inv := by intro q; ext i <;> simp

private def toE2E : E2 ≃L[ℝ] ℝ × ℝ := toE2L.toContinuousLinearEquiv

private lemma toE2E_symm_apply (q : ℝ × ℝ) : toE2E.symm q = toE2 q := rfl

/-- Pullback of test functions from `E2` to `ℝ × ℝ`. -/
private def pullE2 : 𝓢(E2, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ toE2E.symm

private lemma pullE2_apply (ψ : 𝓢(E2, ℂ)) : ⇑(pullE2 ψ) = ψ ∘ toE2 := rfl

/-- Transport of a tempered distribution on `ℝ × ℝ` to `E2`. -/
private def toDist (T : 𝓢'(ℝ × ℝ, ℂ)) : 𝓢'(E2, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ (T ∘L pullE2)

/-- The line distribution `T`, transported to `E2`. -/
private def distE2 : 𝓢'(E2, ℂ) := toDist lineDistribution

private lemma distE2_apply (ψ : 𝓢(E2, ℂ)) :
    distE2 ψ = ∫ s : ℝ, ψ (line2 s) := by
  have h1 : distE2 ψ = ∫ s : ℝ, (pullE2 ψ) (s, -s) := rfl
  rw [h1]
  congr 1

/-- Schwartz bound: `ψ` along the line decays faster than `1/(1+‖·‖²)²`. -/
private lemma psi_bound (ψ : 𝓢(E2, ℂ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : ℝ,
      ‖ψ (toE2 (x, y))‖ ≤ D / (1 + x ^ 2 + y ^ 2) ^ 2 := by
  have h0 : ∀ q : ℝ × ℝ, ‖ψ (toE2 q)‖ ≤ (SchwartzMap.seminorm ℝ 0 0) ψ :=
    fun q => SchwartzMap.norm_le_seminorm ℝ ψ (toE2 q)
  have h4 : ∀ q : ℝ × ℝ, ‖toE2 q‖ ^ 4 * ‖ψ (toE2 q)‖ ≤ (SchwartzMap.seminorm ℝ 4 0) ψ :=
    fun q => SchwartzMap.norm_pow_mul_le_seminorm ℝ ψ 4 (toE2 q)
  have hS0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0) ψ := by
    have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ ψ 0 (0 : E2)
    exact le_trans (norm_nonneg _) (by simpa using h)
  have hS4 : 0 ≤ (SchwartzMap.seminorm ℝ 4 0) ψ := by
    have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ ψ 4 (0 : E2)
    simpa using h
  refine ⟨4 * ((SchwartzMap.seminorm ℝ 0 0) ψ + (SchwartzMap.seminorm ℝ 4 0) ψ),
    by positivity, fun x y => ?_⟩
  have hn : ‖toE2 (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := toE2_norm_sq x y
  have key : ‖ψ (toE2 (x, y))‖ * (1 + x ^ 2 + y ^ 2) ^ 2
      ≤ 4 * ((SchwartzMap.seminorm ℝ 0 0) ψ + (SchwartzMap.seminorm ℝ 4 0) ψ) := by
    by_cases hle : 1 ≤ ‖toE2 (x, y)‖
    · have h4' : ‖ψ (toE2 (x, y))‖ ≤ (SchwartzMap.seminorm ℝ 4 0) ψ / ‖toE2 (x, y)‖ ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        exact mul_comm (‖ψ (toE2 (x, y))‖) _ ▸ h4 _
      have hsq : (1 + x ^ 2 + y ^ 2) ^ 2 ≤ 4 * ‖toE2 (x, y)‖ ^ 4 := by
        have h1 : 1 + x ^ 2 + y ^ 2 = 1 + ‖toE2 (x, y)‖ ^ 2 := by rw [hn]; ring
        have hm : 1 ≤ ‖toE2 (x, y)‖ ^ 2 := by nlinarith [hle]
        have h2 : (1 + ‖toE2 (x, y)‖ ^ 2) ^ 2 ≤ 4 * ‖toE2 (x, y)‖ ^ 4 := by
          nlinarith [hm]
        rw [h1]
        exact h2
      calc ‖ψ (toE2 (x, y))‖ * (1 + x ^ 2 + y ^ 2) ^ 2
          ≤ ((SchwartzMap.seminorm ℝ 4 0) ψ / ‖toE2 (x, y)‖ ^ 4)
              * (4 * ‖toE2 (x, y)‖ ^ 4) :=
            mul_le_mul h4' hsq (by positivity) (by positivity)
        _ = 4 * (SchwartzMap.seminorm ℝ 4 0) ψ := by field_simp
        _ ≤ 4 * ((SchwartzMap.seminorm ℝ 0 0) ψ + (SchwartzMap.seminorm ℝ 4 0) ψ) := by
            nlinarith [hS0, hS4]
    · have hlt : ‖toE2 (x, y)‖ < 1 := by
        by_contra hc
        push_neg at hc
        exact hle hc
      have hsq : (1 + x ^ 2 + y ^ 2) ^ 2 ≤ 4 := by
        have h1 : 1 + x ^ 2 + y ^ 2 = 1 + ‖toE2 (x, y)‖ ^ 2 := by rw [hn]; ring
        have h2 : ‖toE2 (x, y)‖ ^ 2 ≤ 1 := by
          nlinarith [hlt, norm_nonneg (toE2 (x, y))]
        rw [h1]
        nlinarith [h2]
      calc ‖ψ (toE2 (x, y))‖ * (1 + x ^ 2 + y ^ 2) ^ 2
          ≤ (SchwartzMap.seminorm ℝ 0 0) ψ * 4 :=
            mul_le_mul (h0 _) hsq (by positivity) (by positivity)
        _ ≤ 4 * ((SchwartzMap.seminorm ℝ 0 0) ψ + (SchwartzMap.seminorm ℝ 4 0) ψ) := by
            nlinarith [hS0, hS4]
  rw [le_div_iff₀ (by positivity)]
  exact key

private lemma continuous_toE2 : Continuous toE2 := by
  have h : toE2 = fun q => toE2E.symm q := funext toE2E_symm_apply
  rw [h]
  exact toE2E.symm.continuous

private lemma integrable_inv_two : Integrable (fun y : ℝ => (1 + y ^ 2) ^ (-(1 : ℝ))) := by
  have h := integrable_rpow_neg_one_add_norm_sq (r := 2) (E := ℝ) (μ := volume) (by norm_num)
  have heq : (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 : ℝ) / 2))
      = fun x : ℝ => (1 + x ^ 2) ^ (-(1 : ℝ)) := by
    funext x
    have hn : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
    rw [hn, show (-(2 : ℝ) / 2) = -(1 : ℝ) by norm_num]
  rw [heq] at h
  exact h

private lemma integrable_inv_four : Integrable (fun y : ℝ => (1 + y ^ 2) ^ (-(2 : ℝ))) := by
  have h := integrable_rpow_neg_one_add_norm_sq (r := 4) (E := ℝ) (μ := volume) (by norm_num)
  have heq : (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2))
      = fun x : ℝ => (1 + x ^ 2) ^ (-(2 : ℝ)) := by
    funext x
    have hn : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
    rw [hn, show (-(4 : ℝ) / 2) = -(2 : ℝ) by norm_num]
  rw [heq] at h
  exact h

private lemma rpow_inv_two (y : ℝ) : (1 + y ^ 2) ^ (-(1 : ℝ)) = 1 / (1 + y ^ 2) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_one, inv_eq_one_div]

private lemma rpow_inv_four (y : ℝ) :
    (1 + y ^ 2) ^ (-(2 : ℝ)) = 1 / (1 + y ^ 2) ^ 2 := by
  rw [Real.rpow_neg (by positivity)]
  norm_num [Real.rpow_natCast]

private lemma psi_le_line {ψ : 𝓢(E2, ℂ)} {D t y : ℝ} (hD : 0 ≤ D)
    (hbd : ∀ x y : ℝ, ‖ψ (toE2 (x, y))‖ ≤ D / (1 + x ^ 2 + y ^ 2) ^ 2) :
    ‖ψ (toE2 (t + y, y))‖ ≤ D * (1 + y ^ 2) ^ (-(2 : ℝ)) := by
  have h1 := hbd (t + y) y
  have h2 : (1 : ℝ) + y ^ 2 ≤ 1 + (t + y) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (t + y)]
  have h4 : (1 + y ^ 2) ^ 2 ≤ (1 + (t + y) ^ 2 + y ^ 2) ^ 2 := by nlinarith [h2]
  have hp1 : (0 : ℝ) < 1 + (t + y) ^ 2 + y ^ 2 := by nlinarith
  have hp2 : (0 : ℝ) < 1 + y ^ 2 := by nlinarith
  have hp3 : (0 : ℝ) < (1 + (t + y) ^ 2 + y ^ 2) ^ 2 := by nlinarith
  have hp4 : (0 : ℝ) < (1 + y ^ 2) ^ 2 := by nlinarith
  have h3 : D / (1 + (t + y) ^ 2 + y ^ 2) ^ 2 ≤ D / (1 + y ^ 2) ^ 2 :=
    div_le_div_of_nonneg_left (a := D) (b := (1 + (t + y) ^ 2 + y ^ 2) ^ 2)
      (c := (1 + y ^ 2) ^ 2) hD hp4 h4
  have h5 : D / (1 + y ^ 2) ^ 2 = D * (1 + y ^ 2) ^ (-(2 : ℝ)) := by
    rw [rpow_inv_four]
    ring
  rw [← h5]
  exact le_trans h1 h3

private lemma psi_integrable_line (ψ : 𝓢(E2, ℂ)) (t : ℝ) :
    Integrable (fun y : ℝ => ψ (toE2 (t + y, y))) := by
  obtain ⟨D, hD, hbd⟩ := psi_bound ψ
  have hcont : Continuous (fun y : ℝ => ψ (toE2 (t + y, y))) :=
    (ψ.continuous.comp continuous_toE2).comp
      ((continuous_const.add continuous_id).prodMk continuous_id)
  exact ((integrable_inv_four.const_mul D).mono' hcont.aestronglyMeasurable
    (MeasureTheory.ae_of_all volume fun y => psi_le_line hD hbd))

/-- The slice function `F t = ∫ y, ψ (t + y, y)`. -/
private def sliceF (ψ : 𝓢(E2, ℂ)) (t : ℝ) : ℂ := ∫ y : ℝ, ψ (toE2 (t + y, y))

private lemma sliceF_continuous (ψ : 𝓢(E2, ℂ)) : Continuous (sliceF ψ) := by
  obtain ⟨D, hD, hbd⟩ := psi_bound ψ
  have hconty : ∀ t : ℝ, Continuous (fun y : ℝ => ψ (toE2 (t + y, y))) :=
    fun t => (ψ.continuous.comp continuous_toE2).comp
      ((continuous_const.add continuous_id).prodMk continuous_id)
  have hcontt : ∀ y : ℝ, Continuous (fun t : ℝ => ψ (toE2 (t + y, y))) :=
    fun y => (ψ.continuous.comp continuous_toE2).comp
      ((continuous_id.add continuous_const).prodMk continuous_const)
  exact continuous_of_dominated (F := fun (t : ℝ) (y : ℝ) => ψ (toE2 (t + y, y)))
    (bound := fun y => D * (1 + y ^ 2) ^ (-(2 : ℝ)))
    (fun t => (hconty t).aestronglyMeasurable)
    (fun t => MeasureTheory.ae_of_all volume fun y => psi_le_line hD hbd)
    (integrable_inv_four.const_mul D)
    (MeasureTheory.ae_of_all volume fun y => hcontt y)

private lemma sliceF_integrable (ψ : 𝓢(E2, ℂ)) : Integrable (sliceF ψ) := by
  obtain ⟨D, hD, hbd⟩ := psi_bound ψ
  have hC : 0 ≤ ∫ y : ℝ, (1 + y ^ 2) ^ (-(1 : ℝ)) :=
    integral_nonneg (fun y => Real.rpow_nonneg (by positivity) _)
  refine ((integrable_inv_two.const_mul
      (2 * D * (∫ y : ℝ, (1 + y ^ 2) ^ (-(1 : ℝ))))).mono'
    (sliceF_continuous ψ).aestronglyMeasurable
    (MeasureTheory.ae_of_all volume fun t => ?_))
  set C := ∫ y : ℝ, (1 + y ^ 2) ^ (-(1 : ℝ)) with hC'
  -- the pointwise quadratic bound `(1 + (t+y)^2 + y^2)^2 ≥ (1 + t^2/2) * (1 + y^2)`
  have hPQ : ∀ y : ℝ, (1 + t ^ 2 / 2) * (1 + y ^ 2)
      ≤ (1 + (t + y) ^ 2 + y ^ 2) ^ 2 := by
    intro y
    have hs : (t + y) ^ 2 + y ^ 2 = t ^ 2 / 2 + 2 * (y + t / 2) ^ 2 := by ring
    nlinarith [hs, sq_nonneg (y + t / 2)]
  have hb : ∀ y : ℝ, ‖ψ (toE2 (t + y, y))‖ ≤ (2 * D / (2 + t ^ 2))
      * (1 + y ^ 2) ^ (-(1 : ℝ)) := by
    intro y
    have hp : (0 : ℝ) < 1 + (t + y) ^ 2 + y ^ 2 := by nlinarith
    have hp2 : (0 : ℝ) < 2 + t ^ 2 := by nlinarith
    have hp3 : (0 : ℝ) < 1 + y ^ 2 := by nlinarith
    have hpm : (0 : ℝ) < (1 + (t + y) ^ 2 + y ^ 2) ^ 2 := by nlinarith
    have key : D * (2 + t ^ 2) * (1 + y ^ 2)
        ≤ 2 * D * (1 + (t + y) ^ 2 + y ^ 2) ^ 2 := by nlinarith [hPQ y, hD]
    have h1 := hbd (t + y) y
    have hpm : (0 : ℝ) < (1 + (t + y) ^ 2 + y ^ 2) ^ 2 := by nlinarith
    rw [le_div_iff₀ hpm] at h1
    rw [rpow_inv_two]
    have heq : (2 * D / (2 + t ^ 2)) * (1 / (1 + y ^ 2))
        = 2 * D / ((2 + t ^ 2) * (1 + y ^ 2)) := by field_simp
    rw [heq, le_div_iff₀ (by nlinarith : (0 : ℝ) < (2 + t ^ 2) * (1 + y ^ 2))]
    have hm : (0 : ℝ) ≤ (2 + t ^ 2) * (1 + y ^ 2) := by nlinarith
    have h3 : ‖ψ (toE2 (t + y, y))‖ * (1 + (t + y) ^ 2 + y ^ 2) ^ 2
        * ((2 + t ^ 2) * (1 + y ^ 2)) ≤ D * ((2 + t ^ 2) * (1 + y ^ 2)) := by
      nlinarith [h1, hm]
    have h5 : ‖ψ (toE2 (t + y, y))‖ * (1 + (t + y) ^ 2 + y ^ 2) ^ 2
        * ((2 + t ^ 2) * (1 + y ^ 2))
        ≤ 2 * D * (1 + (t + y) ^ 2 + y ^ 2) ^ 2 :=
      le_trans h3 (by nlinarith [hPQ y, hD])
    nlinarith [h5, hpm]
  have hint : Integrable (fun y : ℝ => (2 * D / (2 + t ^ 2)) * (1 + y ^ 2) ^ (-(1 : ℝ))) :=
    integrable_inv_two.const_mul _
  have hfinal : (2 * D / (2 + t ^ 2)) * C ≤ (2 * D * C) * (1 + t ^ 2) ^ (-(1 : ℝ)) := by
    have heq : (2 * D / (2 + t ^ 2)) * C = 2 * D * C / (2 + t ^ 2) := by field_simp
    have heq2 : (2 * D * C) * (1 + t ^ 2) ^ (-(1 : ℝ)) = 2 * D * C / (1 + t ^ 2) := by
      rw [rpow_inv_two]; field_simp
    rw [heq, heq2]
    exact div_le_div_of_nonneg_left (a := 2 * D * C) (b := 2 + t ^ 2) (c := 1 + t ^ 2)
      (by nlinarith) (by nlinarith) (by nlinarith)
  calc ‖sliceF ψ t‖ ≤ ∫ y : ℝ, ‖ψ (toE2 (t + y, y))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (2 * D / (2 + t ^ 2)) * (1 + y ^ 2) ^ (-(1 : ℝ)) :=
        integral_mono (psi_integrable_line ψ t).norm hint (hb)
    _ = (2 * D / (2 + t ^ 2)) * C := integral_const_mul _ _
    _ ≤ (2 * D * C) * (1 + t ^ 2) ^ (-(1 : ℝ)) := hfinal

/-- The Gaussian kernel appearing in `Real.tendsto_integral_gaussian_smul'`. -/
private def ker (c t : ℝ) : ℂ :=
  ((π * c : ℂ) ^ ((1 : ℕ) / 2 : ℂ) * cexp (-(π ^ 2 * c) * t ^ 2))

private lemma fourier_gauss (c : ℝ) (hc : 0 < c) :
    (𝓕 (fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)))
      = fun t : ℝ => ((π * c : ℂ) ^ ((1 : ℕ) / 2 : ℂ)) * cexp (-(π ^ 2 * c) * t ^ 2) := by
  have hb : 0 < (((π * c)⁻¹ : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    positivity
  have hpi : ((c : ℂ)⁻¹) = (π : ℂ) * (((π * c)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hg := fourier_gaussian_pi hb
  have hden : 1 / (((π * c)⁻¹ : ℝ) : ℂ) ^ ((1 : ℕ) / 2 : ℂ)
      = ((π * c : ℂ)) ^ ((1 : ℕ) / 2 : ℂ) := by
    have hx : (((π * c)⁻¹ : ℝ) : ℂ) = ((π * c : ℂ))⁻¹ := by
      rw [show ((π : ℂ) * (c : ℂ)) = ((π * c : ℝ) : ℂ) from by push_cast; ring,
        ← Complex.ofReal_inv]
    rw [hx, show ((π : ℂ) * (c : ℂ)) = ((π * c : ℝ) : ℂ) from by push_cast; ring,
      inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]
        exact (ne_of_gt (show 0 < π by positivity)).symm),
      one_div, inv_inv]
  have hexp : (-(π : ℂ)) / (((π * c)⁻¹ : ℝ) : ℂ) = -(π ^ 2 * c) := by
    have h1 : (((π * c)⁻¹ : ℝ) : ℂ)⁻¹ = ((π * c : ℝ) : ℂ) := by
      rw [Complex.ofReal_inv, inv_inv]
    rw [div_eq_mul_inv, h1]
    push_cast
    ring
  have hL : (𝓕 (fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)))
      = 𝓕 (fun s : ℝ => cexp (-(π : ℂ) * (((π * c)⁻¹ : ℝ) : ℂ) * s ^ 2)) := by
    congr 1
    funext s
    rw [hpi]
    congr 2
    ring
  have hden' : 1 / (((π * c)⁻¹ : ℝ) : ℂ) ^ ((1 : ℕ) / 2 : ℂ)
      = ((π * c : ℂ)) ^ ((1 : ℕ) / 2 : ℂ) := hden
  rw [hL, hg]
  funext t
  have hexp2 : (-(π : ℂ)) / (((π * c)⁻¹ : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ 2
      = -(π ^ 2 * c) * ((t : ℝ) : ℂ) ^ 2 := by rw [hexp]
  have hexpeq : ((1 : ℕ) / 2 : ℂ) = ((1 : ℕ) / 2 : ℂ) := rfl
  norm_num at hden' hexp2 ⊢
  rw [← hden', ← hexp2]

private lemma ker_abs_bound {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖ker c t‖ ≤ ((π * c : ℂ) ^ ((1 : ℕ) / 2 : ℂ)).re := by
  have hpc : 0 < π * c := mul_pos pi_pos hc
  have he : ((1 : ℕ) / 2 : ℂ) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by norm_num
  have hcoef : ‖((π * c : ℂ) ^ ((1 : ℕ) / 2 : ℂ))‖ =
      ((π * c : ℂ) ^ ((1 : ℕ) / 2 : ℂ)).re := by
    rw [show (π * c : ℂ) = ((π * c : ℝ) : ℂ) by push_cast; ring, he,
      Complex.norm_cpow_eq_rpow_re_of_pos hpc, Complex.cpow_ofReal_re,
      Complex.arg_ofReal_of_nonneg hpc.le]
    norm_num [Real.norm_of_nonneg hpc.le]
    rw [abs_of_pos pi_pos, abs_of_pos hc]
  rw [ker, norm_mul, hcoef, Complex.norm_exp]
  apply mul_le_of_le_one_right (hcoef ▸ norm_nonneg _)
  rw [Real.exp_le_one_iff]
  norm_num [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im]
  exact mul_nonneg (mul_nonneg (sq_nonneg π) hc.le) (sq_nonneg t)

/-- The pairing `(s, p) ↦ ⟪line2 s, p⟫` as a bilinear map. -/
private def A : ℝ →ₗ[ℝ] E2 →ₗ[ℝ] ℝ where
  toFun s := s • δline
  map_add' := by intro s s'; ext p; simp [add_smul]
  map_smul' := by intro r s; ext p; simp [mul_smul]

private lemma A_apply (s : ℝ) (p : E2) : A s p = s * δline p := by
  simp [A, smul_eq_mul]

private lemma hδc : Continuous (fun p : E2 => δline p) := by
  have h : (fun p : E2 => δline p) = fun p : E2 => ⟪line2 1, p⟫ := funext δline_apply
  rw [h]
  exact continuous_inner.comp (continuous_const.prodMk continuous_id)

private lemma fourier_line_eq_flip (ψ : 𝓢(E2, ℂ)) {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, cexp (-(c : ℂ)⁻¹ * s ^ 2) * (𝓕 ψ) (line2 s) =
      ∫ p : E2, ψ p * ker c (δline p) := by
  have hLint : Continuous (fun q : ℝ × E2 => A q.1 q.2) := by
    have hf : (fun q : ℝ × E2 => A q.1 q.2)
        = fun q : ℝ × E2 => q.1 * δline q.2 := by
      funext q
      rw [A_apply]
    rw [hf]
    exact continuous_fst.mul (hδc.comp continuous_snd)
  have hgint : Integrable (fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)) := by
    have h1 : ((c : ℂ)⁻¹).re = ((c : ℝ)⁻¹) := by
      rw [← Complex.ofReal_inv, Complex.ofReal_re]
    have hb : 0 < ((c : ℂ)⁻¹).re := by rw [h1]; exact inv_pos.mpr hc
    have h := integrable_cexp_quadratic hb 0 0
    simpa using h
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure E2))
    (L := A) (f := fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)) (g := ⇑ψ)
    Real.continuous_fourierChar hLint hgint ψ.integrable
  have hline (s : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume A.flip (⇑ψ) s =
        FourierTransform.fourier ψ (line2 s) := by
      rw [SchwartzMap.fourier_coe, fourier_eq]
      apply integral_congr_ae
      filter_upwards with p
      congr 3
      rw [LinearMap.flip_apply, A_apply, real_inner_comm, inner_line2]
  have hgauss (p : E2) : VectorFourier.fourierIntegral Real.fourierChar volume A
          (fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)) p = ker c (δline p) := by
      rw [show VectorFourier.fourierIntegral Real.fourierChar volume A
          (fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)) p =
          FourierTransform.fourier (fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)) (δline p) by
        rw [fourier_eq]
        apply integral_congr_ae
        filter_upwards with s
        rw [A_apply]
        congr 3
        rw [show s = s • (1 : ℝ) by simp, real_inner_smul_left,
          show δline p = δline p • (1 : ℝ) by simp, real_inner_smul_right]
        simp [RCLike.inner_apply], fourier_gauss c hc]
      rfl
  calc
    _ = ∫ s : ℝ, cexp (-(c : ℂ)⁻¹ * s ^ 2) •
          VectorFourier.fourierIntegral Real.fourierChar volume A.flip (⇑ψ) s := by
      apply integral_congr_ae
      filter_upwards with s
      rw [hline]
      rfl
    _ = ∫ p : E2, VectorFourier.fourierIntegral Real.fourierChar volume A
          (fun s : ℝ => cexp (-(c : ℂ)⁻¹ * s ^ 2)) p • ψ p := hflip.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hgauss]
      simp [mul_comm]

private lemma slice_eq (ψ : 𝓢(E2, ℂ)) {c : ℝ} (hc : 0 < c) :
    ∫ p : E2, ψ p * ker c (δline p) =
      ∫ t : ℝ, ker c t * sliceF ψ t := by
  obtain ⟨D, hD, hbd⟩ := psi_bound ψ
  let K : ℝ := ((π * c : ℂ) ^ ((1 : ℕ) / 2 : ℂ)).re
  have hK : 0 ≤ K := le_trans (norm_nonneg (ker c 0)) (ker_abs_bound hc 0)
  have hI : Integrable (fun q : ℝ × ℝ => ker c q.1 * ψ (toE2 (q.1 + q.2, q.2))) := by
    have hm : AEStronglyMeasurable
        (fun q : ℝ × ℝ => ker c q.1 * ψ (toE2 (q.1 + q.2, q.2))) := by
      exact (show Continuous
          (fun q : ℝ × ℝ => ker c q.1 * ψ (toE2 (q.1 + q.2, q.2))) by
        apply Continuous.mul
        · unfold ker
          fun_prop
        · exact ψ.continuous.comp (continuous_toE2.comp
            ((continuous_fst.add continuous_snd).prodMk continuous_snd))).aestronglyMeasurable
    refine ((integrable_inv_two.mul_prod integrable_inv_two).const_mul (2 * D * K)).mono' hm ?_
    filter_upwards with q
    have hp : 0 < (1 + q.1 ^ 2) * (1 + q.2 ^ 2) := mul_pos (by positivity) (by positivity)
    have hp' : 0 < (1 + (q.1 + q.2) ^ 2 + q.2 ^ 2) ^ 2 := by positivity
    have hPQ : (1 + q.1 ^ 2 / 2) * (1 + q.2 ^ 2)
        ≤ (1 + (q.1 + q.2) ^ 2 + q.2 ^ 2) ^ 2 := by
      have hs : (q.1 + q.2) ^ 2 + q.2 ^ 2 =
          q.1 ^ 2 / 2 + 2 * (q.2 + q.1 / 2) ^ 2 := by ring
      nlinarith [hs, sq_nonneg (q.2 + q.1 / 2)]
    have hpsi : ‖ψ (toE2 (q.1 + q.2, q.2))‖ ≤
        2 * D / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2)) := by
      have h0 := hbd (q.1 + q.2) q.2
      rw [le_div_iff₀ hp'] at h0
      rw [le_div_iff₀ hp]
      nlinarith [hPQ, h0, norm_nonneg (ψ (toE2 (q.1 + q.2, q.2)))]
    rw [norm_mul, rpow_inv_two, rpow_inv_two]
    have hkq := ker_abs_bound hc q.1
    dsimp [K] at hK hkq ⊢
    calc
      ‖ker c q.1‖ * ‖ψ (toE2 (q.1 + q.2, q.2))‖
          ≤ K * (2 * D / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2))) :=
        mul_le_mul hkq hpsi (norm_nonneg _) hK
      _ = (2 * D * K) * (1 / (1 + q.1 ^ 2) * (1 / (1 + q.2 ^ 2))) := by
        field_simp
        <;> ring
  have hO : Integrable (fun q : ℝ × ℝ => ψ (toE2 q) * ker c (q.1 - q.2)) := by
    have hm : AEStronglyMeasurable
        (fun q : ℝ × ℝ => ψ (toE2 q) * ker c (q.1 - q.2)) := by
      exact (show Continuous
          (fun q : ℝ × ℝ => ψ (toE2 q) * ker c (q.1 - q.2)) by
        apply Continuous.mul
        · exact ψ.continuous.comp (continuous_toE2.comp continuous_id)
        · unfold ker
          fun_prop).aestronglyMeasurable
    refine ((integrable_inv_two.mul_prod integrable_inv_two).const_mul (D * K)).mono' hm ?_
    filter_upwards with q
    have hp : 0 < (1 + q.1 ^ 2) * (1 + q.2 ^ 2) := mul_pos (by positivity) (by positivity)
    have hp' : 0 < (1 + q.1 ^ 2 + q.2 ^ 2) ^ 2 := by positivity
    have hden : (1 + q.1 ^ 2) * (1 + q.2 ^ 2)
        ≤ (1 + q.1 ^ 2 + q.2 ^ 2) ^ 2 := by
      nlinarith [sq_nonneg q.1, sq_nonneg q.2,
        mul_nonneg (sq_nonneg q.1) (sq_nonneg q.2)]
    have hpsi : ‖ψ (toE2 q)‖ ≤ D / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2)) := by
      have h0 := hbd q.1 q.2
      rw [le_div_iff₀ hp'] at h0
      rw [le_div_iff₀ hp]
      nlinarith [hden, h0, norm_nonneg (ψ (toE2 q))]
    rw [norm_mul, rpow_inv_two, rpow_inv_two]
    have hkq := ker_abs_bound hc (q.1 - q.2)
    dsimp [K] at hK hkq ⊢
    calc
      ‖ψ (toE2 q)‖ * ‖ker c (q.1 - q.2)‖
          ≤ (D / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2))) * K :=
        mul_le_mul hpsi hkq (norm_nonneg _) (by positivity)
      _ = (D * K) * (1 / (1 + q.1 ^ 2) * (1 / (1 + q.2 ^ 2))) := by
        field_simp
        <;> ring
  rw [show (fun t : ℝ => ker c t * sliceF ψ t) =
      fun t : ℝ => ∫ y : ℝ, ker c t * ψ (toE2 (t + y, y)) by
    funext t
    rw [sliceF]
    exact (integral_const_mul (ker c t) _).symm]
  rw [integral_integral_swap hI]
  have htrans : (∫ y : ℝ, ∫ t : ℝ, ker c t * ψ (toE2 (t + y, y))) =
      ∫ y : ℝ, ∫ x : ℝ, ψ (toE2 (x, y)) * ker c (x - y) := by
    apply integral_congr_ae
    filter_upwards with y
    calc
      (∫ t : ℝ, ker c t * ψ (toE2 (t + y, y))) =
          ∫ t : ℝ, ψ (toE2 (t + y, y)) * ker c t := by
        apply integral_congr_ae
        filter_upwards with t
        rw [mul_comm]
      _ = _ := by
        rw [← (measurePreserving_add_right volume y).integral_comp
          (Homeomorph.addRight y).isClosedEmbedding.measurableEmbedding
          (fun x : ℝ => ψ (toE2 (x, y)) * ker c (x - y))]
        apply integral_congr_ae
        filter_upwards with t
        rw [add_comm]
        congr 2
        ring
  rw [Measure.volume_eq_prod] at hO
  rw [htrans, ← integral_integral_swap hO, integral_integral hO]
  rw [← Measure.volume_eq_prod]
  rw [← (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).integral_comp
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding]
  simp only [MeasurableEquiv.piFinTwo_apply, toE2]
  rw [show (fun x : Fin 2 → ℝ => ψ (WithLp.toLp 2 ![x 0, x 1]) * ker c (x 0 - x 1)) =
      fun x : Fin 2 → ℝ => ψ (WithLp.toLp 2 x) * ker c (x 0 - x 1) by
    funext x
    congr 3
    ext i
    fin_cases i <;> simp]
  rw [show (fun x : Fin 2 → ℝ => ψ (WithLp.toLp 2 x) * ker c (x 0 - x 1)) =
      fun x : Fin 2 → ℝ => ψ (WithLp.toLp 2 x) * ker c (δline (WithLp.toLp 2 x)) by
    funext x
    congr 2
    rw [δline_apply]
    rw [line2]
    rw [PiLp.inner_apply]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      WithLp.ofLp_toLp, one_mul]
    have hi (z : ℝ) : inner ℝ (1 : ℝ) z = z := by
      rw [show z = z • (1 : ℝ) by simp, real_inner_smul_right]
      simp
    have hn (z : ℝ) : inner ℝ (-1 : ℝ) z = -z := by
      rw [show (-1 : ℝ) = (-1 : ℝ) • (1 : ℝ) by simp, real_inner_smul_left, hi]
      simp
    rw [hi, hn]
    ring]
  exact ((PiLp.volume_preserving_toLp (Fin 2)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    (fun p : E2 => ψ p * ker c (δline p))).symm

private lemma fourier_distE2 (ψ : 𝓢(E2, ℂ)) :
    (𝓕 distE2) ψ = ∫ t : ℝ, ψ (toE2 (t, t)) := by
  have hline : Integrable (fun s : ℝ => (𝓕 ψ) (line2 s)) := by
    obtain ⟨D, hD, hbd⟩ := psi_bound (𝓕 ψ)
    refine (integrable_inv_four.const_mul D).mono'
      ((𝓕 ψ).continuous.comp (show Continuous line2 by
        rw [show line2 = fun s : ℝ => s • line2 1 from funext line2_smul]
        fun_prop)).aestronglyMeasurable ?_
    filter_upwards with s
    rw [rpow_inv_four]
    have h0 := hbd s (-s)
    have hp : 0 < (1 + s ^ 2) ^ 2 := by positivity
    have hp' : 0 < (1 + s ^ 2 + (-s) ^ 2) ^ 2 := by positivity
    rw [le_div_iff₀ hp'] at h0
    change ‖(𝓕 ψ) (toE2 (s, -s))‖ ≤ D * (1 / (1 + s ^ 2) ^ 2)
    rw [mul_one_div, le_div_iff₀ hp]
    have hden : (1 + s ^ 2) ^ 2 ≤ (1 + s ^ 2 + (-s) ^ 2) ^ 2 := by
      nlinarith [sq_nonneg s]
    exact le_trans (mul_le_mul_of_nonneg_left hden (norm_nonneg _)) h0
  have hA := Real.tendsto_integral_cexp_sq_smul hline
  have hA' : Filter.Tendsto (fun c : ℝ => ∫ t : ℝ, ker c t * sliceF ψ t)
      Filter.atTop (𝓝 ((𝓕 distE2) ψ)) := by
    have hlim : Filter.Tendsto (fun c : ℝ =>
        ∫ s : ℝ, cexp (-(c : ℂ)⁻¹ * s ^ 2) * (𝓕 ψ) (line2 s))
        Filter.atTop (𝓝 ((𝓕 distE2) ψ)) := by
      rw [TemperedDistribution.fourier_apply, distE2_apply]
      simpa only [smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_neg,
        Complex.ofReal_mul, ← Complex.ofReal_pow, Real.norm_eq_abs, sq_abs] using hA
    apply hlim.congr'
    filter_upwards [Filter.Ioi_mem_atTop 0] with c hc
    rw [fourier_line_eq_flip ψ hc, slice_eq ψ hc]
  have hB := Real.tendsto_integral_gaussian_smul'
    (sliceF_integrable ψ) (v := (0 : ℝ)) (sliceF_continuous ψ).continuousAt
  have hB' : Filter.Tendsto (fun c : ℝ => ∫ t : ℝ, ker c t * sliceF ψ t)
      Filter.atTop (𝓝 (sliceF ψ 0)) := by
    simpa [ker, CommSemiring.finrank_self, Real.norm_eq_abs, ← Complex.ofReal_pow,
      sq_abs, smul_eq_mul] using hB
  have heq : (𝓕 distE2) ψ = sliceF ψ 0 := tendsto_nhds_unique hA' hB'
  rw [heq, sliceF]
  apply integral_congr_ae
  filter_upwards with t
  congr 2
  simp

private lemma lineDistribution_lineDeriv_apply (φ : 𝓢(ℝ × ℝ, ℂ)) :
    (∂_{((1, 0) : ℝ × ℝ)} lineDistribution) φ =
      -(∫ s : ℝ, (∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s)) := by
  simp only [TemperedDistribution.lineDerivOp_apply_apply, lineDistribution_apply]
  rw [show (∫ s : ℝ, (-∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s))
      = ∫ s : ℝ, -((∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s)) from rfl, integral_neg]

theorem apm_m97a05 :
    ∃ T : 𝓢'(ℝ × ℝ, ℂ),
      (∀ φ : 𝓢(ℝ × ℝ, ℂ), T φ = ∫ s : ℝ, φ (s, -s)) ∧
      (∀ φ : 𝓢(ℝ × ℝ, ℂ), (∂_{((1, 0) : ℝ × ℝ)} T) φ =
        -(∫ s : ℝ, (∂_{((1, 0) : ℝ × ℝ)} φ) (s, -s))) ∧
      (∀ ψ : 𝓢(E2, ℂ), (𝓕 (toDist T)) ψ = ∫ t : ℝ, ψ (toE2 (t, t))) ∧
      ∂_{((1, 0) : ℝ × ℝ)} T = ∂_{((0, 1) : ℝ × ℝ)} T ∧
      ∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} T) =
        ∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} T) := by
  refine ⟨lineDistribution, lineDistribution_apply, lineDistribution_lineDeriv_apply,
    fourier_distE2, lineDistribution_deriv_eq, ?_⟩
  calc
    ∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} lineDistribution) =
        ∂_{((1, 0) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} lineDistribution) :=
      congrArg (∂_{((1, 0) : ℝ × ℝ)} ·) lineDistribution_deriv_eq
    _ = ∂_{((0, 1) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} lineDistribution) :=
      tempered_lineDeriv_comm lineDistribution
    _ = ∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} lineDistribution) :=
      congrArg (∂_{((0, 1) : ℝ × ℝ)} ·) lineDistribution_deriv_eq
