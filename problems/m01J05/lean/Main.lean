import Mathlib

open Filter

noncomputable section

def apm_m01J05_newtonStep {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (fderiv ℝ F x).inverse (F x)

def apm_m01J05_newtonIterate {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 => apm_m01J05_newtonStep F (apm_m01J05_newtonIterate F x₀ k)

universe u

theorem apm_m01j05 :
    (∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [Nonempty X]
        (T : X → X) (q : ℝ),
      0 ≤ q → q < 1 →
      (∀ x y : X, dist (T x) (T y) ≤ q * dist x y) →
        ∃ xStar : X,
          T xStar = xStar ∧
          (∀ y : X, T y = y → y = xStar) ∧
          ∀ x₀ : X,
            Tendsto (fun k ↦ (T^[k]) x₀) atTop (nhds xStar)) ∧
    (∀ (n : ℕ)
        (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (xStar : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      F xStar = 0 →
      Function.Bijective (fderiv ℝ F xStar) →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x₀ : EuclideanSpace ℝ (Fin n), dist x₀ xStar ≤ ε →
            (∀ k : ℕ,
              Function.Bijective
                (fderiv ℝ F (apm_m01J05_newtonIterate F x₀ k))) ∧
            Tendsto (apm_m01J05_newtonIterate F x₀) atTop (nhds xStar)) := by
  constructor
  · intro X instMetric instComplete instNonempty T q hq0 hq1 hdist
    let K : NNReal := ⟨q, hq0⟩
    have hK : ContractingWith K T := by
      refine ⟨?_, ?_⟩
      · exact_mod_cast hq1
      · exact lipschitzWith_iff_dist_le_mul.mpr hdist
    refine ⟨hK.fixedPoint T, hK.fixedPoint_isFixedPt, ?_, ?_⟩
    · intro y hy
      exact hK.fixedPoint_unique hy
    · exact hK.tendsto_iterate_fixedPoint
  · intro n F xStar hF hFx hbij
    let E := EuclideanSpace ℝ (Fin n)
    let L : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective
      (fderiv ℝ F xStar) (LinearMap.ker_eq_bot.mpr hbij.1)
        (LinearMap.range_eq_top.mpr hbij.2)
    have hLeq : (L : E →L[ℝ] E) = fderiv ℝ F xStar := rfl
    have hInv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ContinuousLinearMap.inverse
        (fderiv ℝ F xStar) := by
      rw [← hLeq]
      exact contDiffAt_map_inverse L
    have hDf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) :=
      hF.fderiv_right (by simp)
    have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => (fderiv ℝ F x).inverse) xStar :=
      hInv.comp xStar hDf.contDiffAt
    have hprod : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => (fderiv ℝ F x).inverse (F x)) xStar :=
      hA.clm_apply hF.contDiffAt
    have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (apm_m01J05_newtonStep F) xStar := by
      simpa [apm_m01J05_newtonStep] using contDiffAt_id.sub hprod
    have hGfix : apm_m01J05_newtonStep F xStar = xStar := by
      simp [apm_m01J05_newtonStep, hFx]
    have hGderiv : fderiv ℝ (apm_m01J05_newtonStep F) xStar = 0 := by
      rw [show apm_m01J05_newtonStep F =
          fun x => x - (fderiv ℝ F x).inverse (F x) by rfl]
      change fderiv ℝ ((fun x : E => x) -
        fun x => (fderiv ℝ F x).inverse (F x)) xStar = 0
      rw [fderiv_sub (f := fun x : E => x)
        (g := fun x => (fderiv ℝ F x).inverse (F x))
        differentiableAt_id (hprod.differentiableAt (by simp))]
      rw [show fderiv ℝ (fun x : E => x) xStar =
        ContinuousLinearMap.id ℝ E by
          exact (hasFDerivAt_id (𝕜 := ℝ) (x := xStar)).fderiv]
      rw [fderiv_clm_apply (hA.differentiableAt (by simp))
        (hF.differentiable (by simp) xStar)]
      rw [hFx]
      simp only [ContinuousLinearMap.map_zero, add_zero]
      have hinveq : (L : E →L[ℝ] E).inverse = (L.symm : E →L[ℝ] E) := by
        apply ContinuousLinearMap.inverse_eq
        · apply ContinuousLinearMap.ext
          intro x
          exact L.apply_symm_apply x
        · apply ContinuousLinearMap.ext
          intro x
          exact L.symm_apply_apply x
      have hinv : (fderiv ℝ F xStar).inverse.comp (fderiv ℝ F xStar) =
          ContinuousLinearMap.id ℝ E := by
        rw [← hLeq]
        rw [hinveq]
        apply ContinuousLinearMap.ext
        intro x
        exact L.symm_apply_apply x
      rw [hinv]
      exact sub_self _
    have hGstrict : HasStrictFDerivAt (apm_m01J05_newtonStep F)
        (0 : E →L[ℝ] E) xStar := by
      rw [← hGderiv]
      exact hG.hasStrictFDerivAt (by simp)
    let K : NNReal := 1 / 2
    have hK0 : (0 : NNReal) < K := by norm_num [K]
    have hK1 : K < 1 := by norm_num [K]
    obtain ⟨s, hs, hlip⟩ :=
      hGstrict.exists_lipschitzOnWith_of_nnnorm_lt K (by simpa using hK0)
    have hbij_ev : ∀ᶠ x in nhds xStar, Function.Bijective (fderiv ℝ F x) := by
      have hopen : IsOpen {A : E →L[ℝ] E | IsUnit A} := Units.isOpen
      have hmem : fderiv ℝ F xStar ∈ {A : E →L[ℝ] E | IsUnit A} :=
        ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
      filter_upwards [((hF.continuous_fderiv (by simp)).continuousAt.eventually
        (hopen.mem_nhds hmem))] with x hx
      exact ContinuousLinearMap.isUnit_iff_bijective.mp hx
    have hgood : s ∩ {x | Function.Bijective (fderiv ℝ F x)} ∈ nhds xStar :=
      inter_mem hs hbij_ev
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
    refine ⟨ε / 2, by positivity, ?_⟩
    intro x₀ hx₀
    have hx₀ball : x₀ ∈ Metric.ball xStar ε := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt hx₀ (by linarith)
    have hx₀s : x₀ ∈ s := (hball hx₀ball).1
    have hx₀bij : Function.Bijective (fderiv ℝ F x₀) := (hball hx₀ball).2
    have hiter : ∀ k,
        apm_m01J05_newtonIterate F x₀ k ∈ Metric.ball xStar ε ∧
        dist (apm_m01J05_newtonIterate F x₀ k) xStar ≤
          (K : ℝ) ^ k * dist x₀ xStar := by
      intro k
      induction k with
      | zero =>
          exact ⟨hx₀ball, by simp [apm_m01J05_newtonIterate]⟩
      | succ k ih =>
          have hks : apm_m01J05_newtonIterate F x₀ k ∈ s :=
            (hball ih.1).1
          have hxstars : xStar ∈ s := mem_of_mem_nhds hs
          have hstep := hlip.dist_le_mul
            (apm_m01J05_newtonIterate F x₀ k) hks xStar hxstars
          rw [hGfix] at hstep
          have hdist : dist (apm_m01J05_newtonIterate F x₀ (k + 1)) xStar ≤
              (K : ℝ) ^ (k + 1) * dist x₀ xStar := by
            rw [apm_m01J05_newtonIterate]
            calc
              _ ≤ (K : ℝ) * dist (apm_m01J05_newtonIterate F x₀ k) xStar := hstep
              _ ≤ (K : ℝ) * ((K : ℝ) ^ k * dist x₀ xStar) := by
                gcongr
                exact ih.2
              _ = (K : ℝ) ^ (k + 1) * dist x₀ xStar := by ring
          refine ⟨?_, hdist⟩
          rw [Metric.mem_ball]
          exact lt_of_le_of_lt hdist (by
            have hpow : (K : ℝ) ^ (k + 1) ≤ 1 := by
              exact pow_le_one₀ (by positivity) (by norm_num [K])
            calc
              (K : ℝ) ^ (k + 1) * dist x₀ xStar
                  ≤ 1 * dist x₀ xStar := by gcongr
              _ ≤ ε / 2 := by simpa using hx₀
              _ < ε := by linarith)
    constructor
    · intro k
      exact (hball (hiter k).1).2
    · rw [Metric.tendsto_atTop]
      intro δ hδ
      have hpowt : Tendsto (fun k : ℕ => (K : ℝ) ^ k) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (r := (K : ℝ))
          (by positivity) (by norm_num [K])
      have htend : Tendsto (fun k : ℕ => (K : ℝ) ^ k * dist x₀ xStar)
          atTop (nhds 0) := by
        simpa using hpowt.mul_const (dist x₀ xStar)
      have hev := htend.eventually (Metric.ball_mem_nhds 0 hδ)
      rw [eventually_atTop] at hev
      obtain ⟨N, hN⟩ := hev
      refine ⟨N, fun k hk => ?_⟩
      have hk' := hN k hk
      have hnonneg : 0 ≤ (K : ℝ) ^ k * dist x₀ xStar :=
        mul_nonneg (pow_nonneg (by positivity) _) dist_nonneg
      have hkbound : (K : ℝ) ^ k * dist x₀ xStar < δ := by
        simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hk'
      exact lt_of_le_of_lt (hiter k).2 hkbound
