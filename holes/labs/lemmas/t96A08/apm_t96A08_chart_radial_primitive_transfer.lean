import Mathlib

noncomputable section

open scoped Manifold

/-! The repaired definition requires genuine smoothness on each closed member
of a finite subdivision.  This rules out derivatives with non-integrable
oscillatory singularities at the break points. -/

def apm_t96a08_IsPiecewiseSmoothPath
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (γ : ℝ → M) : Prop :=
  Continuous γ ∧
    ∃ (n : ℕ) (cuts : Fin (n + 1) → ℝ),
      StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last n) = 1 ∧
      ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) γ
        (Set.Icc (cuts i.castSucc) (cuts i.succ))

def apm_t96a08_LineIntegral
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (γ : ℝ → M) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..1,
    ω (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)

/-- The path operation needed by the fundamental theorem, separated from all
chart calculations. -/
def apm_t96A08_HasAdditiveConcatenation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ gamma delta : ℝ → M,
    apm_t96a08_IsPiecewiseSmoothPath I gamma →
    apm_t96a08_IsPiecewiseSmoothPath I delta →
    gamma 1 = delta 0 →
    ∃ eta : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I eta ∧
      eta 0 = gamma 0 ∧ eta 1 = delta 1 ∧
      apm_t96a08_LineIntegral I omega eta =
        apm_t96a08_LineIntegral I omega gamma +
          apm_t96a08_LineIntegral I omega delta

/-- The local output of the chart-linear-segment calculation.  Keeping this
as a proposition makes the analytic seat independent of path concatenation. -/
def apm_t96A08_HasLocalRadialPrimitives
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ g : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) g U ∧
      mfderiv I 𝓘(ℝ, ℝ) g x = omega x ∧
      ∀ z ∈ U, ∃ delta : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I delta ∧
        delta 0 = x ∧ delta 1 = z ∧
        g z - g x = apm_t96a08_LineIntegral I omega delta

/-- Two-speed concatenation: `gamma (2 t)` for `t ≤ 1/2`, then `delta (2 t - 1)`. -/
def apm_t96A08_concat {M : Type*} (gamma delta : ℝ → M) : ℝ → M :=
  fun t => if t ≤ (1 / 2 : ℝ) then gamma (2 * t) else delta (2 * t - 1)

/-- Seat: the concatenation of two repaired piecewise-smooth paths with
`gamma 1 = delta 0` is one (continuity by the matching endpoint; cut points
`cutsγ i / 2` followed by `(1 + cutsδ j) / 2`, dropping the duplicated `1/2`;
on each piece the path is an affine reparametrisation of a smooth piece). -/
theorem apm_t96A08_concat_piecewiseSmooth
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (gamma delta : ℝ → M)
    (hgamma : apm_t96a08_IsPiecewiseSmoothPath I gamma)
    (hdelta : apm_t96a08_IsPiecewiseSmoothPath I delta)
    (hend : gamma 1 = delta 0) :
    apm_t96a08_IsPiecewiseSmoothPath I (apm_t96A08_concat gamma delta) := by
  rcases hgamma with ⟨hγc, nγ, cγ, hγmono, hγzero, hγone, hγsmooth⟩
  rcases hdelta with ⟨hδc, nδ, cδ, hδmono, hδzero, hδone, hδsmooth⟩
  have hnγ : 0 < nγ := by
    by_contra h
    have hn : nγ = 0 := by omega
    subst nγ
    have he : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    rw [he] at hγzero
    linarith
  have hnδ : 0 < nδ := by
    by_contra h
    have hn : nδ = 0 := by omega
    subst nδ
    have he : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    rw [he] at hδzero
    linarith
  let cuts : Fin (nγ + nδ + 1) → ℝ := fun i ↦
    if h : i.val ≤ nγ then cγ ⟨i.val, by omega⟩ / 2
    else (1 + cδ ⟨i.val - nγ, by omega⟩) / 2
  have hcont : Continuous (apm_t96A08_concat gamma delta) := by
    apply Continuous.if_le
    · exact hγc.comp (continuous_const.mul continuous_id)
    · exact hδc.comp ((continuous_const.mul continuous_id).sub continuous_const)
    · exact continuous_id
    · exact continuous_const
    · intro t ht
      have ht' : t = (1 / 2 : ℝ) := by linarith
      subst t
      simpa [hend]
  refine ⟨hcont, nγ + nδ, cuts, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val ≤ nγ
    · by_cases hj : j.val ≤ nγ
      · simp only [cuts, dif_pos hi, dif_pos hj]
        exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
          (hγmono hij)
      · simp only [cuts, dif_pos hi, dif_neg hj]
        have hleft : cγ ⟨i.val, by omega⟩ ≤ 1 := by
          rw [← hγone]
          apply hγmono.monotone
          simpa using hi
        have hright : 0 < cδ ⟨j.val - nγ, by omega⟩ := by
          rw [← hδzero]
          apply hδmono
          change 0 < j.val - nγ
          omega
        linarith
    · have hj : ¬j.val ≤ nγ := by omega
      simp only [cuts, dif_neg hi, dif_neg hj]
      have hv : i.val - nγ < j.val - nγ := by omega
      have hc : cδ ⟨i.val - nγ, by omega⟩ < cδ ⟨j.val - nγ, by omega⟩ :=
        hδmono hv
      linarith
  · simp [cuts, hγzero]
  · have he : (⟨nδ, by omega⟩ : Fin (nδ + 1)) = Fin.last nδ := by ext; simp
    simp [cuts, hnδ.ne', he, hδone]
  · intro i
    by_cases hi : i.val < nγ
    · have hics : (i.castSucc : Fin (nγ + nδ + 1)).val ≤ nγ := by simp; omega
      have his : (i.succ : Fin (nγ + nδ + 1)).val ≤ nγ := by simp; omega
      change i.val ≤ nγ at hics
      change i.val + 1 ≤ nγ at his
      have heq : Set.Icc (cuts i.castSucc) (cuts i.succ) ⊆
          (fun t : ℝ ↦ 2 * t) ⁻¹' Set.Icc (cγ ⟨i.val, by omega⟩)
            (cγ ⟨i.val + 1, by omega⟩) := by
        intro t ht
        simp only [Set.mem_preimage, Set.mem_Icc] at ht ⊢
        rw [show cuts i.castSucc = cγ ⟨i.val, by omega⟩ / 2 by simp [cuts, hics],
          show cuts i.succ = cγ ⟨i.val + 1, by omega⟩ / 2 by simp [cuts, his]] at ht
        constructor <;> linarith
      have haff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
          (fun t : ℝ ↦ 2 * t) := by
        exact contMDiff_const.mul contMDiff_id
      have hc := (hγsmooth ⟨i.val, hi⟩).comp haff.contMDiffOn heq
      apply hc.congr
      intro t ht
      have htle : t ≤ (2 : ℝ)⁻¹ := by
        have := ht.2
        rw [show cuts i.succ = cγ ⟨i.val + 1, by omega⟩ / 2 by simp [cuts, his]] at this
        have hcγ : cγ ⟨i.val + 1, by omega⟩ ≤ 1 := by
          rw [← hγone]
          apply hγmono.monotone
          change i.val + 1 ≤ nγ
          omega
        norm_num at this ⊢
        linarith
      have hp : t ≤ (1 / 2 : ℝ) := by norm_num [one_div] at htle ⊢; exact htle
      simp only [apm_t96A08_concat, if_pos hp, Function.comp_apply]
    · have his : ¬(i.succ : Fin (nγ + nδ + 1)).val ≤ nγ := by simp; omega
      change ¬i.val + 1 ≤ nγ at his
      have hil : i.val < nγ + nδ := i.isLt
      let k : Fin nδ := ⟨i.val - nγ, by omega⟩
      have hcutleft : cuts i.castSucc = (1 + cδ ⟨i.val - nγ, by omega⟩) / 2 := by
        by_cases he : i.val ≤ nγ
        · have hie : i.val = nγ := by omega
          have hefin : (⟨nγ, by omega⟩ : Fin (nγ + 1)) = Fin.last nγ := by ext; simp
          simp [cuts, he, hie, hefin, hγone, hδzero]
        · simp [cuts, he]
      have heq : Set.Icc (cuts i.castSucc) (cuts i.succ) ⊆
          (fun t : ℝ ↦ 2 * t - 1) ⁻¹' Set.Icc (cδ k.castSucc) (cδ k.succ) := by
        intro t ht
        simp only [Set.mem_preimage, Set.mem_Icc] at ht ⊢
        rw [hcutleft,
          show cuts i.succ = (1 + cδ ⟨i.val + 1 - nγ, by omega⟩) / 2 by
              simp [cuts, his]] at ht
        change cδ ⟨i.val - nγ, by omega⟩ ≤ 2 * t - 1 ∧
          2 * t - 1 ≤ cδ ⟨i.val - nγ + 1, by omega⟩
        have he : i.val + 1 - nγ = i.val - nγ + 1 := by omega
        simp [he] at ht
        constructor <;> linarith
      have haff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
          (fun t : ℝ ↦ 2 * t - 1) := by
        exact (contMDiff_const.mul contMDiff_id).sub contMDiff_const
      have hc := (hδsmooth k).comp haff.contMDiffOn heq
      apply hc.congr
      intro t ht
      by_cases hp : t ≤ (1 / 2 : ℝ)
      · have hlow := ht.1
        rw [hcutleft] at hlow
        have hcδ : 0 ≤ cδ ⟨i.val - nγ, by omega⟩ := by
          rw [← hδzero]
          apply hδmono.monotone
          change 0 ≤ i.val - nγ
          omega
        have hcz : cδ ⟨i.val - nγ, by omega⟩ = 0 := by linarith
        let z : Fin nδ := ⟨0, hnδ⟩
        have hidx : (⟨i.val - nγ, by omega⟩ : Fin (nδ + 1)) = 0 := by
          apply hδmono.injective
          simpa [hδzero] using hcz
        have kval : i.val - nγ = 0 := by
          simpa using congrArg Fin.val hidx
        have hkzero : k = z := by
          apply Fin.ext
          simp [k, z, kval]
        have htval : t = 1 / 2 := by linarith
        subst t
        norm_num [apm_t96A08_concat, hend]
      · simp only [apm_t96A08_concat, if_neg hp, Function.comp_apply]

/-- Seat: the line integral is additive under concatenation.  On `(0, 1/2)` the
manifold chain rule gives `mfderiv (concat) t 1 = 2 • mfderiv gamma (2 t) 1`
(similarly on `(1/2, 1)`); the endpoints are null.  Integrability on each closed
smooth piece comes from `homega_smooth` (continuous integrand, bounded on compact
pieces); then substitute `s = 2 t` and `s = 2 t - 1`
(`intervalIntegral.integral_comp_mul_left`, `integral_add_adjacent_intervals`). -/
theorem apm_t96A08_concat_lineIntegral
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (gamma delta : ℝ → M)
    (hgamma : apm_t96a08_IsPiecewiseSmoothPath I gamma)
    (hdelta : apm_t96a08_IsPiecewiseSmoothPath I delta)
    (hend : gamma 1 = delta 0) :
    apm_t96a08_LineIntegral I omega (apm_t96A08_concat gamma delta) =
      apm_t96a08_LineIntegral I omega gamma +
        apm_t96a08_LineIntegral I omega delta := by
  sorry

/-- Closed-piecewise-smooth paths can be concatenated, and the integral is
additive under the standard affine reparameterizations. -/
theorem apm_t96A08_piecewisePath_concat_additive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2)) :
    apm_t96A08_HasAdditiveConcatenation I omega := by
  intro gamma delta hgamma hdelta hend
  refine ⟨apm_t96A08_concat gamma delta,
    apm_t96A08_concat_piecewiseSmooth I gamma delta hgamma hdelta hend, ?_, ?_,
    apm_t96A08_concat_lineIntegral I omega homega_smooth gamma delta hgamma hdelta hend⟩
  · simp [apm_t96A08_concat]
  · norm_num [apm_t96A08_concat]

/-- In a sufficiently small convex chart, integration along the straight
coordinate segment gives a smooth local function whose derivative at the
centre is the prescribed one-form. -/
lemma apm_t96A08_chart_radial_primitive_aux_path_of_contMDiff
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) gamma) :
    apm_t96a08_IsPiecewiseSmoothPath I gamma := by
  refine ⟨hgamma.continuous, 1, fun i ↦ (i.val : ℝ), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · norm_num
  · norm_num
  · intro i
    exact hgamma.contMDiffOn

lemma apm_t96A08_chart_radial_primitive_aux_const_path
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (x : M) :
    apm_t96a08_IsPiecewiseSmoothPath I (fun _ : ℝ ↦ x) := by
  apply apm_t96A08_chart_radial_primitive_aux_path_of_contMDiff
  exact contMDiff_const

/-- A chart can be shrunk using an ambient convex set.  The intersection with
`range I` is essential at boundary points of a manifold with corners. -/
lemma apm_t96A08_chart_radial_primitive_chart_neighborhood
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (x : M) :
    ∃ (U : Set M) (W : Set E), IsOpen U ∧ x ∈ U ∧ IsOpen W ∧
      Convex ℝ W ∧ (extChartAt I x x) ∈ W ∧
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target ∧
      U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W := by
  sorry

/-- Relative convexity in the chart produces the clamped radial paths.  This
seat only does chart and endpoint bookkeeping. -/
lemma apm_t96A08_chart_radial_primitive_radial_paths
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (x : M) (U : Set M) (W : Set E)
    (hU : U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W)
    (hxW : extChartAt I x x ∈ W) (hWconv : Convex ℝ W)
    (hWtarget : W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target) :
    ∀ z ∈ U, ∃ delta : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I delta ∧ delta 0 = x ∧ delta 1 = z ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        extChartAt I x (delta t) = extChartAt I x x +
          t • (extChartAt I x z - extChartAt I x x) := by
  sorry

/-- Pulling the one-form and the radial path into the extended chart gives
the ordinary coordinate interval integral. -/
lemma apm_t96A08_chart_radial_primitive_coordinate_formula
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (x : M) (W : Set E)
    (hWtarget : W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target) :
    ∃ omegaCoord : E → (E →L[ℝ] ℝ),
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) omegaCoord
        (W ∩ Set.range (I : E → E)) ∧
      omegaCoord (extChartAt I x x) = (omega x).comp
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I)
          (extChartAt I x x)) ∧
      ∀ (z : M) (delta : ℝ → M),
        (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) →
        ContMDiffOn 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) delta (Set.Icc (0 : ℝ) 1) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          extChartAt I x (delta t) = extChartAt I x x +
            t • (extChartAt I x z - extChartAt I x x)) →
        apm_t96a08_LineIntegral I omega delta =
          ∫ t : ℝ in (0 : ℝ)..1, omegaCoord
            (extChartAt I x x + t • (extChartAt I x z - extChartAt I x x))
            (extChartAt I x z - extChartAt I x x) := by
  sorry

/-- The parameter-integral calculation in a normed vector space.  Smoothness
is requested on an ambient convex set, so this lemma has no corners issue. -/
lemma apm_t96A08_chart_radial_primitive_euclidean_calculus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (I : ModelWithCorners ℝ E E) (W : Set E) (a : E) (omegaCoord : E → (E →L[ℝ] ℝ))
    (hWopen : IsOpen W) (hWconv : Convex ℝ W) (haW : a ∈ W ∩ Set.range (I : E → E))
    (homega : ContDiffOn ℝ (⊤ : WithTop ℕ∞) omegaCoord
      (W ∩ Set.range (I : E → E))) :
    let G : E → ℝ := fun v ↦ ∫ t : ℝ in (0 : ℝ)..1,
      omegaCoord (a + t • (v - a)) (v - a)
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) G (W ∩ Set.range (I : E → E)) ∧
      fderivWithin ℝ G (W ∩ Set.range (I : E → E)) a = omegaCoord a := by
  sorry

/-- Transfer the ambient parameter-integral result through the chart.  All
four preceding conclusions are explicit hypotheses, keeping this seat
independent of their proofs. -/
-- BEGIN SEAT AREA
lemma apm_t96A08_chart_radial_primitive_transfer
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (hcharts : ∀ x : M, ∃ (U : Set M) (W : Set E), IsOpen U ∧ x ∈ U ∧
      IsOpen W ∧ Convex ℝ W ∧ extChartAt I x x ∈ W ∧
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target ∧
      U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W)
    (hpaths : ∀ (x : M) (U : Set M) (W : Set E),
      U = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' W →
      extChartAt I x x ∈ W → Convex ℝ W →
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target →
      ∀ z ∈ U, ∃ delta : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I delta ∧ delta 0 = x ∧ delta 1 = z ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, extChartAt I x (delta t) =
          extChartAt I x x + t • (extChartAt I x z - extChartAt I x x))
    (hcoord : ∀ (x : M) (W : Set E),
      W ∩ Set.range (I : E → E) ⊆ (extChartAt I x).target →
      ∃ omegaCoord : E → (E →L[ℝ] ℝ),
        ContDiffOn ℝ (⊤ : WithTop ℕ∞) omegaCoord
          (W ∩ Set.range (I : E → E)) ∧
        omegaCoord (extChartAt I x x) = (omega x).comp
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I)
            (extChartAt I x x)) ∧
        ∀ (z : M) (delta : ℝ → M),
          (∀ t ∈ Set.Icc (0 : ℝ) 1, delta t ∈ (extChartAt I x).source) →
          ContMDiffOn 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) delta (Set.Icc (0 : ℝ) 1) →
          (∀ t ∈ Set.Icc (0 : ℝ) 1, extChartAt I x (delta t) =
            extChartAt I x x + t • (extChartAt I x z - extChartAt I x x)) →
          apm_t96a08_LineIntegral I omega delta = ∫ t : ℝ in (0 : ℝ)..1,
            omegaCoord (extChartAt I x x + t •
              (extChartAt I x z - extChartAt I x x))
              (extChartAt I x z - extChartAt I x x))
    (heuclid : ∀ (W : Set E) (a : E) (omegaCoord : E → (E →L[ℝ] ℝ)),
      IsOpen W → Convex ℝ W → a ∈ W ∩ Set.range (I : E → E) →
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) omegaCoord
        (W ∩ Set.range (I : E → E)) →
      let G : E → ℝ := fun v ↦ ∫ t : ℝ in (0 : ℝ)..1,
        omegaCoord (a + t • (v - a)) (v - a)
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) G (W ∩ Set.range (I : E → E)) ∧
      fderivWithin ℝ G (W ∩ Set.range (I : E → E)) a = omegaCoord a) :
    apm_t96A08_HasLocalRadialPrimitives I omega := by
  sorry
-- END SEAT AREA

theorem apm_t96A08_chart_radial_primitive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2)) :
    apm_t96A08_HasLocalRadialPrimitives I omega := by
  apply apm_t96A08_chart_radial_primitive_transfer I omega homega_smooth
  · exact apm_t96A08_chart_radial_primitive_chart_neighborhood I
  · exact apm_t96A08_chart_radial_primitive_radial_paths I
  · exact apm_t96A08_chart_radial_primitive_coordinate_formula I omega homega_smooth
  · exact apm_t96A08_chart_radial_primitive_euclidean_calculus I

/-- Abstract local-to-global step: additive concatenation and local radial
primitives identify the path-defined potential locally with a smooth one. -/
theorem apm_t96A08_potential_of_local_primitives
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (hconcat : apm_t96A08_HasAdditiveConcatenation I omega)
    (hlocal : apm_t96A08_HasLocalRadialPrimitives I omega)
    (hreachable : ∀ p : M, ∃ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma ∧
        gamma 0 = base ∧ gamma 1 = p)
    (f : M → ℝ)
    (hf : ∀ p : M, ∀ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma →
      gamma 0 = base → gamma 1 = p →
      f p = apm_t96a08_LineIntegral I omega gamma) :
    ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = omega p := by
  have h_at : ∀ x : M,
      ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f x ∧
        mfderiv I 𝓘(ℝ, ℝ) f x = omega x := by
    intro x
    rcases hlocal x with ⟨U, hU, hxU, g, hg, hgd, hradial⟩
    rcases hreachable x with ⟨gamma, hgamma, hgamma0, hgamma1⟩
    have heq : ∀ z ∈ U, f z = g z + (f x - g x) := by
      intro z hz
      rcases hradial z hz with ⟨delta, hdelta, hdelta0, hdelta1, hdelta_int⟩
      rcases hconcat gamma delta hgamma hdelta (hgamma1.trans hdelta0.symm) with
        ⟨eta, heta, heta0, heta1, heta_int⟩
      have hfz := hf z eta heta (heta0.trans hgamma0) (heta1.trans hdelta1)
      have hfx := hf x gamma hgamma hgamma0 hgamma1
      linarith
    have hg_at : ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) g x :=
      hg.contMDiffAt (hU.mem_nhds hxU)
    have hq_at : ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
        (fun y ↦ g y + (f x - g x)) x :=
      hg_at.add contMDiffAt_const
    have hfg : Filter.EventuallyEq (nhds x) f (fun y ↦ g y + (f x - g x)) :=
      Filter.mem_of_superset (hU.mem_nhds hxU) (fun z hz ↦ heq z hz)
    refine ⟨hq_at.congr_of_eventuallyEq hfg, ?_⟩
    rw [hfg.mfderiv_eq]
    change mfderiv I 𝓘(ℝ, ℝ) (g + fun _ ↦ f x - g x) x = omega x
    rw [mfderiv_add (hg_at.mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mfderiv_const]
    rw [hgd]
    ext v
    change omega x v + 0 = omega x v
    exact add_zero _
  exact ⟨fun x ↦ (h_at x).1, fun x ↦ (h_at x).2⟩

/-- The fundamental theorem assembled from the three independent library
boundaries above. -/
theorem apm_t96A08_piecewise_lineIntegral_fundamental
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (hreachable : ∀ p : M, ∃ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma ∧
        gamma 0 = base ∧ gamma 1 = p)
    (f : M → ℝ)
    (hf : ∀ p : M, ∀ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma →
      gamma 0 = base → gamma 1 = p →
      f p = apm_t96a08_LineIntegral I omega gamma) :
    ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = omega p := by
  apply apm_t96A08_potential_of_local_primitives I omega base
  · exact apm_t96A08_piecewisePath_concat_additive I omega homega_smooth
  · exact apm_t96A08_chart_radial_primitive I omega homega_smooth
  · exact hreachable
  · exact hf

theorem apm_t96a08
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (hωsmooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => ω v.1 v.2))
    (hreachable : ∀ p : M, ∃ γ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I γ ∧ γ 0 = base ∧ γ 1 = p)
    (hindependent : ∀ γ₁ γ₂ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I γ₁ →
      apm_t96a08_IsPiecewiseSmoothPath I γ₂ →
      γ₁ 0 = γ₂ 0 → γ₁ 1 = γ₂ 1 →
      apm_t96a08_LineIntegral I ω γ₁ = apm_t96a08_LineIntegral I ω γ₂) :
    ∃ f : M → ℝ,
      (∀ p : M, ∀ γ : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I γ → γ 0 = base → γ 1 = p →
        f p = apm_t96a08_LineIntegral I ω γ) ∧
      ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = ω p := by
  classical
  have hreach := hreachable
  choose γ hγ using hreachable
  let f : M → ℝ := fun p ↦ apm_t96a08_LineIntegral I ω (γ p)
  have hf : ∀ p : M, ∀ δ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I δ → δ 0 = base → δ 1 = p →
      f p = apm_t96a08_LineIntegral I ω δ := by
    intro p δ hδ hδ0 hδ1
    exact hindependent (γ p) δ (hγ p).1 hδ
      (by rw [(hγ p).2.1, hδ0]) (by rw [(hγ p).2.2, hδ1])
  exact ⟨f, hf,
    apm_t96A08_piecewise_lineIntegral_fundamental I ω base hωsmooth
      hreach f hf⟩

#print axioms apm_t96a08
