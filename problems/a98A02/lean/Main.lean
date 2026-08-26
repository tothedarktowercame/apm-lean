import Mathlib

/-!
# APM a98A02

## Statement repairs

None.

## Encoding questions

None. A function defined measurably on `[0,1]` is represented by an ambient
function whose zero extension from `[0,1]` is measurable. Membership in
`L¹[0,1]` is encoded by `IntegrableOn` for Lebesgue measure, and the Kronecker
delta is written as `if n = m then 1 else 0`.
-/

open Filter MeasureTheory Set
open scoped Topology

/-- Bessel's inequality supplies summability of squared coefficients for an
abstract orthonormal sequence. -/
lemma apm_a98A02_inner_products_summable
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (hv : Orthonormal ℝ v) (f : E) :
    Summable (fun n => ‖@inner ℝ E _ (v n) f‖ ^ 2) :=
  hv.inner_products_summable f

/-- A bounded measurable member of the frozen family defines an `L²` element
on the finite interval. This closes the first raw-function-to-`Lp` packaging
step needed for Bessel's inequality. -/
lemma apm_a98A02_memLp_two
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (n : ℕ) : MemLp (g n) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable (g n)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    ((hg_meas n).aestronglyMeasurable.mono_measure Measure.restrict_le_self).congr
      (indicator_ae_eq_restrict measurableSet_Icc)
  apply MemLp.of_bound hmeas M
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simpa [Real.norm_eq_abs] using hg_bound n x hx

/-- The frozen raw integral identities induce an actual orthonormal sequence
in `L²[0,1]`. -/
lemma apm_a98A02_orthonormal_toLp
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hg_orthonormal : ∀ n m,
      (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) =
        if n = m then 1 else 0) :
    Orthonormal ℝ (fun n =>
      (apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n)) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [MeasureTheory.L2.inner_def]
  rw [← hg_orthonormal n m]
  apply integral_congr_ae
  filter_upwards
    [(apm_a98A02_memLp_two g M hg_meas hg_bound n).coeFn_toLp,
      (apm_a98A02_memLp_two g M hg_meas hg_bound m).coeFn_toLp]
      with x hxn hxm
  rw [hxn, hxm]
  rw [show g n x = g n x • (1 : ℝ) by simp,
    show g m x = g m x • (1 : ℝ) by simp, inner_smul_left, inner_smul_right]
  simp

/-- The abstract `L²` coefficient of a packaged approximant is the frozen raw
set integral. -/
lemma apm_a98A02_inner_toLp_eq_integral
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (h : ℝ → ℝ)
    (hh : MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1))) (n : ℕ) :
    @inner ℝ
      (Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) _
      ((apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n))
      (hh.toLp h) =
        ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [(apm_a98A02_memLp_two g M hg_meas hg_bound n).coeFn_toLp,
      hh.coeFn_toLp] with x hgx hhx
  rw [hgx, hhx]
  rw [show g n x = g n x • (1 : ℝ) by simp,
    show h x = h x • (1 : ℝ) by simp, inner_smul_left, inner_smul_right]
  simp

/-- Bessel's inequality now gives convergence of every raw coefficient for an
`L²` approximant. -/
lemma apm_a98A02_integral_tendsto_zero_of_memLp_two
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hg_orthonormal : ∀ n m,
      (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) =
        if n = m then 1 else 0)
    (h : ℝ → ℝ)
    (hh : MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1))) :
    Tendsto (fun n => ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume)
      atTop (𝓝 0) := by
  let v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)) := fun n =>
    (apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n)
  let H : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)) := hh.toLp h
  have hv : Orthonormal ℝ v := apm_a98A02_orthonormal_toLp
    g M hg_meas hg_bound hg_orthonormal
  have hs : Summable (fun n => ‖@inner ℝ _ _ (v n) H‖ ^ 2) :=
    hv.inner_products_summable H
  have hz : Tendsto (fun n => ‖@inner ℝ _ _ (v n) H‖ ^ 2) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hz
  have hnorm : Tendsto (fun n => ‖@inner ℝ _ _ (v n) H‖) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using hsqrt
  have hinner : Tendsto (fun n => @inner ℝ _ _ (v n) H) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  apply hinner.congr'
  filter_upwards with n
  simpa [v, H] using
    (apm_a98A02_inner_toLp_eq_integral g M hg_meas hg_bound h hh n)

/-- Why this unblocks `apm_a98a02`: bounded truncations of an `L¹[0,1]`
function lie in `L²[0,1]` and converge back in `L¹`; the uniform bound on
`g n` controls every truncation error by the same estimate
`|∫ (f-h)g n| ≤ M ∫ |f-h|`.  Thus convergence on all `L²` approximants extends
uniformly to every frozen `IntegrableOn` function. -/
theorem apm_a98A02_bridge_1
    (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hL2 : ∀ (h : ℝ → ℝ),
      MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1)) →
        Tendsto
          (fun n => ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume)
          atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc (0 : ℝ) 1) volume) :
    Tendsto
      (fun n => ∫ x in Icc (0 : ℝ) 1, f x * g n x ∂volume)
      atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let h : ℕ → ℝ → ℝ := fun k x => max (-(k : ℝ)) (min (k : ℝ) (f x))
  have hfμ : Integrable f μ := hf
  have hfmeas : AEStronglyMeasurable f μ := hfμ.1
  have hh_meas (k : ℕ) : AEStronglyMeasurable (h k) μ := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact (measurable_const.aemeasurable.max
      (measurable_const.aemeasurable.min hfmeas.aemeasurable))
  have hh_bound (k : ℕ) : ∀ᵐ x ∂μ, ‖h k x‖ ≤ (k : ℝ) := by
    filter_upwards with x
    dsimp [h]
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le ((neg_nonpos.mpr (Nat.cast_nonneg k)).trans (Nat.cast_nonneg k))
        (min_le_left _ _)
  have hhL2 (k : ℕ) : MemLp (h k) 2 μ :=
    MemLp.of_bound (hh_meas k) k (hh_bound k)
  have hM : 0 ≤ M := by
    exact (abs_nonneg (g 0 0)).trans (hg_bound 0 0 ⟨le_rfl, zero_le_one⟩)
  have hgmeas (n : ℕ) : AEStronglyMeasurable (g n) μ :=
    ((hg_meas n).aestronglyMeasurable.mono_measure Measure.restrict_le_self).congr
      (indicator_ae_eq_restrict measurableSet_Icc)
  have hgbound (n : ℕ) : ∀ᵐ x ∂μ, ‖g n x‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa [Real.norm_eq_abs] using hg_bound n x hx
  have hpoint (x : ℝ) : Tendsto (fun k => h k x) atTop (𝓝 (f x)) := by
    obtain ⟨N : ℕ, hN : |f x| < N⟩ := exists_nat_gt |f x|
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro k hk
    have hk' : |f x| ≤ (k : ℝ) := hN.le.trans (Nat.cast_le.mpr hk)
    change max (-(k : ℝ)) (min (k : ℝ) (f x)) = f x
    rw [min_eq_right (abs_le.mp hk').2, max_eq_right (abs_le.mp hk').1]
  have herr : Tendsto (fun k => ∫ x, |f x - h k x| ∂μ) atTop (𝓝 0) := by
    have hd := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => 2 * |f x|)
      (F := fun k x => |f x - h k x|) (f := fun _ => 0)
    have hdmeas : ∀ k, AEStronglyMeasurable (fun x => |f x - h k x|) μ := fun k =>
      (hfmeas.sub (hh_meas k)).norm
    have hdbound : ∀ k, ∀ᵐ x ∂μ, ‖|f x - h k x|‖ ≤ 2 * |f x| := by
      intro k
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_abs]
      calc
        |f x - h k x| ≤ |f x| + |h k x| := abs_sub _ _
        _ ≤ |f x| + |f x| := by
          apply add_le_add (le_refl _)
          change |max (-(k : ℝ)) (min (k : ℝ) (f x))| ≤ |f x|
          simp only [abs_le]
          constructor <;> grind
        _ = 2 * |f x| := by ring
    have hdlim : ∀ᵐ x ∂μ, Tendsto (fun k => |f x - h k x|) atTop (𝓝 0) := by
      filter_upwards with x
      have hc : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)) := tendsto_const_nhds
      simpa using (hc.sub (hpoint x)).abs
    simpa only [integral_zero] using hd hdmeas (hfμ.abs.const_mul 2) hdbound hdlim
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hδ : 0 < ε / (2 * (M + 1)) := div_pos hε (by positivity)
  rcases Metric.tendsto_atTop.1 herr _ hδ with ⟨k, hk⟩
  have hkerr : ∫ x, |f x - h k x| ∂μ < ε / (2 * (M + 1)) := by
    simpa [Real.dist_eq, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] using hk k le_rfl
  have hhk := hL2 (h k) (hhL2 k)
  rcases Metric.tendsto_atTop.1 hhk _ (half_pos hε) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hprod_int : Integrable (fun x => (f x - h k x) * g n x) μ := by
    simpa [smul_eq_mul, mul_comm] using
      (hfμ.sub ((hhL2 k).integrable (by norm_num))).bdd_smul M (hgmeas n) (hgbound n)
  have hprod_bound : ‖∫ x, (f x - h k x) * g n x ∂μ‖ ≤
      M * ∫ x, |f x - h k x| ∂μ := by
    calc
      ‖∫ x, (f x - h k x) * g n x ∂μ‖ ≤
          ∫ x, M * |f x - h k x| ∂μ := by
        apply norm_integral_le_of_norm_le
        · exact (hfμ.sub ((hhL2 k).integrable (by norm_num))).abs.const_mul M
        filter_upwards [hgbound n] with x hx
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg (f x - h k x))
      _ = M * ∫ x, |f x - h k x| ∂μ := by
        rw [integral_const_mul]
  have hsmall : ‖∫ x, (f x - h k x) * g n x ∂μ‖ < ε / 2 := by
    refine hprod_bound.trans_lt ?_
    calc
      M * ∫ x, |f x - h k x| ∂μ ≤ (M + 1) * ∫ x, |f x - h k x| ∂μ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (integral_nonneg fun _ => abs_nonneg _)
      _ < (M + 1) * (ε / (2 * (M + 1))) :=
        mul_lt_mul_of_pos_left hkerr (by linarith)
      _ = ε / 2 := by field_simp
  have happ : dist (∫ x in Icc (0 : ℝ) 1, g n x * h k x ∂volume) 0 < ε / 2 :=
    hN n hn
  have hhprod_int : Integrable (fun x => g n x * h k x) μ := by
    simpa [smul_eq_mul] using
      ((hhL2 k).integrable (by norm_num)).bdd_smul M (hgmeas n) (hgbound n)
  have heq : (∫ x in Icc (0 : ℝ) 1, f x * g n x ∂volume) =
      (∫ x, (f x - h k x) * g n x ∂μ) +
        (∫ x in Icc (0 : ℝ) 1, g n x * h k x ∂volume) := by
    change (∫ x, f x * g n x ∂μ) =
      (∫ x, (f x - h k x) * g n x ∂μ) + (∫ x, g n x * h k x ∂μ)
    rw [← integral_add hprod_int hhprod_int]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [heq]
  rw [dist_zero_right]
  calc
    ‖(∫ x, (f x - h k x) * g n x ∂μ) +
        (∫ x in Icc (0 : ℝ) 1, g n x * h k x ∂volume)‖ ≤
        ‖∫ x, (f x - h k x) * g n x ∂μ‖ +
          ‖∫ x in Icc (0 : ℝ) 1, g n x * h k x ∂volume‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hsmall (by simpa [dist_zero_right] using happ)
    _ = ε := by ring

theorem apm_a98a02 (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hg_orthonormal : ∀ n m,
      (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) =
        if n = m then 1 else 0) :
    ∀ f : ℝ → ℝ, IntegrableOn f (Icc (0 : ℝ) 1) volume →
      Tendsto
        (fun n => ∫ x in Icc (0 : ℝ) 1, f x * g n x ∂volume)
        atTop (𝓝 0) := by
  /-
  PARTIAL boundary (closer hop 3).

  The original blocker diagnosis was incomplete: Mathlib's
  `Analysis.InnerProductSpace.Orthonormal` packages Bessel's inequality as
  `Orthonormal.tsum_inner_products_le`, and coefficient summability as
  `Orthonormal.inner_products_summable`. The latter is exposed above as
  `apm_a98A02_inner_products_summable`, so coefficient convergence is
  available once the raw `g n` and an approximant to `f` are bundled in L².

  The remaining bridge is measure-theoretic packaging: derive `0 ≤ M` and
  square-integrability of every bounded measurable `g n`, construct the
  corresponding `Lp` elements, translate `hg_orthonormal` to Mathlib's
  `Orthonormal` predicate despite almost-everywhere quotienting, approximate
  an arbitrary `L¹[0,1]` function by bounded/L² functions, and use
  `|∫ (f-h)g_n| ≤ M * ∫|f-h|` uniformly in `n`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, closed artifacts,
  Mathlib's `Lp`, simple-function density, bounded-function density, Holder,
  and finite-measure APIs found the individual ingredients but no theorem
  assembling this raw-function-to-Lp orthonormal family and dense-extension
  argument. No statement defect was found.

  CLOSER HOP 2: `apm_a98A02_memLp_two` now compiles the first packaging step:
  each raw `g n` is `MemLp` with exponent two for `volume.restrict (Icc 0 1)`.
  It uses the frozen measurable zero extension, its a.e. equality with `g n`
  under the restricted measure, finite measure of the interval, and the
  uniform bound. Moreover `apm_a98A02_orthonormal_toLp` transports the frozen
  integral identities through the a.e. quotient and proves Mathlib's actual
  `Orthonormal` predicate for the resulting L² sequence. The remaining work
  is the L² coefficient identification and uniform L¹-density extension.

  CLOSER HOP 3: `apm_a98A02_inner_toLp_eq_integral` now identifies the
  abstract Hilbert-space coefficient with the exact frozen raw set integral.
  `apm_a98A02_integral_tendsto_zero_of_memLp_two` then applies Bessel
  summability, takes square roots of the resulting norm-square limit, and
  proves coefficient convergence for every `MemLp 2` approximant. Thus the
  Hilbert-space portion is fully compiled. The remaining bridge is solely the
  uniform passage from an arbitrary `IntegrableOn` (`L¹`) function to bounded
  `L²` truncations, including the estimate
  `|∫ (f-h)g_n| ≤ M ∫|f-h|`; no corpus theorem assembles that raw-function
  truncation and uniform limit in the frozen encoding.
  -/
  intro f hf
  apply apm_a98A02_bridge_1 g M hg_meas hg_bound
  · intro h hh
    exact apm_a98A02_integral_tendsto_zero_of_memLp_two
      g M hg_meas hg_bound hg_orthonormal h hh
  exact hf
