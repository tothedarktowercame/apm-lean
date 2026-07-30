import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# APM a01A07: L¹ convergence of analytic functions implies uniform convergence

**Problem (from `a01A07.tex`).** Let `{fₙ}` be a sequence of analytic functions on
a region `Ω ⊆ ℂ`, and `F` continuous on `Ω`, such that for every disk `D ⊂ Ω`,
`∫_D |fₙ(z) - F(z)| dA → 0`. Show that:
- `F` is analytic on `Ω`;
- `fₙ → F` uniformly on compact subsets of `Ω`;
- `fₙ' → F'` uniformly on compact subsets of `Ω`.

**Key insight.** The mean value property for analytic functions:
`|g(z₀)| ≤ (1/πr²) ∫_{D(z₀,r)} |g| dA`. Applied to `g = fₙ - fₘ`,
this upgrades L¹(disk) convergence to uniform convergence on compacts.

**Statement repair note.**

The generated statement had the right mathematical structure but needed:
1. `MeasureSpace ℂ` instance — `ℂ` does not have a `MeasureSpace` instance
   in Mathlib directly. We add one via the equivalence `ℂ ≃ᵥ ℝ × ℝ` (viewing
   `ℂ` as `ℝ²` with Lebesgue measure). This is the standard `volume` on `ℂ`.
2. The integral `∫ w in closedBall z r, ‖f n w - F w‖` uses the default
   `volume` from our `MeasureSpace ℂ` instance (no explicit `∂volume` needed).
3. `DifferentiableOn ℂ g Ω` is Mathlib's holomorphicity-on-Ω.
4. `TendstoUniformlyOn` from `Topology.UniformSpace.UniformConvergence` is
   the correct API for uniform convergence on a set.

Mathlib provides the circle mean-value property, the Weierstrass theorem for
locally uniform limits, and Cauchy's derivative estimate.  This file now also
builds the disk-area mean-value identity from polar coordinates and Fubini.
The remaining gap is the compact-local uniform Cauchy argument upgrading the
diskwise L¹ hypothesis to locally uniform convergence.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Complex Metric Set Filter Topology

/-- ℂ carries Lebesgue measure via the identification ℂ ≅ ℝ². -/
noncomputable instance : MeasureSpace ℂ := ⟨volume.map Complex.equivRealProd.symm⟩

namespace ApmCanaries.A01A07

noncomputable local instance : IsFiniteMeasureOnCompacts (volume : Measure ℂ) := by
  change IsFiniteMeasureOnCompacts (volume.map Complex.equivRealProd.symm)
  exact Measure.IsFiniteMeasureOnCompacts.map volume
    Complex.equivRealProdCLM.toHomeomorph.symm

variable {Ω : Set ℂ} (hΩ : IsOpen Ω)

/-- L¹ convergence on disks: `∫_D |fₙ - F| dA → 0` for every closed disk `D ⊂ Ω`.
    This is the hypothesis of the theorem.

    Note: `volume` on `ℂ` is via the `MeasureSpace ℂ` instance derived from
    the `RCLike`/`InnerProductSpace` structure (Lebesgue measure on `ℝ²`). -/
def L1ConvergesOnDisks (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ (z : ℂ) (r : ℝ), 0 < r → closedBall z r ⊆ Ω →
    Tendsto (fun n => ∫ w in closedBall z r, ‖f n w - F w‖)
      atTop (𝓝 0)

/-- The circle-level sub-mean inequality underlying
`norm_le_area_integral_div_area`. -/
lemma norm_le_circleAverage_norm
    {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall z₀ r)) :
    ‖g z₀‖ ≤ Real.circleAverage (fun w ↦ ‖g w‖) z₀ r := by
  have hdc : DiffContOnCl ℂ g (ball z₀ |r|) := by
    rw [abs_of_pos hr]
    refine ⟨hg.mono ball_subset_closedBall, ?_⟩
    simpa [closure_ball _ hr.ne'] using hg.continuousOn
  have hmean : Real.circleAverage g z₀ r = g z₀ := hdc.circleAverage
  rw [← hmean]
  simp only [Real.circleAverage_def, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos Real.two_pi_pos, smul_eq_mul]
  gcongr
  exact intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le

/-- Polar-coordinate reduction of a disk integral centered at the origin. -/
lemma integral_closedBall_zero_eq_polar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℂ → E) {r : ℝ} (hr : 0 < r) :
    ∫ w in closedBall (0 : ℂ) r, q w =
      ∫ p in Set.Ioc (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • q (Complex.polarCoord.symm p) := by
  rw [← integral_indicator measurableSet_closedBall,
    show (volume : Measure ℂ) =
      volume.map Complex.equivRealProd.symm from rfl]
  have heq :
      (Complex.equivRealProd.symm : ℝ × ℝ → ℂ) =
        Complex.measurableEquivRealProd.symm := by
    funext p
    apply Complex.ext <;> simp
  rw [heq]
  rw [Complex.volume_preserving_equiv_real_prod.symm.map_eq]
  rw [← Complex.integral_comp_polarCoord_symm ((closedBall (0 : ℂ) r).indicator q)]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (closedBall (0 : ℂ) r).indicator q
      (Complex.polarCoord.symm p)) =
    ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • q (Complex.polarCoord.symm p)
  calc
    (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (closedBall (0 : ℂ) r).indicator q
          (Complex.polarCoord.symm p)) =
        ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • (closedBall (0 : ℂ) r).indicator q
            (Complex.polarCoord.symm p) := by
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
        (measurableSet_Ioi.prod measurableSet_Ioo)
      · exact prod_mono (fun _ h ↦ h.1) Subset.rfl
      · intro p hp
        have hp₁ : 0 < p.1 := hp.1.1
        have hnot : Complex.polarCoord.symm p ∉ closedBall (0 : ℂ) r := by
          simp only [mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
            abs_of_pos hp₁]
          exact fun hle ↦ hp.2 ⟨⟨hp₁, hle⟩, hp.1.2⟩
        rw [Set.indicator_of_notMem hnot, smul_zero]
    _ = ∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • q (Complex.polarCoord.symm p) := by
      apply setIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      have hmem : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) r := by
        simp only [mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
          abs_of_pos hp.1.1]
        exact hp.1.2
      dsimp only
      rw [Set.indicator_of_mem hmem]

/-- The area mean-value identity for a holomorphic function on a disk centered
at the origin. -/
lemma integral_closedBall_zero_eq_area_smul
    {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall (0 : ℂ) r)) :
    ∫ w in closedBall (0 : ℂ) r, g w =
      (Real.pi * r ^ 2 : ℝ) • g 0 := by
  rw [integral_closedBall_zero_eq_polar g hr]
  let Q : ℝ × ℝ → ℂ :=
    fun p ↦ p.1 • g (Complex.polarCoord.symm p)
  have hpolar : Continuous (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hmap :
      MapsTo (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p)
        (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi)
        (closedBall (0 : ℂ) r) := by
    intro p hp
    simp only [mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm,
      abs_of_nonneg hp.1.1]
    exact hp.1.2
  have hQcont :
      ContinuousOn Q (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi) := by
    simpa only [Q, Complex.real_smul] using
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul
        (hg.continuousOn.comp hpolar.continuousOn hmap)
  have hQint :
      IntegrableOn Q (Ioc (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi) := by
    apply (hQcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact prod_mono (fun _ h ↦ ⟨h.1.le, h.2⟩)
      (fun _ h ↦ ⟨h.1.le, h.2.le⟩)
  change (∫ p in Ioc (0 : ℝ) r ×ˢ Ioo (-Real.pi) Real.pi, Q p) =
    (Real.pi * r ^ 2 : ℝ) • g 0
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod Q (by simpa [Measure.volume_eq_prod ℝ ℝ] using hQint)]
  have hinner : ∀ s ∈ Ioc (0 : ℝ) r,
      (∫ θ in Ioo (-Real.pi) Real.pi,
          s • g (Complex.polarCoord.symm (s, θ))) =
        (2 * Real.pi * s : ℝ) • g 0 := by
    intro s hs
    have hdiff : DiffContOnCl ℂ g (ball 0 |s|) := by
      have hspos : 0 < s := hs.1
      rw [abs_of_pos hspos]
      refine ⟨hg.mono ?_, ?_⟩
      · exact ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by simpa using hs.2))
      · have hsub : closedBall (0 : ℂ) s ⊆ closedBall 0 r :=
          closedBall_subset_closedBall hs.2
        simpa [closure_ball _ hspos.ne'] using hg.continuousOn.mono hsub
    have hcircle : Real.circleAverage g 0 s = g 0 := hdiff.circleAverage
    have hpolarCircle : ∀ θ : ℝ,
        (Complex.polarCoord.symm (s, θ) : ℂ) = circleMap 0 s θ := by
      intro θ
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
    have hperiodic :
        Function.Periodic
          (fun θ : ℝ ↦ s • g (Complex.polarCoord.symm (s, θ)))
          (2 * Real.pi) := by
      intro θ
      simp [Complex.polarCoord_symm_apply]
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    have hshift := hperiodic.intervalIntegral_add_eq (-Real.pi) 0
    have hshift' :
        (∫ θ in -Real.pi..Real.pi,
            s • g (Complex.polarCoord.symm (s, θ))) =
          ∫ θ in 0..2 * Real.pi,
            s • g (Complex.polarCoord.symm (s, θ)) := by
      convert hshift using 1 <;> ring_nf
    rw [hshift']
    have hangleInt :
        IntervalIntegrable
          (fun θ : ℝ ↦ g (Complex.polarCoord.symm (s, θ)))
          volume 0 (2 * Real.pi) := by
      have hcontSphere : ContinuousOn g (sphere (0 : ℂ) s) := by
        apply hdiff.2.mono
        simpa [abs_of_pos hs.1, closure_ball _ hs.1.ne'] using
          (sphere_subset_closedBall : sphere (0 : ℂ) s ⊆ closedBall 0 s)
      simpa only [hpolarCircle] using
          hcontSphere.circleIntegrable hs.1.le
    have hangle :
        (∫ θ in 0..2 * Real.pi,
            g (Complex.polarCoord.symm (s, θ))) =
          (2 * Real.pi : ℝ) • g 0 := by
      have hcircle' :
          (2 * Real.pi : ℝ)⁻¹ •
              (∫ θ in 0..2 * Real.pi,
                g (Complex.polarCoord.symm (s, θ))) = g 0 := by
        simpa only [Real.circleAverage_def, hpolarCircle] using hcircle
      calc
        (∫ θ in 0..2 * Real.pi,
            g (Complex.polarCoord.symm (s, θ))) =
            (2 * Real.pi : ℝ) •
              ((2 * Real.pi : ℝ)⁻¹ •
                ∫ θ in 0..2 * Real.pi,
                  g (Complex.polarCoord.symm (s, θ))) := by
                    have hne : (2 * Real.pi : ℝ) ≠ 0 :=
                      Real.two_pi_pos.ne'
                    exact (smul_inv_smul₀ hne _).symm
        _ = (2 * Real.pi : ℝ) • g 0 := by rw [hcircle']
    calc
      (∫ θ in 0..2 * Real.pi,
          s • g (Complex.polarCoord.symm (s, θ))) =
          s • ∫ θ in 0..2 * Real.pi,
            g (Complex.polarCoord.symm (s, θ)) :=
        hangleInt.integral_smul s
      _ = (2 * Real.pi * s : ℝ) • g 0 := by
        rw [hangle]
        module
  rw [setIntegral_congr_fun measurableSet_Ioc hinner]
  have hout :
      (∫ x in Ioc (0 : ℝ) r, (2 * Real.pi * x) • g 0) =
        (∫ x in Ioc (0 : ℝ) r, 2 * Real.pi * x) • g 0 :=
    integral_smul_const (μ := volume.restrict (Ioc (0 : ℝ) r))
      (fun x : ℝ ↦ 2 * Real.pi * x) (g 0)
  rw [hout]
  congr 1
  rw [← intervalIntegral.integral_of_le hr.le]
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ ↦ Real.pi * y ^ 2) (2 * Real.pi * x) x := by
    intro x
    convert ((hasDerivAt_pow 2 x).const_mul Real.pi) using 1
    all_goals ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hderiv x)
    ((continuous_const.mul continuous_id).intervalIntegrable 0 r)]
  ring

/-- Translation of a disk integral to a disk centered at the origin. -/
lemma integral_closedBall_eq_translate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℂ → E) (z₀ : ℂ) (r : ℝ) :
    ∫ w in closedBall z₀ r, q w =
      ∫ w in closedBall (0 : ℂ) r, q (w + z₀) := by
  rw [← integral_indicator measurableSet_closedBall,
    ← integral_indicator measurableSet_closedBall]
  change (∫ w, (closedBall z₀ r).indicator q w
      ∂volume.map Complex.equivRealProd.symm) =
    ∫ w, (closedBall (0 : ℂ) r).indicator (fun w ↦ q (w + z₀)) w
      ∂volume.map Complex.equivRealProd.symm
  have heq :
      (Complex.equivRealProd.symm : ℝ × ℝ → ℂ) =
        Complex.measurableEquivRealProd.symm := by
    funext p
    apply Complex.ext <;> simp
  rw [heq, Complex.volume_preserving_equiv_real_prod.symm.map_eq]
  rw [← integral_add_right_eq_self
    ((closedBall z₀ r).indicator q) z₀]
  apply integral_congr_ae
  filter_upwards with w
  have hm :
      w + z₀ ∈ closedBall z₀ r ↔ w ∈ closedBall (0 : ℂ) r := by
    simp [mem_closedBall]
  by_cases hw : w ∈ closedBall (0 : ℂ) r
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hm.mpr hw)]
  · rw [Set.indicator_of_notMem hw,
      Set.indicator_of_notMem (fun h ↦ hw (hm.mp h))]

/-- The vector-valued area mean identity on an arbitrary closed disk. -/
lemma integral_closedBall_eq_area_smul
    {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall z₀ r)) :
    ∫ w in closedBall z₀ r, g w =
      (Real.pi * r ^ 2 : ℝ) • g z₀ := by
  rw [integral_closedBall_eq_translate g z₀ r]
  have htranslated :
      DifferentiableOn ℂ (fun w ↦ g (w + z₀))
        (closedBall (0 : ℂ) r) := by
    apply hg.comp
    · exact differentiableOn_id.add (differentiableOn_const z₀)
    · intro w hw
      simpa [mem_closedBall, dist_eq] using hw
  rw [integral_closedBall_zero_eq_area_smul hr htranslated]
  simp

/-- The requested disk sub-mean inequality follows formally from the
vector-valued disk mean identity.  Thus the remaining analytic construction is
exactly that identity, rather than any additional norm estimate. -/
lemma norm_le_area_integral_div_area_of_integral_eq
    {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hmean : ∫ w in closedBall z₀ r, g w =
      (Real.pi * r ^ 2 : ℝ) • g z₀) :
    ‖g z₀‖ ≤ (1 / (Real.pi * r ^ 2)) *
      ∫ w in closedBall z₀ r, ‖g w‖ := by
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hnorm :
      Real.pi * r ^ 2 * ‖g z₀‖ ≤ ∫ w in closedBall z₀ r, ‖g w‖ := by
    simpa [hmean, norm_smul, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using
      (norm_integral_le_integral_norm
        (μ := volume.restrict (closedBall z₀ r)) g)
  calc
    ‖g z₀‖ = (1 / (Real.pi * r ^ 2)) *
        (Real.pi * r ^ 2 * ‖g z₀‖) := by field_simp
    _ ≤ (1 / (Real.pi * r ^ 2)) *
        ∫ w in closedBall z₀ r, ‖g w‖ :=
      mul_le_mul_of_nonneg_left hnorm (one_div_nonneg.mpr harea.le)

/-- Mean value inequality for analytic functions:
    `‖g(z₀)‖ ≤ (1/πr²) ∫_{D(z₀,r)} ‖g‖ dA`.

    This is the key engine: it converts L¹ information into pointwise bounds.
    For analytic `g`, `g(z₀) = (1/πr²) ∫_{D(z₀,r)} g dA` (the area mean value
    property), and taking absolute values gives the inequality.

    Mathlib's `DiffContOnCl.circleAverage` supplies the circle identity.  The
    lemmas above integrate it in the radius with weight `2s`, use
    `Complex.integral_comp_polarCoord_symm` and Fubini, translate the disk from
    `0` to `z₀`, and identify its area as `πr²`. -/
lemma norm_le_area_integral_div_area
    {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall z₀ r)) :
    ‖g z₀‖ ≤ (1 / (Real.pi * r ^ 2)) *
      ∫ w in closedBall z₀ r, ‖g w‖ := by
  exact norm_le_area_integral_div_area_of_integral_eq hr
    (integral_closedBall_eq_area_smul hr hg)

/-- Sub-mean inequality centered at an arbitrary constant, the form used to
compare an analytic function with a merely continuous candidate limit. -/
lemma norm_sub_le_area_integral_div_area
    {g : ℂ → ℂ} {z₀ c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall z₀ r)) :
    ‖g z₀ - c‖ ≤ (1 / (Real.pi * r ^ 2)) *
      ∫ w in closedBall z₀ r, ‖g w - c‖ := by
  simpa only using
    (norm_le_area_integral_div_area (g := fun w ↦ g w - c)
      (z₀ := z₀) hr (hg.sub (differentiableOn_const c)))

/-- Every point of an open subset of `ℂ` is the center of a positive-radius
closed disk contained in that subset. -/
lemma exists_closedBall_subset_of_mem_open
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨ε / 2, half_pos hε, ?_⟩
  exact (closedBall_subset_ball (half_lt_self hε)).trans hεU

/-- Diskwise L¹ convergence makes a holomorphic sequence uniformly Cauchy on
the concentric disk of half the radius. -/
lemma uniformCauchySeqOn_closedBall_half
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hF : ContinuousOn F U)
    (hconv : L1ConvergesOnDisks f F U)
    {x : ℂ} {R : ℝ} (hR : 0 < R) (hRU : closedBall x R ⊆ U) :
    UniformCauchySeqOn f atTop (closedBall x (R / 2)) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let c : ℝ := 1 / (Real.pi * (R / 2) ^ 2)
  have hc : 0 < c := one_div_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos (half_pos hR)))
  have hthreshold : 0 < ε / (2 * c) := div_pos hε (mul_pos two_pos hc)
  have hm_small :
      ∀ᶠ n in atTop,
        (∫ w in closedBall x R, ‖f n w - F w‖) < ε / (2 * c) :=
    (hconv x R hR hRU).eventually_lt_const hthreshold
  obtain ⟨N, hN⟩ := eventually_atTop.mp hm_small
  refine ⟨N, fun m hm n hn y hy ↦ ?_⟩
  have hsmall_subset : closedBall y (R / 2) ⊆ closedBall x R := by
    intro w hw
    rw [mem_closedBall] at hw hy ⊢
    exact (dist_triangle w y x).trans (by linarith)
  have hsmallU : closedBall y (R / 2) ⊆ U := hsmall_subset.trans hRU
  have hfm : DifferentiableOn ℂ (f m) (closedBall y (R / 2)) :=
    (hf m).mono hsmallU
  have hfn : DifferentiableOn ℂ (f n) (closedBall y (R / 2)) :=
    (hf n).mono hsmallU
  have hsubmean :
      ‖f m y - f n y‖ ≤
        c * ∫ w in closedBall y (R / 2), ‖f m w - f n w‖ := by
    simpa only [c] using
      norm_le_area_integral_div_area (g := fun w ↦ f m w - f n w)
        (z₀ := y) (half_pos hR) (hfm.sub hfn)
  have hfm_cont : ContinuousOn (f m) (closedBall x R) :=
    ((hf m).mono hRU).continuousOn
  have hfn_cont : ContinuousOn (f n) (closedBall x R) :=
    ((hf n).mono hRU).continuousOn
  have hF_cont : ContinuousOn F (closedBall x R) := hF.mono hRU
  have hIm : IntegrableOn (fun w ↦ ‖f m w - F w‖) (closedBall x R) :=
    (hfm_cont.sub hF_cont).norm.integrableOn_compact (isCompact_closedBall x R)
  have hIn : IntegrableOn (fun w ↦ ‖f n w - F w‖) (closedBall x R) :=
    (hfn_cont.sub hF_cont).norm.integrableOn_compact (isCompact_closedBall x R)
  have hdiff :
      (∫ w in closedBall y (R / 2), ‖f m w - f n w‖) ≤
        (∫ w in closedBall x R, ‖f m w - F w‖) +
          ∫ w in closedBall x R, ‖f n w - F w‖ := by
    calc
      (∫ w in closedBall y (R / 2), ‖f m w - f n w‖) ≤
          ∫ w in closedBall y (R / 2),
            (‖f m w - F w‖ + ‖f n w - F w‖) := by
              apply integral_mono
              · exact ((hfm_cont.sub hfn_cont).norm.integrableOn_compact
                  (isCompact_closedBall x R)).mono_set hsmall_subset
              · exact (hIm.add hIn).mono_set hsmall_subset
              · intro w
                calc
                  ‖f m w - f n w‖ =
                      ‖(f m w - F w) - (f n w - F w)‖ := by ring_nf
                  _ ≤ ‖f m w - F w‖ + ‖f n w - F w‖ := norm_sub_le _ _
      _ = (∫ w in closedBall y (R / 2), ‖f m w - F w‖) +
          ∫ w in closedBall y (R / 2), ‖f n w - F w‖ := by
            rw [integral_add (hIm.mono_set hsmall_subset) (hIn.mono_set hsmall_subset)]
      _ ≤ (∫ w in closedBall x R, ‖f m w - F w‖) +
          ∫ w in closedBall x R, ‖f n w - F w‖ := by
            exact add_le_add
              (setIntegral_mono_set hIm
                (ae_of_all _ fun _ ↦ norm_nonneg _) hsmall_subset.eventuallyLE)
              (setIntegral_mono_set hIn
                (ae_of_all _ fun _ ↦ norm_nonneg _) hsmall_subset.eventuallyLE)
  rw [dist_eq_norm]
  calc
    ‖f m y - f n y‖ ≤
        c * ∫ w in closedBall y (R / 2), ‖f m w - f n w‖ := hsubmean
    _ ≤ c * ((∫ w in closedBall x R, ‖f m w - F w‖) +
        ∫ w in closedBall x R, ‖f n w - F w‖) :=
      mul_le_mul_of_nonneg_left hdiff hc.le
    _ < ε := by
      have hm' := hN m hm
      have hn' := hN n hn
      have hcne : c ≠ 0 := hc.ne'
      have hm'' :
          c * (∫ w in closedBall x R, ‖f m w - F w‖) < ε / 2 := by
        calc
          c * (∫ w in closedBall x R, ‖f m w - F w‖) <
              c * (ε / (2 * c)) := mul_lt_mul_of_pos_left hm' hc
          _ = ε / 2 := by field_simp
      have hn'' :
          c * (∫ w in closedBall x R, ‖f n w - F w‖) < ε / 2 := by
        calc
          c * (∫ w in closedBall x R, ‖f n w - F w‖) <
              c * (ε / (2 * c)) := mul_lt_mul_of_pos_left hn' hc
          _ = ε / 2 := by field_simp
      rw [mul_add]
      linarith

/-- Step 1: L¹ convergence on disks implies uniform convergence on compact subsets.

    The remaining proof can be organized locally at each `x ∈ Ω`.  Choose an
    outer closed disk in `Ω`.  The constant-centered disk sub-mean bound above,
    continuity of `F`, and diskwise L¹ convergence give `f n x → F x`.
    On a smaller concentric disk, the ordinary sub-mean bound applied to
    `f n - f m` on fixed-radius disks gives a uniform Cauchy sequence, bounded
    by the two L¹ errors on the outer disk.  Combine
    `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` with the pointwise limit,
    then package the local result using
    `tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ`.
-/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). `hΩ : IsOpen Ω` is declared on
-- line 50 as a section variable but this theorem never referenced it, so Lean 4
-- did not include it and the statement quantified over an ARBITRARY Ω. That made
-- it FALSE: at Ω = {0} the L1-on-disks hypothesis holds VACUOUSLY (no
-- positive-radius closed ball fits inside a singleton) while the conclusion
-- asserts the constant 1 converges uniformly to 0. Refutation machine-checked;
-- faithfulness-ledger entry #9. Added as an explicit binder to match the other
-- three theorems in this file, which all declare `(hΩ : IsOpen Ω)` themselves.
theorem tendstoUniformlyOn_of_L1_on_disks
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn f F atTop K := by
  sorry

/-- Step 2: The L¹ limit `F` is analytic.

    Proof strategy: by Morera's theorem, for any triangle `Δ ⊂ Ω`,
    `∮_Δ F dz = lim ∮_Δ fₙ dz = 0` (Cauchy's theorem + uniform convergence
    passes the limit through the contour integral).

    Once Step 1 is available, no Morera construction is needed:
    `tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ` packages Step 1 as
    local uniform convergence, and
    `TendstoLocallyUniformlyOn.differentiableOn` is precisely Weierstrass'
    theorem. -/
theorem differentiableOn_of_L1_limit
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω) :
    DifferentiableOn ℂ F Ω := by
  have hloc : TendstoLocallyUniformlyOn f F atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
    intro K hKΩ hK
    exact tendstoUniformlyOn_of_L1_on_disks hΩ hf hF hconv hK hKΩ
  exact hloc.differentiableOn (Eventually.of_forall hf) hΩ

/-- Cauchy estimate for derivatives:
    `‖g'(z₀)‖ ≤ (M/ρ)` when `‖g‖ ≤ M` on `closedBall z₀ ρ`.

    This is `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, after
    packaging differentiability and continuity as `DiffContOnCl`. -/
lemma deriv_norm_le_sup_div_radius
    {g : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (closedBall z₀ ρ))
    {M : ℝ} (hM : ∀ w ∈ closedBall z₀ ρ, ‖g w‖ ≤ M) :
    ‖deriv g z₀‖ ≤ M / ρ := by
  apply norm_deriv_le_of_forall_mem_sphere_norm_le hρ
  · constructor
    · exact hg.mono ball_subset_closedBall
    · simpa [closure_ball _ hρ.ne'] using hg.continuousOn
  · exact fun w hw ↦ hM w (sphere_subset_closedBall hw)

/-- Step 3: `fₙ' → F'` uniformly on compact subsets.

    By the Cauchy estimate, `‖fₙ'(z) - F'(z)‖ ≤ (1/ρ) sup_{|w-z|=ρ} ‖fₙ(w)-F(w)‖`,
    and Step 1 gives uniform convergence of `fₙ → F` on the `ρ`-neighbourhood of `K`.

    Once Step 1 is available,
    `TendstoLocallyUniformlyOn.deriv` gives this result directly after
    converting between local uniform convergence and uniform convergence on
    compact subsets. -/
theorem tendstoUniformlyOn_deriv_of_L1
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun n z => deriv (f n) z) (deriv F) atTop K := by
  have hloc : TendstoLocallyUniformlyOn f F atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
    intro L hLΩ hL
    exact tendstoUniformlyOn_of_L1_on_disks hΩ hf hF hconv hL hLΩ
  have hderiv := hloc.deriv (Eventually.of_forall hf) hΩ
  simpa only [Function.comp_apply] using
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hderiv K hKΩ hK

/-- Full theorem: L¹(disk) convergence of analytic functions to a continuous
    limit implies the limit is analytic and both function and derivative
    converge uniformly on compacts. -/
theorem L1_disk_convergence_analytic_upgrade
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω) :
    DifferentiableOn ℂ F Ω ∧
    (∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn f F atTop K) ∧
    (∀ K, IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn (fun n z => deriv (f n) z) (deriv F) atTop K) := by
  refine ⟨?_, ?_, ?_⟩
  · exact differentiableOn_of_L1_limit hΩ hf hF hconv
  · exact fun K hK hKΩ => tendstoUniformlyOn_of_L1_on_disks hΩ hf hF hconv hK hKΩ
  · exact fun K hK hKΩ => tendstoUniformlyOn_deriv_of_L1 hΩ hf hF hconv hK hKΩ

end ApmCanaries.A01A07
