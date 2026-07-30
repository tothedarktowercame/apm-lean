import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
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

Mathlib now provides the circle mean-value property, the Weierstrass theorem
for locally uniform limits, and Cauchy's derivative estimate.  The remaining
foundational gap in this file is the polar-coordinate/Fubini conversion from
circle averages at every radius to the stated disk-area integral.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Complex Metric Set Filter Topology

/-- ℂ carries Lebesgue measure via the identification ℂ ≅ ℝ². -/
noncomputable instance : MeasureSpace ℂ := ⟨volume.map Complex.equivRealProd.symm⟩

namespace ApmCanaries.A01A07

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
`norm_le_area_integral_div_area`.  This separates the complex-analytic input
from the remaining polar-coordinate conversion from circle averages to disk
area. -/
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

/-- Mean value inequality for analytic functions:
    `‖g(z₀)‖ ≤ (1/πr²) ∫_{D(z₀,r)} ‖g‖ dA`.

    This is the key engine: it converts L¹ information into pointwise bounds.
    For analytic `g`, `g(z₀) = (1/πr²) ∫_{D(z₀,r)} g dA` (the area mean value
    property), and taking absolute values gives the inequality.

    Mathlib's `DiffContOnCl.circleAverage` supplies the circle identity.
    The remaining construction is to integrate that identity in the radius
    with weight `2s`, use `Complex.integral_comp_polarCoord_symm` and Fubini,
    translate the disk from `0` to `z₀`, and identify its area as `πr²`.
    There is no direct disk-area mean-value lemma. -/
lemma norm_le_area_integral_div_area
    {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall z₀ r)) :
    ‖g z₀‖ ≤ (1 / (Real.pi * r ^ 2)) *
      ∫ w in closedBall z₀ r, ‖g w‖ := by
  sorry

/-- Step 1: L¹ convergence on disks implies uniform convergence on compact subsets.

    Given compact `K ⊂ Ω`, choose `r = dist(K, ∂Ω)/2 > 0` so that `D(z,r) ⊂ Ω`
    for all `z ∈ K`. Then for `g = fₙ - fₘ` (analytic):
    `sup_K ‖fₙ - fₘ‖ ≤ (1/πr²) ∫_{D_K} ‖fₙ - fₘ‖ dA ≤ (1/πr²)(∫‖fₙ-F‖ + ∫‖fₘ-F‖) → 0`.
    So `{fₙ}` is uniformly Cauchy on K.

    BLOCKER: Requires `norm_le_area_integral_div_area` (the disk-area property),
    plus:
    - Compact sets in `ℂ` have positive distance to `∂Ω` (needs `IsCompact`
      + `IsOpen` + `Metric.infDist_pos_of_isCompact` or similar)
    - The `r`-neighbourhood of `K` is contained in a finite union of disks
      whose total area integral bounds the sup on K
    - `TendstoUniformlyOn` is then obtained from the Cauchy criterion
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
