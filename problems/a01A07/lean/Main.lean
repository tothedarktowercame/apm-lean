import Mathlib.Analysis.Complex.CauchyIntegral
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

The key analytic lemmas (mean value property, Morera's theorem, Cauchy
derivative estimates) are stated correctly but blocked on Mathlib API gaps.
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

/-- Mean value inequality for analytic functions:
    `‖g(z₀)‖ ≤ (1/πr²) ∫_{D(z₀,r)} ‖g‖ dA`.

    This is the key engine: it converts L¹ information into pointwise bounds.
    For analytic `g`, `g(z₀) = (1/πr²) ∫_{D(z₀,r)} g dA` (the area mean value
    property), and taking absolute values gives the inequality.

    BLOCKER: Mathlib has circle-integral Cauchy formulas
    (`circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus`)
    but does not have a direct area-integral mean value property for
    holomorphic functions. The standard proof uses either:
    (a) the Cauchy integral formula on a circle of radius r,
        then `g(z₀) = (1/2π) ∫₀^{2π} g(z₀ + re^{iθ}) dθ`, and
        integrating in r gives the area formula; or
    (b) the fact that `g` is harmonic so satisfies the mean value property.
    Neither path is available as a single Mathlib lemma. -/
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

    BLOCKER: Requires `norm_le_area_integral_div_area` (the mean value property),
    plus:
    - Compact sets in `ℂ` have positive distance to `∂Ω` (needs `IsCompact`
      + `IsOpen` + `Metric.infDist_pos_of_isCompact` or similar)
    - The `r`-neighbourhood of `K` is contained in a finite union of disks
      whose total area integral bounds the sup on K
    - `TendstoUniformlyOn` is then obtained from the Cauchy criterion
-/
theorem tendstoUniformlyOn_of_L1_on_disks
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
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

    BLOCKER: Mathlib's Morera theorem
    (`DifferentiableOn.of_diffContOnCl_triangle` or similar) requires
    contour integrals over triangles, which need `Complex.integralBoundaryTriangle`
    or equivalent. Additionally, passing from Step 1's uniform convergence to
    interchange of limit and integral requires `TendstoUniformlyOn` to imply
    convergence of contour integrals — available but requires plumbing. -/
theorem differentiableOn_of_L1_limit
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω) :
    DifferentiableOn ℂ F Ω := by
  sorry

/-- Cauchy estimate for derivatives:
    `‖g'(z₀)‖ ≤ (M/ρ)` when `‖g‖ ≤ M` on `closedBall z₀ ρ`.

    This follows from the Cauchy integral formula for derivatives:
    `g'(z₀) = (1/2πi) ∮_{|w-z₀|=ρ} g(w)/(w-z₀)² dw`. -/
lemma deriv_norm_le_sup_div_radius
    {g : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (closedBall z₀ ρ))
    {M : ℝ} (hM : ∀ w ∈ closedBall z₀ ρ, ‖g w‖ ≤ M) :
    ‖deriv g z₀‖ ≤ M / ρ := by
  sorry

/-- Step 3: `fₙ' → F'` uniformly on compact subsets.

    By the Cauchy estimate, `‖fₙ'(z) - F'(z)‖ ≤ (1/ρ) sup_{|w-z|=ρ} ‖fₙ(w)-F(w)‖`,
    and Step 1 gives uniform convergence of `fₙ → F` on the `ρ`-neighbourhood of `K`.

    BLOCKER: depends on Steps 1 and 2, plus the Cauchy estimate above. -/
theorem tendstoUniformlyOn_deriv_of_L1
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun n z => deriv (f n) z) (deriv F) atTop K := by
  sorry

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
  · exact fun K hK hKΩ => tendstoUniformlyOn_of_L1_on_disks hf hF hconv hK hKΩ
  · exact fun K hK hKΩ => tendstoUniformlyOn_deriv_of_L1 hΩ hf hF hconv hK hKΩ

end ApmCanaries.A01A07
