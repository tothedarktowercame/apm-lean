import Mathlib
import ConstructionTargets.Rouche

/-!
# APM a01J05 — critical points of a finite Blaschke product

## Statement repairs

The hypothesis `0 < N` is made explicit.  Without it the source permits the
constant function `f = 1`: it has no zeros, while its derivative vanishes
identically, so the claimed `N - 1` zero count is false.

Zeros are counted with multiplicity using Mathlib's `analyticOrderAt`, rather
than by the cardinality of a set of distinct zeros.
-/

open Complex Filter MeromorphicOn Metric Set
open scoped ENNReal

noncomputable section

def apm_a01J05_disk : Set ℂ :=
  ball 0 1

def apm_a01J05_circle : Set ℂ :=
  sphere 0 1

/-- Total order of vanishing over the open unit disk. -/
def apm_a01J05_zeroMultiplicity (f : ℂ → ℂ) : ℕ∞ :=
  by
    classical
    exact ∑' z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderAt f z else 0

/-- Analyticity on a slightly larger closed disk gives analyticity at every
point of the unit disk. -/
lemma apm_a01J05_analyticAt_of_closedBall
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) : AnalyticAt ℂ f z := by
  have hr : (1 : ℝ) < 1 + ε := by linarith
  have hz' : z ∈ ball (0 : ℂ) (1 + ε) := by
    exact (ball_subset_ball hr.le) hz
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  exact hdiff.analyticAt (isOpen_ball.mem_nhds hz')

/-- The derivative is analytic throughout the unit disk under the same
neighborhood hypothesis. -/
lemma apm_a01J05_deriv_analyticAt_of_closedBall
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) : AnalyticAt ℂ (deriv f) z := by
  have hr : (1 : ℝ) < 1 + ε := by linarith
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  have han : AnalyticOnNhd ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hdiff.analyticOnNhd isOpen_ball
  exact han.deriv z ((ball_subset_ball hr.le) hz)

/-- Pointwise multiplicity drop under differentiation.  Summing this identity
is one local ingredient of the global critical-point count. -/
lemma apm_a01J05_order_deriv_add_one
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) :
    analyticOrderAt (deriv f) z + 1 =
      analyticOrderAt (fun w => f w - f z) z := by
  exact (apm_a01J05_analyticAt_of_closedBall hε hf hz).analyticOrderAt_deriv_add_one

/-- The hypotheses already give Mathlib's finite-divisor factorization on the
closed unit disk. This supplies the finiteness/attainment layer needed before
the specifically Blaschke symmetry argument. -/
lemma apm_a01J05_exists_finiteDivisor_factorization
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (closedBall 0 1) ∧
        (∀ z : closedBall (0 : ℂ) 1, h z ≠ 0) ∧
        f =ᶠ[codiscreteWithin (closedBall 0 1)]
          (∏ᶠ u, (· - u) ^ divisor f (closedBall 0 1) u) * h := by
  obtain ⟨ε, hε, hf⟩ := hf_analytic
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 (1 + ε) := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  have hfan : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) := by
    intro z hz
    exact hdiff.analyticAt (isOpen_ball.mem_nhds (hsub hz))
  have hne : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ 0 := by
    intro z hz hzero
    have hnorm := hf_boundary z hz
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  exact ConstructionTargets.Rouche.exists_zeroFree_factorization_on_closedBall
    (by norm_num) hfan hne

/-- Natural-valued finite form of the open-disk zero count. -/
def apm_a01J05_zeroMultiplicityNat (f : ℂ → ℂ) : ℕ :=
  by
    classical
    exact ∑ᶠ z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderNatAt f z else 0

/-- Naturalized total of the meromorphic divisor on the closed unit disk. -/
def apm_a01J05_divisorMultiplicityNat (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ z : ℂ, Int.toNat (divisor f (closedBall 0 1) z)

/-- Finite set supporting the closed-unit-disk divisor. -/
noncomputable def apm_a01J05_divisorSupport (f : ℂ → ℂ) : Finset ℂ :=
  ((divisor f (closedBall 0 1)).finiteSupport
    (isCompact_closedBall (0 : ℂ) 1)).toFinset

/-- The finite canonical-factor product attached to the closed-disk divisor. -/
noncomputable def apm_a01J05_canonicalProduct (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ ∏ u ∈ apm_a01J05_divisorSupport f,
    (canonicalFactor 1 u z) ^ Int.toNat (divisor f (closedBall 0 1) u)

/-- The canceled product with each removable value filled by its meromorphic
trailing coefficient. -/
noncomputable def apm_a01J05_regularizedCanonicalProduct (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ meromorphicTrailingCoeffAt (f * apm_a01J05_canonicalProduct f) z


/-- Unit boundary norm gives the nonvanishing hypothesis used by divisor and
argument-principle interfaces. -/
lemma apm_a01J05_boundary_ne_zero
    {f : ℂ → ℂ}
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    ∀ z ∈ apm_a01J05_circle, f z ≠ 0 := by
  intro z hz hzero
  have hnorm := hf_boundary z hz
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Analyticity on a larger closed disk supplies neighborhood analyticity on
the closed unit disk, in the form consumed by divisor and argument-principle
theorems. -/
lemma apm_a01J05_analyticOnNhd_closedBall
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε))) :
    AnalyticOnNhd ℂ f (closedBall 0 1) := by
  obtain ⟨ε, hε, hf⟩ := hf_analytic
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 (1 + ε) := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  intro z hz
  exact hdiff.analyticAt (isOpen_ball.mem_nhds (hsub hz))

/-- Boundary nonvanishing and analytic continuation rule out infinite order at
every point of the open unit disk. -/
lemma apm_a01J05_analyticOrderAt_ne_top
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) :
    analyticOrderAt f z ≠ ⊤ := by
  intro htop
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  have han : AnalyticOnNhd ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hdiff.analyticOnNhd isOpen_ball
  have hzlarge : z ∈ ball (0 : ℂ) (1 + ε) := by
    exact (ball_subset_ball (by linarith : (1 : ℝ) ≤ 1 + ε)) hz
  have hzero : EqOn f 0 (ball (0 : ℂ) (1 + ε)) :=
    han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball 0 (1 + ε)).isPreconnected hzlarge
      (analyticOrderAt_eq_top.mp htop)
  have hone_ball : (1 : ℂ) ∈ ball 0 (1 + ε) := by
    rw [mem_ball, dist_zero_right, norm_one]
    linarith
  have hone_zero : f 1 = 0 := hzero hone_ball
  exact (apm_a01J05_boundary_ne_zero hf_boundary 1 (by simp [apm_a01J05_circle])) hone_zero

/-- The analytic order of `f` is finite at every point of the closed unit
disk, including its boundary. -/
lemma apm_a01J05_analyticOrderAt_ne_top_of_mem_closedBall
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    analyticOrderAt f z ≠ ⊤ := by
  rw [mem_closedBall] at hz
  rcases lt_or_eq_of_le hz with hzlt | hzeq
  · exact apm_a01J05_analyticOrderAt_ne_top hε hf hf_boundary
      (by simpa [apm_a01J05_disk, mem_ball] using hzlt)
  · have hzsphere : z ∈ apm_a01J05_circle := by
      simpa [apm_a01J05_circle, mem_sphere] using hzeq
    have hzne : f z ≠ 0 := apm_a01J05_boundary_ne_zero hf_boundary z hzsphere
    intro htop
    exact hzne ((analyticOrderAt_eq_top.mp htop).self_of_nhds)

/-- On the open unit disk, the meromorphic divisor coefficient on the closed
disk is the finite natural analytic order. -/
lemma apm_a01J05_divisor_eq_analyticOrderNatAt
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) :
    divisor f (closedBall 0 1) z = (analyticOrderNatAt f z : ℤ) := by
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) 1) :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩).meromorphicOn
  have haz : AnalyticAt ℂ f z :=
    apm_a01J05_analyticAt_of_closedBall hε hf hz
  have hfinite : analyticOrderAt f z ≠ ⊤ :=
    apm_a01J05_analyticOrderAt_ne_top hε hf hf_boundary hz
  rw [divisor_apply hmer (ball_subset_closedBall hz), haz.meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt hfinite]
  simp

/-- On the entire closed unit disk, including the boundary, the divisor
coefficient is the finite natural analytic order. -/
lemma apm_a01J05_divisor_eq_analyticOrderNatAt_of_mem_closedBall
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    divisor f (closedBall 0 1) z = (analyticOrderNatAt f z : ℤ) := by
  have hfan : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) :=
    apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩
  have hfinite : analyticOrderAt f z ≠ ⊤ :=
    apm_a01J05_analyticOrderAt_ne_top_of_mem_closedBall hε hf hf_boundary hz
  rw [divisor_apply hfan.meromorphicOn hz,
    (hfan z hz).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt hfinite]
  simp

/-- Meromorphic order of `f` on the closed disk, expressed as the cast of its
finite natural analytic order. -/
lemma apm_a01J05_meromorphicOrderAt_eq_analyticOrderNatAt
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    meromorphicOrderAt f z = (analyticOrderNatAt f z : WithTop ℤ) := by
  have hfan : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) :=
    apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩
  have hfinite : analyticOrderAt f z ≠ ⊤ :=
    apm_a01J05_analyticOrderAt_ne_top_of_mem_closedBall hε hf hf_boundary hz
  rw [(hfan z hz).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt hfinite]
  rfl

/-- The disk-restricted analytic-order function has finite support. This is
the summability bridge from the custom `tsum` multiplicity to the finite
meromorphic divisor. -/
lemma apm_a01J05_zeroMultiplicity_support_finite
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    {z : ℂ | z ∈ apm_a01J05_disk ∧ analyticOrderAt f z ≠ 0}.Finite := by
  have hmer : MeromorphicOn f (closedBall (0 : ℂ) 1) :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩).meromorphicOn
  apply ((divisor f (closedBall (0 : ℂ) 1)).finiteSupport
    (isCompact_closedBall (0 : ℂ) 1)).subset
  rintro z ⟨hz, hzsupport⟩
  apply Function.mem_support.mpr
  intro hdiv
  have hn : analyticOrderNatAt f z = 0 := by
    rw [apm_a01J05_divisor_eq_analyticOrderNatAt hε hf hf_boundary hz] at hdiv
    exact_mod_cast hdiv
  apply hzsupport
  have hfinite : analyticOrderAt f z ≠ ⊤ :=
    apm_a01J05_analyticOrderAt_ne_top hε hf hf_boundary hz
  simp [← Nat.cast_analyticOrderNatAt hfinite, hn]

open Classical in
/-- Under the analytic and boundary hypotheses, the custom multiplicity
`tsum` is an actual finite sum. -/
lemma apm_a01J05_zeroMultiplicity_eq_finsum
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    apm_a01J05_zeroMultiplicity f =
      ∑ᶠ z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderAt f z else 0 := by
  classical
  rw [apm_a01J05_zeroMultiplicity, tsum_eq_finsum]
  apply (apm_a01J05_zeroMultiplicity_support_finite hε hf hf_boundary).subset
  intro z hz
  simp only [Function.mem_support] at hz
  by_cases hzdisk : z ∈ apm_a01J05_disk
  · exact ⟨hzdisk, by simpa [hzdisk] using hz⟩
  · exact False.elim (hz (by simp [hzdisk]))

/-- The `ℕ∞` multiplicity is the cast of its natural-valued finite count. -/
lemma apm_a01J05_zeroMultiplicity_eq_natCast
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    apm_a01J05_zeroMultiplicity f = apm_a01J05_zeroMultiplicityNat f := by
  classical
  have hnat : (Function.support fun z : ℂ ↦
      if z ∈ apm_a01J05_disk then analyticOrderNatAt f z else 0).Finite := by
    apply (apm_a01J05_zeroMultiplicity_support_finite hε hf hf_boundary).subset
    intro z hz
    simp only [Function.mem_support] at hz
    by_cases hzdisk : z ∈ apm_a01J05_disk
    · refine ⟨hzdisk, ?_⟩
      intro horder
      apply hz
      simp [hzdisk, analyticOrderNatAt, horder]
    · exact False.elim (hz (by simp [hzdisk]))
  rw [apm_a01J05_zeroMultiplicity_eq_finsum hε hf hf_boundary,
    apm_a01J05_zeroMultiplicityNat]
  change (∑ᶠ z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderAt f z else 0) =
    (Nat.castAddMonoidHom ℕ∞)
      (∑ᶠ z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderNatAt f z else 0)
  rw [(Nat.castAddMonoidHom ℕ∞).map_finsum hnat]
  apply finsum_congr
  intro z
  by_cases hz : z ∈ apm_a01J05_disk
  · have hfinite : analyticOrderAt f z ≠ ⊤ :=
      apm_a01J05_analyticOrderAt_ne_top hε hf hf_boundary hz
    simp only [if_pos hz]
    exact (Nat.cast_analyticOrderNatAt hfinite).symm
  · simp [hz]

/-- Boundary nonvanishing removes all boundary coefficients from the
closed-ball divisor, so its support is contained in the open unit disk. -/
lemma apm_a01J05_divisor_support_subset_disk
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    (divisor f (closedBall 0 1)).support ⊆ apm_a01J05_disk := by
  have hfan : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) :=
    apm_a01J05_analyticOnNhd_closedBall hf_analytic
  intro z hzsupport
  have hzclosed : z ∈ closedBall (0 : ℂ) 1 :=
    (divisor f (closedBall (0 : ℂ) 1)).supportWithinDomain hzsupport
  rw [apm_a01J05_disk, mem_ball]
  have hzle : dist z 0 ≤ 1 := by
    simpa [dist_comm] using (mem_closedBall.mp hzclosed)
  exact lt_of_le_of_ne hzle fun heq ↦ by
    have hzsphere : z ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere]
      exact heq
    have hzorder : meromorphicOrderAt f z = 0 :=
      (hfan z hzclosed).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (apm_a01J05_boundary_ne_zero hf_boundary z hzsphere)
    have hzdiv : divisor f (closedBall (0 : ℂ) 1) z = 0 := by
      simp [MeromorphicOn.divisor_apply hfan.meromorphicOn hzclosed, hzorder]
    exact (Function.mem_support.mp hzsupport) hzdiv

@[simp]
lemma apm_a01J05_mem_divisorSupport_iff {f : ℂ → ℂ} {z : ℂ} :
    z ∈ apm_a01J05_divisorSupport f ↔
      z ∈ (divisor f (closedBall 0 1)).support := by
  simp [apm_a01J05_divisorSupport]

/-- Every center appearing in the canonical product lies in the open disk. -/
lemma apm_a01J05_divisorSupport_subset_disk
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    ∀ u ∈ apm_a01J05_divisorSupport f, u ∈ apm_a01J05_disk := by
  intro u hu
  exact apm_a01J05_divisor_support_subset_disk hf_analytic hf_boundary
    (apm_a01J05_mem_divisorSupport_iff.mp hu)

/-- The natural analytic-order count and naturalized meromorphic-divisor count
agree under the target hypotheses. -/
lemma apm_a01J05_zeroMultiplicityNat_eq_divisorMultiplicityNat
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    apm_a01J05_zeroMultiplicityNat f =
      apm_a01J05_divisorMultiplicityNat f := by
  classical
  rw [apm_a01J05_zeroMultiplicityNat, apm_a01J05_divisorMultiplicityNat]
  apply finsum_congr
  intro z
  by_cases hz : z ∈ apm_a01J05_disk
  · rw [if_pos hz, apm_a01J05_divisor_eq_analyticOrderNatAt hε hf hf_boundary hz]
    simp
  · rw [if_neg hz]
    have hdiv : divisor f (closedBall (0 : ℂ) 1) z = 0 := by
      by_contra hne
      exact hz (apm_a01J05_divisor_support_subset_disk ⟨ε, hε, hf⟩ hf_boundary
        (Function.mem_support.mpr hne))
    simp [hdiv]

/-! The derivative does not have constant norm on the circle.  The following
variants isolate the weaker boundary-nonvanishing hypothesis actually used by
the analytic-order/divisor transport. -/

lemma apm_a01J05_analyticOrderAt_ne_top_of_boundary_ne_zero
    {g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hboundary : ∀ z ∈ apm_a01J05_circle, g z ≠ 0)
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) :
    analyticOrderAt g z ≠ ⊤ := by
  intro htop
  have hdiff : DifferentiableOn ℂ g (ball (0 : ℂ) (1 + ε)) :=
    hg.mono ball_subset_closedBall
  have han : AnalyticOnNhd ℂ g (ball (0 : ℂ) (1 + ε)) :=
    hdiff.analyticOnNhd isOpen_ball
  have hzlarge : z ∈ ball (0 : ℂ) (1 + ε) :=
    (ball_subset_ball (by linarith : (1 : ℝ) ≤ 1 + ε)) hz
  have hzero : EqOn g 0 (ball (0 : ℂ) (1 + ε)) :=
    han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball 0 (1 + ε)).isPreconnected hzlarge
      (analyticOrderAt_eq_top.mp htop)
  have hone : (1 : ℂ) ∈ ball 0 (1 + ε) := by
    rw [mem_ball, dist_zero_right, norm_one]
    linarith
  exact hboundary 1 (by simp [apm_a01J05_circle]) (hzero hone)

lemma apm_a01J05_divisor_eq_analyticOrderNatAt_of_boundary_ne_zero
    {g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hboundary : ∀ z ∈ apm_a01J05_circle, g z ≠ 0)
    {z : ℂ} (hz : z ∈ apm_a01J05_disk) :
    divisor g (closedBall 0 1) z = (analyticOrderNatAt g z : ℤ) := by
  have hmer : MeromorphicOn g (closedBall (0 : ℂ) 1) :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hg⟩).meromorphicOn
  have haz : AnalyticAt ℂ g z :=
    apm_a01J05_analyticAt_of_closedBall hε hg hz
  have hfinite := apm_a01J05_analyticOrderAt_ne_top_of_boundary_ne_zero
    hε hg hboundary hz
  rw [divisor_apply hmer (ball_subset_closedBall hz), haz.meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt hfinite]
  simp

lemma apm_a01J05_zeroMultiplicity_support_finite_of_boundary_ne_zero
    {g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hboundary : ∀ z ∈ apm_a01J05_circle, g z ≠ 0) :
    {z : ℂ | z ∈ apm_a01J05_disk ∧ analyticOrderAt g z ≠ 0}.Finite := by
  have hmer : MeromorphicOn g (closedBall (0 : ℂ) 1) :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hg⟩).meromorphicOn
  apply ((divisor g (closedBall (0 : ℂ) 1)).finiteSupport
    (isCompact_closedBall (0 : ℂ) 1)).subset
  rintro z ⟨hz, hzsupport⟩
  apply Function.mem_support.mpr
  intro hdiv
  have hn : analyticOrderNatAt g z = 0 := by
    rw [apm_a01J05_divisor_eq_analyticOrderNatAt_of_boundary_ne_zero
      hε hg hboundary hz] at hdiv
    exact_mod_cast hdiv
  apply hzsupport
  have hfinite := apm_a01J05_analyticOrderAt_ne_top_of_boundary_ne_zero
    hε hg hboundary hz
  simp [← Nat.cast_analyticOrderNatAt hfinite, hn]

lemma apm_a01J05_zeroMultiplicity_eq_natCast_of_boundary_ne_zero
    {g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hboundary : ∀ z ∈ apm_a01J05_circle, g z ≠ 0) :
    apm_a01J05_zeroMultiplicity g = apm_a01J05_zeroMultiplicityNat g := by
  classical
  have hsupp := apm_a01J05_zeroMultiplicity_support_finite_of_boundary_ne_zero
    hε hg hboundary
  have hnat : (Function.support fun z : ℂ ↦
      if z ∈ apm_a01J05_disk then analyticOrderNatAt g z else 0).Finite := by
    apply hsupp.subset
    intro z hz
    simp only [Function.mem_support] at hz
    by_cases hzdisk : z ∈ apm_a01J05_disk
    · refine ⟨hzdisk, ?_⟩
      intro horder
      apply hz
      simp [hzdisk, analyticOrderNatAt, horder]
    · exact False.elim (hz (by simp [hzdisk]))
  rw [apm_a01J05_zeroMultiplicity, tsum_eq_finsum]
  · rw [apm_a01J05_zeroMultiplicityNat]
    change (∑ᶠ z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderAt g z else 0) =
      (Nat.castAddMonoidHom ℕ∞)
        (∑ᶠ z : ℂ, if z ∈ apm_a01J05_disk then analyticOrderNatAt g z else 0)
    rw [(Nat.castAddMonoidHom ℕ∞).map_finsum hnat]
    apply finsum_congr
    intro z
    by_cases hz : z ∈ apm_a01J05_disk
    · have hfinite := apm_a01J05_analyticOrderAt_ne_top_of_boundary_ne_zero
        hε hg hboundary hz
      simp only [if_pos hz]
      exact (Nat.cast_analyticOrderNatAt hfinite).symm
    · simp [hz]
  · apply hsupp.subset
    intro z hz
    simp only [Function.mem_support] at hz
    by_cases hzdisk : z ∈ apm_a01J05_disk
    · exact ⟨hzdisk, by simpa [hzdisk] using hz⟩
    · exact False.elim (hz (by simp [hzdisk]))

lemma apm_a01J05_divisor_support_subset_disk_of_boundary_ne_zero
    {g : ℂ → ℂ}
    (hg_analytic : ∃ ε > 0,
      DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hboundary : ∀ z ∈ apm_a01J05_circle, g z ≠ 0) :
    (divisor g (closedBall 0 1)).support ⊆ apm_a01J05_disk := by
  have hfan := apm_a01J05_analyticOnNhd_closedBall hg_analytic
  intro z hzsupport
  have hzclosed := (divisor g (closedBall (0 : ℂ) 1)).supportWithinDomain hzsupport
  rw [apm_a01J05_disk, mem_ball]
  have hzle : dist z 0 ≤ 1 := by
    simpa [dist_comm] using (mem_closedBall.mp hzclosed)
  exact lt_of_le_of_ne hzle fun heq ↦ by
    have hzsphere : z ∈ apm_a01J05_circle := by
      simpa [apm_a01J05_circle, mem_sphere] using heq
    have hzorder : meromorphicOrderAt g z = 0 :=
      (hfan z hzclosed).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (hboundary z hzsphere)
    have hzdiv : divisor g (closedBall (0 : ℂ) 1) z = 0 := by
      simp [MeromorphicOn.divisor_apply hfan.meromorphicOn hzclosed, hzorder]
    exact (Function.mem_support.mp hzsupport) hzdiv

lemma apm_a01J05_zeroMultiplicityNat_eq_divisorMultiplicityNat_of_boundary_ne_zero
    {g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hboundary : ∀ z ∈ apm_a01J05_circle, g z ≠ 0) :
    apm_a01J05_zeroMultiplicityNat g =
      apm_a01J05_divisorMultiplicityNat g := by
  classical
  rw [apm_a01J05_zeroMultiplicityNat, apm_a01J05_divisorMultiplicityNat]
  apply finsum_congr
  intro z
  by_cases hz : z ∈ apm_a01J05_disk
  · rw [if_pos hz,
      apm_a01J05_divisor_eq_analyticOrderNatAt_of_boundary_ne_zero
        hε hg hboundary hz]
    simp
  · rw [if_neg hz]
    have hdiv : divisor g (closedBall (0 : ℂ) 1) z = 0 := by
      by_contra hne
      exact hz (apm_a01J05_divisor_support_subset_disk_of_boundary_ne_zero
        ⟨ε, hε, hg⟩ hboundary (Function.mem_support.mpr hne))
    simp [hdiv]

lemma apm_a01J05_zeroMultiplicity_eq_divisorMultiplicityNat_of_boundary_ne_zero
    {g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hg : DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hboundary : ∀ z ∈ apm_a01J05_circle, g z ≠ 0) :
    apm_a01J05_zeroMultiplicity g = apm_a01J05_divisorMultiplicityNat g := by
  rw [apm_a01J05_zeroMultiplicity_eq_natCast_of_boundary_ne_zero
    hε hg hboundary,
    apm_a01J05_zeroMultiplicityNat_eq_divisorMultiplicityNat_of_boundary_ne_zero
      hε hg hboundary]

/-- A finite product of canonical factors whose centers lie in the unit disk
has unit norm on the boundary circle. This is the boundary half of the finite
Blaschke representation used by the remaining divisor theorem. -/
lemma apm_a01J05_norm_canonicalFactor_prod
    (s : Finset ℂ) (n : ℂ → ℕ)
    (hs : ∀ u ∈ s, u ∈ apm_a01J05_disk)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    ‖∏ u ∈ s, (canonicalFactor 1 u z) ^ n u‖ = 1 := by
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro u hu
  rw [norm_pow, norm_canonicalFactor_eval_circle_eq_one (hs u hu) hz, one_pow]

/-- The canonical product attached to `f` has unit norm on the boundary. -/
lemma apm_a01J05_norm_canonicalProduct
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    ‖apm_a01J05_canonicalProduct f z‖ = 1 := by
  exact apm_a01J05_norm_canonicalFactor_prod
    (apm_a01J05_divisorSupport f)
    (fun u ↦ Int.toNat (divisor f (closedBall 0 1) u))
    (apm_a01J05_divisorSupport_subset_disk hf_analytic hf_boundary) hz

/-- The finite canonical product is meromorphic on the whole plane. -/
lemma apm_a01J05_canonicalProduct_meromorphicOn
    (f : ℂ → ℂ) : MeromorphicOn (apm_a01J05_canonicalProduct f) univ := by
  intro z hz
  unfold apm_a01J05_canonicalProduct
  have hp : MeromorphicAt
      (∏ u ∈ apm_a01J05_divisorSupport f,
        (canonicalFactor 1 u) ^ Int.toNat (divisor f (closedBall 0 1) u)) z := by
    apply MeromorphicAt.prod
    intro u hu
    exact (meromorphicOn_canonicalFactor 1 u z (mem_univ z)).pow _
  convert hp using 1
  ext w
  simp

/-- Away from its finite center set, the canonical product is analytic. -/
lemma apm_a01J05_canonicalProduct_analyticAt_of_not_mem
    (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∉ apm_a01J05_divisorSupport f) :
    AnalyticAt ℂ (apm_a01J05_canonicalProduct f) z := by
  unfold apm_a01J05_canonicalProduct
  have hp : AnalyticAt ℂ
      (∏ u ∈ apm_a01J05_divisorSupport f,
        (canonicalFactor 1 u) ^ Int.toNat (divisor f (closedBall 0 1) u)) z := by
    apply (apm_a01J05_divisorSupport f).analyticAt_prod
    intro u hu
    apply AnalyticAt.pow
    exact analyticOnNhd_canonicalFactor 1 u z (by
      intro hzu
      apply hz
      exact hzu.symm ▸ hu)
  convert hp using 1
  ext w
  simp

/-- Off divisor support, the raw canceled product is analytic. -/
lemma apm_a01J05_mul_canonicalProduct_analyticAt_of_not_mem
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    AnalyticAt ℂ (f * apm_a01J05_canonicalProduct f) z := by
  exact (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩ z hz).mul
    (apm_a01J05_canonicalProduct_analyticAt_of_not_mem f hzsupport)

/-- Off divisor support, the raw canceled product is nonzero. -/
lemma apm_a01J05_mul_canonicalProduct_ne_zero_of_not_mem
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    (f * apm_a01J05_canonicalProduct f) z ≠ 0 := by
  have hdiv : divisor f (closedBall (0 : ℂ) 1) z = 0 := by
    apply not_ne_iff.mp
    intro hne
    exact hzsupport (apm_a01J05_mem_divisorSupport_iff.mpr
      (Function.mem_support.mpr hne))
  have hn : analyticOrderNatAt f z = 0 := by
    rw [apm_a01J05_divisor_eq_analyticOrderNatAt_of_mem_closedBall
      hε hf hf_boundary hz] at hdiv
    exact_mod_cast hdiv
  have hfan : AnalyticAt ℂ f z :=
    apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩ z hz
  have hfinite : analyticOrderAt f z ≠ ⊤ :=
    apm_a01J05_analyticOrderAt_ne_top_of_mem_closedBall hε hf hf_boundary hz
  have hfz : f z ≠ 0 := by
    have hordzero : analyticOrderAt f z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hfinite, hn]
      simp
    exact (analyticOrderAt_eq_zero.mp hordzero).resolve_left (not_not.mpr hfan)
  rw [Pi.mul_apply, mul_ne_zero_iff]
  refine ⟨hfz, ?_⟩
  rw [apm_a01J05_canonicalProduct]
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu
  apply pow_ne_zero
  apply canonicalFactor_ne_zero
    (apm_a01J05_divisorSupport_subset_disk ⟨ε, hε, hf⟩ hf_boundary u hu)
    hz
  intro hzu
  apply hzsupport
  exact hzu ▸ hu

/-- Local order of the canonical product is the finite sum of the local
orders of its powered canonical factors. -/
lemma apm_a01J05_meromorphicOrderAt_canonicalProduct
    (f : ℂ → ℂ) (z : ℂ) :
    meromorphicOrderAt (apm_a01J05_canonicalProduct f) z =
      ∑ u ∈ apm_a01J05_divisorSupport f,
        (Int.toNat (divisor f (closedBall 0 1) u) : WithTop ℤ) *
          meromorphicOrderAt (canonicalFactor 1 u) z := by
  unfold apm_a01J05_canonicalProduct
  rw [meromorphicOrderAt_fun_prod]
  · apply Finset.sum_congr rfl
    intro u hu
    change meromorphicOrderAt
      ((canonicalFactor 1 u) ^ Int.toNat (divisor f (closedBall 0 1) u)) z = _
    rw [meromorphicOrderAt_pow
      (meromorphicOn_canonicalFactor 1 u z (mem_univ z))]
  · intro u hu
    exact (meromorphicOn_canonicalFactor 1 u z (mem_univ z)).pow _

/-- A canonical factor contributes zero meromorphic order away from its own
center throughout the closed unit disk. -/
lemma apm_a01J05_meromorphicOrderAt_canonicalFactor_of_ne
    {u z : ℂ} (hu : u ∈ apm_a01J05_disk)
    (hz : z ∈ closedBall (0 : ℂ) 1) (hzu : z ≠ u) :
    meromorphicOrderAt (canonicalFactor 1 u) z = 0 := by
  have han : AnalyticAt ℂ (canonicalFactor 1 u) z :=
    analyticOnNhd_canonicalFactor 1 u z (by simpa using hzu)
  exact han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (canonicalFactor_ne_zero hu hz hzu)

/-- At a divisor center, the canonical product has precisely the opposite
order to the analytic zero order of `f`. -/
lemma apm_a01J05_meromorphicOrderAt_canonicalProduct_at_center
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {u : ℂ} (hu : u ∈ apm_a01J05_divisorSupport f) :
    meromorphicOrderAt (apm_a01J05_canonicalProduct f) u =
      -(analyticOrderNatAt f u : WithTop ℤ) := by
  have hudisk : u ∈ apm_a01J05_disk :=
    apm_a01J05_divisorSupport_subset_disk ⟨ε, hε, hf⟩ hf_boundary u hu
  rw [apm_a01J05_meromorphicOrderAt_canonicalProduct, Finset.sum_eq_single u]
  · rw [apm_a01J05_divisor_eq_analyticOrderNatAt hε hf hf_boundary hudisk,
      meromorphicOrderAt_canonicalFactor hudisk]
    change (((analyticOrderNatAt f u : ℕ) : ℤ) : WithTop ℤ) *
      ((-1 : ℤ) : WithTop ℤ) =
        ((-((analyticOrderNatAt f u : ℕ) : ℤ) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_mul]
    norm_num
  · intro z hz hzu
    rw [apm_a01J05_meromorphicOrderAt_canonicalFactor_of_ne
      (apm_a01J05_divisorSupport_subset_disk ⟨ε, hε, hf⟩ hf_boundary z hz)
      (ball_subset_closedBall hudisk) hzu.symm]
    simp
  · intro hnot
    exact (hnot hu).elim

/-- Away from the divisor support, the canonical product has order zero on
the closed unit disk. -/
lemma apm_a01J05_meromorphicOrderAt_canonicalProduct_of_not_mem
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hzclosed : z ∈ closedBall (0 : ℂ) 1)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    meromorphicOrderAt (apm_a01J05_canonicalProduct f) z = 0 := by
  rw [apm_a01J05_meromorphicOrderAt_canonicalProduct]
  apply Finset.sum_eq_zero
  intro u hu
  have hzu : z ≠ u := by
    intro h
    apply hzsupport
    simpa [h] using hu
  rw [apm_a01J05_meromorphicOrderAt_canonicalFactor_of_ne
    (apm_a01J05_divisorSupport_subset_disk hf_analytic hf_boundary u hu)
    hzclosed hzu]
  simp

/-- Multiplying by the canonical product cancels every zero order of `f` on
the closed disk, leaving meromorphic order zero everywhere. -/
lemma apm_a01J05_meromorphicOrderAt_mul_canonicalProduct_eq_zero
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    meromorphicOrderAt (f * apm_a01J05_canonicalProduct f) z = 0 := by
  have hmerf : MeromorphicAt f z :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩ z hz).meromorphicAt
  have hmerprod : MeromorphicAt (apm_a01J05_canonicalProduct f) z :=
    apm_a01J05_canonicalProduct_meromorphicOn f z (mem_univ z)
  rw [meromorphicOrderAt_mul hmerf hmerprod,
    apm_a01J05_meromorphicOrderAt_eq_analyticOrderNatAt hε hf hf_boundary hz]
  by_cases hzsupport : z ∈ apm_a01J05_divisorSupport f
  · rw [apm_a01J05_meromorphicOrderAt_canonicalProduct_at_center
      hε hf hf_boundary hzsupport]
    change (((analyticOrderNatAt f z : ℕ) : ℤ) : WithTop ℤ) +
      ((-((analyticOrderNatAt f z : ℕ) : ℤ) : ℤ) : WithTop ℤ) = 0
    rw [← WithTop.coe_add]
    simp
  · have hdiv : divisor f (closedBall (0 : ℂ) 1) z = 0 := by
      apply not_ne_iff.mp
      intro hne
      exact hzsupport (apm_a01J05_mem_divisorSupport_iff.mpr
        (Function.mem_support.mpr hne))
    have hn : analyticOrderNatAt f z = 0 := by
      rw [apm_a01J05_divisor_eq_analyticOrderNatAt_of_mem_closedBall
        hε hf hf_boundary hz] at hdiv
      exact_mod_cast hdiv
    rw [apm_a01J05_meromorphicOrderAt_canonicalProduct_of_not_mem
      ⟨ε, hε, hf⟩ hf_boundary hz hzsupport, hn]
    simp

/-- At every closed-disk point, the canonical-product cancellation admits a
nonvanishing analytic local extension. The agreement is punctured because
Mathlib's canonical factor assigns `0` at its pole. -/
lemma apm_a01J05_exists_local_analyticExtension_mul_canonicalProduct
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      f * apm_a01J05_canonicalProduct f =ᶠ[nhdsWithin z {z}ᶜ] g := by
  have hmerf : MeromorphicAt f z :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩ z hz).meromorphicAt
  have hmerprod : MeromorphicAt (apm_a01J05_canonicalProduct f) z :=
    apm_a01J05_canonicalProduct_meromorphicOn f z (mem_univ z)
  have hmer : MeromorphicAt (f * apm_a01J05_canonicalProduct f) z :=
    hmerf.mul hmerprod
  have hord : meromorphicOrderAt (f * apm_a01J05_canonicalProduct f) z =
      (0 : ℤ) := by
    simpa using apm_a01J05_meromorphicOrderAt_mul_canonicalProduct_eq_zero
      hε hf hf_boundary hz
  obtain ⟨g, hgan, hgne, hagree⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp hord
  refine ⟨g, hgan, hgne, ?_⟩
  filter_upwards [hagree] with w hw
  simpa using hw

/-- The regularized canceled product is nonzero at every point of the closed
unit disk. -/
lemma apm_a01J05_regularizedCanonicalProduct_ne_zero
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    apm_a01J05_regularizedCanonicalProduct f z ≠ 0 := by
  have hmerf : MeromorphicAt f z :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩ z hz).meromorphicAt
  have hmerprod : MeromorphicAt (apm_a01J05_canonicalProduct f) z :=
    apm_a01J05_canonicalProduct_meromorphicOn f z (mem_univ z)
  have hmer : MeromorphicAt (f * apm_a01J05_canonicalProduct f) z :=
    hmerf.mul hmerprod
  rw [apm_a01J05_regularizedCanonicalProduct]
  exact hmer.meromorphicTrailingCoeffAt_ne_zero (by
    rw [apm_a01J05_meromorphicOrderAt_mul_canonicalProduct_eq_zero
      hε hf hf_boundary hz]
    exact WithTop.coe_ne_top)

/-- Away from divisor support, regularization leaves the raw canceled product
unchanged. -/
lemma apm_a01J05_regularizedCanonicalProduct_eq_of_not_mem
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    apm_a01J05_regularizedCanonicalProduct f z =
      (f * apm_a01J05_canonicalProduct f) z := by
  rw [apm_a01J05_regularizedCanonicalProduct]
  exact (apm_a01J05_mul_canonicalProduct_analyticAt_of_not_mem
    hε hf hz hzsupport).meromorphicTrailingCoeffAt_of_ne_zero
      (apm_a01J05_mul_canonicalProduct_ne_zero_of_not_mem
        hε hf hf_boundary hz hzsupport)

/-- The regularized canceled product has unit norm on the boundary circle. -/
lemma apm_a01J05_norm_regularizedCanonicalProduct
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    ‖apm_a01J05_regularizedCanonicalProduct f z‖ = 1 := by
  obtain ⟨ε, hε, hf⟩ := hf_analytic
  have hzclosed : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
  have hzsupport : z ∉ apm_a01J05_divisorSupport f := by
    intro hzs
    have hzball := apm_a01J05_divisorSupport_subset_disk ⟨ε, hε, hf⟩
      hf_boundary z hzs
    rw [apm_a01J05_disk, mem_ball] at hzball
    rw [apm_a01J05_circle, mem_sphere] at hz
    linarith
  rw [apm_a01J05_regularizedCanonicalProduct_eq_of_not_mem
    hε hf hf_boundary hzclosed hzsupport, Pi.mul_apply, norm_mul,
    hf_boundary z hz,
    apm_a01J05_norm_canonicalProduct ⟨ε, hε, hf⟩ hf_boundary hz]
  norm_num

/-- A finite set is locally reduced to a chosen point. -/
lemma apm_a01J05_eventually_mem_finset_imp_eq
    (s : Finset ℂ) (z : ℂ) :
    ∀ᶠ w in nhds z, w ∈ s → w = z := by
  have hznot : z ∉ ((↑(s.erase z) : Set ℂ)) := by simp
  have hnhds : ((↑(s.erase z) : Set ℂ))ᶜ ∈ nhds z :=
    (s.erase z).finite_toSet.isClosed.compl_mem_nhds hznot
  filter_upwards [hnhds] with w hw hws
  by_contra hwz
  exact hw (by simp [Finset.mem_erase, hwz, hws])

/-- The regularized canceled product is analytic at every divisor center. -/
lemma apm_a01J05_regularizedCanonicalProduct_analyticAt_of_mem
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hzsupport : z ∈ apm_a01J05_divisorSupport f) :
    AnalyticAt ℂ (apm_a01J05_regularizedCanonicalProduct f) z := by
  have hzball : z ∈ apm_a01J05_disk :=
    apm_a01J05_divisorSupport_subset_disk ⟨ε, hε, hf⟩
      hf_boundary z hzsupport
  obtain ⟨g, hgan, hgne, hagree⟩ :=
    apm_a01J05_exists_local_analyticExtension_mul_canonicalProduct
      hε hf hf_boundary (ball_subset_closedBall hzball)
  have hcenter : apm_a01J05_regularizedCanonicalProduct f z = g z := by
    rw [apm_a01J05_regularizedCanonicalProduct]
    apply hgan.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0) hgne
    filter_upwards [hagree] with w hw
    simpa using hw
  apply (analyticAt_congr ?_).mpr hgan
  have hballnhds : apm_a01J05_disk ∈ nhds z :=
    isOpen_ball.mem_nhds hzball
  have hisolate := apm_a01J05_eventually_mem_finset_imp_eq
    (apm_a01J05_divisorSupport f) z
  have hagree' : ∀ᶠ w in nhdsWithin z {z}ᶜ,
      (f * apm_a01J05_canonicalProduct f) w = g w := hagree
  rw [eventually_nhdsWithin_iff] at hagree'
  filter_upwards [hballnhds, hisolate, hagree'] with w hwball hwisolate hwagree
  by_cases hwz : w = z
  · simpa [hwz] using hcenter
  · have hwsupport : w ∉ apm_a01J05_divisorSupport f := by
      intro hws
      exact hwz (hwisolate hws)
    rw [apm_a01J05_regularizedCanonicalProduct_eq_of_not_mem
      hε hf hf_boundary (ball_subset_closedBall hwball) hwsupport]
    exact hwagree hwz

/-- The regularized canceled product is analytic at closed-disk points away
from divisor support. -/
lemma apm_a01J05_regularizedCanonicalProduct_analyticAt_of_not_mem
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    AnalyticAt ℂ (apm_a01J05_regularizedCanonicalProduct f) z := by
  let raw := f * apm_a01J05_canonicalProduct f
  have hrawan : AnalyticAt ℂ raw z :=
    apm_a01J05_mul_canonicalProduct_analyticAt_of_not_mem hε hf hz hzsupport
  have hrawne : raw z ≠ 0 :=
    apm_a01J05_mul_canonicalProduct_ne_zero_of_not_mem
      hε hf hf_boundary hz hzsupport
  have hevne : ∀ᶠ w in nhds z, raw w ≠ 0 :=
    (hrawan.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hrawne
  apply (analyticAt_congr ?_).mpr hrawan
  filter_upwards [hrawan.eventually_analyticAt, hevne] with w hwan hwne
  rw [apm_a01J05_regularizedCanonicalProduct]
  exact hwan.meromorphicTrailingCoeffAt_of_ne_zero hwne

/-- The regularized canceled product is analytic on a neighborhood of the
closed unit disk. -/
lemma apm_a01J05_regularizedCanonicalProduct_analyticOnNhd
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    AnalyticOnNhd ℂ (apm_a01J05_regularizedCanonicalProduct f)
      (closedBall 0 1) := by
  intro z hz
  by_cases hzsupport : z ∈ apm_a01J05_divisorSupport f
  · exact apm_a01J05_regularizedCanonicalProduct_analyticAt_of_mem
      hε hf hf_boundary hzsupport
  · exact apm_a01J05_regularizedCanonicalProduct_analyticAt_of_not_mem
      hε hf hf_boundary hz hzsupport

/-- Maximum modulus gives the unit upper bound for the regularized product on
the closed unit disk. -/
lemma apm_a01J05_norm_regularizedCanonicalProduct_le_one
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖apm_a01J05_regularizedCanonicalProduct f z‖ ≤ 1 := by
  apply norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    ((apm_a01J05_regularizedCanonicalProduct_analyticOnNhd
      hε hf hf_boundary).differentiableOn.diffContOnCl_ball subset_rfl)
  · intro w hw
    rw [frontier_ball (0 : ℂ) one_ne_zero] at hw
    rw [apm_a01J05_norm_regularizedCanonicalProduct ⟨ε, hε, hf⟩
      hf_boundary hw]
  · simpa [closure_ball] using hz

/-- Applying maximum modulus to the inverse gives the matching lower bound. -/
lemma apm_a01J05_one_le_norm_regularizedCanonicalProduct
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    1 ≤ ‖apm_a01J05_regularizedCanonicalProduct f z‖ := by
  let G := apm_a01J05_regularizedCanonicalProduct f
  have hdiff : DiffContOnCl ℂ G (ball (0 : ℂ) 1) :=
    (apm_a01J05_regularizedCanonicalProduct_analyticOnNhd
      hε hf hf_boundary).differentiableOn.diffContOnCl_ball subset_rfl
  have hzero : ∀ w ∈ closure (ball (0 : ℂ) 1), G w ≠ 0 := by
    intro w hw
    apply apm_a01J05_regularizedCanonicalProduct_ne_zero hε hf hf_boundary
    simpa [closure_ball] using hw
  have hinv : ‖(G⁻¹) z‖ ≤ 1 := by
    apply norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdiff.inv hzero)
    · intro w hw
      rw [frontier_ball (0 : ℂ) one_ne_zero] at hw
      simp [G, norm_inv,
        apm_a01J05_norm_regularizedCanonicalProduct ⟨ε, hε, hf⟩ hf_boundary hw]
    · simpa [closure_ball] using hz
  have hznonzero : G z ≠ 0 :=
    apm_a01J05_regularizedCanonicalProduct_ne_zero hε hf hf_boundary hz
  apply (inv_le_one₀ (norm_pos_iff.mpr hznonzero)).mp
  simpa [G, norm_inv] using hinv

/-- The regularized canceled product has norm exactly one throughout the
closed disk. -/
lemma apm_a01J05_norm_regularizedCanonicalProduct_eq_one
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖apm_a01J05_regularizedCanonicalProduct f z‖ = 1 := by
  exact le_antisymm
    (apm_a01J05_norm_regularizedCanonicalProduct_le_one hε hf hf_boundary hz)
    (apm_a01J05_one_le_norm_regularizedCanonicalProduct hε hf hf_boundary hz)

/-- The regularized canceled product is a unimodular constant on the closed
unit disk. -/
lemma apm_a01J05_regularizedCanonicalProduct_eq_const
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ z ∈ closedBall (0 : ℂ) 1,
        apm_a01J05_regularizedCanonicalProduct f z = c := by
  let G := apm_a01J05_regularizedCanonicalProduct f
  let c := G 0
  have hdiff : DiffContOnCl ℂ G (ball (0 : ℂ) 1) :=
    (apm_a01J05_regularizedCanonicalProduct_analyticOnNhd
      hε hf hf_boundary).differentiableOn.diffContOnCl_ball subset_rfl
  have hmax : IsMaxOn (norm ∘ G) (ball (0 : ℂ) 1) 0 := by
    intro z hz
    change ‖apm_a01J05_regularizedCanonicalProduct f z‖ ≤
      ‖apm_a01J05_regularizedCanonicalProduct f 0‖
    rw [apm_a01J05_norm_regularizedCanonicalProduct_eq_one
      hε hf hf_boundary (ball_subset_closedBall hz)]
    change 1 ≤ ‖G 0‖
    rw [apm_a01J05_norm_regularizedCanonicalProduct_eq_one
      hε hf hf_boundary (by simp)]
  have heq := eqOn_closure_of_isPreconnected_of_isMaxOn_norm
    (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hdiff
    (mem_ball_self (by norm_num : (0 : ℝ) < 1)) hmax
  refine ⟨c, ?_, ?_⟩
  · exact apm_a01J05_norm_regularizedCanonicalProduct_eq_one
      hε hf hf_boundary (by simp)
  · intro z hz
    exact heq (by simpa [closure_ball] using hz)

/-- Finite-Blaschke identity in the form needed for differentiation: away
from the finite zero set, `f` times its canonical divisor product is a
unimodular constant. -/
lemma apm_a01J05_exists_mul_canonicalProduct_eq_const
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ z ∈ closedBall (0 : ℂ) 1,
        z ∉ apm_a01J05_divisorSupport f →
          (f * apm_a01J05_canonicalProduct f) z = c := by
  obtain ⟨c, hc, hconst⟩ :=
    apm_a01J05_regularizedCanonicalProduct_eq_const hε hf hf_boundary
  refine ⟨c, hc, ?_⟩
  intro z hz hzsupport
  rw [← apm_a01J05_regularizedCanonicalProduct_eq_of_not_mem
    hε hf hf_boundary hz hzsupport]
  exact hconst z hz

/-- Differentiated finite-Blaschke identity away from the divisor support. -/
lemma apm_a01J05_deriv_mul_canonicalProduct_eq_zero
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_disk)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    deriv (f * apm_a01J05_canonicalProduct f) z = 0 := by
  obtain ⟨c, hc, hidentity⟩ :=
    apm_a01J05_exists_mul_canonicalProduct_eq_const hε hf hf_boundary
  have hballnhds : apm_a01J05_disk ∈ nhds z := isOpen_ball.mem_nhds hz
  have hisolate := apm_a01J05_eventually_mem_finset_imp_eq
    (apm_a01J05_divisorSupport f) z
  have heq : f * apm_a01J05_canonicalProduct f =ᶠ[nhds z] fun _ ↦ c := by
    filter_upwards [hballnhds, hisolate] with w hwball hwisolate
    apply hidentity w (ball_subset_closedBall hwball)
    intro hwsupport
    exact hzsupport ((hwisolate hwsupport).symm ▸ hwsupport)
  have hderiv := heq.deriv_eq
  simpa using hderiv

/-- Product-rule form of the differentiated finite-Blaschke identity. -/
lemma apm_a01J05_deriv_mul_canonicalProduct_add_eq_zero
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_disk)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    deriv f z * apm_a01J05_canonicalProduct f z +
      f z * deriv (apm_a01J05_canonicalProduct f) z = 0 := by
  have hdf : DifferentiableAt ℂ f z :=
    (apm_a01J05_analyticAt_of_closedBall hε hf hz).differentiableAt
  have hdp : DifferentiableAt ℂ (apm_a01J05_canonicalProduct f) z :=
    (apm_a01J05_canonicalProduct_analyticAt_of_not_mem f hzsupport).differentiableAt
  rw [← deriv_mul hdf hdp]
  exact apm_a01J05_deriv_mul_canonicalProduct_eq_zero
    hε hf hf_boundary hz hzsupport

/-- Logarithmic-derivative form of the finite-Blaschke identity off the zero
set. -/
lemma apm_a01J05_deriv_eq_neg_mul_deriv_canonicalProduct_div
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_disk)
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    deriv f z = -f z * deriv (apm_a01J05_canonicalProduct f) z /
      apm_a01J05_canonicalProduct f z := by
  have hrawne := apm_a01J05_mul_canonicalProduct_ne_zero_of_not_mem
    hε hf hf_boundary (ball_subset_closedBall hz) hzsupport
  have hpne : apm_a01J05_canonicalProduct f z ≠ 0 :=
    (mul_ne_zero_iff.mp hrawne).2
  have heq := apm_a01J05_deriv_mul_canonicalProduct_add_eq_zero
    hε hf hf_boundary hz hzsupport
  apply (eq_div_iff hpne).mpr
  linear_combination heq

/-- Explicit derivative of a unit-disk canonical factor away from its pole. -/
lemma apm_a01J05_deriv_canonicalFactor
    {u z : ℂ} (hzu : z ≠ u) :
    deriv (canonicalFactor 1 u) z =
      ((starRingEnd ℂ) u * u - 1) / (z - u) ^ 2 := by
  have hnum : HasDerivAt (fun w : ℂ ↦ 1 - (starRingEnd ℂ) u * w)
      (-(starRingEnd ℂ) u) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) u)) using 1 <;> ring
  have hden : HasDerivAt (fun w : ℂ ↦ w - u) 1 z :=
    (hasDerivAt_id z).sub_const u
  have hquot := hnum.div hden (sub_ne_zero.mpr hzu)
  unfold canonicalFactor
  norm_num at hquot ⊢
  have hd : deriv (fun w : ℂ ↦ (1 - (starRingEnd ℂ) u * w) / (w - u)) z =
      (-(starRingEnd ℂ) u * (z - u) -
        (1 - (starRingEnd ℂ) u * z)) / (z - u) ^ 2 := by
    have hquot' : HasDerivAt
        (fun w : ℂ ↦ (1 - (starRingEnd ℂ) u * w) / (w - u))
        ((-(starRingEnd ℂ) u * (z - u) -
          (1 - (starRingEnd ℂ) u * z)) / (z - u) ^ 2) z := by
      convert hquot using 1 <;> ring
    exact hquot'.deriv
  rw [hd]
  field_simp [sub_ne_zero.mpr hzu]
  ring

/-- Explicit finite-product derivative of the canonical divisor product away
from its centers. -/
lemma apm_a01J05_deriv_canonicalProduct
    (f : ℂ → ℂ) {z : ℂ}
    (hzsupport : z ∉ apm_a01J05_divisorSupport f) :
    deriv (apm_a01J05_canonicalProduct f) z =
      ∑ u ∈ apm_a01J05_divisorSupport f,
        (∏ j ∈ (apm_a01J05_divisorSupport f).erase u,
          canonicalFactor 1 j z ^ Int.toNat (divisor f (closedBall 0 1) j)) *
        ((Int.toNat (divisor f (closedBall 0 1) u) : ℂ) *
          canonicalFactor 1 u z ^
            (Int.toNat (divisor f (closedBall 0 1) u) - 1) *
          (((starRingEnd ℂ) u * u - 1) / (z - u) ^ 2)) := by
  unfold apm_a01J05_canonicalProduct
  rw [deriv_fun_finset_prod]
  · apply Finset.sum_congr rfl
    intro u hu
    have hzu : z ≠ u := by
      intro h
      exact hzsupport (h.symm ▸ hu)
    rw [deriv_fun_pow
      ((analyticOnNhd_canonicalFactor 1 u z (by simpa using hzu)).differentiableAt),
      apm_a01J05_deriv_canonicalFactor hzu]
    simp only [smul_eq_mul]
  · intro u hu
    exact (analyticOnNhd_canonicalFactor 1 u z (by
      intro h
      exact hzsupport (h.symm ▸ hu))).differentiableAt.pow _

/-- Logarithmic derivative of one canonical factor. -/
lemma apm_a01J05_logDeriv_canonicalFactor
    {u z : ℂ} (hu : u ∈ apm_a01J05_disk)
    (hz : z ∈ closedBall (0 : ℂ) 1) (hzu : z ≠ u) :
    deriv (canonicalFactor 1 u) z / canonicalFactor 1 u z =
      ((starRingEnd ℂ) u * u - 1) /
        ((z - u) * (1 - (starRingEnd ℂ) u * z)) := by
  rw [apm_a01J05_deriv_canonicalFactor hzu, canonicalFactor_apply]
  norm_num
  have hfactor := canonicalFactor_ne_zero hu hz hzu
  rw [canonicalFactor_apply] at hfactor
  norm_num at hfactor
  have hnum : 1 - (starRingEnd ℂ) u * z ≠ 0 := hfactor.1
  field_simp [sub_ne_zero.mpr hzu, hnum]

/-- On the unit circle, the two linear factors in the canonical-factor
logarithmic derivative combine into a positive real norm square. -/
lemma apm_a01J05_circle_denominator_identity
    {u z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    (z - u) * (1 - (starRingEnd ℂ) u * z) =
      z * (Complex.normSq (z - u) : ℂ) := by
  have hnorm : ‖z‖ = 1 := by
    rw [apm_a01J05_circle, mem_sphere, dist_zero_right] at hz
    exact hz
  have hzunit : (starRingEnd ℂ) z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [Complex.normSq_eq_conj_mul_self, map_sub]
  rw [← hzunit]
  ring

/-- The boundary logarithmic derivative of one canonical factor, in its
real Poisson-kernel form (with the negative sign appropriate to our
reciprocal convention for `canonicalFactor`). -/
lemma apm_a01J05_circle_logDeriv_canonicalFactor
    {u z : ℂ} (hu : u ∈ apm_a01J05_disk)
    (hz : z ∈ apm_a01J05_circle) (hzu : z ≠ u) :
    z * (deriv (canonicalFactor 1 u) z / canonicalFactor 1 u z) =
      ((Complex.normSq u : ℂ) - 1) /
        (Complex.normSq (z - u) : ℂ) := by
  have hzclosed : z ∈ closedBall (0 : ℂ) 1 :=
    sphere_subset_closedBall hz
  rw [apm_a01J05_logDeriv_canonicalFactor hu hzclosed hzu,
    apm_a01J05_circle_denominator_identity hz,
    ← Complex.normSq_eq_conj_mul_self]
  have hz0 : z ≠ 0 := by
    intro hzzero
    subst z
    simpa [apm_a01J05_circle] using hz
  have hsq : (Complex.normSq (z - u) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_eq_zero.not.mpr (sub_ne_zero.mpr hzu))
  field_simp

/-- The real Poisson-kernel coefficient contributed by an interior center is
strictly negative at every boundary point. -/
lemma apm_a01J05_circle_logDeriv_coefficient_neg
    {u z : ℂ} (hu : u ∈ apm_a01J05_disk) (hzu : z ≠ u) :
    (Complex.normSq u - 1) / Complex.normSq (z - u) < 0 := by
  have hunorm : ‖u‖ < 1 := by
    simpa [apm_a01J05_disk, mem_ball] using hu
  have hnum : Complex.normSq u - 1 < 0 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg u]
  have hden : 0 < Complex.normSq (z - u) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hzu)
  exact div_neg_of_neg_of_pos hnum hden

/-- The one-factor boundary logarithmic derivative is the coercion of the
strictly negative real Poisson-kernel coefficient. -/
lemma apm_a01J05_circle_logDeriv_canonicalFactor_real
    {u z : ℂ} (hu : u ∈ apm_a01J05_disk)
    (hz : z ∈ apm_a01J05_circle) (hzu : z ≠ u) :
    z * (deriv (canonicalFactor 1 u) z / canonicalFactor 1 u z) =
      (((Complex.normSq u - 1) / Complex.normSq (z - u) : ℝ) : ℂ) := by
  rw [apm_a01J05_circle_logDeriv_canonicalFactor hu hz hzu]
  norm_cast

/-- Every member of the divisor support carries a strictly positive natural
multiplicity (analyticity rules out pole coefficients). -/
lemma apm_a01J05_divisorMultiplicity_pos_at_support
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {u : ℂ} (hu : u ∈ apm_a01J05_divisorSupport f) :
    0 < Int.toNat (divisor f (closedBall 0 1) u) := by
  have hudisk : u ∈ apm_a01J05_disk :=
    apm_a01J05_divisorSupport_subset_disk ⟨ε, hε, hf⟩ hf_boundary u hu
  have hdivne : divisor f (closedBall (0 : ℂ) 1) u ≠ 0 :=
    Function.mem_support.mp (apm_a01J05_mem_divisorSupport_iff.mp hu)
  rw [apm_a01J05_divisor_eq_analyticOrderNatAt hε hf hf_boundary hudisk]
  have horderne : analyticOrderNatAt f u ≠ 0 := by
    intro hzero
    apply hdivne
    rw [apm_a01J05_divisor_eq_analyticOrderNatAt hε hf hf_boundary hudisk,
      hzero]
    norm_num
  simpa using Nat.pos_of_ne_zero horderne

/-- A supported center contributes a strictly negative weighted Poisson
kernel coefficient on the unit circle. -/
lemma apm_a01J05_weighted_circle_logDeriv_coefficient_neg
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {u z : ℂ} (hu : u ∈ apm_a01J05_divisorSupport f)
    (hz : z ∈ apm_a01J05_circle) :
    (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) *
        ((Complex.normSq u - 1) / Complex.normSq (z - u)) < 0 := by
  have hudisk : u ∈ apm_a01J05_disk :=
    apm_a01J05_divisorSupport_subset_disk ⟨ε, hε, hf⟩ hf_boundary u hu
  have hzu : z ≠ u := by
    intro h
    subst z
    have hu_norm : ‖u‖ < 1 := by
      simpa [apm_a01J05_disk, mem_ball] using hudisk
    have hu_circle : ‖u‖ = 1 := by
      simpa [apm_a01J05_circle, mem_sphere] using hz
    linarith
  have hmultiplicity := apm_a01J05_divisorMultiplicity_pos_at_support
    hε hf hf_boundary hu
  have hmultiplicity_real :
      0 < (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) := by
    exact_mod_cast hmultiplicity
  exact mul_neg_of_pos_of_neg hmultiplicity_real
    (apm_a01J05_circle_logDeriv_coefficient_neg hudisk hzu)

/-- Consequently, the total weighted Poisson-kernel sum is strictly negative
as soon as the divisor support is nonempty. -/
lemma apm_a01J05_circle_logDeriv_sum_neg
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hsupport : (apm_a01J05_divisorSupport f).Nonempty)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    ∑ u ∈ apm_a01J05_divisorSupport f,
      (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) *
        ((Complex.normSq u - 1) / Complex.normSq (z - u)) < 0 := by
  classical
  let S := apm_a01J05_divisorSupport f
  let g : ℂ → ℝ := fun u ↦
    (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) *
      ((Complex.normSq u - 1) / Complex.normSq (z - u))
  change ∑ u ∈ S, g u < 0
  rcases hsupport with ⟨u, hu⟩
  have huS : u ∈ S := hu
  rw [← Finset.sum_erase_add _ _ huS]
  have herase : ∑ v ∈ S.erase u, g v ≤ 0 := by
    apply Finset.sum_nonpos
    intro v hv
    exact le_of_lt (apm_a01J05_weighted_circle_logDeriv_coefficient_neg
      hε hf hf_boundary (by exact (Finset.mem_erase.mp hv).2) hz)
  have hu_neg : g u < 0 :=
    apm_a01J05_weighted_circle_logDeriv_coefficient_neg
      hε hf hf_boundary hu hz
  linarith

/-- Positive total zero multiplicity forces the finite divisor support to be
nonempty. -/
lemma apm_a01J05_divisorSupport_nonempty
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    (apm_a01J05_divisorSupport f).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hdivzero : ∀ z : ℂ, divisor f (closedBall 0 1) z = 0 := by
    intro z
    by_contra hz
    have hzmem : z ∈ apm_a01J05_divisorSupport f :=
      apm_a01J05_mem_divisorSupport_iff.mpr (Function.mem_support.mpr hz)
    rw [hempty] at hzmem
    simp at hzmem
  have hcountzero : apm_a01J05_divisorMultiplicityNat f = 0 := by
    rw [apm_a01J05_divisorMultiplicityNat]
    calc
      (∑ᶠ z : ℂ, Int.toNat (divisor f (closedBall 0 1) z)) =
          ∑ᶠ _z : ℂ, 0 := by
            apply finsum_congr
            intro z
            simp [hdivzero z]
      _ = 0 := by simp
  have hnat : apm_a01J05_zeroMultiplicityNat f = N := by
    have hcast := hf_zeros
    rw [apm_a01J05_zeroMultiplicity_eq_natCast hε hf hf_boundary] at hcast
    exact_mod_cast hcast
  rw [apm_a01J05_zeroMultiplicityNat_eq_divisorMultiplicityNat
    hε hf hf_boundary, hcountzero] at hnat
  omega

/-- Logarithmic differentiation converts a finite product of differentiable,
nonvanishing functions into the sum of their logarithmic derivatives. -/
lemma apm_a01J05_logDeriv_finset_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℂ → ℂ) (z : ℂ)
    (hdiff : ∀ i ∈ s, DifferentiableAt ℂ (g i) z)
    (hne : ∀ i ∈ s, g i z ≠ 0) :
    deriv (fun w ↦ ∏ i ∈ s, g i w) z / (∏ i ∈ s, g i z) =
      ∑ i ∈ s, deriv (g i) z / g i z := by
  simpa [logDeriv] using (logDeriv_prod hne hdiff)

/-- Boundary logarithmic derivative of a powered canonical factor. -/
lemma apm_a01J05_circle_logDeriv_canonicalFactor_pow
    {u z : ℂ} (n : ℕ) (hu : u ∈ apm_a01J05_disk)
    (hz : z ∈ apm_a01J05_circle) (hzu : z ≠ u) :
    z * (deriv (fun w ↦ canonicalFactor 1 u w ^ n) z /
        canonicalFactor 1 u z ^ n) =
      (n : ℂ) *
        (((Complex.normSq u - 1) / Complex.normSq (z - u) : ℝ) : ℂ) := by
  change z * logDeriv (fun w ↦ canonicalFactor 1 u w ^ n) z = _
  rw [logDeriv_fun_pow
    ((analyticOnNhd_canonicalFactor 1 u z (by simpa using hzu)).differentiableAt),
    show logDeriv (canonicalFactor 1 u) z =
      deriv (canonicalFactor 1 u) z / canonicalFactor 1 u z from rfl,
    ← apm_a01J05_circle_logDeriv_canonicalFactor_real hu hz hzu]
  ring

/-- Boundary logarithmic derivative of the complete finite canonical product
as the coercion of its real weighted Poisson-kernel sum. -/
lemma apm_a01J05_circle_logDeriv_canonicalProduct
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    z * (deriv (apm_a01J05_canonicalProduct f) z /
        apm_a01J05_canonicalProduct f z) =
      ((∑ u ∈ apm_a01J05_divisorSupport f,
        (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) *
          ((Complex.normSq u - 1) / Complex.normSq (z - u)) : ℝ) : ℂ) := by
  classical
  let S := apm_a01J05_divisorSupport f
  let n : ℂ → ℕ := fun u ↦ Int.toNat (divisor f (closedBall 0 1) u)
  let g : ℂ → ℂ → ℂ := fun u w ↦ canonicalFactor 1 u w ^ n u
  have hcenter : ∀ u ∈ S, u ∈ apm_a01J05_disk :=
    apm_a01J05_divisorSupport_subset_disk hf_analytic hf_boundary
  have hzu : ∀ u ∈ S, z ≠ u := by
    intro u hu h
    subst z
    have hlt : ‖u‖ < 1 := by
      simpa [apm_a01J05_disk, mem_ball] using hcenter u hu
    have heq : ‖u‖ = 1 := by
      simpa [apm_a01J05_circle, mem_sphere] using hz
    linarith
  have hzclosed : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
  unfold apm_a01J05_canonicalProduct
  rw [apm_a01J05_logDeriv_finset_prod S g z]
  · rw [Finset.mul_sum]
    push_cast
    dsimp [S, g, n]
    apply Finset.sum_congr rfl
    intro u hu
    convert apm_a01J05_circle_logDeriv_canonicalFactor_pow
      (Int.toNat (divisor f (closedBall 0 1) u))
      (hcenter u hu) hz (hzu u hu) using 1 <;> norm_cast
  · intro u hu
    exact ((analyticOnNhd_canonicalFactor 1 u z
      (by simpa using hzu u hu)).differentiableAt.pow _)
  · intro u hu
    exact pow_ne_zero _ (canonicalFactor_ne_zero (hcenter u hu)
      hzclosed (hzu u hu))

/-- The canceled finite-Blaschke product has zero derivative also at boundary
points.  Although the constant identity was first obtained only on the closed
disk away from the finite divisor support, derivative uniqueness within the
closed disk is enough at its boundary. -/
lemma apm_a01J05_deriv_mul_canonicalProduct_eq_zero_on_circle
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    deriv (f * apm_a01J05_canonicalProduct f) z = 0 := by
  classical
  let K : Set ℂ := closedBall 0 1
  have hzK : z ∈ K := sphere_subset_closedBall hz
  have hzsupport : z ∉ apm_a01J05_divisorSupport f := by
    intro hzs
    have hzball := apm_a01J05_divisorSupport_subset_disk
      ⟨ε, hε, hf⟩ hf_boundary z hzs
    rw [apm_a01J05_disk, mem_ball] at hzball
    rw [apm_a01J05_circle, mem_sphere] at hz
    linarith
  obtain ⟨c, _hc, hidentity⟩ :=
    apm_a01J05_exists_mul_canonicalProduct_eq_const hε hf hf_boundary
  have hisolate := apm_a01J05_eventually_mem_finset_imp_eq
    (apm_a01J05_divisorSupport f) z
  have hisolate' : ∀ᶠ w in nhdsWithin z K,
      w ∈ apm_a01J05_divisorSupport f → w = z :=
    hisolate.filter_mono inf_le_left
  have heq : f * apm_a01J05_canonicalProduct f =ᶠ[nhdsWithin z K] fun _ ↦ c := by
    filter_upwards [hisolate', self_mem_nhdsWithin] with w hw hwK
    apply hidentity w hwK
    intro hws
    exact hzsupport ((hw hws).symm ▸ hws)
  have hdf : DifferentiableAt ℂ f z := by
    have hzlarge : z ∈ ball (0 : ℂ) (1 + ε) := by
      rw [mem_ball] at ⊢
      rw [apm_a01J05_circle, mem_sphere] at hz
      linarith
    exact (hf.mono ball_subset_closedBall).differentiableAt
      (isOpen_ball.mem_nhds hzlarge)
  have hdp : DifferentiableAt ℂ (apm_a01J05_canonicalProduct f) z :=
    (apm_a01J05_canonicalProduct_analyticAt_of_not_mem f hzsupport).differentiableAt
  have hprod : HasDerivWithinAt (f * apm_a01J05_canonicalProduct f)
      (deriv (f * apm_a01J05_canonicalProduct f) z) K z :=
    (hdf.mul hdp).hasDerivAt.hasDerivWithinAt
  have hzero : HasDerivWithinAt (f * apm_a01J05_canonicalProduct f) 0 K z :=
    (hasDerivWithinAt_const z K c).congr_of_eventuallyEq_of_mem heq
      hzK
  have hunique : UniqueDiffWithinAt ℂ K z := by
    apply (uniqueDiffOn_convex_of_isRCLikeNormedField (convex_closedBall 0 1) ?_) z hzK
    rw [interior_closedBall 0 (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.nonempty_ball.mpr (by norm_num)
  exact hunique.eq_deriv K hprod hzero

/-- Product-rule form of the boundary constant identity. -/
lemma apm_a01J05_deriv_mul_canonicalProduct_add_eq_zero_on_circle
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    deriv f z * apm_a01J05_canonicalProduct f z +
      f z * deriv (apm_a01J05_canonicalProduct f) z = 0 := by
  have hzsupport : z ∉ apm_a01J05_divisorSupport f := by
    intro hzs
    have hzball := apm_a01J05_divisorSupport_subset_disk
      ⟨ε, hε, hf⟩ hf_boundary z hzs
    rw [apm_a01J05_disk, mem_ball] at hzball
    rw [apm_a01J05_circle, mem_sphere] at hz
    linarith
  have hdf : DifferentiableAt ℂ f z := by
    have hzlarge : z ∈ ball (0 : ℂ) (1 + ε) := by
      rw [mem_ball] at ⊢
      rw [apm_a01J05_circle, mem_sphere] at hz
      linarith
    exact (hf.mono ball_subset_closedBall).differentiableAt
      (isOpen_ball.mem_nhds hzlarge)
  have hdp : DifferentiableAt ℂ (apm_a01J05_canonicalProduct f) z :=
    (apm_a01J05_canonicalProduct_analyticAt_of_not_mem f hzsupport).differentiableAt
  rw [← deriv_mul hdf hdp]
  exact apm_a01J05_deriv_mul_canonicalProduct_eq_zero_on_circle
    hε hf hf_boundary hz

/-- A nonconstant canonical product associated to positive total multiplicity
has no critical point on the unit circle. -/
lemma apm_a01J05_deriv_canonicalProduct_ne_zero_on_circle
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    deriv (apm_a01J05_canonicalProduct f) z ≠ 0 := by
  have hsum := apm_a01J05_circle_logDeriv_sum_neg hε hf hf_boundary
    (apm_a01J05_divisorSupport_nonempty hN hε hf hf_boundary hf_zeros) hz
  have hlog := apm_a01J05_circle_logDeriv_canonicalProduct
    ⟨ε, hε, hf⟩ hf_boundary hz
  intro hderiv
  rw [hderiv] at hlog
  norm_num at hlog
  have hcastzero :
      (∑ u ∈ apm_a01J05_divisorSupport f,
        (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) *
          ((Complex.normSq u - 1) / Complex.normSq (z - u))) = 0 := by
    exact_mod_cast hlog.symm
  linarith

/-- Positive degree forces the original finite Blaschke function itself to
have no critical point on the boundary.  This transfers the preceding result
from the reciprocal canonical product using the differentiated constant
product identity. -/
lemma apm_a01J05_deriv_ne_zero_on_circle
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    deriv f z ≠ 0 := by
  have hpderiv : deriv (apm_a01J05_canonicalProduct f) z ≠ 0 :=
    apm_a01J05_deriv_canonicalProduct_ne_zero_on_circle
      hN hε hf hf_boundary hf_zeros hz
  have hfne : f z ≠ 0 := apm_a01J05_boundary_ne_zero hf_boundary z hz
  have hprod := apm_a01J05_deriv_mul_canonicalProduct_add_eq_zero_on_circle
    hε hf hf_boundary hz
  intro hfderiv
  rw [hfderiv] at hprod
  norm_num at hprod
  exact hpderiv (hprod.resolve_left hfne)

/-- The derivative inherits analyticity on a still larger-than-unit closed
disk; shrinking the original margin by one half supplies the closed
neighborhood required by the multiplicity/divisor infrastructure. -/
lemma apm_a01J05_deriv_differentiableOn_larger_closedBall
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε))) :
    DifferentiableOn ℂ (deriv f) (closedBall 0 (1 + ε / 2)) := by
  have hsub : closedBall (0 : ℂ) (1 + ε / 2) ⊆ ball 0 (1 + ε) := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hfan : AnalyticOnNhd ℂ f (ball (0 : ℂ) (1 + ε)) :=
    (hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball
  exact (hfan.deriv.mono hsub).differentiableOn

/-- The target's custom derivative multiplicity is exactly the naturalized
closed-disk derivative divisor.  This discharges the derivative-side
`tsum`/finite-support transport independently of the remaining winding count. -/
lemma apm_a01J05_zeroMultiplicity_deriv_eq_divisorMultiplicityNat
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    apm_a01J05_zeroMultiplicity (deriv f) =
      apm_a01J05_divisorMultiplicityNat (deriv f) := by
  apply apm_a01J05_zeroMultiplicity_eq_divisorMultiplicityNat_of_boundary_ne_zero
    (show 0 < ε / 2 by positivity)
    (apm_a01J05_deriv_differentiableOn_larger_closedBall hε hf)
  intro z hz
  exact apm_a01J05_deriv_ne_zero_on_circle
    hN hε hf hf_boundary hf_zeros hz

/-- A global branch of the complex logarithm on the boundary image makes the
logarithmic derivative exact, hence its circle integral vanishes. -/
lemma apm_a01J05_circleIntegral_logDeriv_eq_zero_of_mapsTo_slitPlane
    {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hdiff : ∀ z ∈ sphere c R, DifferentiableAt ℂ g z)
    (hslit : ∀ z ∈ sphere c R, g z ∈ Complex.slitPlane) :
    (∮ z in C(c, R), logDeriv g z) = 0 := by
  apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
  intro z hz
  simpa only [logDeriv_apply] using
    ((hdiff z hz).hasDerivAt.clog (hslit z hz)).hasDerivWithinAt

/-- On the unit circle, `z f'/f` is the negative of the reciprocal canonical
product's real Poisson-kernel sum. -/
lemma apm_a01J05_circle_logSlope_eq_neg_sum
    {f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    z * (deriv f z / f z) =
      -((∑ u ∈ apm_a01J05_divisorSupport f,
        (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) *
          ((Complex.normSq u - 1) / Complex.normSq (z - u)) : ℝ) : ℂ) := by
  have hfne : f z ≠ 0 := apm_a01J05_boundary_ne_zero hf_boundary z hz
  have hzsupport : z ∉ apm_a01J05_divisorSupport f := by
    intro hzs
    have hzball := apm_a01J05_divisorSupport_subset_disk
      ⟨ε, hε, hf⟩ hf_boundary z hzs
    rw [apm_a01J05_disk, mem_ball] at hzball
    rw [apm_a01J05_circle, mem_sphere] at hz
    linarith
  have hpne : apm_a01J05_canonicalProduct f z ≠ 0 := by
    intro hpzero
    have hnorm := apm_a01J05_norm_canonicalProduct
      ⟨ε, hε, hf⟩ hf_boundary hz
    rw [hpzero, norm_zero] at hnorm
    norm_num at hnorm
  let S : ℂ := ((∑ u ∈ apm_a01J05_divisorSupport f,
    (Int.toNat (divisor f (closedBall 0 1) u) : ℝ) *
      ((Complex.normSq u - 1) / Complex.normSq (z - u)) : ℝ) : ℂ)
  change z * (deriv f z / f z) = -S
  have hprod := apm_a01J05_deriv_mul_canonicalProduct_add_eq_zero_on_circle
    hε hf hf_boundary hz
  have hlog := apm_a01J05_circle_logDeriv_canonicalProduct
    ⟨ε, hε, hf⟩ hf_boundary hz
  change z * (deriv (apm_a01J05_canonicalProduct f) z /
    apm_a01J05_canonicalProduct f z) = S at hlog
  have hrel :
      z * deriv f z * apm_a01J05_canonicalProduct f z +
        f z * (z * deriv (apm_a01J05_canonicalProduct f) z) = 0 := by
    linear_combination z * hprod
  have hlog' : z * deriv (apm_a01J05_canonicalProduct f) z =
      apm_a01J05_canonicalProduct f z * S := by
    field_simp [hpne] at hlog
    convert hlog using 1 <;> ring
  rw [hlog'] at hrel
  have hcore : z * deriv f z + f z * S = 0 := by
    apply (mul_right_cancel₀ hpne)
    linear_combination hrel
  field_simp [hfne]
  linear_combination hcore

/-- The boundary logarithmic slope `z f'/f` has winding zero: the finite
Blaschke Poisson-kernel formula places its entire boundary image in the
positive real ray, where the principal complex logarithm is a primitive. -/
lemma apm_a01J05_circleIntegral_logDeriv_logSlope_eq_zero
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    (∮ z in C(0, 1), logDeriv (fun w ↦ w * (deriv f w / f w)) z) = 0 := by
  apply apm_a01J05_circleIntegral_logDeriv_eq_zero_of_mapsTo_slitPlane
    (by norm_num)
  · intro z hz
    have hz' : z ∈ apm_a01J05_circle := by
      simpa [apm_a01J05_circle] using hz
    have hzclosed : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
    have hfat : DifferentiableAt ℂ f z :=
      (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩ z hzclosed).differentiableAt
    have hdat : DifferentiableAt ℂ (deriv f) z := by
      have hzlarge : z ∈ ball (0 : ℂ) (1 + ε) := by
        rw [mem_ball] at ⊢
        rw [apm_a01J05_circle, mem_sphere] at hz'
        linarith
      have hfan : AnalyticOnNhd ℂ f (ball (0 : ℂ) (1 + ε)) :=
        (hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball
      exact (hfan.deriv z hzlarge).differentiableAt
    exact differentiableAt_id.mul (hdat.div hfat
      (apm_a01J05_boundary_ne_zero hf_boundary z hz'))
  · intro z hz
    have hz' : z ∈ apm_a01J05_circle := by
      simpa [apm_a01J05_circle] using hz
    have hsum := apm_a01J05_circle_logDeriv_sum_neg hε hf hf_boundary
      (apm_a01J05_divisorSupport_nonempty hN hε hf hf_boundary hf_zeros) hz'
    rw [apm_a01J05_circle_logSlope_eq_neg_sum hε hf hf_boundary hz']
    simpa using Complex.ofReal_mem_slitPlane.mpr (neg_pos.mpr hsum)

/-- Pointwise logarithmic differentiation of the boundary slope. -/
lemma apm_a01J05_logDeriv_logSlope
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N)
    {z : ℂ} (hz : z ∈ apm_a01J05_circle) :
    logDeriv (fun w ↦ w * (deriv f w / f w)) z =
      1 / z + logDeriv (deriv f) z - logDeriv f z := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simpa [apm_a01J05_circle] using hz
  have hzclosed : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
  have hfat : DifferentiableAt ℂ f z :=
    (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩ z hzclosed).differentiableAt
  have hdat : DifferentiableAt ℂ (deriv f) z := by
    have hzlarge : z ∈ ball (0 : ℂ) (1 + ε) := by
      rw [mem_ball] at ⊢
      rw [apm_a01J05_circle, mem_sphere] at hz
      linarith
    have hfan : AnalyticOnNhd ℂ f (ball (0 : ℂ) (1 + ε)) :=
      (hf.mono ball_subset_closedBall).analyticOnNhd isOpen_ball
    exact (hfan.deriv z hzlarge).differentiableAt
  have hfne : f z ≠ 0 := apm_a01J05_boundary_ne_zero hf_boundary z hz
  have hdne : deriv f z ≠ 0 :=
    apm_a01J05_deriv_ne_zero_on_circle hN hε hf hf_boundary hf_zeros hz
  rw [logDeriv_mul (f := fun w : ℂ ↦ w)
      (g := fun w ↦ deriv f w / f w) z hz0 (div_ne_zero hdne hfne)
      differentiableAt_id (hdat.div hfat hfne),
    logDeriv_id',
    logDeriv_div (f := deriv f) (g := f) z hdne hfne hdat hfat]
  ring

/-- The derivative is analytic on a neighborhood of the entire closed unit
disk, the regularity hypothesis needed by the argument principle. -/
lemma apm_a01J05_deriv_analyticOnNhd_closedBall
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε))) :
    AnalyticOnNhd ℂ (deriv f) (closedBall (0 : ℂ) 1) := by
  obtain ⟨ε, hε, hf⟩ := hf_analytic
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 (1 + ε) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    linarith
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hf.mono ball_subset_closedBall
  have han : AnalyticOnNhd ℂ f (ball (0 : ℂ) (1 + ε)) :=
    hdiff.analyticOnNhd isOpen_ball
  intro z hz
  exact han.deriv z (hsub hz)

/-- Argument-principle bridge for the derivative, with the boundary
nonvanishing premise isolated from the already compiled analytic premise. -/
lemma apm_a01J05_circleIntegral_logDeriv_deriv_eq_divisor_sum
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hderiv_boundary : ∀ z ∈ apm_a01J05_circle, deriv f z ≠ 0) :
    (∮ z in C(0, 1), logDeriv (deriv f) z) =
      (∑ᶠ z, (divisor (deriv f) (closedBall 0 1) z : ℂ)) *
        (2 * Real.pi * Complex.I) := by
  exact ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum
    (by norm_num) (apm_a01J05_deriv_analyticOnNhd_closedBall hf_analytic)
    (by simpa [apm_a01J05_circle] using hderiv_boundary)

/-- Argument-principle equation for the original finite-Blaschke function. -/
lemma apm_a01J05_circleIntegral_logDeriv_eq_divisor_sum
    {f : ℂ → ℂ}
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) :
    (∮ z in C(0, 1), logDeriv f z) =
      (∑ᶠ z, (divisor f (closedBall 0 1) z : ℂ)) *
        (2 * Real.pi * Complex.I) := by
  exact ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum
    (by norm_num) (apm_a01J05_analyticOnNhd_closedBall hf_analytic)
    (by simpa [apm_a01J05_circle] using
      apm_a01J05_boundary_ne_zero hf_boundary)

/-- The source closed-disk divisor total is exactly the multiplicity supplied
in the theorem statement. -/
lemma apm_a01J05_divisorMultiplicityNat_eq
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    apm_a01J05_divisorMultiplicityNat f = N := by
  have hnat : apm_a01J05_zeroMultiplicityNat f = N := by
    have hcast := hf_zeros
    rw [apm_a01J05_zeroMultiplicity_eq_natCast hε hf hf_boundary] at hcast
    exact_mod_cast hcast
  rw [← apm_a01J05_zeroMultiplicityNat_eq_divisorMultiplicityNat
    hε hf hf_boundary]
  exact hnat

/-- The complex cast of an analytic closed-disk divisor sum is the cast of
its naturalized multiplicity total. -/
lemma apm_a01J05_divisor_sum_eq_natCast
    {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1)) :
    (∑ᶠ z, (divisor g (closedBall 0 1) z : ℂ)) =
      (apm_a01J05_divisorMultiplicityNat g : ℂ) := by
  classical
  rw [apm_a01J05_divisorMultiplicityNat]
  change (∑ᶠ z, (divisor g (closedBall 0 1) z : ℂ)) =
    (Nat.castAddMonoidHom ℂ)
      (∑ᶠ z, Int.toNat (divisor g (closedBall 0 1) z))
  rw [(Nat.castAddMonoidHom ℂ).map_finsum]
  · apply finsum_congr
    intro z
    rw [← Int.toNat_of_nonneg (hg.divisor_nonneg z)]
    norm_cast
  · exact ((divisor g (closedBall (0 : ℂ) 1)).finiteSupport
      (isCompact_closedBall (0 : ℂ) 1)).subset fun z hz ↦ by
        simp only [Function.mem_support] at hz ⊢
        intro hzero
        exact hz (by simp [hzero])

/-- Integrating the logarithmic-slope decomposition and using its zero
winding gives the one-turn difference between the derivative and source
logarithmic derivatives. -/
lemma apm_a01J05_circleIntegral_logDeriv_deriv_eq_sub_one
    {f : ℂ → ℂ} {N : ℕ} {ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    (∮ z in C(0, 1), logDeriv (deriv f) z) =
      (∮ z in C(0, 1), logDeriv f z) - 2 * Real.pi * Complex.I := by
  let S := sphere (0 : ℂ) 1
  have hfan := apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩
  have hdan := apm_a01J05_deriv_analyticOnNhd_closedBall ⟨ε, hε, hf⟩
  have hfne : ∀ z ∈ S, f z ≠ 0 := by
    simpa [S, apm_a01J05_circle] using apm_a01J05_boundary_ne_zero hf_boundary
  have hdne : ∀ z ∈ S, deriv f z ≠ 0 := by
    intro z hz
    apply apm_a01J05_deriv_ne_zero_on_circle hN hε hf hf_boundary hf_zeros
    simpa [S, apm_a01J05_circle] using hz
  have hflog : AnalyticOnNhd ℂ (logDeriv f) S := by
    simpa only [logDeriv_apply, div_eq_mul_inv] using
      (hfan.mono sphere_subset_closedBall).deriv.mul
        ((hfan.mono sphere_subset_closedBall).inv hfne)
  have hdlog : AnalyticOnNhd ℂ (logDeriv (deriv f)) S := by
    simpa only [logDeriv_apply, div_eq_mul_inv] using
      (hdan.mono sphere_subset_closedBall).deriv.mul
        ((hdan.mono sphere_subset_closedBall).inv hdne)
  have hone : CircleIntegrable (fun z : ℂ ↦ 1 / z) 0 1 := by
    apply (continuousOn_const.div continuousOn_id ?_).circleIntegrable (by norm_num)
    intro z hz hz0
    change z = 0 at hz0
    subst z
    simpa [S] using hz
  have hfint : CircleIntegrable (logDeriv f) 0 1 :=
    hflog.continuousOn.circleIntegrable (by norm_num)
  have hdint : CircleIntegrable (logDeriv (deriv f)) 0 1 :=
    hdlog.continuousOn.circleIntegrable (by norm_num)
  have hzero := apm_a01J05_circleIntegral_logDeriv_logSlope_eq_zero
    hN hε hf hf_boundary hf_zeros
  rw [circleIntegral.integral_congr (by norm_num) fun z hz ↦
      apm_a01J05_logDeriv_logSlope hN hε hf hf_boundary hf_zeros
        (by simpa [apm_a01J05_circle] using hz)] at hzero
  have hsplit :
      (∮ z in C(0, 1), 1 / z + logDeriv (deriv f) z - logDeriv f z) =
        ((∮ z in C(0, 1), 1 / z) +
          (∮ z in C(0, 1), logDeriv (deriv f) z)) -
            (∮ z in C(0, 1), logDeriv f z) := by
    calc
      (∮ z in C(0, 1), 1 / z + logDeriv (deriv f) z - logDeriv f z) =
          (∮ z in C(0, 1), (fun w ↦ 1 / w + logDeriv (deriv f) w) z -
            logDeriv f z) := rfl
      _ = (∮ z in C(0, 1), 1 / z + logDeriv (deriv f) z) -
          (∮ z in C(0, 1), logDeriv f z) :=
        circleIntegral.integral_sub (hone.add hdint) hfint
      _ = ((∮ z in C(0, 1), 1 / z) +
          (∮ z in C(0, 1), logDeriv (deriv f) z)) -
            (∮ z in C(0, 1), logDeriv f z) := by
        rw [circleIntegral.integral_add hone hdint]
  rw [hsplit] at hzero
  have honeint : (∮ z in C(0, 1), 1 / z) = 2 * Real.pi * Complex.I := by
    convert circleIntegral.integral_sub_center_inv
      (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0) using 1 <;>
      simp [div_eq_mul_inv]
  rw [honeint] at hzero
  linear_combination hzero

/-- Why this unblocks `apm_a01j05`: this is the missing finite-Blaschke
critical-point theorem, stated directly with the artifact's genuine analytic
and open-disk multiplicity notions. Its proof must connect the finite divisor
factorization to reflection across the unit circle and show that differentiation
reduces the total interior divisor by exactly one. -/
theorem apm_a01J05_bridge_1
    (f : ℂ → ℂ) (N : ℕ)
    (hN : 0 < N)
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    apm_a01J05_zeroMultiplicity (deriv f) = (N - 1 : ℕ) := by
  obtain ⟨ε, hε, hf⟩ := hf_analytic
  have hdne : ∀ z ∈ apm_a01J05_circle, deriv f z ≠ 0 :=
    fun z hz ↦ apm_a01J05_deriv_ne_zero_on_circle
      hN hε hf hf_boundary hf_zeros hz
  have hwind := apm_a01J05_circleIntegral_logDeriv_deriv_eq_sub_one
    hN hε hf hf_boundary hf_zeros
  rw [apm_a01J05_circleIntegral_logDeriv_deriv_eq_divisor_sum
      ⟨ε, hε, hf⟩ hdne,
    apm_a01J05_circleIntegral_logDeriv_eq_divisor_sum
      ⟨ε, hε, hf⟩ hf_boundary,
    apm_a01J05_divisor_sum_eq_natCast
      (apm_a01J05_deriv_analyticOnNhd_closedBall ⟨ε, hε, hf⟩),
    apm_a01J05_divisor_sum_eq_natCast
      (apm_a01J05_analyticOnNhd_closedBall ⟨ε, hε, hf⟩)] at hwind
  let C : ℂ := 2 * Real.pi * Complex.I
  have hC : C ≠ 0 := by
    dsimp [C]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  have hcast : (apm_a01J05_divisorMultiplicityNat (deriv f) : ℂ) =
      (apm_a01J05_divisorMultiplicityNat f : ℂ) - 1 := by
    apply (mul_right_cancel₀ hC)
    dsimp [C] at hwind ⊢
    linear_combination hwind
  have haddcast : (apm_a01J05_divisorMultiplicityNat (deriv f) : ℂ) + 1 =
      (apm_a01J05_divisorMultiplicityNat f : ℂ) := by
    linear_combination hcast
  have hadd : apm_a01J05_divisorMultiplicityNat (deriv f) + 1 =
      apm_a01J05_divisorMultiplicityNat f := by
    exact_mod_cast haddcast
  have hfcount := apm_a01J05_divisorMultiplicityNat_eq
    hε hf hf_boundary hf_zeros
  have hdcount : apm_a01J05_divisorMultiplicityNat (deriv f) = N - 1 := by
    omega
  rw [apm_a01J05_zeroMultiplicity_deriv_eq_divisorMultiplicityNat
      hN hε hf hf_boundary hf_zeros,
    hdcount]

theorem apm_a01j05 (f : ℂ → ℂ) (N : ℕ)
    (hN : 0 < N)
    (hf_analytic : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1)
    (hf_zeros : apm_a01J05_zeroMultiplicity f = N) :
    apm_a01J05_zeroMultiplicity (deriv f) = (N - 1 : ℕ) := by
  /-
  Closer hop 3 builds on the local analytic layer compiled by hop 2. The
  neighborhood hypothesis gives `AnalyticAt` for both `f` and `deriv f` at every point of
  the unit disk, and `apm_a01J05_order_deriv_add_one` records Mathlib's exact
  pointwise multiplicity-drop identity.

  Going beyond that boundary, `apm_a01J05_exists_finiteDivisor_factorization`
  applies `ConstructionTargets.Rouche.exists_zeroFree_factorization_on_closedBall`.
  The larger-disk differentiability hypothesis supplies neighborhood
  analyticity on the closed unit disk, and boundary norm one supplies
  nonvanishing on its circle. The resulting compiled factorization has the
  finite divisor product and an analytic zero-free remainder on the entire
  closed disk. Thus finite divisor extraction is no longer open.

  Renewed searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  `CanonicalDecomposition`, divisor, argument-principle, and Gauss--Lucas
  sources, related artifacts `a94A09` and `a94A10`, and git history found no
  theorem turning constant boundary norm into a finite Blaschke-product
  factorization, nor a theorem counting the critical points of such a product.
  `ConstructionTargets.Rouche.circleIntegral_logDeriv_eq_divisor_sum` counts
  zeros of one analytic function, but it does not provide the required global
  relation between the divisor sums of `f` and `deriv f`.

  Closure still requires upgrading the compiled divisor factorization to the
  reflected finite Blaschke factorization and relating its divisor finsum to
  the custom open-disk `tsum`, then proving the classical `N - 1` interior
  critical-point count, e.g. by reflection and the rational-map critical
  divisor or by an argument-principle calculation for the logarithmic derivative.
  -/
  exact apm_a01J05_bridge_1 f N hN hf_analytic hf_boundary hf_zeros
