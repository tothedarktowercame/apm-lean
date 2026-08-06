import Mathlib

/-! # APM b99A01: a half-plane maximum principle and valuation domains

The source file contains two independent problems.  Both are retained in the
single statement-bank theorem below.

## Statement repairs

* The boundary hypothesis binds `x : ℝ` but writes `|f(z)| ≤ M`.  This is the
  evident free-variable typo; it is encoded as `‖f (x : ℂ)‖ ≤ M`.
* Part (c) writes a degree-`n` expression with coefficients through
  `a_(n-1)`, so `n` is implicitly positive.  The formal statement makes
  `0 < n` explicit, excluding the syntactically meaningless degree-zero case.
-/

open Complex Set

noncomputable section

/-- The upper half-plane maximum principle followed by all five valuation-domain
claims from the bundled source problem. -/
theorem apm_b99a01 :
    (∀ (f : ℂ → ℂ) (M : ℝ),
      Bornology.IsBounded (f '' {z : ℂ | 0 ≤ z.im}) →
      ContinuousOn f {z : ℂ | 0 ≤ z.im} →
      DifferentiableOn ℂ f {z : ℂ | 0 < z.im} →
      (∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) →
      ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ M) ∧
    (∀ (V F : Type*) [CommRing V] [IsDomain V] [Field F] [Algebra V F]
      [IsFractionRing V F],
      (∀ α : F, α ≠ 0 →
        α ∈ Set.range (algebraMap V F) ∨
          α⁻¹ ∈ Set.range (algebraMap V F)) →
      (∀ I J : Ideal V, I ≤ J ∨ J ≤ I) ∧
      (∃! m : Ideal V, m.IsMaximal) ∧
      (∀ I : Ideal V, I.FG → I.IsPrincipal) ∧
      (∀ (α : F), α ≠ 0 → ∀ (n : ℕ), 0 < n → ∀ a : Fin n → V,
        α ^ n + ∑ i : Fin n, algebraMap V F (a i) * α ^ (i : ℕ)
            ∈ Set.range (algebraMap V F) →
        α ∈ Set.range (algebraMap V F)) ∧
      (∀ W : Subring F, Set.range (algebraMap V F) ⊆ W →
        (∀ α : F, α ≠ 0 → α ∈ W ∨ α⁻¹ ∈ W) ∧
        ∃ m : Ideal W, m.IsMaximal ∧
          (∀ n : Ideal W, n.IsMaximal → n = m) ∧
          (W : Set F) =
            {x | ∃ a s : V,
              algebraMap V F s ∉ ((↑) '' (m : Set W) : Set F) ∧
                x = algebraMap V F a / algebraMap V F s})) := by
  constructor
  · intro f M hbounded hcont hdiff hboundary z hz
    let g : ℂ → ℂ := fun w ↦ f (I * w)
    have hgdc : DiffContOnCl ℂ g {w : ℂ | 0 < w.re} := by
      constructor
      · apply hdiff.comp ((differentiable_const I).mul differentiable_id).differentiableOn
        intro w hw
        simpa [mul_im] using hw
      · apply hcont.comp (continuous_const_mul I).continuousOn
        intro w hw
        rw [closure_setOf_lt_re] at hw
        simpa [mul_im] using hw
    obtain ⟨C, hC⟩ := hbounded.exists_norm_le
    have hg_bound : ∀ w : ℂ, 0 ≤ w.re → ‖g w‖ ≤ C := by
      intro w hw
      apply hC
      exact ⟨I * w, by simpa [mul_im] using hw, rfl⟩
    have hgexp : ∃ c < (2 : ℝ), ∃ B,
        g =O[Bornology.cobounded ℂ ⊓ Filter.principal {w : ℂ | 0 < w.re}]
          fun w ↦ Real.exp (B * ‖w‖ ^ c) := by
      refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound C ?_⟩
      apply Filter.Eventually.filter_mono inf_le_right
      rw [Filter.eventually_principal]
      intro w hw
      simpa only [zero_mul, Real.exp_zero, Real.norm_eq_abs, abs_one, mul_one] using
        hg_bound w hw.le
    have hgreal : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop fun x : ℝ ↦ ‖g x‖ := by
      refine ⟨C, (Filter.eventually_ge_atTop 0).mono fun x hx ↦ ?_⟩
      exact hg_bound x (by simpa using hx)
    have hgimag : ∀ x : ℝ, ‖g (x * I)‖ ≤ M := by
      intro x
      have heq : I * ((x : ℂ) * I) = ((-x : ℝ) : ℂ) := calc
        I * ((x : ℂ) * I) = (x : ℂ) * (I * I) := by ring
        _ = (-x : ℝ) := by rw [I_mul_I]; norm_num
      simpa only [g, heq] using hboundary (-x)
    have hright : ‖g (-I * z)‖ ≤ M := by
      apply PhragmenLindelof.right_half_plane_of_bounded_on_real hgdc hgexp hgreal hgimag
      simpa [mul_re] using hz.le
    have heq : I * (-I * z) = z := calc
      I * (-I * z) = -(I * I) * z := by ring
      _ = z := by rw [I_mul_I]; simp
    simpa only [g, heq] using hright
  · intro V F _ _ _ _ _ hvaluation
    letI : ValuationRing V := (ValuationRing.iff_isInteger_or_isInteger V F).mpr fun α ↦ by
      by_cases hα : α = 0
      · left
        exact ⟨0, by simpa [hα]⟩
      · rcases hvaluation α hα with ⟨a, ha⟩ | ⟨a, ha⟩
        · exact Or.inl ⟨a, ha⟩
        · exact Or.inr ⟨a, ha⟩
    constructor
    · exact fun I J ↦
        ((ValuationRing.iff_ideal_total (R := V)).mp (inferInstance : ValuationRing V)).total I J
    constructor
    · exact IsLocalRing.maximal_ideal_unique V
    constructor
    · exact fun I hI ↦ IsBezout.isPrincipal_of_FG I hI
    /-
    Boundary after the compiled analytic half and valuation reductions:
    `PhragmenLindelof.right_half_plane_of_bounded_on_real`, applied after
    rotation by `I`, proves the complete upper-half-plane maximum principle.
    For the independent algebra half, Mathlib's
    `ValuationRing.iff_isInteger_or_isInteger`,
    `ValuationRing.iff_ideal_total`, and the `IsBezout` instance package the
    first three valuation-domain conclusions, proved above.  The remaining
    bundled conclusion includes the explicit monic-equation calculation and,
    especially, the final equality describing every intermediate subring `W`
    as fractions with denominators outside its unique maximal ideal, requires
    transporting the given range-based axiom to a `ValuationRing W` instance
    without an `IsFractionRing W F` hypothesis and then constructing the exact
    localization equality.  No theorem matching that overring bridge was found.
    -/
    sorry
