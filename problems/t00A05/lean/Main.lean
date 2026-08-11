import Mathlib

open MeasureTheory

/-!
# APM t00A05 — a closed angle form and two periods

## Statement repairs

1. The final absolute-value bar in the TeX display is a typographical
   delimiter; the intended error-free claims are the exterior derivative and
   two integrals.
2. The parametrization of `C₂` is required to be injective on the half-open
   period `[0, 2π)`.  This expresses the source's single traversal of the
   oriented intersection while retaining the closed endpoint equation, and
   excludes multiply-traversed parametrizations whose periods are multiplied.

## Encoding note

A one-form on the coordinate domain is represented by its three coefficient
functions, and its line integral is the integral of evaluation on the curve's
velocity.  `C₂` is retained through its two defining equations and its stated
counterclockwise orientation; injectivity on the half-open period records that
the geometric component is traversed exactly once.
-/

def apm_t00a05_U := {p : ℝ × ℝ × ℝ // p.1 ≠ 0 ∨ p.2.1 ≠ 0}

noncomputable def apm_t00a05_omega (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2),
    -p.1 / (p.1 ^ 2 + p.2.1 ^ 2), Real.cos p.2.2)

noncomputable def apm_t00a05_dOmega (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (deriv (fun x => (apm_t00a05_omega (x, p.2.1, p.2.2)).2.1) p.1 -
      deriv (fun y => (apm_t00a05_omega (p.1, y, p.2.2)).1) p.2.1,
   deriv (fun x => (apm_t00a05_omega (x, p.2.1, p.2.2)).2.2) p.1 -
      deriv (fun z => (apm_t00a05_omega (p.1, p.2.1, z)).1) p.2.2,
   deriv (fun y => (apm_t00a05_omega (p.1, y, p.2.2)).2.2) p.2.1 -
      deriv (fun z => (apm_t00a05_omega (p.1, p.2.1, z)).2.1) p.2.2)

noncomputable def apm_t00a05_lineIntegral
    (γ : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in Set.Icc a b,
    let v := apm_t00a05_omega (γ t)
    v.1 * deriv (fun s => (γ s).1) t +
      v.2.1 * deriv (fun s => (γ s).2.1) t +
      v.2.2 * deriv (fun s => (γ s).2.2) t

noncomputable def apm_t00a05_C1 (t : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos t, Real.sin t, 0)

def apm_t00a05_IsC2 (γ : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = γ (2 * Real.pi) ∧
  Set.InjOn γ (Set.Ico (0 : ℝ) (2 * Real.pi)) ∧
  (∀ t, 0 ≤ t → t ≤ 2 * Real.pi →
    2 * (γ t).1 ^ 2 + (γ t).2.1 ^ 2 + (γ t).2.2 ^ 2 = 10 ∧
    (γ t).2.2 = Real.exp ((γ t).2.1 - (γ t).1)) ∧
  0 < ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
    (γ t).1 * deriv (fun s => (γ s).2.1) t -
      (γ t).2.1 * deriv (fun s => (γ s).1) t

lemma apm_t00a05_dOmega_eq_zero (p : apm_t00a05_U) :
    apm_t00a05_dOmega p.1 = 0 := by
  rcases p with ⟨⟨x, y, z⟩, hxy⟩
  have hden : x ^ 2 + y ^ 2 ≠ 0 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx]
    · nlinarith [sq_pos_of_ne_zero hy]
  ext <;>
    simp only [apm_t00a05_dOmega, apm_t00a05_omega, Prod.fst,
      Prod.snd, deriv_const, sub_zero]
  · have hxden : HasDerivAt (fun u : ℝ ↦ u ^ 2 + y ^ 2) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1 <;> simp [id] <;> ring
    have hyden : HasDerivAt (fun v : ℝ ↦ x ^ 2 + v ^ 2) (2 * y) y := by
      convert (hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2) using 1 <;>
        simp [id] <;> ring
    have hxnum : HasDerivAt (fun u : ℝ ↦ -u) (-1) x := by
      simpa using (hasDerivAt_id x).neg
    have hynum : HasDerivAt (fun v : ℝ ↦ v) 1 y := hasDerivAt_id y
    have hxquot := hxnum.div hxden hden
    have hyquot := hynum.div hyden hden
    have hxder := hxquot.deriv
    have hyder := hyquot.deriv
    simp only [Pi.div_apply] at hxder hyder
    change deriv ((fun u : ℝ ↦ -u) / (fun u ↦ u ^ 2 + y ^ 2)) x -
      deriv ((fun v : ℝ ↦ v) / (fun v ↦ x ^ 2 + v ^ 2)) y = 0
    rw [hxder, hyder]
    field_simp
    ring
  · simp
  · simp

lemma apm_t00a05_lineIntegral_C1 :
    apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) =
      -2 * Real.pi := by
  unfold apm_t00a05_lineIntegral
  calc
    _ = ∫ _t in Set.Icc (0 : ℝ) (2 * Real.pi), (-1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [apm_t00a05_C1, apm_t00a05_omega, Prod.fst, Prod.snd]
      rw [Real.hasDerivAt_cos t |>.deriv, Real.hasDerivAt_sin t |>.deriv]
      rw [Real.cos_sq_add_sin_sq]
      simp
      nlinarith [Real.sin_sq_add_cos_sq t]
    _ = -2 * Real.pi := by
      rw [setIntegral_const]
      simp [Real.volume_Icc, Real.pi_pos.le]

theorem apm_t00a05 :
    (∀ p : apm_t00a05_U, apm_t00a05_dOmega p.1 = 0) ∧
    apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) = -2 * Real.pi ∧
    (∀ γ, apm_t00a05_IsC2 γ →
      apm_t00a05_lineIntegral γ 0 (2 * Real.pi) = -2 * Real.pi) := by
  refine ⟨apm_t00a05_dOmega_eq_zero, apm_t00a05_lineIntegral_C1, ?_⟩
  /-
  This pass closes the exterior-derivative computation and the complete `C1`
  period calculation.  The remaining assertion is genuinely global: an
  injective, positively oriented parametrization of the specified connected
  component must have winding number one around the deleted axis, after which
  the exact angular-form integral is `-2π`; the `cos z dz` term is exact.
  Mathlib exposes no theorem connecting these raw coordinate `deriv` integrals
  and the frozen implicit-surface/simple-loop predicate to winding number or a
  change-of-variables formula.
  -/
  intro γ hγ
  sorry
