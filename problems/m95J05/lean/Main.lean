import Mathlib

/-!
# APM m95J05: A first-order fundamental solution

## Statement repairs

None.

## Encoding questions

None. The general definition uses Mathlib's genuine space of distributions.
For `d/dt + λ`, the distributional equation is stated in its exact weak form
against test functions, and the inhomogeneous solution is the actual causal
convolution integral.  The main theorem asserts that the displayed kernel
satisfies that weak equation; it does not restate the definition of
`apm_m95J05_isFundamentalSolution` as an equivalence.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions

noncomputable section

def apm_m95J05_realDomain : Opens ℝ := ⊤

def apm_m95J05_isFundamentalSolution
    (A : 𝓓'(apm_m95J05_realDomain, ℝ) → 𝓓'(apm_m95J05_realDomain, ℝ))
    (dirac T : 𝓓'(apm_m95J05_realDomain, ℝ)) : Prop :=
  A T = dirac

def apm_m95J05_isTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ

def apm_m95J05_fundamental (lam t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-lam * t) else 0

/-- A locally integrable kernel is a fundamental solution of `d/dt + λ` when
its distributional pairing with the formal adjoint sends every test function
to evaluation at zero. -/
def apm_m95J05_isFundamentalKernel (lam : ℝ) (E : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, apm_m95J05_isTestFunction ψ →
    (∫ t, E t * (-deriv ψ t + lam * ψ t)) = ψ 0

def apm_m95J05_solution (lam : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Iic t, Real.exp (-lam * (t - s)) * φ s

/-- The causal exponential kernel satisfies the weak fundamental-solution
identity. -/
lemma apm_m95J05_fundamental_isFundamentalKernel (lam : ℝ) :
    apm_m95J05_isFundamentalKernel lam (apm_m95J05_fundamental lam) := by
  intro ψ hψ
  let g : ℝ → ℝ := fun t ↦ Real.exp (-lam * t) * ψ t
  have hg : ContDiff ℝ 1 g := by
    dsimp [g]
    apply ContDiff.mul
    · fun_prop
    · exact hψ.1.of_le (by simp)
  have hgcompact : HasCompactSupport g := hψ.2.mul_left
  have hderiv (t : ℝ) : deriv g t =
      Real.exp (-lam * t) * (deriv ψ t - lam * ψ t) := by
    have hψd := hψ.1.differentiable (by simp) t
    have he : HasDerivAt (fun s : ℝ ↦ Real.exp (-lam * s))
        (-lam * Real.exp (-lam * t)) t := by
      convert Real.hasDerivAt_exp (-lam * t) |>.comp t
        ((hasDerivAt_const t (-lam)).mul (hasDerivAt_id t)) using 1 <;> ring
    have hp := he.mul hψd.hasDerivAt
    change deriv ((fun s : ℝ ↦ Real.exp (-lam * s)) * ψ) t = _
    rw [hp.deriv]
    ring
  have hint := hgcompact.integral_Ioi_deriv_eq hg 0
  rw [show (∫ t, apm_m95J05_fundamental lam t *
      (-deriv ψ t + lam * ψ t)) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
        (-deriv ψ t + lam * ψ t) by
      rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards [] with t
      simp [apm_m95J05_fundamental, Set.indicator, mem_Ici]
    ]
  calc
    _ = ∫ t in Ioi (0 : ℝ), -deriv g t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hderiv]
      ring
    _ = -(∫ t in Ioi (0 : ℝ), deriv g t) := by
      simpa only [Pi.neg_apply] using
        (integral_neg (μ := volume.restrict (Ioi (0 : ℝ))) (fun t ↦ deriv g t))
    _ = ψ 0 := by rw [hint]; simp [g]

theorem apm_m95j05 :
    (∀ lam : ℝ,
      apm_m95J05_isFundamentalKernel lam (apm_m95J05_fundamental lam)) ∧
    (∀ (lam : ℝ) (φ : ℝ → ℝ),
      apm_m95J05_isTestFunction φ →
        ContDiff ℝ ⊤ (apm_m95J05_solution lam φ) ∧
        ∀ t : ℝ,
          deriv (apm_m95J05_solution lam φ) t +
            lam * apm_m95J05_solution lam φ t = φ t) := by
  constructor
  · exact apm_m95J05_fundamental_isFundamentalKernel
  · /-
    PARTIAL boundary (closer hop 1).  The fundamental-kernel clause is closed
    by `apm_m95J05_fundamental_isFundamentalKernel`.  For a test function `ψ`,
    the product `g(t) = exp (-λt) ψ(t)` is `C¹` and compactly supported;
    `HasCompactSupport.integral_Ioi_deriv_eq` evaluates its derivative on the
    positive half-line, while `integral_Ici_eq_integral_Ioi` removes the
    measure-zero endpoint.  The derivative identity then exactly matches the
    formal adjoint integrand.

    The remaining inhomogeneous clause requires proving `C∞` regularity of
    `t ↦ ∫_{(-∞,t]} exp (-λ(t-s)) φ(s) ds` and its pointwise ODE.  Searches of
    `LEMMA-INDEX.md`, all closed artifacts, `ConstructionTargets/`, Mathlib's
    improper-integral FTC, parameter-dependent interval-integral, convolution,
    and compact-support APIs found no packaged smoothness theorem for this
    moving half-line integral.  A local completion can extract a finite lower
    support bound for `φ`, rewrite the improper integral as an ordinary
    interval integral, prove the first derivative using the interval FTC, and
    bootstrap all higher derivatives from the ODE.  That support-bound and
    smoothness assembly remains open.
    -/
    sorry
