import Mathlib

/-!
# APM m95J04: A nonlinear two-point boundary value problem

## Statement repairs

None. The decimal `7.99` is encoded exactly as `799 / 100`.

## Encoding questions

None. A solution is twice continuously differentiable on the exact interval
`[0,1]`, satisfies the differential equation there using within-interval
derivatives, and uniqueness is equality on that interval.
-/

open Set

noncomputable section

def apm_m95J04_green (t s : ℝ) : ℝ :=
  if t ≤ s then t * (1 - s) else s * (1 - t)

lemma apm_m95J04_green_nonneg {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ apm_m95J04_green t s := by
  simp only [apm_m95J04_green]
  split_ifs
  · exact mul_nonneg ht.1 (sub_nonneg.mpr hs.2)
  · exact mul_nonneg hs.1 (sub_nonneg.mpr ht.2)

lemma apm_m95J04_green_le_quarter {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    apm_m95J04_green t s ≤ (1 / 4 : ℝ) := by
  simp only [apm_m95J04_green]
  split_ifs with hts
  · have hprod : t * (1 - s) ≤ s * (1 - s) :=
      mul_le_mul_of_nonneg_right hts (sub_nonneg.mpr hs.2)
    have hsq : 0 ≤ (s - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  · have hst : s ≤ t := le_of_not_ge hts
    have hprod : s * (1 - t) ≤ t * (1 - t) :=
      mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr ht.2)
    have hsq : 0 ≤ (t - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith

def apm_m95J04_isSolution (f : ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 x (Icc 0 1) ∧
  x 0 = 0 ∧ x 1 = 0 ∧
  ∀ t ∈ Icc (0 : ℝ) 1,
    iteratedDerivWithin 2 x (Icc 0 1) t = f t (x t)

def apm_m95J04_specific (t x : ℝ) : ℝ :=
  Real.sin (x - t) * Real.sin (x + t - 1)

lemma apm_m95J04_specific_reflection (t x : ℝ) :
    apm_m95J04_specific (1 - t) x = apm_m95J04_specific t x := by
  rw [apm_m95J04_specific, apm_m95J04_specific]
  have h₁ : x - (1 - t) = x + t - 1 := by ring
  have h₂ : x + (1 - t) - 1 = x - t := by ring
  rw [h₁, h₂, mul_comm]

lemma apm_m95J04_specific_continuous :
    Continuous fun p : ℝ × ℝ ↦ apm_m95J04_specific p.1 p.2 := by
  unfold apm_m95J04_specific
  fun_prop

theorem apm_m95j04 :
    (∀ f : ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ ↦ f p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
        |f t u - f t v| ≤ (799 / 100 : ℝ) * |u - v|) →
      ∃ x : ℝ → ℝ,
        apm_m95J04_isSolution f x ∧
        ∀ y : ℝ → ℝ,
          apm_m95J04_isSolution f y → EqOn x y (Icc 0 1)) ∧
    (∃ x : ℝ → ℝ,
      apm_m95J04_isSolution apm_m95J04_specific x ∧
      (∀ t ∈ Icc (0 : ℝ) 1, x t = x (1 - t)) ∧
      ∀ y : ℝ → ℝ,
        apm_m95J04_isSolution apm_m95J04_specific y →
          EqOn x y (Icc 0 1)) := by
  /-
  Boundary (closer hop 1): the elementary kernel and symmetry layer is now
  compiled.  `apm_m95J04_green_nonneg` and
  `apm_m95J04_green_le_quarter` prove `0 ≤ G(t,s) ≤ 1/4` on the unit square.
  `apm_m95J04_specific_reflection` proves the exact invariance under
  `t ↦ 1-t`, and `apm_m95J04_specific_continuous` supplies its global
  continuity.  These facts are the scalar inputs to the Green-operator
  contraction and the final symmetry-by-uniqueness argument.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets`, the partial
  Green developments `m94J05`, `m02A06`, and `m99J02`, Mathlib's
  `ContractingWith` and interval-integral APIs, and git history found no
  bundled inverse for the second derivative with Dirichlet boundary data.
  The remaining bridge is to package `g ↦ -∫ G(t,s)g(s) ds` as a continuous
  self-map of `C([0,1])`, prove the fixed-point/ODE equivalence using within
  derivatives at the endpoints, lift the kernel estimate to the sup norm,
  and apply contraction.  For the specific nonlinearity one must additionally
  compile its sharp Lipschitz-one estimate; the Green operator's norm is below
  one, so the strict `799/100` hypothesis of the first conjunct is not needed
  for that clause.

  Original boundary:
  SKIPPED: nonlinear BVP via Green's function + contraction mapping.
  -- (a) Existence & uniqueness for x''=f(t,x), x(0)=x(1)=0, Lipschitz < 1:
  --     Green's function converts to integral equation, contraction mapping gives unique solution.
  -- (b) Specific nonlinearity f=sin(x-t)sin(x+t-1): symmetry + existence.
  -- Blocker: requires Green's function integral equation formulation, contraction
  -- mapping theorem on C²[0,1], and specific ODE analysis — none available as
  -- ready-to-use Mathlib lemmas for this setting.
  APIs: `ContDiffOn`, `iteratedDerivWithin`, `ContinuousOn`, `Icc`.
  -/
  sorry
