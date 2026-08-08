import Mathlib

/-!
# APM m02A06

## Statement repairs

The source claims uniqueness for every `ε > 0`, but the contraction argument only
gives uniqueness in a bounded ball when `ε` is sufficiently small.  This is
load-bearing: already for `f = 0`, the first integral of the ODE rules out a
decaying solution with `u(0) = 1` when `ε > 3/2`.  The statement below makes
the contraction regime and its uniqueness ball explicit, using a supplied
uniform bound `C` for `f`.

## Encoding notes

The solution is a genuine twice continuously differentiable function on the
closed half-line, and `u(∞) = 0` is encoded as convergence along `atTop`.
-/

open Filter Set
open scoped ContDiff Topology

def apm_m02a06_IsSolution (ε : ℝ) (f u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Ici 0) ∧
  (∀ x ∈ Ioi (0 : ℝ), -deriv (deriv u) x + u x - ε * (u x) ^ 2 = f x) ∧
  u 0 = 1 ∧ Tendsto u atTop (nhds 0)

lemma apm_m02a06_radius_pos (C : ℝ) (hC : 0 ≤ C) :
    0 < 2 * (1 + C) := by positivity

lemma apm_m02a06_contraction_constant_lt_one
    (C ε : ℝ) (hC : 0 ≤ C) (hε_small : ε < 1 / (4 * (1 + C))) :
    4 * ε * (1 + C) < 1 := by
  have hpos : 0 < 1 + C := by positivity
  calc
    4 * ε * (1 + C) < 4 * (1 / (4 * (1 + C))) * (1 + C) := by
      gcongr
    _ = 1 := by field_simp

lemma apm_m02a06_quadratic_lipschitz
    (C ε u v : ℝ) (hε : 0 ≤ ε)
    (hu : |u| ≤ 2 * (1 + C)) (hv : |v| ≤ 2 * (1 + C)) :
    |ε * u ^ 2 - ε * v ^ 2| ≤
      (4 * ε * (1 + C)) * |u - v| := by
  rw [← mul_sub, sq_sub_sq, abs_mul, abs_mul, abs_of_nonneg hε]
  have hadd : |u + v| ≤ 4 * (1 + C) := by
    calc
      |u + v| ≤ |u| + |v| := abs_add_le u v
      _ ≤ 4 * (1 + C) := by linarith
  calc
    ε * (|u + v| * |u - v|) = (ε * |u + v|) * |u - v| := by ring
    _ ≤ (ε * (4 * (1 + C))) * |u - v| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hadd hε) (abs_nonneg _)
    _ = 4 * ε * (1 + C) * |u - v| := by ring

/-- The Dirichlet Green kernel for `-u'' + u` on the nonnegative half-line. -/
noncomputable def apm_m02a06_greenKernel (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.exp (-|x - y|) - Real.exp (-(x + y)))

lemma apm_m02a06_greenKernel_comm (x y : ℝ) :
    apm_m02a06_greenKernel x y = apm_m02a06_greenKernel y x := by
  simp only [apm_m02a06_greenKernel, add_comm]
  rw [abs_sub_comm]

lemma apm_m02a06_greenKernel_zero_left {y : ℝ} (hy : 0 ≤ y) :
    apm_m02a06_greenKernel 0 y = 0 := by
  simp [apm_m02a06_greenKernel, abs_of_nonneg hy]

lemma apm_m02a06_greenKernel_zero_right {x : ℝ} (hx : 0 ≤ x) :
    apm_m02a06_greenKernel x 0 = 0 := by
  simp [apm_m02a06_greenKernel, abs_of_nonneg hx]

lemma apm_m02a06_greenKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ apm_m02a06_greenKernel x y := by
  have habs : |x - y| ≤ x + y := by
    calc
      |x - y| ≤ |x| + |y| := abs_sub x y
      _ = x + y := by rw [abs_of_nonneg hx, abs_of_nonneg hy]
  have hexp : Real.exp (-(x + y)) ≤ Real.exp (-|x - y|) := by
    exact Real.exp_le_exp.mpr (neg_le_neg habs)
  unfold apm_m02a06_greenKernel
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr hexp)

lemma apm_m02a06_greenKernel_le_half {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    apm_m02a06_greenKernel x y ≤ 1 / 2 := by
  have hsum : 0 ≤ x + y := add_nonneg hx hy
  have hfirst : Real.exp (-|x - y|) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  have hsecond : 0 ≤ Real.exp (-(x + y)) := Real.exp_pos _ |>.le
  unfold apm_m02a06_greenKernel
  nlinarith

/-- On the lower triangle the absolute value in the Green kernel disappears. -/
lemma apm_m02a06_greenKernel_of_le {x y : ℝ} (hyx : y ≤ x) :
    apm_m02a06_greenKernel x y =
      (1 / 2 : ℝ) * (Real.exp (-(x - y)) - Real.exp (-(x + y))) := by
  simp [apm_m02a06_greenKernel, abs_of_nonneg (sub_nonneg.mpr hyx)]

/-- On the upper triangle the absolute value in the Green kernel disappears
with the opposite affine branch. -/
lemma apm_m02a06_greenKernel_of_ge {x y : ℝ} (hxy : x ≤ y) :
    apm_m02a06_greenKernel x y =
      (1 / 2 : ℝ) * (Real.exp (-(y - x)) - Real.exp (-(x + y))) := by
  rw [apm_m02a06_greenKernel_comm]
  simpa [add_comm] using apm_m02a06_greenKernel_of_le hxy

/-- The exponentially decaying part of the kernel is already a pointwise
majorant; this is the domination needed for the improper Green integral. -/
lemma apm_m02a06_greenKernel_le_exp {x y : ℝ} :
    apm_m02a06_greenKernel x y ≤ (1 / 2 : ℝ) * Real.exp (-|x - y|) := by
  have hnonneg : 0 ≤ Real.exp (-(x + y)) := (Real.exp_pos _).le
  unfold apm_m02a06_greenKernel
  nlinarith

/-- The concrete nonlinear half-line Green transform whose fixed point is the
desired solution.  Exposing it makes the remaining parameter-integral and
Banach-contraction bridge precise. -/
noncomputable def apm_m02a06_greenTransform
    (ε : ℝ) (f u : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-x) +
    ∫ y in Ici (0 : ℝ),
      apm_m02a06_greenKernel x y * (f y + ε * (u y) ^ 2)

theorem apm_m02a06
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hf_support : Function.support f ⊆ Ioi 0)
    (C : ℝ) (hC : 0 ≤ C) (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * (1 + C))) :
    ∃! u : ℝ → ℝ,
      apm_m02a06_IsSolution ε f u ∧
      ∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C) := by
  /-
  Boundary (closer hop 1): the informal contraction argument requires
  constructing the Dirichlet Green operator for `-deriv (deriv ·) + id` on
  `Ici 0`, proving that it preserves decay at `atTop`, and establishing its
  sup-norm maximum-principle estimate. Repository searches found only the
  abstract fixed-point layer (`ContractingWith.fixedPoint` and
  `ContractingWith.fixedPoint_unique`, used by `m01J05` and `t91A04`), not a
  compiled half-line Green operator or the required maximum-principle bound.

  This hop compiles the nonlinear and numerical layers independently.
  `apm_m02a06_radius_pos` proves positivity of the frozen ball radius,
  `apm_m02a06_contraction_constant_lt_one` derives the exact strict constant
  `4 * ε * (1 + C) < 1`, and `apm_m02a06_quadratic_lipschitz` proves the
  pointwise quadratic difference estimate on that ball.

  The abstract `ContractingWith` API therefore remains blocked only before
  these estimates: the missing work is the concrete inverse of
  `-deriv (deriv ·) + id` on the half-line, with regularity, boundary value,
  decay, and operator sup-norm bound. Searches of `LEMMA-INDEX.md`, all solved
  artifacts, `ConstructionTargets/`, Mathlib's ODE/integration/maximum-principle
  sources, and git history found no such Green operator. Siblings `m94A05`,
  `m94J05`, and `m96A02` record the same concrete-operator boundary, while
  `t91A04` only supplies the already-known abstract fixed-point wrapper.

  Closer hop 2 begins the missing concrete operator rather than repeating the
  API search. `apm_m02a06_greenKernel` defines the half-line Dirichlet kernel
  `G(x,y) = (exp(-|x-y|) - exp(-(x+y)))/2`.
  `apm_m02a06_greenKernel_comm`, the two boundary lemmas, and the pointwise
  bounds prove that it is symmetric, vanishes when either nonnegative
  argument is zero, and satisfies `0 ≤ G(x,y) ≤ 1/2` on the half-line. The
  remaining bridge is to define the improper integral operator, split at
  `y=x` to differentiate twice, prove decay and the full kernel-mass/sup-norm
  estimate, and then apply the compiled contraction layer. Searches of the
  exponential integral and parameter-integral APIs found primitives for these
  steps but no packaged half-line Green-operator theorem.

  Closer hop 3 carries out the exact algebraic preparation for that split.
  `apm_m02a06_greenKernel_of_le` and `apm_m02a06_greenKernel_of_ge` give the
  two smooth exponential formulas on `y ≤ x` and `x ≤ y`, respectively,
  and `apm_m02a06_greenKernel_le_exp` gives the integrable exponential
  majorant needed for dominated improper integration. Inspection of
  `ImproperIntegrals.lean` found `integrableOn_exp_neg_Ioi` and
  `integral_exp_neg_Ioi`, so the scalar tails are available. What remains is
  still the substantial parameter-integral assembly: combine the two moving
  domains, differentiate both pieces twice including their boundary terms,
  prove the resulting function tends to zero, then bundle a complete
  sup-norm function space and apply Banach contraction. No packaged theorem
  performs that assembly, and it was not completed in this final hop.

  HOP 4 GAP AUDIT (outcomes A and B both failed). The nonlinear operator is
  now explicit as `apm_m02a06_greenTransform`. Searches of the complete
  bounded-continuous-function spaces, improper parameter integrals, moving-
  endpoint differentiation, and fixed-point APIs found the ingredients but no
  theorem establishing the required combined regularity and contraction.

  The precise missing lemma is:

      theorem apm_m02a06_greenTransform_fixedPoint
          (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
          (hf_compact : HasCompactSupport f)
          (hf_support : Function.support f ⊆ Ioi 0)
          (C : ℝ) (hC : 0 ≤ C)
          (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
          (ε : ℝ) (hε : 0 < ε)
          (hε_small : ε < 1 / (4 * (1 + C))) :
          ∃! u : ℝ → ℝ,
            (∀ x ∈ Ici (0 : ℝ),
              u x = apm_m02a06_greenTransform ε f u x) ∧
            apm_m02a06_IsSolution ε f u ∧
            ∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C)

  This is stronger than the frozen conclusion only by recording the defining
  fixed-point identity, and is the exact theorem delivered by the intended
  Green-operator contraction proof. Its proof must establish the moving-
  domain twice-differentiation, boundary value, decay, kernel-mass bound,
  completeness of the chosen sup-norm space, and contraction. The statement
  is unchanged and the existing sorry is retained honestly.
  -/
  sorry
