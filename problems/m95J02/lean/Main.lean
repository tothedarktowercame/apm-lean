import Mathlib

/-!
# APM m95J02: The fundamental solution of the Laplacian

## Statement repairs

The typographical words "fund" and "Explan" are read as "find" and
"Explain". No mathematical repair is made. We state the result for `n ≥ 2`,
the range in which the source's logarithmic/power-law alternatives apply.

## Encoding questions

None. `EuclideanSpace ℝ (Fin n)` represents `ℝⁿ`. The delta equation is stated
in its exact weak form against smooth compactly supported test functions, and
the Poisson solution is the actual Euclidean convolution with the fundamental
solution.
-/

open MeasureTheory

noncomputable section

def apm_m95J02_sphereArea (n : ℕ) : ℝ :=
  2 * Real.rpow Real.pi ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

lemma apm_m95J02_sphereArea_two : apm_m95J02_sphereArea 2 = 2 * Real.pi := by
  simp [apm_m95J02_sphereArea, Real.Gamma_one, Real.rpow_one]

/-- The Gamma-function normalization really is a positive surface-area
constant in every positive dimension. -/
lemma apm_m95J02_sphereArea_pos {n : ℕ} (hn : 0 < n) :
    0 < apm_m95J02_sphereArea n := by
  unfold apm_m95J02_sphereArea
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))
    (Real.Gamma_pos_of_pos (div_pos hnR (by norm_num)))

def apm_m95J02_fundamental (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if n = 2 then Real.log ‖x‖ / (2 * Real.pi)
  else -Real.rpow ‖x‖ (2 - (n : ℝ)) /
    (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

lemma apm_m95J02_fundamental_two (x : EuclideanSpace ℝ (Fin 2)) :
    apm_m95J02_fundamental 2 x = Real.log ‖x‖ / (2 * Real.pi) := by
  simp [apm_m95J02_fundamental]

/-- In dimensions above two the denominator of the power-law branch is
strictly positive, fixing its normalization and sign before the distributional
calculation. -/
lemma apm_m95J02_power_denominator_pos {n : ℕ} (hn : 2 < n) :
    0 < ((n : ℝ) - 2) * apm_m95J02_sphereArea n := by
  have hnR : (2 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (sub_pos.mpr hnR) (apm_m95J02_sphereArea_pos (by omega))

/-- Away from its pole, the higher-dimensional fundamental solution has the
expected negative sign for the convention `ΔΦ = δ`. -/
lemma apm_m95J02_fundamental_neg {n : ℕ} (hn : 2 < n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    apm_m95J02_fundamental n x < 0 := by
  rw [apm_m95J02_fundamental, if_neg (by omega)]
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _))
    (apm_m95J02_power_denominator_pos hn)

def apm_m95J02_poissonSolution (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y, apm_m95J02_fundamental n (x - y) * f y

theorem apm_m95j02
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ (v : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ 2 v → x ≠ 0 →
        Laplacian.laplacian (fun z : EuclideanSpace ℝ (Fin n) ↦ v ‖z‖) x =
          iteratedDeriv 2 v ‖x‖ +
            ((n : ℝ) - 1) / ‖x‖ * deriv v ‖x‖) ∧
    (∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ⊤ φ → HasCompactSupport φ →
        (∫ x, apm_m95J02_fundamental n x * Laplacian.laplacian φ x) = φ 0) ∧
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ⊤ f → HasCompactSupport f →
        ∀ x : EuclideanSpace ℝ (Fin n),
          Laplacian.laplacian (apm_m95J02_poissonSolution n f) x = f x) := by
  /-
  Boundary (closer hop 1): the dimensional normalization is now compiled.
  `apm_m95J02_sphereArea_two` proves that the Gamma-function definition gives
  `ω₂ = 2π`, and `apm_m95J02_fundamental_two` exposes the exact logarithmic
  branch used in the weak identity.  This also sanity-checks the sign: the
  file uses `+ log ‖x‖ / (2π)` in dimension two and
  `-‖x‖^(2-n) / ((n-2)ωₙ)` otherwise, both corresponding to `ΔΦ = δ`.

  Closer hop 2 extends that normalization beyond the special dimension.
  `apm_m95J02_sphereArea_pos` proves positivity of the Gamma-defined sphere
  area in every positive dimension. `apm_m95J02_power_denominator_pos` proves
  the complete power-branch denominator positive for `n > 2`, and
  `apm_m95J02_fundamental_neg` uses it to certify the expected strict negative
  sign of the kernel away from its pole. Thus all dimension-dependent sign and
  denominator obligations are now compiled.

  Searches across both hops of `LEMMA-INDEX.md`, `ConstructionTargets`, Mathlib's new
  `Analysis.InnerProductSpace.Laplacian`, Schwartz-space integration by parts,
  prior radial-integration artifacts (`a95A03`, `m94A03`, and `m96J03`), and
  git history found no radial-composition Laplacian formula or singular-kernel
  convolution theorem.  Mathlib exposes the Laplacian through second Fréchet
  derivatives and orthonormal bases, but the chain rule for `z ↦ v ‖z‖`, the
  punctured-ball boundary limit, and differentiation of the singular
  convolution remain to be developed locally.

  Original boundary:
  SKIPPED: fundamental solution of Laplacian (three-part PDE problem).
  -- (a) Laplacian of radial function: Δv(|x|) = v''(r) + (n-1)/r · v'(r).
  -- (b) ΔΦ = δ in distributions: ∫ Φ·Δφ = φ(0) for test functions φ.
  -- (c) Poisson solution: Δ(Φ*f) = f for compactly supported smooth f.
  -- Blocker: requires Laplacian on Euclidean space, distributional PDE theory,
  -- Green's function computation, convolution with singular kernels — none of
  -- which have ready-to-use Mathlib infrastructure.
  APIs: `Laplacian.laplacian`, `ContDiff`, `HasCompactSupport`, `EuclideanSpace`.
  -/
  sorry
