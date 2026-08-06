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

def apm_m95J02_fundamental (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if n = 2 then Real.log ‖x‖ / (2 * Real.pi)
  else -Real.rpow ‖x‖ (2 - (n : ℝ)) /
    (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

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
  -- SKIPPED: fundamental solution of Laplacian (three-part PDE problem).
  -- (a) Laplacian of radial function: Δv(|x|) = v''(r) + (n-1)/r · v'(r).
  -- (b) ΔΦ = δ in distributions: ∫ Φ·Δφ = φ(0) for test functions φ.
  -- (c) Poisson solution: Δ(Φ*f) = f for compactly supported smooth f.
  -- Blocker: requires Laplacian on Euclidean space, distributional PDE theory,
  -- Green's function computation, convolution with singular kernels — none of
  -- which have ready-to-use Mathlib infrastructure.
  -- APIs: `Laplacian.laplacian`, `ContDiff`, `HasCompactSupport`, `EuclideanSpace`
  sorry
