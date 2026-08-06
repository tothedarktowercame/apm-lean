import Mathlib

/-!
# APM m99J06: Galerkin approximation in `H¹₀(0,1)`

## Statement repairs

Part (d) says that `uₙ` itself converges weakly, but the suggested boundedness
argument guarantees only a weakly convergent subsequence. We state that precise
conclusion, as does the supplied solution. Uniqueness can subsequently upgrade
it to convergence of the full sequence, but that is not needed for part (e).

## Encoding questions

None. `H¹₀(0,1)` is represented by its exact one-dimensional realization:
absolutely continuous functions with `L²` weak derivative and zero endpoint
trace. An explicit Hilbert-space model retains genuine finite-dimensional
subspaces and Mathlib's genuine weak topology.
-/

open Filter MeasureTheory Set

noncomputable section

def apm_m99J06_isH01Pair (u du : ℝ → ℝ) : Prop :=
  AbsolutelyContinuousOnInterval u 0 1 ∧
  MemLp u 2 (volume.restrict (Icc 0 1)) ∧
  MemLp du 2 (volume.restrict (Icc 0 1)) ∧
  (∀ᵐ x ∂volume.restrict (Icc 0 1), HasDerivAt u (du x) x) ∧
  u 0 = 0 ∧ u 1 = 0

structure apm_m99J06_H01Model (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  val : H → ℝ → ℝ
  weakDeriv : H → ℝ → ℝ
  represents : ∀ u : H, apm_m99J06_isH01Pair (val u) (weakDeriv u)
  realizes : ∀ (u du : ℝ → ℝ), apm_m99J06_isH01Pair u du →
    ∃ w : H, val w = u ∧ weakDeriv w = du
  inner_eq : ∀ u v : H,
    inner ℝ u v = ∫ x in Icc (0 : ℝ) 1,
      val u x * val v x + weakDeriv u x * weakDeriv v x

def apm_m99J06_weakSolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (u : H) : Prop :=
  ∀ v : H, inner ℝ u v = ∫ x in Icc (0 : ℝ) 1, f x * M.val v x

def apm_m99J06_strongSolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (u : H) : Prop :=
  ∃ ddu : ℝ → ℝ,
    MemLp ddu 2 (volume.restrict (Icc 0 1)) ∧
    AbsolutelyContinuousOnInterval (M.weakDeriv u) 0 1 ∧
    (∀ᵐ x ∂volume.restrict (Icc 0 1),
      HasDerivAt (M.weakDeriv u) (ddu x) x) ∧
    (∀ᵐ x ∂volume.restrict (Icc 0 1), M.val u x - ddu x = f x)

def apm_m99J06_galerkinEquation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (V : Submodule ℝ H) (u : V) : Prop :=
  ∀ v : V, inner ℝ (u : H) (v : H) =
    ∫ x in Icc (0 : ℝ) 1, f x * M.val (v : H) x

theorem apm_m99j06
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Icc 0 1))) :
    (∀ u : H,
      apm_m99J06_weakSolution M f u ↔
        apm_m99J06_strongSolution M f u) ∧
    (∀ V : ℕ → Submodule ℝ H,
      (∀ n : ℕ, FiniteDimensional ℝ (V n)) →
      (∀ n : ℕ, V n ≤ V (n + 1)) →
      Dense (⋃ n : ℕ, (V n : Set H)) →
        (∀ n : ℕ, ∃! u : V n, apm_m99J06_galerkinEquation M f (V n) u) ∧
        ∀ uSeq : ∀ n : ℕ, V n,
          (∀ n, apm_m99J06_galerkinEquation M f (V n) (uSeq n)) →
          (∀ n, ‖(uSeq n : H)‖ ≤
            (eLpNorm f 2 (volume.restrict (Icc 0 1))).toReal) ∧
          ∃ k : ℕ → ℕ, StrictMono k ∧
            ∃ u : H,
              Tendsto (fun j ↦ toWeakSpace ℝ H (uSeq (k j) : H)) atTop
                (nhds (toWeakSpace ℝ H u)) ∧
              apm_m99J06_weakSolution M f u) := by
  have hweak_unique :
      ∀ u v : H,
        apm_m99J06_weakSolution M f u →
        apm_m99J06_weakSolution M f v → u = v := by
    intro u v hu hv
    apply ext_inner_right ℝ
    intro w
    rw [hu w, hv w]
  /-
  Boundary: uniqueness of the weak solution is proved above directly from
  the Hilbert inner product. Completing the frozen theorem requires (1) a
  Sobolev integration-by-parts/regularity theorem for the custom
  `AbsolutelyContinuousOnInterval` plus a.e. `HasDerivAt` representation,
  (2) finite-dimensional Riesz representation for the Galerkin functional,
  and (3) weak sequential compactness of a bounded Hilbert-space sequence
  followed by passage to the limit on a dense increasing union. I searched
  Mathlib's `MemLp`, interval absolute-continuity, Bochner integration,
  finite-dimensional duality, `toWeakSpace`, reflexivity, and weak compactness
  APIs, but did not find a route connecting all of them to this custom model
  within this pass.
  -/
  sorry
