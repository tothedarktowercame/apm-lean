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

lemma apm_m99J06_galerkin_energy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (f : ℝ → ℝ)
    (V : Submodule ℝ H) (u : V)
    (hu : apm_m99J06_galerkinEquation M f V u) :
    ‖(u : H)‖ ^ 2 = ∫ x in Icc (0 : ℝ) 1, f x * M.val (u : H) x := by
  simpa [real_inner_self_eq_norm_sq] using hu u

/-- Coercivity of the ambient inner product gives uniqueness of every
Galerkin solution, independently of finite dimensionality. -/
lemma apm_m99J06_galerkin_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (f : ℝ → ℝ)
    (V : Submodule ℝ H) (u v : V)
    (hu : apm_m99J06_galerkinEquation M f V u)
    (hv : apm_m99J06_galerkinEquation M f V v) : u = v := by
  have hinner : inner ℝ ((u - v : V) : H) ((u - v : V) : H) = 0 := by
    have heq := (hu (u - v)).trans (hv (u - v)).symm
    rw [Submodule.coe_sub, inner_sub_left]
    exact sub_eq_zero.mpr heq
  have hnorm : ‖((u - v : V) : H)‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hinner
  have hzero : ((u - v : V) : H) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  apply Subtype.ext
  exact sub_eq_zero.mp hzero

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
  Boundary (closer hop 1): uniqueness of the weak solution, the Galerkin
  energy identity, and now uniqueness of every Galerkin solution
  (`apm_m99J06_galerkin_unique`) are proved above. The latter closes the
  coercivity half of finite-dimensional solvability by testing the difference
  of two solutions against itself.

  Completing the frozen theorem still requires (1) a
  Sobolev integration-by-parts/regularity theorem for the custom
  `AbsolutelyContinuousOnInterval` plus a.e. `HasDerivAt` representation,
  (2) construction of a genuinely linear Galerkin functional from the
  representative-level `M.val`, followed by finite-dimensional Riesz
  representation (Mathlib has `LinearMap.surjective_of_injective`, but the
  linear map must first be constructed),
  and (3) weak sequential compactness of a bounded Hilbert-space sequence
  followed by passage to the limit on a dense increasing union. I searched
  `integral_mul_le_Lp_mul_Lq_of_nonneg`, finite-dimensional duality,
  `FiniteDimensional.surjective_of_injective`, `toWeakSpace`, and
  `isCompact_closure_of_isBounded`. The last compactness theorem is not by
  itself sequential compactness without an additional metrizability bridge.
  `ConstructionTargets.LusinN` supplies interval absolute-continuity
  identities, but not the Sobolev regularity theorem required here.
  -/
  sorry
