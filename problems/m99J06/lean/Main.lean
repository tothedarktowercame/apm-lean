import Mathlib

/-!
# APM m99J06: Galerkin approximation in `H¹₀(0,1)`

## Statement repairs

The former model stored weak derivatives as literal functions even though its
inner product observed them only almost everywhere, making the hypothesized
structure inconsistent. Weak derivatives are now elements of Mathlib's `L²`
space, which quotients functions by almost-everywhere equality. Thus changing a
derivative on a singleton no longer creates a distinct representative.

Part (d) says that `uₙ` itself converges weakly, but the suggested boundedness
argument guarantees only a weakly convergent subsequence. We state that precise
conclusion, as does the supplied solution. Uniqueness can subsequently
upgrade it to convergence of the full sequence, but that is not needed for
part (e).

## Encoding questions

None. `H¹₀(0,1)` is represented by absolutely continuous functions with an
`L²` weak derivative and zero endpoint trace. The derivative is an `L²`
equivalence class, so all identities have the correct almost-everywhere
semantics.
-/

open Filter MeasureTheory Set

noncomputable section

abbrev apm_m99J06_intervalMeasure : Measure ℝ :=
  volume.restrict (Icc 0 1)

abbrev apm_m99J06_L2 :=
  Lp ℝ 2 apm_m99J06_intervalMeasure

def apm_m99J06_isH01Pair (u : ℝ → ℝ) (du : apm_m99J06_L2) : Prop :=
  AbsolutelyContinuousOnInterval u 0 1 ∧
  MemLp u 2 apm_m99J06_intervalMeasure ∧
  (∃ duRep : ℝ → ℝ,
    ∃ hdu : MemLp duRep 2 apm_m99J06_intervalMeasure,
      hdu.toLp duRep = du ∧
      ∀ᵐ x ∂apm_m99J06_intervalMeasure, HasDerivAt u (duRep x) x) ∧
  u 0 = 0 ∧ u 1 = 0

structure apm_m99J06_H01Model (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  val : H → ℝ → ℝ
  weakDeriv : H → apm_m99J06_L2
  represents : ∀ u : H, apm_m99J06_isH01Pair (val u) (weakDeriv u)
  realizes : ∀ (u : ℝ → ℝ) (du : apm_m99J06_L2),
    apm_m99J06_isH01Pair u du →
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
  ∃ du ddu : ℝ → ℝ,
    ∃ hdu : MemLp du 2 apm_m99J06_intervalMeasure,
    ∃ hddu : MemLp ddu 2 apm_m99J06_intervalMeasure,
      hdu.toLp du = M.weakDeriv u ∧
      AbsolutelyContinuousOnInterval du 0 1 ∧
      (∀ᵐ x ∂apm_m99J06_intervalMeasure, HasDerivAt du (ddu x) x) ∧
      (∀ᵐ x ∂apm_m99J06_intervalMeasure, M.val u x - ddu x = f x)

def apm_m99J06_galerkinEquation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (V : Submodule ℝ H) (u : V) : Prop :=
  ∀ v : V, inner ℝ (u : H) (v : H) =
    ∫ x in Icc (0 : ℝ) 1, f x * M.val (v : H) x

theorem apm_m99j06
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 apm_m99J06_intervalMeasure) :
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
          (∀ n, ‖(uSeq n : H)‖ ≤ (eLpNorm f 2 apm_m99J06_intervalMeasure).toReal) ∧
          ∃ k : ℕ → ℕ, StrictMono k ∧
            ∃ u : H,
              Tendsto (fun j ↦ toWeakSpace ℝ H (uSeq (k j) : H)) atTop
                (nhds (toWeakSpace ℝ H u)) ∧
              apm_m99J06_weakSolution M f u) := by
  sorry
