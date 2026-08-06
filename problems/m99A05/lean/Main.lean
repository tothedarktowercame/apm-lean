import Mathlib

/-! # APM m99A05: weak and strong convergence in normed spaces

## Statement repairs

None.
-/

open Filter

noncomputable section

def M99A05WeaklyConverges {𝕜 X : Type*}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (u : ℕ → X) (x : X) : Prop :=
  ∀ ℓ : X →L[𝕜] 𝕜, Tendsto (fun n => ℓ (u n)) atTop (nhds (ℓ x))

abbrev m99A05L2 := lp (fun _ : ℕ => ℂ) 2

def m99A05BasisSequence (n : ℕ) : m99A05L2 := lp.single 2 n 1

theorem apm_m99a05
    (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    (M99A05WeaklyConverges (𝕜 := ℂ) m99A05BasisSequence 0 ∧
      ¬Tendsto m99A05BasisSequence atTop (nhds 0)) ∧
    (∀ (u : ℕ → X) (x : X),
      Tendsto u atTop (nhds x) → M99A05WeaklyConverges (𝕜 := 𝕜) u x) ∧
    (∀ (Y : Type*) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [FiniteDimensional 𝕜 Y] (u : ℕ → Y) (x : Y),
      Tendsto u atTop (nhds x) ↔ M99A05WeaklyConverges (𝕜 := 𝕜) u x) ∧
    (∀ (u : ℕ → X) (x : X), M99A05WeaklyConverges (𝕜 := 𝕜) u x →
      ∃ C : ℝ, ∀ n : ℕ, ‖u n‖ ≤ C) ∧
    (∀ (u : ℕ → X) (x y : X),
      M99A05WeaklyConverges (𝕜 := 𝕜) u x →
      M99A05WeaklyConverges (𝕜 := 𝕜) u y → x = y) := by
  constructor
  · /-
    Boundary: the `lp.single` basis counterexample requires identifying every
    continuous functional on complex `ℓ²` with an inner-product vector (or an
    equivalent coordinate-decay theorem), then proving the basis norms remain
    one. I searched the `lp` Riesz-representation, `lp.single`, orthonormal
    basis, and weak-convergence APIs; I did not complete that bridge in this
    pass.
    -/
    sorry
  constructor
  · intro u x hu ℓ
    exact ℓ.continuous.continuousAt.tendsto.comp hu
  · /-
    Boundary: the remaining clauses require (i) finite-dimensional coordinate
    reconstruction from continuous dual coordinates, (ii) Banach--Steinhaus on
    the canonical embedding into the bidual to obtain norm boundedness, and
    (iii) Hahn--Banach separation for uniqueness. I searched
    `FiniteDimensional`, `UniformBoundedness`, `NormedSpace.inclusionInDoubleDual`,
    and geometric Hahn--Banach APIs. Their ingredients exist, but I did not
    complete the coercions and typeclass assembly for the statement's arbitrary
    `RCLike` scalar in this pass. The general strong-to-weak implication is
    proved above directly by continuity of each functional.
    -/
    sorry
