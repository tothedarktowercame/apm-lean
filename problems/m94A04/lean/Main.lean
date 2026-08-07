import Mathlib

/-!
# APM m94A04

## Statement repairs

None.

## Encoding notes

Both domain and codomain are genuine quotient `Lp` spaces over `[0,1]`.
The Nemytskii operator and its derivative are characterized almost everywhere,
so their definitions do not depend on representatives of `Lp` classes.
-/

open MeasureTheory Set

/-- Exact pointwise remainder for the cubic Nemytskii map. -/
lemma apm_m94a04_cubic_remainder (a b : ℝ) :
    (a + b) ^ 3 - a ^ 3 - 3 * a ^ 2 * b = 3 * a * b ^ 2 + b ^ 3 := by
  ring

def apm_m94a04_IsOperator
    (T : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →
      Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) : Prop :=
  ∀ f : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      T f t = Real.sin t + (f t) ^ 3

def apm_m94a04_IsFrechetDerivative
    (T : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →
      Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (f : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)))
    (L : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ h : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
    eLpNorm (L h) 2 (volume.restrict (Icc (0 : ℝ) 1)) ≤
      ENNReal.ofReal C * eLpNorm h 8 (volume.restrict (Icc (0 : ℝ) 1))) ∧
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
    eLpNorm h 8 (volume.restrict (Icc (0 : ℝ) 1)) < ENNReal.ofReal δ →
    eLpNorm ((T (f + h) : ℝ → ℝ) - (T f : ℝ → ℝ) - (L h : ℝ → ℝ)) 2
        (volume.restrict (Icc (0 : ℝ) 1)) ≤
      ENNReal.ofReal ε * eLpNorm h 8 (volume.restrict (Icc (0 : ℝ) 1))

theorem apm_m94a04 :
    ∃ T : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →
        Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)),
      apm_m94a04_IsOperator T ∧
      ∀ f : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
        ∃ L : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)) →ₗ[ℝ]
            Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)),
          apm_m94a04_IsFrechetDerivative T f L ∧
          ∀ h : Lp ℝ 8 (volume.restrict (Icc (0 : ℝ) 1)),
            ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
              L h t = 3 * (f t) ^ 2 * h t := by
  /-
  Boundary: the proof must first lift the representative-level maps
  `f ↦ sin + f ^ 3` and `h ↦ 3 * f ^ 2 * h` through almost-everywhere
  equivalence, prove the resulting representatives belong to the target
  `Lp ℝ 2`, and package the latter map as a quotient-level `LinearMap`.

  I searched the `Lp` APIs in
  `Mathlib.MeasureTheory.Function.LpSpace.Basic`, including `MemLp` power
  lemmas, `MemLp.mono_exponent`, `MemLp.toLp`, and the norm comparison
  machinery. There is no direct quotient-level multiplication constructor
  matching the mixed exponents here. Completing the construction requires
  explicit generalized-Hölder estimates for `f ^ 2 * h`, `f * h ^ 2`, and
  `h ^ 3`, representative-independence proofs, and ENNReal arithmetic to turn
  the exact cubic remainder into the statement's epsilon-delta estimate.
  No compiled sibling supplied this mixed-exponent Nemytskii construction
  within this pass.

  Closer hop 1 proves the exact pointwise identity
  `apm_m94a04_cubic_remainder`, reducing the nonlinear remainder to
  `3 * f * h² + h³`. More importantly, a deeper Mathlib search finds the
  quotient-level constructor that the initial pass missed:
  `MeasureTheory.Function.Holder` installs heterogeneous scalar multiplication
  `Lp p × Lp q → Lp r` under `ENNReal.HolderTriple p q r`.
  `Lp.coeFn_lpSMul` supplies representative independence and
  `Lp.norm_smul_le` supplies Hölder's norm estimate; the raw counterparts are
  `MemLp.mul'` and `eLpNorm_smul_le_mul_eLpNorm`.

  Thus the live bridge is narrower: instantiate the exponent chain
  `L⁸·L⁸ → L⁴`, `L⁸·L⁴ → L^(8/3)`, downgrade to `L²` on the finite interval,
  package multiplication by `3f²` as a `LinearMap`, and turn the two remainder
  bounds into the frozen ENNReal epsilon-delta inequality. Searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling Nemytskii artifacts, and
  git history found no completed version of that chain. The statement remains
  unchanged.
  -/
  sorry
