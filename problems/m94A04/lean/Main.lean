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

noncomputable abbrev apm_m94a04_measure : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

local instance apm_m94a04_holder_884 : ENNReal.HolderTriple 8 8 4 := by
  rw [ENNReal.holderTriple_iff]
  apply (ENNReal.toReal_eq_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_inv]
  simp
  norm_num

/-- The first heterogeneous Hölder stage: squaring an `L⁸` class produces a
well-defined `L⁴` class. -/
noncomputable def apm_m94a04_square
    (f : Lp ℝ 8 apm_m94a04_measure) : Lp ℝ 4 apm_m94a04_measure :=
  f • f

/-- The quotient-level square has the expected representative almost
everywhere. -/
lemma apm_m94a04_square_coeFn
    (f : Lp ℝ 8 apm_m94a04_measure) :
    (apm_m94a04_square f : ℝ → ℝ) =ᵐ[apm_m94a04_measure]
      fun t ↦ (f t) ^ 2 := by
  filter_upwards [Lp.coeFn_lpSMul (r := 4) f f] with t ht
  simpa [apm_m94a04_square, pow_two] using ht

/-- Hölder gives the sharp quotient norm estimate for the square stage. -/
lemma apm_m94a04_norm_square_le
    (f : Lp ℝ 8 apm_m94a04_measure) :
    ‖apm_m94a04_square f‖ ≤ ‖f‖ ^ 2 := by
  simpa [apm_m94a04_square, pow_two] using
    (Lp.norm_smul_le (r := 4) f f)

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

  CLOSER HOP 2 (partial). The first heterogeneous quotient-level stage is now
  fully compiled. `apm_m94a04_holder_884` proves the concrete exponent
  relation `1/8 + 1/8 = 1/4`; `apm_m94a04_square` constructs the `L⁴` square
  of an `L⁸` class using Mathlib's heterogeneous scalar multiplication;
  `apm_m94a04_square_coeFn` proves its representative is a.e. `f²`; and
  `apm_m94a04_norm_square_le` proves the sharp estimate
  `‖f²‖₄ ≤ ‖f‖₈²` via `Lp.norm_smul_le`. This closes representative
  independence, target membership, and the norm estimate for the first link
  of the planned exponent chain.

  Further inspection of `MeasureTheory.Function.Holder`, the raw
  `LpSeminorm.CompareExp` API, and siblings `a96A03`, `m01J04`, `m03J05`, and
  `m98A03` found no packaged downgrade-plus-linear-map construction. The
  remaining bridge is the `L⁸·L⁴ → L^(8/3)` stage, finite-measure downgrade
  to `L²`, construction and boundedness of multiplication by `3f²`, and the
  ENNReal epsilon-delta remainder estimate. The frozen statement remains
  unchanged.
  -/
  sorry
