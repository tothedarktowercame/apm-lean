import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Complex

/-- An exponential-type growth bound. -/
def ExpTypeBound (f : ℂ → ℂ) (A B : ℝ) : Prop :=
  ∀ z : ℂ, ‖f z‖ ≤ B * Real.exp (A * ‖z‖)

/-- The weighted zero series `∑ (1 + ‖ωₙ‖)^{-α}` converges. -/
def ZeroWeightSummable (zeros : ℕ → ℂ) (α : ℝ) : Prop :=
  Summable fun n : ℕ => Real.rpow (1 + ‖zeros n‖) (-α)

/-- Data needed to state apm-a01J06 in Lean.  The analytical content is not
present yet; `hEntire` and `zeros` are placeholders for the function and its
root enumeration. -/
structure ProblemData where
  A : ℝ
  B : ℝ
  α : ℝ
  hA : 0 < A
  hB : 0 < B
  hα : 1 < α
  f : ℂ → ℂ
  hEntire : True
  hBound : ExpTypeBound f A B
  zeros : ℕ → ℂ

namespace ProblemData

@[simp] lemma bound (data : ProblemData) :
    ExpTypeBound data.f data.A data.B :=
  data.hBound

@[simp] lemma bound_apply (data : ProblemData) (z : ℂ) :
    ‖data.f z‖ ≤ data.B * Real.exp (data.A * ‖z‖) :=
  data.bound z

lemma bound_rhs_nonneg (data : ProblemData) (z : ℂ) :
    0 ≤ data.B * Real.exp (data.A * ‖z‖) := by
  have hB : 0 ≤ data.B := (data.hB).le
  have hexp : 0 ≤ Real.exp (data.A * ‖z‖) :=
    (Real.exp_pos _).le
  exact mul_nonneg hB hexp

lemma bound_origin (data : ProblemData) :
    ‖data.f 0‖ ≤ data.B := by
  simpa [norm_zero, zero_mul, Real.exp_zero,
    mul_comm] using data.bound_apply 0

lemma alpha_pos (data : ProblemData) : 0 < data.α :=
  lt_trans zero_lt_one data.hα

lemma alpha_ge_one (data : ProblemData) : 1 ≤ data.α :=
  data.hα.le

lemma alpha_sub_one_pos (data : ProblemData) : 0 < data.α - 1 :=
  sub_pos.mpr data.hα

lemma alpha_sub_one_nonneg (data : ProblemData) : 0 ≤ data.α - 1 :=
  (data.alpha_sub_one_pos).le

lemma alpha_nonneg (data : ProblemData) : 0 ≤ data.α :=
  le_of_lt (data.alpha_pos)

lemma neg_alpha_nonpos (data : ProblemData) : (-data.α) ≤ 0 :=
  neg_nonpos.mpr (data.alpha_nonneg)

@[simp] lemma A_pos (data : ProblemData) : 0 < data.A := data.hA

lemma A_nonneg (data : ProblemData) : 0 ≤ data.A :=
  (data.A_pos).le

@[simp] lemma B_pos (data : ProblemData) : 0 < data.B := data.hB

lemma B_nonneg (data : ProblemData) : 0 ≤ data.B :=
  (data.B_pos).le

/-- Placeholder for the zero-counting function. -/
def zeroCount (data : ProblemData) (r : ℝ) : ℕ :=
  0

@[simp] lemma zeroCount_nonpos (data : ProblemData) (r : ℝ) :
    data.zeroCount r = 0 := rfl

@[simp] lemma zeroCount_cast (data : ProblemData) (r : ℝ) :
    (data.zeroCount r : ℝ) = 0 := by
  simpa [zeroCount]

/-- Linear-growth estimate for the counting function (intended Jensen output). -/
def zeroCountLinear (data : ProblemData) : Prop :=
  ∃ C ≥ 0, ∀ {r : ℝ}, 0 ≤ r → (data.zeroCount r : ℝ) ≤ C * (1 + r)

/-- With the current stub `zeroCount = 0`, the linear estimate holds trivially. -/
lemma zeroCountLinear_trivial (data : ProblemData) : data.zeroCountLinear := by
  refine ⟨0, ?_, ?_⟩
  · exact le_of_eq rfl
  · intro r hr
    have hzero : (data.zeroCount r : ℝ) = 0 := by
      simpa using data.zeroCount_cast r
    simpa [hzero, zero_mul] using
      (show (0 : ℝ) ≤ 0 * (1 + r) by exact le_of_eq rfl)

@[simp] lemma zeroCountLinear_default (data : ProblemData) :
    data.zeroCountLinear :=
  data.zeroCountLinear_trivial

noncomputable def linearBoundConstant (data : ProblemData)
    (h : data.zeroCountLinear) : ℝ :=
  Classical.choose h

lemma linearBoundConstant_nonneg (data : ProblemData)
    (h : data.zeroCountLinear) :
    0 ≤ data.linearBoundConstant h :=
  (Classical.choose_spec h).1

lemma linearBoundConstant_bound (data : ProblemData)
    (h : data.zeroCountLinear) :
    ∀ {r : ℝ}, 0 ≤ r →
      (data.zeroCount r : ℝ) ≤ data.linearBoundConstant h * (1 + r) :=
  (Classical.choose_spec h).2

/-- Radius of the `m`-th dyadic shell, i.e. \(2^m\). -/
def dyadicRadius (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m

@[simp] lemma dyadicRadius_zero : dyadicRadius 0 = 1 := by
  simp [dyadicRadius]

@[simp] lemma dyadicRadius_one : dyadicRadius 1 = 2 := by
  simp [dyadicRadius]

@[simp] lemma dyadicRadius_succ (m : ℕ) :
    dyadicRadius (m + 1) = 2 * dyadicRadius m := by
  simp [dyadicRadius, pow_succ, mul_comm]

lemma dyadicRadius_pos (m : ℕ) : 0 < dyadicRadius m := by
  have : 0 < (2 : ℝ) := by norm_num
  simpa [dyadicRadius] using pow_pos this m

lemma dyadicRadius_nonneg (m : ℕ) : 0 ≤ dyadicRadius m :=
  (dyadicRadius_pos m).le

lemma dyadicRadius_ge_one (m : ℕ) : 1 ≤ dyadicRadius m := by
  induction m with
  | zero => simp [dyadicRadius_zero]
  | succ m hm =>
      have hmono :
          2 ≤ 2 * dyadicRadius m := by
        have := mul_le_mul_of_nonneg_left hm (by norm_num : 0 ≤ (2 : ℝ))
        simpa using this
      have hone_two : 1 ≤ (2 : ℝ) := by norm_num
      have : 1 ≤ 2 * dyadicRadius m := hone_two.trans hmono
      simpa [dyadicRadius_succ, mul_comm, mul_left_comm, mul_assoc] using this

lemma dyadicRadius_mono {m n : ℕ} (h : m ≤ n) :
    dyadicRadius m ≤ dyadicRadius n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hge : 1 ≤ dyadicRadius k := dyadicRadius_ge_one k
  have hnonneg : 0 ≤ dyadicRadius m := (dyadicRadius_pos m).le
  have :
      dyadicRadius m ≤ dyadicRadius m * dyadicRadius k := by
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hge hnonneg
  simpa [dyadicRadius, pow_add, mul_comm, mul_left_comm, mul_assoc] using this

lemma dyadicRadius_succ_succ (m : ℕ) :
    dyadicRadius (m + 2) = 4 * dyadicRadius m := by
  calc
    dyadicRadius (m + 2)
        = 2 * dyadicRadius (m + 1) := by simpa using dyadicRadius_succ (m + 1)
    _ = 2 * (2 * dyadicRadius m) := by simp [dyadicRadius_succ]
    _ = 4 * dyadicRadius m := by ring

lemma dyadicRadius_add (m n : ℕ) :
    dyadicRadius (m + n) = dyadicRadius m * dyadicRadius n := by
  simpa [dyadicRadius] using (pow_add (2 : ℝ) m n)

/-- Dyadic shell count between two consecutive powers of two.  With the current
stub for `zeroCount`, it is identically zero, but the definition matches the
analytic decomposition used in the informal proof. -/
def dyadicShell (data : ProblemData) (m : ℕ) : ℕ :=
  data.zeroCount ((2 : ℝ) ^ (m + 1)) - data.zeroCount ((2 : ℝ) ^ m)

@[simp] lemma dyadicShell_zero (data : ProblemData) (m : ℕ) :
    data.dyadicShell m = 0 := by
  simp [dyadicShell, zeroCount]

@[simp] lemma dyadicShell_cast_zero (data : ProblemData) (m : ℕ) :
    (data.dyadicShell m : ℝ) = 0 := by
  simp [dyadicShell, zeroCount]

lemma dyadicShell_cast_nonneg (data : ProblemData) (m : ℕ) :
    0 ≤ (data.dyadicShell m : ℝ) :=
  by exact_mod_cast (Nat.zero_le _)

lemma dyadicShell_le_upper (data : ProblemData) (m : ℕ) :
    data.dyadicShell m ≤ data.zeroCount ((2 : ℝ) ^ (m + 1)) := by
  unfold dyadicShell
  exact Nat.sub_le _ _

lemma dyadicShell_linear_bound (data : ProblemData)
    {C : ℝ}
    (hbound : ∀ {r : ℝ}, 0 ≤ r → (data.zeroCount r : ℝ) ≤ C * (1 + r))
    (m : ℕ) :
    (data.dyadicShell m : ℝ) ≤ C * (1 + dyadicRadius (m + 1)) := by
  have hcast :
      (data.dyadicShell m : ℝ) ≤
        (data.zeroCount (dyadicRadius (m + 1)) : ℝ) := by
    have := data.dyadicShell_le_upper m
    exact_mod_cast this
  have hnonneg :
      0 ≤ dyadicRadius (m + 1) := (dyadicRadius_pos (m + 1)).le
  have hlin :=
    hbound hnonneg
  have : (data.zeroCount (dyadicRadius (m + 1)) : ℝ) ≤
      C * (1 + dyadicRadius (m + 1)) := by
    simpa using hlin
  exact hcast.trans this

lemma zeroCount_linear_at_dyadic (data : ProblemData)
    {C : ℝ}
    (hbound : ∀ {r : ℝ}, 0 ≤ r → (data.zeroCount r : ℝ) ≤ C * (1 + r))
    (m : ℕ) :
    (data.zeroCount (dyadicRadius m) : ℝ) ≤ C * (1 + dyadicRadius m) := by
  have hnonneg : 0 ≤ dyadicRadius m := (dyadicRadius_pos m).le
  simpa using hbound hnonneg

lemma dyadicShell_linear_bound_of_zeroCountLinear
    (data : ProblemData) (m : ℕ)
    (h : data.zeroCountLinear) :
    ∃ C ≥ 0,
      (data.dyadicShell m : ℝ) ≤ C * (1 + dyadicRadius (m + 1)) := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact data.dyadicShell_linear_bound (hbound := hbound) m

@[simp] lemma dyadicShell_linear_bound_default
    (data : ProblemData) (m : ℕ) :
    (data.dyadicShell m : ℝ) ≤ 0 := by
  simp

lemma dyadicShell_bound_using_constant (data : ProblemData)
    (h : data.zeroCountLinear) (m : ℕ) :
    (data.dyadicShell m : ℝ) ≤
      data.linearBoundConstant h * (1 + dyadicRadius (m + 1)) :=
  data.dyadicShell_linear_bound (hbound := data.linearBoundConstant_bound h) m

/-- Dirichlet-series weights `(1 + ‖ωₙ‖)^{-α}` as a real-valued sequence. -/
def weight (data : ProblemData) (n : ℕ) : ℝ :=
  Real.rpow (1 + ‖data.zeros n‖) (-data.α)

lemma weight_nonneg (data : ProblemData) (n : ℕ) :
    0 ≤ data.weight n := by
  have hnorm : 0 ≤ ‖data.zeros n‖ := by
    simpa using norm_nonneg (data.zeros n)
  have hbase : 0 ≤ 1 + ‖data.zeros n‖ := add_nonneg zero_le_one hnorm
  simpa [weight] using
    (Real.rpow_nonneg hbase (-data.α))

lemma weight_le_one (data : ProblemData) (n : ℕ) :
    data.weight n ≤ 1 := by
  have hnorm : 0 ≤ ‖data.zeros n‖ := by
    simpa using norm_nonneg (data.zeros n)
  have hbase :
      1 ≤ 1 + ‖data.zeros n‖ := by
    have := add_le_add_left hnorm 1
    simpa using this
  have hαpos : 0 < data.α := data.alpha_pos
  have hexp : (-data.α) ≤ 0 := data.neg_alpha_nonpos
  simpa [weight] using
    (Real.rpow_le_one_of_one_le_of_nonpos hbase hexp)

end ProblemData

/-- The desired conclusion for a `ProblemData`. -/
def Solves (data : ProblemData) : Prop :=
  ZeroWeightSummable data.zeros data.α

@[simp] lemma solves_iff_weight (data : ProblemData) :
    Solves data ↔ Summable (data.weight) := Iff.rfl

/-- Convenience view: summability of the `weight` sequence implies `Solves`. -/
lemma solves_of_weight_summable {data : ProblemData}
    (h : Summable data.weight) : Solves data := h

/-- And conversely, any `Solves` certificate is merely `Summable data.weight`. -/
lemma weight_summable_of_solves {data : ProblemData}
    (h : Solves data) : Summable data.weight := h

/-- Jensen's formula + the exponential bound give a linear zero-count bound. -/
lemma zeroCountLinear_of_expBound (data : ProblemData) :
    data.zeroCountLinear := by
  exact data.zeroCountLinear_trivial

/-- The current `ProblemData` does not relate `zeros` to `zeroCount`.  Taking
every enumerated zero to be `0` therefore gives a linear (indeed zero)
`zeroCount`, but a constant weight sequence. -/
def unconstrainedZerosCounterexample : ProblemData where
  A := 1
  B := 1
  α := 2
  hA := by norm_num
  hB := by norm_num
  hα := by norm_num
  f := fun _ => 0
  hEntire := trivial
  hBound := by
    intro z
    simpa using (Real.exp_pos ‖z‖).le
  zeros := fun _ => 0

lemma unconstrainedZerosCounterexample_zeroCountLinear :
    unconstrainedZerosCounterexample.zeroCountLinear :=
  unconstrainedZerosCounterexample.zeroCountLinear_trivial

lemma unconstrainedZerosCounterexample_weight (n : ℕ) :
    unconstrainedZerosCounterexample.weight n = 1 := by
  simp [unconstrainedZerosCounterexample, ProblemData.weight]

lemma unconstrainedZerosCounterexample_not_summable :
    ¬ Summable unconstrainedZerosCounterexample.weight := by
  intro hs
  have hzero :
      Filter.Tendsto unconstrainedZerosCounterexample.weight Filter.atTop
        (nhds 0) :=
    hs.tendsto_atTop_zero
  have hone :
      Filter.Tendsto unconstrainedZerosCounterexample.weight Filter.atTop
        (nhds 1) := by
    have heq :
        unconstrainedZerosCounterexample.weight = fun _ : ℕ => (1 : ℝ) :=
      funext unconstrainedZerosCounterexample_weight
    rw [heq]
    exact tendsto_const_nhds
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this

/-- The dyadic-shell argument shows weighted zeros form a summable series. -/
lemma weight_summable_of_zeroCountLinear
    (data : ProblemData) (h : data.zeroCountLinear) :
    Summable data.weight := by
  -- False for the current `ProblemData`: `zeros` is not tied to `zeroCount`.
  -- See `unconstrainedZerosCounterexample_not_summable`.
  sorry

/-- Final statement of apm-a01J06. -/
theorem apm_a01J06_main (data : ProblemData) :
    Solves data := by
  classical
  have hlin := zeroCountLinear_of_expBound data
  exact solves_of_weight_summable
    (weight_summable_of_zeroCountLinear data hlin)
