import Mathlib

/-!
# APM a98A03

## Statement repairs

None.

## Encoding notes

The problem's functions on `[0, 1]` are represented by functions on `ℝ`, with
all hypotheses restricted to the unit interval.  Since Mathlib's integral is
the Lebesgue integral, the Riemann-integrable strengthening is expressed using
the tagged-partition definition below, including its proposed integral value.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- `g` has Riemann integral `I` on `[0, 1]`, expressed by convergence of all
tagged sums as the mesh tends to zero. -/
def HasRiemannIntegralOnUnitInterval (g : ℝ → ℝ) (I : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℝ) (tag : Fin n → ℝ),
        x 0 = 0 → x (Fin.last n) = 1 → StrictMono x →
        (∀ i : Fin n, x i.castSucc ≤ tag i ∧ tag i ≤ x i.succ) →
        (∀ i : Fin n, x i.succ - x i.castSucc < δ) →
        |(∑ i, g (tag i) * (x i.succ - x i.castSucc)) - I| < ε

/-- Mean-value tags in exactly the increment form required by the custom
tagged Riemann sums. -/
lemma apm_a98a03_exists_mvt_tag
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_deriv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a < b) :
    ∃ t ∈ Ioo a b, f b - f a = f' t * (b - a) := by
  have hcont : ContinuousOn f (Icc a b) := hf_cont.mono fun x hx ↦
    ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x := by
    intro x hx
    exact hf_deriv x ⟨ha.1.trans_lt hx.1, hx.2.trans_le hb.2⟩
  obtain ⟨t, ht, hslope⟩ :=
    exists_hasDerivAt_eq_slope f f' hab hcont hderiv
  refine ⟨t, ht, ?_⟩
  rw [hslope]
  exact (div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')).symm

/-- Adjacent increments along a `Fin`-indexed partition telescope to the
endpoint increment.  This is the finite algebraic step needed after choosing
the mean-value tags above. -/
lemma apm_a98a03_sum_adjacent_sub
    {G : Type*} [AddCommGroup G] (n : ℕ) (f : ℝ → G)
    (x : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (f (x i.succ) - f (x i.castSucc))) =
      f (x (Fin.last n)) - f (x 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp_rw [← Fin.castSucc_succ]
      rw [ih (fun i ↦ x i.castSucc)]
      simp only [Fin.castSucc_zero, Fin.succ_last]
      abel

/-- A uniform `Fin`-indexed partition of `[0,1]` can be chosen with mesh
smaller than any prescribed positive number. -/
lemma apm_a98a03_exists_fine_uniform_partition {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℝ),
      x 0 = 0 ∧ x (Fin.last n) = 1 ∧ StrictMono x ∧
      ∀ i : Fin n, x i.succ - x i.castSucc < δ := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  let n := k + 1
  have hn : 0 < n := Nat.succ_pos k
  let x : Fin (n + 1) → ℝ := fun i ↦ (i : ℝ) / n
  refine ⟨n, hn, x, ?_, ?_, ?_, ?_⟩
  · simp [x]
  · simp [x, n, Nat.cast_add, Nat.cast_one,
      show (k : ℝ) + 1 ≠ 0 by positivity]
  · intro i j hij
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)
  · intro i
    calc
      x i.succ - x i.castSucc = 1 / (n : ℝ) := by
        simp only [x, Fin.val_castSucc]
        rw [show (i.succ.val : ℝ) = i.val + 1 by norm_num]
        field_simp
        ring
      _ < δ := by simpa [n, Nat.cast_add, Nat.cast_one] using hk

theorem apm_a98a03 :
    (∃ (f f' : ℝ → ℝ),
      ContinuousOn f (Icc 0 1) ∧
      (∀ᵐ x ∂volume.restrict (Icc 0 1), HasDerivAt f (f' x) x) ∧
      (∃ C : ℝ, ∀ᵐ x ∂volume.restrict (Icc 0 1), f' x ≤ C) ∧
      f 1 - f 0 ≠ ∫ x in Icc (0 : ℝ) 1, f' x ∂volume) ∧
    (∀ (f f' : ℝ → ℝ) (I : ℝ),
      ContinuousOn f (Icc 0 1) →
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x) →
      HasRiemannIntegralOnUnitInterval f' I →
      f 1 - f 0 = I) := by
  /-
  Boundary (closer hops 1--2): the strengthened FTC half is narrowed by the
  compiled helper `apm_a98a03_exists_mvt_tag`.  It applies Mathlib's exact
  `exists_hasDerivAt_eq_slope` theorem on every partition cell and returns
  `f b - f a = f' t * (b-a)`, precisely the summand needed by
  `HasRiemannIntegralOnUnitInterval`.  Hop 2 additionally proves
  `apm_a98a03_sum_adjacent_sub`, which telescopes all adjacent increments of
  any `Fin`-indexed partition to its endpoint increment.  The remaining FTC
  assembly is to choose a sufficiently fine uniform `Fin (n+1)` partition and
  its dependent family of MVT tags, then apply the defining estimate.

  The counterexample half remains the hard boundary.  Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets/` (including `LusinN` and
  `BanachZarecki`), Mathlib's real/cardinality, singular-function, measure, and
  bounded-variation sources, prior Riemann-integral artifacts `a95A01` and
  `a94A02`, and git history found no devil's staircase or equivalent continuous
  singular function with derivative zero almost everywhere.  Mathlib's
  `Cardinal.cantorFunction` parametrizes binary sequences and is not the Cantor
  staircase on `[0,1]`.  `ConstructionTargets.LusinN` proves FTC and null-set
  preservation for already absolutely continuous functions, so it cannot
  produce the required non-AC witness.

  Closure requires constructing the middle-thirds Cantor function (continuity,
  endpoints, local constancy off a null Cantor set), while the independent FTC
  conjunct can be finished from the compiled MVT tags and Fin telescoping.

  CLOSER HOP 3: `apm_a98a03_exists_fine_uniform_partition` now compiles the
  remaining Archimedean/`Fin` geometry: for every `δ > 0` it returns a positive
  `n`, the uniform partition `x i = i/n`, its endpoint equations and strict
  monotonicity, and the mesh bound required verbatim by the custom Riemann
  predicate. Thus the FTC conjunct is reduced only to choosing the dependent
  family of MVT tags and rewriting its sum with the two compiled helpers.

  Going beyond the prior named searches, I inspected Mathlib's measure
  decomposition and `AbsolutelyContinuousFun` developments for a distribution
  function of a singular measure. They provide Radon--Nikodym/Lebesgue
  decomposition and prove rigidity for already absolutely continuous
  functions, but do not construct a nonzero atomless singular measure or its
  continuous cumulative distribution. The real-cardinality digit series also
  lacks an inverse/extension from the ternary Cantor set. Consequently the
  Cantor-staircase construction remains the independent open boundary; the
  statement is unchanged.
  -/
  sorry
