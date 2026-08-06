import Mathlib

open Filter

/-!
# APM m96A02 — contraction mapping, iterates, and Picard existence

## Statement repairs

None.
-/

def apm_m96a02_IsContraction {M : Type*} [MetricSpace M] (T : M → M) : Prop :=
  ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ x y, dist (T x) (T y) ≤ k * dist x y

def apm_m96a02_Solves (f : ℝ → ℝ) (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  u 0 = u₀ ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt u (f (u t)) t

theorem apm_m96a02 :
    (∀ (M : Type*) [MetricSpace M] [CompleteSpace M] (T : M → M),
      apm_m96a02_IsContraction T →
      ∃ xstar : M, T xstar = xstar ∧
        (∀ x, Tendsto (fun n : ℕ => (T^[n]) x) atTop (nhds xstar)) ∧
        ∀ y, T y = y → y = xstar) ∧
    (∀ (M : Type*) [MetricSpace M] [CompleteSpace M] (T : M → M),
      (∃ N : ℕ, 1 ≤ N ∧ apm_m96a02_IsContraction (T^[N])) →
      ∃! x : M, T x = x) ∧
    (∀ (f : ℝ → ℝ) (u₀ : ℝ),
      (∃ L ≥ 0, ∀ x y, |f x - f y| ≤ L * |x - y|) →
      ∃ u : ℝ → ℝ, apm_m96a02_Solves f u₀ u ∧
        ∀ v : ℝ → ℝ, apm_m96a02_Solves f u₀ v →
          Set.EqOn u v (Set.Icc 0 1)) := by
  /-
  SKIPPED (two frozen-statement defects).

  First, the first and second conjuncts omit `[Nonempty M]`.  Take
  `M := Empty`, which has Mathlib `MetricSpace` and `CompleteSpace` instances.
  Its unique self-map satisfies `apm_m96a02_IsContraction` vacuously (for
  example with `k = 0`), but neither conjunct's existential fixed-point
  conclusion can be inhabited.  Sibling `m01J05` documents exactly this
  counterexample for the same formulation.  Mathlib's
  `ContractingWith.fixedPoint` and sibling `t91A04` both explicitly require
  `[Nonempty M]`; the lower-level `ContractingWith.exists_fixedPoint` instead
  requires an explicit starting point.

  Second, `apm_m96a02_Solves` imposes the differential equation only on
  `Ioo 0 1` and fixes only `u 0`, whereas uniqueness is `EqOn` on `Icc 0 1`.
  In particular `u 1` is completely unconstrained.  For `f = 0` and `u₀ = 0`,
  the zero solution and the function obtained by changing only its value at
  `1` both satisfy the predicate, since they agree on a neighborhood of every
  point of `Ioo 0 1`, but they are not equal on `Icc 0 1`.  Adding
  `ContinuousOn u (Icc 0 1)` or weakening uniqueness to `Ico 0 1` would close
  this endpoint gap.

  Desk research found the abstract contraction and iterate APIs in Mathlib's
  `Topology.MetricSpace.Contracting` and local Picard existence in
  `Analysis.ODE.PicardLindelof`.  Sibling `t91A04` proves the valid nonempty
  contraction theorem.  Partial siblings `m00A05` and `m93J06` document the
  remaining globalization and predicate-conversion work for ODE existence.
  The fully closed artifact scan, `LEMMA-INDEX.md`, `ConstructionTargets/`,
  and `YoungL2.lean` supplied no convention or lemma that repairs either
  logical defect.  The statement is frozen, so it was not altered.
  -/
  sorry
