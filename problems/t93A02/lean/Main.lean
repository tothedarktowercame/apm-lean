import Mathlib

/-! # APM t93A02: completeness of the Hausdorff hyperspace

## Statement repairs

The empty set must be excluded: the displayed Hausdorff formula is a metric
only on nonempty closed bounded subsets.  This standard missing hypothesis is
made explicit in `t93A02H`.
-/

open Filter Set

def t93A02H (X : Type*) [PseudoMetricSpace X] :=
  {A : Set X // A.Nonempty ∧ IsClosed A ∧ Bornology.IsBounded A}

def IsT93A02HausdorffCauchy {X : Type*} [PseudoMetricSpace X]
    (A : ℕ → t93A02H X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    Metric.hausdorffDist (A m).1 (A n).1 < ε

theorem apm_t93a02
    (X : Type*) [MetricSpace X] [CompleteSpace X] :
    ∀ A : ℕ → t93A02H X, IsT93A02HausdorffCauchy A →
      ∃ L : t93A02H X,
        Tendsto (fun n => Metric.hausdorffDist (A n).1 L.1)
          atTop (nhds 0) := by
  /-
  Boundary (skipped): Mathlib has
  `TopologicalSpace.Closeds.instCompleteSpace`, proving completeness of all
  closed subsets for the extended Hausdorff distance. The frozen statement,
  however, uses a custom subtype of nonempty closed bounded sets, a
  real-valued `Metric.hausdorffDist` Cauchy predicate, and asks for real
  convergence. I searched `Closeds`, `NonemptyCompacts`, Hausdorff
  distance/edistance, completeness, and Cauchy-sequence APIs. There is no
  packaged complete metric space of nonempty closed bounded subsets. To use
  the existing `Closeds` theorem one must still translate the real Cauchy
  hypothesis to extended-metric Cauchy convergence, prove that its closed-set
  limit is nonempty and bounded (excluding escape to infinity and the empty
  limit), and translate convergence back to `hausdorffDist`. That substantial
  bridge is exactly the main theorem requested and is beyond this pass; the
  existential conclusion exposes no smaller honest partial result.
  -/
  sorry
