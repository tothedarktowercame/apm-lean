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
  sorry
