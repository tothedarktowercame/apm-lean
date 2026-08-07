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

/-- Forget nonemptiness and boundedness, retaining the closed set on which
Mathlib's complete extended Hausdorff metric is defined. -/
def t93A02H.toCloseds {X : Type*} [PseudoMetricSpace X] (A : t93A02H X) :
    TopologicalSpace.Closeds X :=
  ⟨A.1, A.2.2.1⟩

/-- Any two members of the intended hyperspace are at finite extended
Hausdorff distance.  This is the finiteness bridge needed to compare the
real-valued and extended-valued Cauchy formulations. -/
lemma t93A02H.hausdorffEDist_ne_top {X : Type*} [PseudoMetricSpace X]
    (A B : t93A02H X) : Metric.hausdorffEDist A.1 B.1 ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    A.2.1 B.2.1 A.2.2.2 B.2.2.2

@[simp] lemma t93A02H.edist_toCloseds {X : Type*} [MetricSpace X]
    (A B : t93A02H X) :
    edist A.toCloseds B.toCloseds = Metric.hausdorffEDist A.1 B.1 := rfl

/-- On the intended bounded nonempty hyperspace, the extended distance is the
`ENNReal.ofReal` image of the real Hausdorff distance. -/
lemma t93A02H.edist_toCloseds_eq_ofReal_hausdorffDist
    {X : Type*} [MetricSpace X] (A B : t93A02H X) :
    edist A.toCloseds B.toCloseds =
      ENNReal.ofReal (Metric.hausdorffDist A.1 B.1) := by
  rw [t93A02H.edist_toCloseds, Metric.hausdorffDist,
    ENNReal.ofReal_toReal (t93A02H.hausdorffEDist_ne_top A B)]

/-- The frozen real-valued Cauchy condition gives a Cauchy sequence in
Mathlib's complete extended-metric space of closed sets. -/
lemma t93A02H.cauchySeq_toCloseds {X : Type*} [MetricSpace X]
    (A : ℕ → t93A02H X) (hA : IsT93A02HausdorffCauchy A) :
    CauchySeq (fun n => (A n).toCloseds) := by
  rw [EMetric.cauchySeq_iff_NNReal]
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε (by exact_mod_cast hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [t93A02H.edist_toCloseds_eq_ofReal_hausdorffDist]
  have hdist := hN n hn N le_rfl
  simpa using
    ((ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hε)).2 hdist)

theorem apm_t93a02
    (X : Type*) [MetricSpace X] [CompleteSpace X] :
    ∀ A : ℕ → t93A02H X, IsT93A02HausdorffCauchy A →
      ∃ L : t93A02H X,
        Tendsto (fun n => Metric.hausdorffDist (A n).1 L.1)
          atTop (nhds 0) := by
  /-
  Boundary (closer hop 2, still open): Mathlib has
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
  bridge is exactly the main theorem requested. The closer search additionally
  checked `LEMMA-INDEX.md`, all fully closed artifacts, `ConstructionTargets/`,
  `NonemptyCompacts`, Gromov--Hausdorff sources, and git history. The
  `NonemptyCompacts` complete instance cannot be used because closed bounded
  subsets of an arbitrary complete metric space need not be compact. The local
  definitions and lemmas `t93A02H.toCloseds`,
  `t93A02H.hausdorffEDist_ne_top`, and `t93A02H.edist_toCloseds` now compile
  the embedding and pairwise-finiteness part of the route. This hop additionally
  proves `t93A02H.edist_toCloseds_eq_ofReal_hausdorffDist`, the exact
  real-to-extended conversion made valid by pairwise finiteness, and
  `t93A02H.cauchySeq_toCloseds`, which completes the translation of the
  frozen Cauchy hypothesis into the complete `Closeds` space. Still missing is a
  proof that the complete `Closeds` limit is nonempty and bounded, plus the
  final real/extended convergence conversion. The existential conclusion
  exposes no further smaller result without developing that core argument.
  -/
  sorry
