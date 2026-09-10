import ConstructionTargets.C1GraphLocalApproximation
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.Piecewise
noncomputable section
namespace ConstructionTargets.C1GraphPartition
open LinearGraphMeasure C1GraphLocalApproximation Set Metric
open scoped Function
variable (d : ℕ) (f : E d → ℝ) (U : Set (E d))
variable (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (ε : ℝ) (hε : 0 < ε)
include hU hf hε in
theorem partition_exists : ∃ (t : ℕ → Set (E d)) (A : ℕ → E d →L[ℝ] ℝ),
    Pairwise (Disjoint on t) ∧ (∀ n, MeasurableSet (t n)) ∧ (⋃ n, t n) = U ∧
    (∀ n, (t n).Nonempty → ∃ x ∈ U, A n = fderiv ℝ f x) ∧
    (∀ n, ∀ y ∈ t n, ‖fderiv ℝ f y-A n‖ ≤ ε) ∧
    (∀ n, ∀ y ∈ t n, ∀ z ∈ t n, ‖f y-f z-A n (y-z)‖ ≤ ε*‖y-z‖) := by
  classical
  by_cases hu : U.Nonempty
  · letI : Nonempty U := hu.to_subtype
    let B : U → Set (E d) := fun x => ball x.val (radius d f U hU hf ε hε x.val x.property)
    have hBU (x : U) : B x ⊆ U := radius_subset d f U hU hf ε hε x.val x.property
    have hcover : U ⊆ ⋃ x, B x := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩, center_member d f U hU hf ε hε x hx⟩
    obtain ⟨c,hc⟩ := (HereditarilyLindelofSpace.isLindelof U).indexed_countable_subcover B (fun _ => isOpen_ball) hcover
    let V : ℕ → Set (E d) := fun n => B (c n)
    refine ⟨disjointed V, (fun n => fderiv ℝ f (c n).val), disjoint_disjointed V,
      MeasurableSet.disjointed (fun _ => isOpen_ball.measurableSet), ?_, ?_, ?_, ?_⟩
    · rw [iUnion_disjointed]
      exact Subset.antisymm (iUnion_subset (fun n => hBU (c n))) hc
    · intro n _
      exact ⟨(c n).val,(c n).property,rfl⟩
    · intro n y hy
      exact derivative_bound d f U hU hf ε hε (c n).val (c n).property y (disjointed_subset V n hy)
    · intro n y hy z hz
      exact residual_bound d f U hU hf ε hε (c n).val (c n).property
        y (disjointed_subset V n hy) z (disjointed_subset V n hz)
  · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hu
    subst U
    refine ⟨fun _ => ∅, fun _ => 0, ?_⟩
    simp [Pairwise]

include hU hf in
theorem graph_measurable (t : Set (E d)) (ht : MeasurableSet t) (htu : t ⊆ U) :
    MeasurableSet (GraphMetricComparison.Graph d f t) := by
  classical
  let g := U.piecewise f (fun _ => 0)
  have hg : Measurable g := hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hfst : Measurable (fun z : Ambient d => z.fst) := (WithLp.continuous_fst ..).measurable
  have hsnd : Measurable (fun z : Ambient d => z.snd) := (WithLp.continuous_snd ..).measurable
  have he : GraphMetricComparison.Graph d f t =
      {z : Ambient d | z.fst ∈ t} ∩ {z : Ambient d | z.snd = g z.fst} := by
    ext z
    change (z.fst ∈ t ∧ z.snd = f z.fst) ↔ (z.fst ∈ t ∧ z.snd = g z.fst)
    constructor <;> rintro ⟨hz,he⟩ <;> refine ⟨hz,?_⟩
    · simpa [g, Set.piecewise_eq_of_mem U f (fun _ => 0) (htu hz)] using he
    · simpa [g, Set.piecewise_eq_of_mem U f (fun _ => 0) (htu hz)] using he
  rw [he]
  exact (hfst ht).inter (measurableSet_eq_fun hsnd (hg.comp hfst))

theorem graph_disjoint (s t : Set (E d)) (hst : Disjoint s t) :
    Disjoint (GraphMetricComparison.Graph d f s) (GraphMetricComparison.Graph d f t) := by
  rw [Set.disjoint_left] at hst ⊢
  intro z hz ht
  exact hst hz.1 ht.1

theorem graph_union (t : ℕ → Set (E d)) :
    (⋃ n, GraphMetricComparison.Graph d f (t n)) = GraphMetricComparison.Graph d f (⋃ n, t n) := by
  ext z
  simp [GraphMetricComparison.Graph, exists_and_right]

def pieces : ℕ → Set (E d) := (partition_exists d f U hU hf ε hε).choose
def linear : ℕ → E d →L[ℝ] ℝ := (partition_exists d f U hU hf ε hε).choose_spec.choose

theorem pieces_disjoint : Pairwise (Disjoint on pieces d f U hU hf ε hε) :=
  (partition_exists d f U hU hf ε hε).choose_spec.choose_spec.1

theorem pieces_measurable (n : ℕ) : MeasurableSet (pieces d f U hU hf ε hε n) :=
  (partition_exists d f U hU hf ε hε).choose_spec.choose_spec.2.1 n

theorem pieces_union : (⋃ n, pieces d f U hU hf ε hε n) = U :=
  (partition_exists d f U hU hf ε hε).choose_spec.choose_spec.2.2.1

theorem pieces_subset (n : ℕ) : pieces d f U hU hf ε hε n ⊆ U := by
  exact (subset_iUnion (pieces d f U hU hf ε hε) n).trans
    (le_of_eq (pieces_union d f U hU hf ε hε))

theorem selected_derivative (n : ℕ) (hn : (pieces d f U hU hf ε hε n).Nonempty) :
    ∃ x ∈ U, linear d f U hU hf ε hε n = fderiv ℝ f x :=
  (partition_exists d f U hU hf ε hε).choose_spec.choose_spec.2.2.2.1 n hn

theorem derivative_proximity (n : ℕ) (y : E d) (hy : y ∈ pieces d f U hU hf ε hε n) :
    ‖fderiv ℝ f y-linear d f U hU hf ε hε n‖ ≤ ε :=
  (partition_exists d f U hU hf ε hε).choose_spec.choose_spec.2.2.2.2.1 n y hy

theorem residual (n : ℕ) (y : E d) (hy : y ∈ pieces d f U hU hf ε hε n)
    (z : E d) (hz : z ∈ pieces d f U hU hf ε hε n) :
    ‖f y-f z-linear d f U hU hf ε hε n (y-z)‖ ≤ ε*‖y-z‖ :=
  (partition_exists d f U hU hf ε hε).choose_spec.choose_spec.2.2.2.2.2 n y hy z hz

theorem images_measurable (n : ℕ) :
    MeasurableSet (GraphMetricComparison.Graph d f (pieces d f U hU hf ε hε n)) :=
  graph_measurable d f U hU hf _ (pieces_measurable d f U hU hf ε hε n)
    (pieces_subset d f U hU hf ε hε n)

theorem images_disjoint : Pairwise (Disjoint on fun n =>
    GraphMetricComparison.Graph d f (pieces d f U hU hf ε hε n)) := by
  intro i j hij
  exact graph_disjoint d f _ _ (pieces_disjoint d f U hU hf ε hε hij)

theorem images_union : (⋃ n, GraphMetricComparison.Graph d f (pieces d f U hU hf ε hε n)) =
    GraphMetricComparison.Graph d f U := by
  rw [graph_union, pieces_union]

open MeasureTheory
open scoped ENNReal

theorem piece_bounds (hε1 : ε < 1) (n : ℕ) :
    ((ENNReal.ofReal (1-ε))^d * ENNReal.ofReal (Real.sqrt (1+‖linear d f U hU hf ε hε n‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) (pieces d f U hU hf ε hε n) ≤
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d))
        (GraphMetricComparison.Graph d f (pieces d f U hU hf ε hε n))) ∧
    ((Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d))
        (GraphMetricComparison.Graph d f (pieces d f U hU hf ε hε n)) ≤
      (ENNReal.ofReal (1+ε))^d * ENNReal.ofReal (Real.sqrt (1+‖linear d f U hU hf ε hε n‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) (pieces d f U hU hf ε hε n)) :=
  GraphMetricComparison.bounds d f _ _ ε hε.le (residual d f U hU hf ε hε n) hε1

theorem empty_pieces (h : U = ∅) (n : ℕ) : pieces d f U hU hf ε hε n = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have := pieces_subset d f U hU hf ε hε n hy
  simp [h] at this


theorem dimension_two (f : E 2 → ℝ) (U : Set (E 2))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    ((ENNReal.ofReal (1-ε))^2 * ENNReal.ofReal (Real.sqrt (1+‖linear 2 f U hU hf ε hε n‖^2)) *
      (Measure.hausdorffMeasure (2 : ℝ) : Measure (E 2)) (pieces 2 f U hU hf ε hε n) ≤
      (Measure.hausdorffMeasure (2 : ℝ) : Measure (Ambient 2))
        (GraphMetricComparison.Graph 2 f (pieces 2 f U hU hf ε hε n))) ∧
    ((Measure.hausdorffMeasure (2 : ℝ) : Measure (Ambient 2))
        (GraphMetricComparison.Graph 2 f (pieces 2 f U hU hf ε hε n)) ≤
      (ENNReal.ofReal (1+ε))^2 * ENNReal.ofReal (Real.sqrt (1+‖linear 2 f U hU hf ε hε n‖^2)) *
      (Measure.hausdorffMeasure (2 : ℝ) : Measure (E 2)) (pieces 2 f U hU hf ε hε n)) := piece_bounds 2 f U hU hf ε hε hε1 n

theorem dimension_three (f : E 3 → ℝ) (U : Set (E 3))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    ((ENNReal.ofReal (1-ε))^3 * ENNReal.ofReal (Real.sqrt (1+‖linear 3 f U hU hf ε hε n‖^2)) *
      (Measure.hausdorffMeasure (3 : ℝ) : Measure (E 3)) (pieces 3 f U hU hf ε hε n) ≤
      (Measure.hausdorffMeasure (3 : ℝ) : Measure (Ambient 3))
        (GraphMetricComparison.Graph 3 f (pieces 3 f U hU hf ε hε n))) ∧
    ((Measure.hausdorffMeasure (3 : ℝ) : Measure (Ambient 3))
        (GraphMetricComparison.Graph 3 f (pieces 3 f U hU hf ε hε n)) ≤
      (ENNReal.ofReal (1+ε))^3 * ENNReal.ofReal (Real.sqrt (1+‖linear 3 f U hU hf ε hε n‖^2)) *
      (Measure.hausdorffMeasure (3 : ℝ) : Measure (E 3)) (pieces 3 f U hU hf ε hε n)) := piece_bounds 3 f U hU hf ε hε hε1 n

end ConstructionTargets.C1GraphPartition

#print axioms ConstructionTargets.C1GraphPartition.partition_exists
#print axioms ConstructionTargets.C1GraphPartition.graph_measurable
#print axioms ConstructionTargets.C1GraphPartition.graph_disjoint
#print axioms ConstructionTargets.C1GraphPartition.graph_union
#print axioms ConstructionTargets.C1GraphPartition.pieces_disjoint
#print axioms ConstructionTargets.C1GraphPartition.pieces_measurable
#print axioms ConstructionTargets.C1GraphPartition.pieces_union
#print axioms ConstructionTargets.C1GraphPartition.pieces_subset
#print axioms ConstructionTargets.C1GraphPartition.selected_derivative
#print axioms ConstructionTargets.C1GraphPartition.derivative_proximity
#print axioms ConstructionTargets.C1GraphPartition.residual
#print axioms ConstructionTargets.C1GraphPartition.images_measurable
#print axioms ConstructionTargets.C1GraphPartition.images_disjoint
#print axioms ConstructionTargets.C1GraphPartition.images_union
#print axioms ConstructionTargets.C1GraphPartition.piece_bounds
#print axioms ConstructionTargets.C1GraphPartition.empty_pieces
#print axioms ConstructionTargets.C1GraphPartition.dimension_two
#print axioms ConstructionTargets.C1GraphPartition.dimension_three
