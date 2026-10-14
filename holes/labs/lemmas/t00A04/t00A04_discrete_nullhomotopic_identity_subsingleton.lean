import Mathlib

open scoped ContDiff Manifold

/-! # APM t00A04 — a retract inclusion is not null-homotopic -/

def apm_t00a04_NullHomotopic {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∃ (y : Y) (H : X × ℝ → Y), Continuous H ∧
    (∀ x, H (x, 0) = f x) ∧ ∀ x, H (x, 1) = y

/-- A zero-dimensional real normed space is a singleton. -/
theorem t00A04_model_subsingleton_of_finrank_zero
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 0) :
    Subsingleton E := by
  sorry

/-- A manifold modelled on a singleton has the discrete topology.  The
`Subsingleton E` conclusion is passed in explicitly so this leaf is independent
of the preceding linear-algebra leaf. -/
theorem t00A04_manifold_discrete_of_model_subsingleton
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ModelWithCorners ℝ E E) [Subsingleton E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X] :
    DiscreteTopology X := by
  sorry

/-- A continuous real-parameter homotopy cannot move a point in a discrete
space.  Thus a null-homotopic identity on a discrete space forces the space to
be a singleton. -/
-- BEGIN SEAT AREA
theorem t00A04_discrete_nullhomotopic_identity_subsingleton
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X]
    (hnull : apm_t00a04_NullHomotopic (fun x : X => x)) :
    Subsingleton X := by
  sorry
-- END SEAT AREA

/-- A nontrivial type is not a subsingleton. -/
theorem t00A04_nontrivial_not_subsingleton
    (X : Type*) [Nontrivial X] : ¬ Subsingleton X := by
  sorry

/-- Positive-dimensional compact boundaryless manifolds are not
null-homotopic.  This is the remaining global fundamental-class input. -/
theorem t00A04_positive_dimensional_manifold_identity_not_nullhomotopic
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nontrivial X]
    [ChartedSpace E X] [IsManifold I ∞ X]
    (hdim : 0 < Module.finrank ℝ E) :
    ¬ apm_t00a04_NullHomotopic (fun x : X => x) := by
  sorry

/-- A nontrivial compact manifold without boundary cannot have its identity
map homotopic to a constant.  This theorem only assembles the independent
zero- and positive-dimensional leaves above. -/
theorem t00A04_manifold_identity_not_nullhomotopic
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nontrivial X]
    [ChartedSpace E X] [IsManifold I ∞ X] :
    ¬ apm_t00a04_NullHomotopic (fun x : X => x) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hdim | hdim
  · letI : Subsingleton E :=
      t00A04_model_subsingleton_of_finrank_zero E hdim
    letI : DiscreteTopology X :=
      t00A04_manifold_discrete_of_model_subsingleton E X I
    intro hnull
    exact t00A04_nontrivial_not_subsingleton X
      (t00A04_discrete_nullhomotopic_identity_subsingleton X hnull)
  · exact t00A04_positive_dimensional_manifold_identity_not_nullhomotopic
      E X I hdim

/-- Composing a null-homotopy with a retraction would null-homotope the
identity. -/
theorem t00A04_retract_inclusion_not_nullhomotopic
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (ι : X → Y) (r : Y → X)
    (hr : Continuous r) (hret : ∀ x, r (ι x) = x)
    (hid : ¬ apm_t00a04_NullHomotopic (fun x : X => x)) :
    ¬ apm_t00a04_NullHomotopic ι := by
  intro hnull
  rcases hnull with ⟨y, H, hH, hH0, hH1⟩
  apply hid
  refine ⟨r y, fun z ↦ r (H z), hr.comp hH, ?_, ?_⟩
  · intro x
    change r (H (x, 0)) = x
    rw [hH0 x, hret x]
  · intro x
    change r (H (x, 1)) = r y
    rw [hH1 x]

theorem apm_t00a04 :
    ∀ (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] (I : ModelWithCorners ℝ E E)
      (J : ModelWithCorners ℝ F F)
      (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [CompactSpace X] [Nontrivial X]
      [T2Space Y] [CompactSpace Y]
      [ChartedSpace E X] [IsManifold I ∞ X]
      [ChartedSpace F Y] [IsManifold J ∞ Y],
      ∀ (ι : C(X, Y)) (r : C(Y, X)),
      ContMDiff I J ∞ ι → ContMDiff J I ∞ r →
      (∀ x, r (ι x) = x) → ¬ apm_t00a04_NullHomotopic ι := by
  intro E F _ _ _ _ _ _ I J X Y _ _ _ _ _ _ _ _ _ _ _ ι r hι hr hret
  exact t00A04_retract_inclusion_not_nullhomotopic X Y ι r r.continuous hret
    (t00A04_manifold_identity_not_nullhomotopic E X I)

#print axioms apm_t00a04
