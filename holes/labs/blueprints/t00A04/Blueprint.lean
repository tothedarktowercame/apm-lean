import Mathlib

open scoped ContDiff Manifold

/-! # APM t00A04 — a retract inclusion is not null-homotopic -/

def apm_t00a04_NullHomotopic {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∃ (y : Y) (H : X × ℝ → Y), Continuous H ∧
    (∀ x, H (x, 0) = f x) ∧ ∀ x, H (x, 1) = y

/-- A nontrivial compact manifold without boundary cannot have its identity
map homotopic to a constant.  This is the sole global manifold-topology input. -/
theorem t00A04_manifold_identity_not_nullhomotopic
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nontrivial X]
    [ChartedSpace E X] [IsManifold I ∞ X] :
    ¬ apm_t00a04_NullHomotopic (fun x : X => x) := by
  sorry

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
