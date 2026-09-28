import Mathlib

open scoped ContDiff Manifold

/-!
# APM t00A04 — a retract inclusion is not null-homotopic

## Statement repairs

The source omits positive dimension.  For a one-point oriented zero-manifold
the inclusion is constant, so the claim is false.  We add the minimal
noncontractibility consequence supplied by a positive-dimensional closed
oriented manifold: its identity is not homotopic to a constant map.
-/

def apm_t00a04_NullHomotopic {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∃ (y : Y) (H : X × ℝ → Y), Continuous H ∧
    (∀ x, H (x, 0) = f x) ∧ ∀ x, H (x, 1) = y

/-- Superseded: the hypothesis that `id_X` is not null-homotopic supplied the
main topological content of the problem. -/
theorem apm_t00a04_previous_encoding :
    ∀ (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
      (ι : X → Y) (r : Y → X),
      Continuous ι → Continuous r → (∀ x, r (ι x) = x) →
      (¬ apm_t00a04_NullHomotopic (fun x : X => x)) →
      ¬ apm_t00a04_NullHomotopic ι := by
  intro X Y _ _ ι r hι hr hret hid hnull
  rcases hnull with ⟨y, H, hH, hH0, hH1⟩
  apply hid
  refine ⟨r y, fun z ↦ r (H z), hr.comp hH, ?_, ?_⟩
  · intro x
    change r (H (x, 0)) = x
    rw [hH0 x, hret x]
  · intro x
    change r (H (x, 1)) = r y
    rw [hH1 x]

/-- Faithful minimally corrected statement of the prelim: a compact smooth
manifold with at least two points cannot occur as a retract inclusion that is
null-homotopic (see PRELIM-DEFECT.md). -/
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
  sorry

#print axioms apm_t00a04
