import Mathlib

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

theorem apm_t00a04 :
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

#print axioms apm_t00a04
