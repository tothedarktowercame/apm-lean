import Mathlib

/-!
# APM m96A01 — nonzero eigenspaces of compact operators

## Statement repairs

None. Compactness is encoded by Mathlib's `IsCompactOperator`: bounded sets
have relatively compact image.
-/

/-- The statement's kernel encoding is the standard eigenspace. -/
lemma m96A01_eigenspace_eq_ker {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (L : X →L[ℂ] X) (eigenvalue : ℂ) :
    Module.End.eigenspace L.toLinearMap eigenvalue =
      LinearMap.ker (L.toLinearMap - eigenvalue • LinearMap.id) := by
  ext x
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  simp [sub_eq_zero]

theorem apm_m96a01 :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
      (L : X →L[ℂ] X),
      IsCompactOperator L → ∀ (eigenvalue : ℂ), eigenvalue ≠ 0 →
        FiniteDimensional ℂ
          (LinearMap.ker (L.toLinearMap - eigenvalue • LinearMap.id)) := by
  intro X _ _ L hL eigenvalue heigenvalue
  let V : Submodule ℂ X := Module.End.eigenspace L.toLinearMap eigenvalue
  have hV_closed : IsClosed (V : Set X) := by dsimp [V]; infer_instance
  have hV_invariant : ∀ v ∈ V, L.toLinearMap v ∈ V := by
    intro v hv
    exact Module.End.eigenspace_mem_invtSubmodule L.toLinearMap eigenvalue hv
  have hrestrict : IsCompactOperator (L.toLinearMap.restrict hV_invariant) :=
    hL.restrict hV_invariant hV_closed
  have hid : IsCompactOperator (id : V → V) := by
    dsimp [V] at hrestrict ⊢
    rw [Module.End.restrict_eigenspace, LinearMap.coe_smul,
      IsCompactOperator.smul_iff₀ heigenvalue] at hrestrict
    simpa using hrestrict
  letI : ContinuousSMul ℂ
      (Module.End.eigenspace L.toLinearMap eigenvalue) :=
    Topology.IsInducing.subtypeVal.continuousSMul continuous_id rfl
  have hcompact : IsCompact (Metric.closedBall (0 : V) 1) := by
    have hid' : IsCompactOperator ((LinearMap.id : V →ₗ[ℂ] V)) := by
      simpa using hid
    have h := hid'.isCompact_closure_image_closedBall 1
    have h' : IsCompact (closure (Metric.closedBall (0 : V) 1)) := by
      simpa only [LinearMap.id_coe, id_eq, Set.image_id'] using h
    exact IsCompact.of_isClosed_subset h' Metric.isClosed_closedBall subset_closure
  have hfinite : FiniteDimensional ℂ V := by
    change FiniteDimensional ℂ
      (Module.End.eigenspace L.toLinearMap eigenvalue)
    exact @FiniteDimensional.of_isCompact_closedBall₀ ℂ inferInstance inferInstance
      (Module.End.eigenspace L.toLinearMap eigenvalue) inferInstance inferInstance this
      1 zero_lt_one hcompact
  rw [← m96A01_eigenspace_eq_ker L eigenvalue]
  exact hfinite
