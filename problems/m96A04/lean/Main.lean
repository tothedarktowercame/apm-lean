import Mathlib

open Filter

/-!
# APM m96A04

## Statement repairs

None.

## Encoding notes

The operator `A` is an algebraic `LinearMap`, so continuity is not built into
its type.  The arbitrary function `B` is asserted linear by exhibiting the
corresponding `LinearMap` with the same underlying function.
-/

theorem apm_m96a04
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →ₗ[ℂ] X) (B : X → X)
    (hAB : ∀ x y : X, inner ℂ (A x) y = inner ℂ x (B y)) :
    (∃ Blin : X →ₗ[ℂ] X, (Blin : X → X) = B) ∧ Continuous B ∧ Continuous A := by
  let Blin : X →ₗ[ℂ] X :=
    { toFun := B
      map_add' := by
        intro y z
        apply ext_inner_left ℂ
        intro x
        rw [← hAB, inner_add_right, hAB, hAB]
        rw [inner_add_right]
      map_smul' := by
        intro c y
        apply ext_inner_left ℂ
        intro x
        rw [← hAB, inner_smul_right, hAB, inner_smul_right]
        simp }
  have hBlin : (Blin : X → X) = B := rfl
  have hBcont : Continuous Blin := by
    -- Mathlib's Hellinger--Toeplitz proof uses this same closed-graph API.
    apply Blin.continuous_of_seq_closed_graph
    intro u x y hu hBu
    apply ext_inner_left ℂ
    intro z
    have h₁ : Tendsto (fun n => inner ℂ z (Blin (u n))) atTop (nhds (inner ℂ z y)) :=
      tendsto_const_nhds.inner hBu
    have h₂ : Tendsto (fun n => inner ℂ z (Blin (u n))) atTop
        (nhds (inner ℂ z (Blin x))) := by
      have h : Tendsto (fun n => inner ℂ (A z) (u n)) atTop
          (nhds (inner ℂ (A z) x)) := tendsto_const_nhds.inner hu
      simpa [Blin, ← hAB] using h
    exact tendsto_nhds_unique h₁ h₂
  have hAcont : Continuous A := by
    -- Repeat the closed-graph argument with the two sides of `hAB` exchanged.
    apply A.continuous_of_seq_closed_graph
    intro u x y hu hAu
    apply ext_inner_right ℂ
    intro z
    have h₁ : Tendsto (fun n => inner ℂ (A (u n)) z) atTop (nhds (inner ℂ y z)) :=
      hAu.inner tendsto_const_nhds
    have h₂ : Tendsto (fun n => inner ℂ (A (u n)) z) atTop
        (nhds (inner ℂ (A x) z)) := by
      have h : Tendsto (fun n => inner ℂ (u n) (B z)) atTop
          (nhds (inner ℂ x (B z))) := hu.inner tendsto_const_nhds
      simpa [hAB] using h
    exact tendsto_nhds_unique h₁ h₂
  exact ⟨⟨Blin, hBlin⟩, hBlin ▸ hBcont, hAcont⟩
