/-
  C4 — UT Austin Prelim m96A04 (Functional Analysis)

  Let X be a Hilbert space, A : X →ₗ[ℂ] X linear (not assumed continuous).
  Let B : X → X (not assumed linear or continuous) satisfy
    ⟪A x, y⟫ = ⟪x, B y⟫  for all x, y.

  Prove: (a) B is linear  (b) B is continuous  (c) A is continuous.
-/
import Mathlib

open InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- Part (a): B is additive. From ⟪Ax, y⟫ = ⟪x, By⟫ and nondegeneracy. -/
theorem adjoint_map_additive
    (A : X →ₗ[ℂ] X)
    (B : X → X)
    (hadj : ∀ x y, @inner ℂ X _ (A x) y = @inner ℂ X _ x (B y)) :
    ∀ y₁ y₂ : X, B (y₁ + y₂) = B y₁ + B y₂ := by
  intro y₁ y₂
  refine ext_inner_left ℂ fun x => ?_
  simp only [← hadj, inner_add_right]

/-- Part (a): B respects scalar multiplication. -/
theorem adjoint_map_smul
    (A : X →ₗ[ℂ] X)
    (B : X → X)
    (hadj : ∀ x y, @inner ℂ X _ (A x) y = @inner ℂ X _ x (B y)) :
    ∀ (c : ℂ) (y : X), B (c • y) = c • B y := by
  intro c y
  refine ext_inner_left ℂ fun x => ?_
  simp only [← hadj, inner_smul_right]

/-- Helper: if ⟪Ax, y⟫ = ⟪x, By⟫ for all x,y and uₙ → u and Auₙ → z,
    then z = Au. This is the closed-graph condition. -/
theorem adjoint_seq_closed
    (A : X →ₗ[ℂ] X) (B : X →ₗ[ℂ] X)
    (hadj : ∀ x y, @inner ℂ X _ (A x) y = @inner ℂ X _ x (B y))
    (u : ℕ → X) (x z : X)
    (hu : Filter.Tendsto u Filter.atTop (nhds x))
    (hAu : Filter.Tendsto (A ∘ u) Filter.atTop (nhds z)) :
    z = A x := by
  refine ext_inner_left ℂ fun w => ?_
  -- ⟪w, z⟫ = lim ⟪w, A(uₙ)⟫ = lim ⟪B*w, uₙ⟫ = ⟪B*w, x⟫ = ⟪w, Ax⟫
  have h1 : Filter.Tendsto (fun n => @inner ℂ X _ w (A (u n))) Filter.atTop
      (nhds (@inner ℂ X _ w z)) :=
    (continuous_const.inner continuous_id').tendsto z |>.comp hAu
  have h2 : Filter.Tendsto (fun n => @inner ℂ X _ w (A (u n))) Filter.atTop
      (nhds (@inner ℂ X _ w (A x))) := by
    have : Filter.Tendsto (fun n => @inner ℂ X _ (B w) (u n)) Filter.atTop
        (nhds (@inner ℂ X _ (B w) x)) :=
      (continuous_const.inner continuous_id').tendsto x |>.comp hu
    have rewrite_n : ∀ n, @inner ℂ X _ (B w) (u n) = @inner ℂ X _ w (A (u n)) := by
      intro n
      have := hadj w (u n)  -- ⟪Aw, un⟫ = ⟪w, Bun⟫
      calc @inner ℂ X _ (B w) (u n)
          = starRingEnd ℂ (@inner ℂ X _ (u n) (B w)) := by rw [inner_conj_symm]
        _ = starRingEnd ℂ (@inner ℂ X _ (A (u n)) w) := by rw [← hadj (u n) w]
        _ = @inner ℂ X _ w (A (u n)) := by rw [inner_conj_symm]
    have rewrite_x : @inner ℂ X _ (B w) x = @inner ℂ X _ w (A x) := by
      calc @inner ℂ X _ (B w) x
          = starRingEnd ℂ (@inner ℂ X _ x (B w)) := by rw [inner_conj_symm]
        _ = starRingEnd ℂ (@inner ℂ X _ (A x) w) := by rw [← hadj x w]
        _ = @inner ℂ X _ w (A x) := by rw [inner_conj_symm]
    simp only [rewrite_n] at this
    rwa [rewrite_x] at this
  exact tendsto_nhds_unique h1 h2

/-- Part (c): A is continuous. By the Closed Graph Theorem. -/
theorem adjoint_map_A_continuous
    (A : X →ₗ[ℂ] X) (B : X →ₗ[ℂ] X)
    (hadj : ∀ x y, @inner ℂ X _ (A x) y = @inner ℂ X _ x (B y)) :
    Continuous A :=
  A.continuous_of_seq_closed_graph (adjoint_seq_closed A B hadj)

/-- Part (b): B is continuous. The adjoint relation is symmetric:
    ⟪By, x⟫ = conj⟪x, By⟫ = conj⟪Ax, y⟫ = ⟪y, Ax⟫.
    So B has adjoint A, and the same argument applies. -/
theorem adjoint_map_B_continuous
    (A : X →ₗ[ℂ] X) (B : X →ₗ[ℂ] X)
    (hadj : ∀ x y, @inner ℂ X _ (A x) y = @inner ℂ X _ x (B y)) :
    Continuous B := by
  apply B.continuous_of_seq_closed_graph
  intro u x z hu hBu
  -- B has adjoint A: ⟪By, x⟫ = ⟪y, Ax⟫
  have hadj' : ∀ x y, @inner ℂ X _ (B x) y = @inner ℂ X _ x (A y) := by
    intro a b
    calc @inner ℂ X _ (B a) b
        = starRingEnd ℂ (@inner ℂ X _ b (B a)) := by rw [inner_conj_symm]
      _ = starRingEnd ℂ (@inner ℂ X _ (A b) a) := by rw [← hadj b a]
      _ = @inner ℂ X _ a (A b) := by rw [inner_conj_symm]
  exact adjoint_seq_closed B A hadj' u x z hu hBu
