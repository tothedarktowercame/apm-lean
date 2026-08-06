import Mathlib

/-!
# APM m03J01

## Statement repairs

The final item prints `U ∈ H²(U)`; this is repaired to `u ∈ H²(Ω)`, as
required by both the boundary-value problem and its requested conclusion.

## Encoding questions

Mathlib currently has no packaged `H₀¹(Ω)` type. It is encoded here by its
standard definition: `L²` functions with `L²` weak gradient that are limits of
smooth functions compactly supported in `Ω`. The `H²` conclusion is encoded by
an `L²` weak Hessian, and uniqueness is consequently stated up to a.e. equality.
-/

open Filter MeasureTheory Set

abbrev apm_m03J01_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The `i`th coordinate vector in Euclidean `ℝⁿ`. -/
noncomputable def apm_m03J01_basis (n : ℕ) (i : Fin n) : apm_m03J01_E n :=
  EuclideanSpace.single i 1

/-- The classical gradient used for smooth approximants. -/
noncomputable def apm_m03J01_gradient (n : ℕ)
    (u : apm_m03J01_E n → ℝ) (x : apm_m03J01_E n) : apm_m03J01_E n :=
  ∑ i : Fin n,
    fderiv ℝ u x (apm_m03J01_basis n i) • apm_m03J01_basis n i

/-- Smooth functions compactly supported in the domain. -/
def apm_m03J01_testFunction (n : ℕ) (Ω : Set (apm_m03J01_E n))
    (φ : apm_m03J01_E n → ℝ) : Prop :=
  ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ ∧ Function.support φ ⊆ Ω

/-- An explicit representative of an element of `H₀¹(Ω)`. -/
structure apm_m03J01_H01 (n : ℕ) (Ω : Set (apm_m03J01_E n)) where
  val : apm_m03J01_E n → ℝ
  grad : apm_m03J01_E n → apm_m03J01_E n
  val_memLp : MemLp val 2 volume
  grad_memLp : MemLp grad 2 volume
  approximable : ∃ φ : ℕ → apm_m03J01_E n → ℝ,
    (∀ k, apm_m03J01_testFunction n Ω (φ k)) ∧
    Tendsto (fun k ↦ eLpNorm (fun x ↦ φ k x - val x) 2 volume) atTop (nhds 0) ∧
    Tendsto (fun k ↦ eLpNorm
      (fun x ↦ apm_m03J01_gradient n (φ k) x - grad x) 2 volume) atTop (nhds 0)

/-- Weak formulation of `-Δu + u = F` with zero Dirichlet boundary data. -/
def apm_m03J01_weakSolution {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (F : apm_m03J01_E n → ℝ) (u : apm_m03J01_H01 n Ω) : Prop :=
  ∀ v : apm_m03J01_H01 n Ω,
    ∫ x, (inner ℝ (u.grad x) (v.grad x) + u.val x * v.val x) ∂volume =
      ∫ x, F x * v.val x ∂volume

/-- `H` is the weak Hessian of the weak gradient `g`. -/
def apm_m03J01_weakHessian {n : ℕ}
    (g : apm_m03J01_E n → apm_m03J01_E n)
    (H : apm_m03J01_E n → Fin n → Fin n → ℝ) : Prop :=
  MemLp H 2 volume ∧
  ∀ (i j : Fin n) (φ : apm_m03J01_E n → ℝ),
    ContDiff ℝ ⊤ φ → HasCompactSupport φ →
    ∫ x, g x i * fderiv ℝ φ x (apm_m03J01_basis n j) ∂volume =
      -∫ x, H x i j * φ x ∂volume

/-- The explicit `H²` size of a representative and a weak Hessian. -/
noncomputable def apm_m03J01_H2size {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (u : apm_m03J01_H01 n Ω)
    (H : apm_m03J01_E n → Fin n → Fin n → ℝ) : ENNReal :=
  eLpNorm u.val 2 volume + eLpNorm u.grad 2 volume + eLpNorm H 2 volume

theorem apm_m03j01 :
    (∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [CompleteSpace V],
      ∃ T : (V →L[ℝ] ℝ) →L[ℝ] V, ∀ f : V →L[ℝ] ℝ,
        (∃ C : ℝ, ∀ v : V, C ≤ (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ v : V,
          (2 : ℝ)⁻¹ * ‖T f‖ ^ 2 - f (T f) ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ u : V,
          (∀ v : V, (2 : ℝ)⁻¹ * ‖u‖ ^ 2 - f u ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) → u = T f) ∧
        (∀ v : V, inner ℝ (T f) v = f v)) ∧
    (∀ (n : ℕ) (Ω : Set (apm_m03J01_E n)),
      IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      ∀ F : apm_m03J01_E n → ℝ, MemLp F 2 volume →
        ∃ u : apm_m03J01_H01 n Ω,
          apm_m03J01_weakSolution F u ∧
          ∀ v : apm_m03J01_H01 n Ω,
            apm_m03J01_weakSolution F v → u.val =ᵐ[volume] v.val) ∧
    (∀ (n : ℕ) (Ω : Set (apm_m03J01_E n)),
      IsOpen Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      (∀ (F : apm_m03J01_E n → ℝ) (hF : MemLp F 2 volume)
        (u : apm_m03J01_H01 n Ω), apm_m03J01_weakSolution F u →
          ∃ H, apm_m03J01_weakHessian u.grad H) →
      ∃ C : ENNReal, C < ⊤ ∧
        ∀ (F : apm_m03J01_E n → ℝ) (hF : MemLp F 2 volume)
          (u : apm_m03J01_H01 n Ω), apm_m03J01_weakSolution F u →
            ∃ H, apm_m03J01_weakHessian u.grad H ∧
              apm_m03J01_H2size u H ≤ C * eLpNorm F 2 volume) := by
  /-
  SKIPPED (custom Sobolev-space structure boundary). Mathlib supplies the
  abstract ingredients `InnerProductSpace.toDual` (Fréchet–Riesz) and
  `LinearMap.continuous_of_seq_closed_graph`. However, the PDE clauses use the
  bespoke representative record `apm_m03J01_H01`, which has no additive,
  normed, inner-product, or complete-space instances and is not quotiented by
  a.e. equality. Thus the abstract Riesz map cannot be instantiated on it.

  A proof must first construct the Hilbert-space quotient of value/gradient
  pairs satisfying `approximable`, prove completeness and compatibility of its
  energy inner product with the displayed integrals, lift `F ↦ ∫ Fv` as a
  continuous functional, and descend the resulting solution back to the record.
  The final clause additionally needs a Banach space of weak-Hessian classes,
  uniqueness modulo a.e. equality, continuity of the embedding to the energy
  space, and a closed-graph argument producing the ENNReal estimate. Searches
  found no compiled sibling connecting these APIs to this custom encoding, so
  no sibling code was reused and the frozen statement was left unchanged.
  -/
  sorry
