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

/-- The zero value/gradient pair is represented by the constant zero test
sequence. This is the first closure datum needed for the eventual quotient
Hilbert space. -/
noncomputable def apm_m03J01_zeroH01 (n : ℕ) (Ω : Set (apm_m03J01_E n)) :
    apm_m03J01_H01 n Ω where
  val := 0
  grad := 0
  val_memLp := by simp
  grad_memLp := by simp
  approximable := by
    refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · intro k
      refine ⟨contDiff_const, ?_, ?_⟩
      · exact HasCompactSupport.zero
      · simp
    · simp
    · simp [apm_m03J01_gradient]

/-- Weak formulation of `-Δu + u = F` with zero Dirichlet boundary data. -/
def apm_m03J01_weakSolution {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (F : apm_m03J01_E n → ℝ) (u : apm_m03J01_H01 n Ω) : Prop :=
  ∀ v : apm_m03J01_H01 n Ω,
    ∫ x, (inner ℝ (u.grad x) (v.grad x) + u.val x * v.val x) ∂volume =
      ∫ x, F x * v.val x ∂volume

lemma apm_m03J01_weakSolution_zero_iff {n : ℕ} {Ω : Set (apm_m03J01_E n)}
    (F : apm_m03J01_E n → ℝ) :
    apm_m03J01_weakSolution F (apm_m03J01_zeroH01 n Ω) ↔
      ∀ v : apm_m03J01_H01 n Ω, ∫ x, F x * v.val x ∂volume = 0 := by
  simp only [apm_m03J01_weakSolution, apm_m03J01_zeroH01, Pi.zero_apply,
    inner_zero_left, zero_mul, zero_add, integral_zero]
  constructor
  · intro h v
    exact (h v).symm
  · intro h v
    exact (h v).symm

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

/-- The zero representative has the zero weak Hessian. This is the origin
needed by a future closed weak-Hessian graph construction. -/
lemma apm_m03J01_zero_weakHessian (n : ℕ) (Ω : Set (apm_m03J01_E n)) :
    apm_m03J01_weakHessian (apm_m03J01_zeroH01 n Ω).grad
      (0 : apm_m03J01_E n → Fin n → Fin n → ℝ) := by
  constructor
  · simp
  · intro i j φ hφ hφc
    simp [apm_m03J01_zeroH01]

lemma apm_m03J01_zero_H2size (n : ℕ) (Ω : Set (apm_m03J01_E n)) :
    apm_m03J01_H2size (apm_m03J01_zeroH01 n Ω)
      (0 : apm_m03J01_E n → Fin n → Fin n → ℝ) = 0 := by
  simp [apm_m03J01_H2size, apm_m03J01_zeroH01]

/-- The continuous Fréchet--Riesz solution operator used in the theorem's
abstract Hilbert-space clause. -/
noncomputable def apm_m03J01_riesz
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] : (V →L[ℝ] ℝ) →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma apm_m03J01_inner_riesz
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V →L[ℝ] ℝ) (v : V) :
    inner ℝ (apm_m03J01_riesz V f) v = f v := by
  exact InnerProductSpace.toDual_symm_apply

lemma apm_m03J01_abstract_variational :
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [CompleteSpace V],
      ∃ T : (V →L[ℝ] ℝ) →L[ℝ] V, ∀ f : V →L[ℝ] ℝ,
        (∃ C : ℝ, ∀ v : V, C ≤ (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ v : V,
          (2 : ℝ)⁻¹ * ‖T f‖ ^ 2 - f (T f) ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧
        (∀ u : V,
          (∀ v : V, (2 : ℝ)⁻¹ * ‖u‖ ^ 2 - f u ≤
            (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) → u = T f) ∧
        (∀ v : V, inner ℝ (T f) v = f v) := by
  intro V _ _ _
  let T := apm_m03J01_riesz V
  refine ⟨T, ?_⟩
  intro f
  have hinner (v : V) : inner ℝ (T f) v = f v :=
    apm_m03J01_inner_riesz f v
  have henergy (v : V) :
      (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v =
        (2 : ℝ)⁻¹ * ‖v - T f‖ ^ 2 - (2 : ℝ)⁻¹ * ‖T f‖ ^ 2 := by
    rw [← hinner v, norm_sub_sq_real, real_inner_comm]
    ring
  refine ⟨?_, ?_, ?_, hinner⟩
  · refine ⟨-(2 : ℝ)⁻¹ * ‖T f‖ ^ 2, ?_⟩
    intro v
    rw [henergy]
    nlinarith [sq_nonneg ‖v - T f‖]
  · intro v
    rw [henergy, henergy]
    simp
  · intro u hu
    have hle := hu (T f)
    rw [henergy, henergy] at hle
    have hs : 0 ≤ ‖u - T f‖ ^ 2 := sq_nonneg _
    have hz : ‖u - T f‖ = 0 := by
      simp only [sub_self, norm_zero] at hle
      nlinarith [norm_nonneg (u - T f)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

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
  CLOSER HOP 1 (partial). The continuous Fréchet--Riesz solution operator is
  now constructed as `apm_m03J01_riesz`, and
  `apm_m03J01_inner_riesz` proves its exact defining identity. The helper
  `apm_m03J01_abstract_variational` then completes the theorem's entire first
  conjunct by the Hilbert norm-square identity, including boundedness below,
  minimization, and uniqueness.

  The custom Sobolev-space boundary remains. Mathlib supplies the abstract
  ingredients `InnerProductSpace.toDual` (Fréchet–Riesz) and
  `LinearMap.continuous_of_seq_closed_graph`. However, the PDE clauses use the
  bespoke representative record `apm_m03J01_H01`, which has no additive,
  normed, inner-product, or complete-space instances and is not quotiented by
  a.e. equality. Thus the abstract Riesz map cannot be instantiated on it.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, solved PDE
  artifacts, Mathlib's Lax--Milgram and Sobolev sources, and git history found
  no implementation of the required custom quotient. A proof must first
  construct the Hilbert-space quotient of value/gradient
  pairs satisfying `approximable`, prove completeness and compatibility of its
  energy inner product with the displayed integrals, lift `F ↦ ∫ Fv` as a
  continuous functional, and descend the resulting solution back to the record.
  The final clause additionally needs a Banach space of weak-Hessian classes,
  uniqueness modulo a.e. equality, continuity of the embedding to the energy
  space, and a closed-graph argument producing the ENNReal estimate. Searches
  found no compiled sibling connecting these APIs to this custom encoding, so
  no sibling code was reused and the frozen statement was left unchanged.

  Closer hop 2 begins the missing custom-space construction rather than only
  surveying quotient APIs. `apm_m03J01_zeroH01` builds the zero Sobolev
  representative with the constant zero test-function approximation, proving
  the record is inhabited for every `n` and `Ω` and supplying the additive
  identity needed by a future quotient. `apm_m03J01_weakSolution_zero_iff`
  also computes its weak equation exactly: zero is a solution precisely when
  the forcing functional vanishes on every custom test representative.
  Further inspection of `AEEqFun`, `Lp`, product Hilbert spaces, and closed
  submodules found reusable ambient structures, but the record's
  `approximable` predicate must still be shown closed under addition/scaling
  and identified with a closed subspace before those structures apply. The
  forcing functional and weak-Hessian closed-graph estimate remain open.

  Closer hop 3 also begins the weak-Hessian graph at its origin:
  `apm_m03J01_zero_weakHessian` proves directly from the distributional
  definition that the zero representative has zero weak Hessian, and
  `apm_m03J01_zero_H2size` computes its exact size as zero. Together with the
  hop-2 zero `H₀¹` representative, both the energy space and proposed graph
  space now have compiled origins. Searches were extended to graph subspaces,
  closed operators, distributional derivatives, `MemLp` addition/scaling,
  and analogous custom Sobolev records in `m00A04`; none supplies closure of
  this record's approximation witnesses or the completeness/closed-graph
  assembly. The nonzero additive/scalar cases and both PDE conclusions remain
  honestly open.
  -/
  sorry
