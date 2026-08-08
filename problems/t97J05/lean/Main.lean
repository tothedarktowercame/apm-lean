import Mathlib

/-!
# APM t97J05 — a regular fiber and its local normal form

## Statement repairs

Part (c) prints `φ` as a map from a neighborhood of the origin in `ℝ²`
to a neighborhood of `p ∈ ℝ³`, but then evaluates it at `(x,y,z)`.
Its domain is minimally corrected to a neighborhood of the origin in `ℝ³`.

The former opaque submanifold predicate is replaced by an actual
one-dimensional smooth manifold structure on the fiber subtype whose
inclusion into `ℝ³` is both smooth and a topological embedding.

## Encoding questions

Euclidean spaces are encoded as `EuclideanSpace ℝ (Fin n)`. The Jacobian
is stated by its action on every tangent vector. The fiber is the actual
preimage set, and its requested explicit local parameterization is a smooth
bijection from `(1/2,3/2)` onto the corresponding neighborhood in the fiber.
Local diffeomorphisms are actual `LocalHomeomorph`s with smooth forward and
inverse maps.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t97J05_R3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t97J05_R2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t97J05_R1 := EuclideanSpace ℝ (Fin 1)

def apm_t97J05_f (q : apm_t97J05_R3) : apm_t97J05_R2 :=
  WithLp.toLp 2 ![Real.exp (q 0) * Real.cos (q 1), q 0 * q 2]

def apm_t97J05_p : apm_t97J05_R3 :=
  WithLp.toLp 2 ![(1 : ℝ), Real.pi / 2, 1]

def apm_t97J05_value : apm_t97J05_R2 :=
  WithLp.toLp 2 ![(0 : ℝ), 1]

def apm_t97J05_W : Set apm_t97J05_R3 :=
  apm_t97J05_f ⁻¹' {apm_t97J05_value}

/-- The explicit curve `t ↦ (t, π/2, 1/t)` in the fiber. -/
def apm_t97J05_gamma (t : ℝ) : apm_t97J05_R3 :=
  WithLp.toLp 2 ![t, Real.pi / 2, 1 / t]

def apm_t97J05_parameterDomain : Set ℝ :=
  Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)

def apm_t97J05_parameterTarget : Set apm_t97J05_R3 :=
  {q | q ∈ apm_t97J05_W ∧ q 0 ∈ apm_t97J05_parameterDomain ∧
    q 1 ∈ Ioo (0 : ℝ) Real.pi}

def apm_t97J05_IsSmoothSubmanifold
    (s : Set apm_t97J05_R3) : Prop :=
  ∃ charts : ChartedSpace apm_t97J05_R1 s,
    let _ := charts
    IsManifold (𝓘(ℝ, apm_t97J05_R1)) (⊤ : ℕ∞) s ∧
      ContMDiff (𝓘(ℝ, apm_t97J05_R1)) (𝓘(ℝ, apm_t97J05_R3))
        (⊤ : ℕ∞) (Subtype.val : s → apm_t97J05_R3) ∧
      Topology.IsEmbedding (Subtype.val : s → apm_t97J05_R3)

lemma apm_t97J05_f_gamma_eq_value {t : ℝ}
    (ht : t ∈ apm_t97J05_parameterDomain) :
    apm_t97J05_f (apm_t97J05_gamma t) = apm_t97J05_value := by
  have ht0 : t ≠ 0 := by
    dsimp [apm_t97J05_parameterDomain] at ht
    linarith [ht.1]
  ext i
  fin_cases i <;>
    simp [apm_t97J05_f, apm_t97J05_gamma, apm_t97J05_value, ht0,
      Real.cos_pi_div_two]

lemma apm_t97J05_gamma_mem_parameterTarget {t : ℝ}
    (ht : t ∈ apm_t97J05_parameterDomain) :
    apm_t97J05_gamma t ∈ apm_t97J05_parameterTarget := by
  refine ⟨?_, ht, ?_⟩
  · exact apm_t97J05_f_gamma_eq_value ht
  · simp [apm_t97J05_gamma, Real.pi_pos]

lemma apm_t97J05_gamma_injOn :
    Set.InjOn apm_t97J05_gamma apm_t97J05_parameterDomain := by
  intro x hx y hy hxy
  have := congrArg (fun q : apm_t97J05_R3 ↦ q 0) hxy
  simpa [apm_t97J05_gamma] using this

lemma apm_t97J05_gamma_surjOn :
    Set.SurjOn apm_t97J05_gamma apm_t97J05_parameterDomain
      apm_t97J05_parameterTarget := by
  intro q hq
  refine ⟨q 0, hq.2.1, ?_⟩
  have hfq : apm_t97J05_f q = apm_t97J05_value := hq.1
  have hfirst := congrArg (fun u : apm_t97J05_R2 ↦ u 0) hfq
  have hsecond := congrArg (fun u : apm_t97J05_R2 ↦ u 1) hfq
  have hcos : Real.cos (q 1) = 0 := by
    simpa [apm_t97J05_f, apm_t97J05_value, Real.exp_ne_zero] using hfirst
  have hy : q 1 = Real.pi / 2 := by
    apply Real.strictAntiOn_cos.injOn
    · exact ⟨le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩
    · constructor <;> linarith [Real.pi_pos]
    · simpa [hcos, Real.cos_pi_div_two]
  have hx0 : q 0 ≠ 0 := by
    have hxpos : 0 < q 0 := lt_trans (by norm_num) hq.2.1.1
    exact ne_of_gt hxpos
  ext i
  fin_cases i
  · simp [apm_t97J05_gamma]
  · simpa [apm_t97J05_gamma] using hy.symm
  · simp [apm_t97J05_gamma]
    have hmul : q 0 * q 2 = 1 := by
      simpa [apm_t97J05_f, apm_t97J05_value] using hsecond
    rw [inv_eq_one_div]
    apply (div_eq_iff hx0).2
    nlinarith [hmul]

lemma apm_t97J05_gamma_bijOn :
    Set.BijOn apm_t97J05_gamma apm_t97J05_parameterDomain
      apm_t97J05_parameterTarget := by
  refine ⟨?_, apm_t97J05_gamma_injOn, apm_t97J05_gamma_surjOn⟩
  intro t ht
  exact apm_t97J05_gamma_mem_parameterTarget ht

theorem apm_t97j05 :
    (∀ h : apm_t97J05_R3,
      fderiv ℝ apm_t97J05_f apm_t97J05_p h =
        WithLp.toLp 2 ![-Real.exp 1 * h 1, h 0 + h 2]) ∧
    Function.Surjective (fderiv ℝ apm_t97J05_f apm_t97J05_p) ∧
    apm_t97J05_IsSmoothSubmanifold apm_t97J05_W ∧
    ContDiffOn ℝ ∞ apm_t97J05_gamma apm_t97J05_parameterDomain ∧
    Set.BijOn apm_t97J05_gamma
      apm_t97J05_parameterDomain apm_t97J05_parameterTarget ∧
    ∃ (φ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3)
        (ψ : OpenPartialHomeomorph apm_t97J05_R2 apm_t97J05_R2),
      0 ∈ φ.source ∧ φ 0 = apm_t97J05_p ∧
      apm_t97J05_value ∈ ψ.source ∧ ψ apm_t97J05_value = 0 ∧
      ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧
      ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ q ∈ φ.source,
        apm_t97J05_f (φ q) ∈ ψ.source ∧
        ψ (apm_t97J05_f (φ q)) = WithLp.toLp 2 ![q 0, q 1] := by
  /-
  CLOSER HOP 3 boundary: the explicit fiber parameterization is now compiled
  through its full set-theoretic bijection. `apm_t97J05_f_gamma_eq_value`
  proves the curve lies in the frozen fiber; the target-membership and
  injectivity lemmas expose its first coordinate; and
  `apm_t97J05_gamma_surjOn` proves every target point is on the curve. The
  latter extracts `cos (q 1) = 0`, uses strict antitonicity of cosine on
  `[0,π]` to obtain `q 1 = π/2`, and solves `q 0 * q 2 = 1` using the
  positive parameter interval. Thus `apm_t97J05_gamma_bijOn` closes the fifth
  frozen conjunct without a generic regular-value theorem.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's constant-
  rank, inverse-function, `OpenPartialHomeomorph`, regular-level, and subtype-
  manifold APIs, prior regular-value artifacts, and git history found no
  theorem assembling the demanded global manifold structure on the entire
  fiber or the exact pair of smooth open partial homeomorphisms. The remaining
  bridge consists of the derivative computation/surjectivity, smoothness of
  `gamma`, the global fiber manifold instance, and especially the explicit
  local normal-form charts. The frozen statement is unchanged.
  -/
  sorry
