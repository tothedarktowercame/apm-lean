import Mathlib

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

def apm_t97J05_gamma (t : ℝ) : apm_t97J05_R3 :=
  WithLp.toLp 2 ![t, Real.pi / 2, 1 / t]

def apm_t97J05_parameterDomain : Set ℝ := Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)

def apm_t97J05_parameterTarget : Set apm_t97J05_R3 :=
  {q | q ∈ apm_t97J05_W ∧ q 0 ∈ apm_t97J05_parameterDomain ∧
    q 1 ∈ Ioo (0 : ℝ) Real.pi}

/-- A genuine embedded smooth one-manifold: the added differential condition
rules out parametrized corners whose inclusion is smooth but not immersive. -/
def apm_t97J05_IsSmoothSubmanifold (s : Set apm_t97J05_R3) : Prop :=
  ∃ charts : ChartedSpace apm_t97J05_R1 s,
    let _ := charts
    IsManifold (𝓘(ℝ, apm_t97J05_R1)) (⊤ : ℕ∞) s ∧
      ContMDiff (𝓘(ℝ, apm_t97J05_R1)) (𝓘(ℝ, apm_t97J05_R3))
        (⊤ : ℕ∞) (Subtype.val : s → apm_t97J05_R3) ∧
      Topology.IsEmbedding (Subtype.val : s → apm_t97J05_R3) ∧
      ∀ x : s, Function.Injective
        (mfderiv (𝓘(ℝ, apm_t97J05_R1)) (𝓘(ℝ, apm_t97J05_R3))
          (Subtype.val : s → apm_t97J05_R3) x)

theorem apm_t97j05 :
    (∀ h : apm_t97J05_R3,
      fderiv ℝ apm_t97J05_f apm_t97J05_p h =
        WithLp.toLp 2 ![-Real.exp 1 * h 1, h 0 + h 2]) ∧
    Function.Surjective (fderiv ℝ apm_t97J05_f apm_t97J05_p) ∧
    apm_t97J05_IsSmoothSubmanifold apm_t97J05_W ∧
    ContDiffOn ℝ ∞ apm_t97J05_gamma apm_t97J05_parameterDomain ∧
    Set.BijOn apm_t97J05_gamma apm_t97J05_parameterDomain apm_t97J05_parameterTarget ∧
    ∃ (φ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3)
        (ψ : OpenPartialHomeomorph apm_t97J05_R2 apm_t97J05_R2),
      0 ∈ φ.source ∧ φ 0 = apm_t97J05_p ∧
      apm_t97J05_value ∈ ψ.source ∧ ψ apm_t97J05_value = 0 ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ q ∈ φ.source,
        apm_t97J05_f (φ q) ∈ ψ.source ∧
        ψ (apm_t97J05_f (φ q)) = WithLp.toLp 2 ![q 0, q 1] := by
  sorry

#print axioms apm_t97j05
