import Mathlib

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t94a06_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t94a06_E3 := EuclideanSpace ℝ (Fin 3)

def apm_t94a06_zAxis : Set apm_t94a06_E3 :=
  {y | y 0 = 0 ∧ y 1 = 0}

def apm_t94a06_normalTranslation (s : apm_t94a06_E2) : apm_t94a06_E3 :=
  WithLp.toLp 2 ![s 0, s 1, 0]

def apm_t94a06_family {X : Type*} (f : X → apm_t94a06_E3)
    (s : apm_t94a06_E2) (x : X) : apm_t94a06_E3 :=
  f x + apm_t94a06_normalTranslation s

def apm_t94a06_normalPart {X : Type*} (f : X → apm_t94a06_E3)
    (x : X) : apm_t94a06_E2 :=
  WithLp.toLp 2 ![f x 0, f x 1]

def apm_t94a06_IsTransverseToZAxis
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace X] [ChartedSpace H X]
    (h : X → apm_t94a06_E3) : Prop :=
  ∀ x : X, h x ∈ apm_t94a06_zAxis →
    LinearMap.range
        (mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E3) h x).toLinearMap ⊔
      Submodule.span ℝ
        ({EuclideanSpace.single (2 : Fin 3) 1} : Set apm_t94a06_E3) = ⊤

lemma apm_t94a06_family_zero {X : Type*} (f : X → apm_t94a06_E3) :
    apm_t94a06_family f 0 = f := by
  funext x
  simp [apm_t94a06_family, apm_t94a06_normalTranslation]

lemma apm_t94a06_mfderiv_family
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I (modelWithCornersSelf ℝ apm_t94a06_E3) ∞ f)
    (s : apm_t94a06_E2) (x : X) :
    mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E3) (apm_t94a06_family f s) x =
      mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E3) f x := by
  rw [show apm_t94a06_family f s = f + fun _ ↦ apm_t94a06_normalTranslation s by rfl]
  rw [mfderiv_add ((hf.mdifferentiable (by simp)) x) mdifferentiableAt_const]
  simp
  rfl

/-- LIBRARY (Morse--Sard for finite-dimensional manifolds with corners):
almost every point of the normal plane is a regular value of the normal part. -/
theorem apm_t94a06_ae_regularValue_normalPart
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    [SecondCountableTopology X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I (modelWithCornersSelf ℝ apm_t94a06_E3) ∞ f) :
    ∀ᵐ y : apm_t94a06_E2,
      ∀ x : X, apm_t94a06_normalPart f x = y →
        Function.Surjective
          (mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E2)
            (apm_t94a06_normalPart f) x) := by
  sorry

/-- The regular-value formulation for the first two coordinates implies
transversality of the corresponding translated slice to the z-axis. -/
theorem apm_t94a06_transverse_ae_of_regularValues
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I (modelWithCornersSelf ℝ apm_t94a06_E3) ∞ f)
    (hregular : ∀ᵐ y : apm_t94a06_E2,
      ∀ x : X, apm_t94a06_normalPart f x = y →
        Function.Surjective
          (mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E2)
            (apm_t94a06_normalPart f) x)) :
    ∀ᵐ s : apm_t94a06_E2,
      apm_t94a06_IsTransverseToZAxis I (apm_t94a06_family f s) := by
  sorry

theorem apm_t94a06
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X]
    [SecondCountableTopology X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X] (f : X → apm_t94a06_E3)
    (hf : ContMDiff I (modelWithCornersSelf ℝ apm_t94a06_E3) ∞ f) :
    apm_t94a06_family f 0 = f ∧
      ∀ᵐ s : apm_t94a06_E2,
        apm_t94a06_IsTransverseToZAxis I (apm_t94a06_family f s) := by
  refine ⟨apm_t94a06_family_zero f, ?_⟩
  exact apm_t94a06_transverse_ae_of_regularValues I f hf
    (apm_t94a06_ae_regularValue_normalPart I f hf)

#print axioms apm_t94a06
