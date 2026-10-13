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
def apm_t94a06_transverse_ae_of_regularValues_aux_proj :
    apm_t94a06_E3 →L[ℝ] apm_t94a06_E2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 2 ↦
      (ContinuousLinearMap.proj (R := ℝ) (Fin.castSucc i)).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).toContinuousLinearMap))

set_option backward.isDefEq.respectTransparency false in
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
  have hs : ∀ᵐ s : apm_t94a06_E2,
      ∀ x : X, apm_t94a06_normalPart f x = -s →
        Function.Surjective
          (mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E2)
            (apm_t94a06_normalPart f) x) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure apm_t94a06_E2)).map_eq] at hregular
    exact ae_of_ae_map measurable_neg.aemeasurable hregular
  filter_upwards [hs] with s hs
  intro x hx
  have hnormal : apm_t94a06_normalPart f x = -s := by
    ext i
    fin_cases i
    · simp [apm_t94a06_normalPart, apm_t94a06_family,
        apm_t94a06_normalTranslation, apm_t94a06_zAxis] at hx ⊢
      exact eq_neg_of_add_eq_zero_left hx.1
    · simp [apm_t94a06_normalPart, apm_t94a06_family,
        apm_t94a06_normalTranslation, apm_t94a06_zAxis] at hx ⊢
      exact eq_neg_of_add_eq_zero_left hx.2
  have hproj : apm_t94a06_normalPart f =
      apm_t94a06_transverse_ae_of_regularValues_aux_proj ∘ f := by
    funext z
    ext i
    fin_cases i <;> rfl
  have hderiv :
      mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E2)
          (apm_t94a06_normalPart f) x =
        apm_t94a06_transverse_ae_of_regularValues_aux_proj.comp
          (mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E3) f x) := by
    rw [hproj, mfderiv_comp x
      ((apm_t94a06_transverse_ae_of_regularValues_aux_proj.contMDiff.mdifferentiable
        (n := ∞) (by simp)) (f x))
      ((hf.mdifferentiable (by simp)) x)]
    rw [apm_t94a06_transverse_ae_of_regularValues_aux_proj.hasFDerivAt.hasMFDerivAt.mfderiv]
  rw [apm_t94a06_mfderiv_family I f hf s x]
  apply Submodule.eq_top_iff'.2
  intro z
  let z' : apm_t94a06_E3 := NormedSpace.fromTangentSpace _ z
  obtain ⟨v, hv⟩ := hs x hnormal
    (WithLp.toLp 2 ![z' 0, z' 1] : apm_t94a06_E2)
  let w := (mfderiv I (modelWithCornersSelf ℝ apm_t94a06_E3) f x) v
  let w' : apm_t94a06_E3 := NormedSpace.fromTangentSpace _ w
  refine Submodule.mem_sup.2 ⟨w, ⟨v, rfl⟩,
    (z' 2 - w' 2) • EuclideanSpace.single (2 : Fin 3) 1, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply (NormedSpace.fromTangentSpace _).injective
    ext i
    fin_cases i
    · have := congrArg (fun q : apm_t94a06_E2 ↦ q 0) hv
      have hw : w' 0 = z' 0 := by
        simpa [hderiv, w, w', z', NormedSpace.fromTangentSpace,
          apm_t94a06_transverse_ae_of_regularValues_aux_proj] using this
      change w' 0 + (z' 2 - w' 2) * 0 = z' 0
      simpa using hw
    · have := congrArg (fun q : apm_t94a06_E2 ↦ q 1) hv
      have hw : w' 1 = z' 1 := by
        simpa [hderiv, w, w', z', NormedSpace.fromTangentSpace,
          apm_t94a06_transverse_ae_of_regularValues_aux_proj] using this
      change w' 1 + (z' 2 - w' 2) * 0 = z' 1
      simpa using hw
    · change w' 2 + (z' 2 - w' 2) * 1 = z' 2
      ring

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
