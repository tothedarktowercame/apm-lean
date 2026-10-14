import Mathlib

open scoped ContDiff Manifold

noncomputable section

def apm_t91a01_vectorField (z : ℂ) : ℂ := z ^ 3

abbrev apm_t91a01_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t91a01_Model2 := 𝓘(ℝ, apm_t91a01_E2)
abbrev apm_t91a01_Disk2 := Metric.closedBall (0 : ℂ) 1
abbrev apm_t91a01_Circle := Metric.sphere (0 : ℂ) 1

def apm_t91a01_oriented
    (F : Type*) [TopologicalSpace F] : Prop :=
  ∃ atlas : Set (OpenPartialHomeomorph F apm_t91a01_E2),
    (∀ x : F, ∃ c ∈ atlas, x ∈ c.source) ∧
    ∀ c ∈ atlas, ∀ d ∈ atlas, ∀ x ∈ c.source ∩ d.source,
      0 < (LinearMap.det : (apm_t91a01_E2 →ₗ[ℝ] apm_t91a01_E2) →* ℝ)
        (fderiv ℝ (fun y ↦ d (c.symm y)) (c x))

def apm_t91a01_chartField
    {F : Type*} [TopologicalSpace F] [ChartedSpace apm_t91a01_E2 F]
    (V : (x : F) → TangentSpace apm_t91a01_Model2 x) (p : F)
    (y : apm_t91a01_E2) : apm_t91a01_E2 :=
  mfderiv apm_t91a01_Model2 apm_t91a01_Model2 (extChartAt apm_t91a01_Model2 p)
    ((extChartAt apm_t91a01_Model2 p).symm y)
    (V ((extChartAt apm_t91a01_Model2 p).symm y))

abbrev apm_t91a01_planeEquiv : ℂ ≃ₗᵢ[ℝ] apm_t91a01_E2 :=
  Complex.orthonormalBasisOneI.repr

def apm_t91a01_circlePoint
    {F : Type*} [TopologicalSpace F] [ChartedSpace apm_t91a01_E2 F]
    (p : F) (r : ℝ) (z : apm_t91a01_Circle) : apm_t91a01_E2 :=
  extChartAt apm_t91a01_Model2 p p + r • apm_t91a01_planeEquiv z.1

def apm_t91a01_cube : C(apm_t91a01_Circle, apm_t91a01_Circle) where
  toFun z := ⟨z.1 ^ 3, by
    simpa [Metric.mem_sphere, norm_pow] using congrArg (fun r : ℝ ↦ r ^ 3) z.2⟩
  continuous_toFun := by fun_prop

def apm_t91a01_hasIndexThreeZero
    {F : Type*} [TopologicalSpace F] [ChartedSpace apm_t91a01_E2 F]
    (V : (x : F) → TangentSpace apm_t91a01_Model2 x) (p : F) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Metric.closedBall (extChartAt apm_t91a01_Model2 p p) r ⊆
      (extChartAt apm_t91a01_Model2 p).target ∧
    ∃ link : C(apm_t91a01_Circle, apm_t91a01_Circle),
      (∀ z : apm_t91a01_Circle,
        ∃ hw : apm_t91a01_planeEquiv.symm
            (apm_t91a01_chartField V p (apm_t91a01_circlePoint p r z)) ≠ 0,
          (link z).1 =
            apm_t91a01_planeEquiv.symm
                (apm_t91a01_chartField V p (apm_t91a01_circlePoint p r z)) /
              (‖apm_t91a01_planeEquiv.symm
                (apm_t91a01_chartField V p (apm_t91a01_circlePoint p r z))‖ : ℂ)) ∧
      ContinuousMap.Homotopic link apm_t91a01_cube

lemma apm_t91a01_vectorField_zero_iff (z : ℂ) :
    apm_t91a01_vectorField z = 0 ↔ z = 0 := by
  simp [apm_t91a01_vectorField]

lemma apm_t91a01_vectorField_on_unit_circle (θ : ℝ) :
    apm_t91a01_vectorField (Complex.exp (Complex.I * (θ : ℂ))) =
      Complex.exp (Complex.I * ((3 * θ : ℝ) : ℂ)) := by
  simp only [apm_t91a01_vectorField]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- LIBRARY: the surface Poincaré--Hopf theorem, including identification of
the chart-boundary homotopy to `z ↦ z³` with local index `3`, and evenness of
the Euler characteristic of a compact connected oriented closed surface. -/
theorem apm_t91a01_index_three_forces_other_zero
    (F : Type*) [TopologicalSpace F] [T2Space F]
    [SecondCountableTopology F] [CompactSpace F] [ConnectedSpace F]
    [ChartedSpace apm_t91a01_E2 F]
    [IsManifold apm_t91a01_Model2 ∞ F]
    [BoundarylessManifold apm_t91a01_Model2 F]
    (hOrient : apm_t91a01_oriented F)
    (V : (x : F) → TangentSpace apm_t91a01_Model2 x) (p : F)
    (hV : ContMDiff apm_t91a01_Model2 apm_t91a01_Model2.tangent ∞
      (fun x ↦ (⟨x, V x⟩ : TangentBundle apm_t91a01_Model2 F)))
    (hp : V p = 0)
    (hisolated : ∃ U ∈ nhds p, ∀ q ∈ U, V q = 0 → q = p)
    (hindex : apm_t91a01_hasIndexThreeZero V p) :
    ∃ q : F, q ≠ p ∧ V q = 0 := by
  sorry

theorem apm_t91a01 :
    (∀ z : ℂ, apm_t91a01_vectorField z = 0 ↔ z = 0) ∧
    (∀ θ : ℝ,
      apm_t91a01_vectorField (Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.exp (Complex.I * ((3 * θ : ℝ) : ℂ))) ∧
    ∀ (F : Type*) [TopologicalSpace F] [T2Space F]
      [SecondCountableTopology F] [CompactSpace F] [ConnectedSpace F]
      [ChartedSpace apm_t91a01_E2 F]
      [IsManifold apm_t91a01_Model2 ∞ F]
      [BoundarylessManifold apm_t91a01_Model2 F]
      (hOrient : apm_t91a01_oriented F)
      (V : (x : F) → TangentSpace apm_t91a01_Model2 x) (p : F),
      ContMDiff apm_t91a01_Model2 apm_t91a01_Model2.tangent ∞
        (fun x ↦ (⟨x, V x⟩ : TangentBundle apm_t91a01_Model2 F)) →
      V p = 0 →
      (∃ U ∈ nhds p, ∀ q ∈ U, V q = 0 → q = p) →
      apm_t91a01_hasIndexThreeZero V p →
      ∃ q : F, q ≠ p ∧ V q = 0 := by
  refine ⟨fun z ↦ apm_t91a01_vectorField_zero_iff z,
    fun θ ↦ apm_t91a01_vectorField_on_unit_circle θ, ?_⟩
  intro F _ _ _ _ _ _ _ _ hOrient V p hV hp hisolated hindex
  exact apm_t91a01_index_three_forces_other_zero
    F hOrient V p hV hp hisolated hindex

#print axioms apm_t91a01
