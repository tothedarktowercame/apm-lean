import ConstructionTargets.CircleUniversalCover

open CategoryTheory
open ConstructionTargets.CircleUniversalCover

noncomputable section

namespace ConstructionTargets.CircleMetricFundamentalGroup

/-- The image of the winding-one loop class under a homeomorphism from `X` to
`Circle`, based at the pulled-back point `e.symm 1`. -/
def nonidentityClass_of_homeomorphCircle
    {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ Circle) : FundamentalGroup X (e.symm 1) := by
  let f : C(Circle, X) := e.symm
  exact (FundamentalGroup.map f 1)
    (circleFundamentalGroupMulEquivInt.symm (Multiplicative.ofAdd (1 : ℤ)))

theorem nonidentityClass_ne_one_of_homeomorphCircle
    {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ Circle) :
    nonidentityClass_of_homeomorphCircle e ≠ 1 := by
  let f : C(Circle, X) := e.symm
  let g : C(X, Circle) := e
  let φ := FundamentalGroup.map f 1
  have hφ : Function.Injective φ := by
    intro p q hpq
    have h := congrArg (fun z ↦ (FundamentalGroup.map g (f 1)) z) hpq
    have hcomp : g.comp f = ContinuousMap.id Circle := by
      ext z
      simp [f, g]
    change ((FundamentalGroupoid.map f ⋙ FundamentalGroupoid.map g).map p) =
      ((FundamentalGroupoid.map f ⋙ FundamentalGroupoid.map g).map q) at h
    rw [← FundamentalGroupoid.map_comp, hcomp, FundamentalGroupoid.map_id] at h
    exact h
  let p : FundamentalGroup Circle 1 :=
    circleFundamentalGroupMulEquivInt.symm (Multiplicative.ofAdd (1 : ℤ))
  have hp : p ≠ 1 := by
    intro hp
    have h := congrArg circleFundamentalGroupMulEquivInt hp
    simp [p] at h
  exact fun h => by
    have h' : φ p = φ 1 := by
      simpa [nonidentityClass_of_homeomorphCircle, f, φ] using h
    exact hp (hφ h')

@[reducible] def nontrivial_fundamentalGroup_of_homeomorphCircle
    {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ Circle) :
    Nontrivial (FundamentalGroup X (e.symm 1)) :=
  ⟨⟨nonidentityClass_of_homeomorphCircle e, 1,
    nonidentityClass_ne_one_of_homeomorphCircle e⟩⟩

abbrev MetricCircle := Metric.sphere (0 : ℂ) 1
abbrev NormOneCircle := {z : ℂ // ‖z‖ = 1}

def metricCircleHomeomorphCircle : MetricCircle ≃ₜ Circle :=
  Homeomorph.setCongr (by ext z; rfl)

def normOneCircleHomeomorphMetricCircle : NormOneCircle ≃ₜ MetricCircle :=
  Homeomorph.setCongr (by
    ext z
    constructor <;> intro h
    · simpa [Metric.mem_sphere, dist_zero_right] using h
    · simpa [Metric.mem_sphere, dist_zero_right] using h)

def normOneCircleHomeomorphCircle : NormOneCircle ≃ₜ Circle :=
  normOneCircleHomeomorphMetricCircle.trans metricCircleHomeomorphCircle

theorem metricCircle_symm_one :
    metricCircleHomeomorphCircle.symm 1 = (⟨1, by simp⟩ : MetricCircle) := rfl

theorem normOneCircle_symm_one :
    normOneCircleHomeomorphCircle.symm 1 = (⟨1, by simp⟩ : NormOneCircle) := rfl

noncomputable def metricCircleNonidentityClass :
    FundamentalGroup MetricCircle (⟨1, by simp⟩ : MetricCircle) := by
  simpa [metricCircle_symm_one] using
    (nonidentityClass_of_homeomorphCircle metricCircleHomeomorphCircle)

theorem metricCircleNonidentityClass_ne_one :
    metricCircleNonidentityClass ≠ 1 := by
  simpa [metricCircleNonidentityClass, metricCircle_symm_one] using
    (nonidentityClass_ne_one_of_homeomorphCircle metricCircleHomeomorphCircle)

noncomputable def normOneCircleNonidentityClass :
    FundamentalGroup NormOneCircle (⟨1, by simp⟩ : NormOneCircle) := by
  simpa [normOneCircle_symm_one] using
    (nonidentityClass_of_homeomorphCircle normOneCircleHomeomorphCircle)

theorem normOneCircleNonidentityClass_ne_one :
    normOneCircleNonidentityClass ≠ 1 := by
  simpa [normOneCircleNonidentityClass, normOneCircle_symm_one] using
    (nonidentityClass_ne_one_of_homeomorphCircle normOneCircleHomeomorphCircle)

noncomputable instance metricCircleFundamentalGroupNontrivial :
    Nontrivial (FundamentalGroup MetricCircle (⟨1, by simp⟩ : MetricCircle)) :=
  ⟨⟨metricCircleNonidentityClass, 1, metricCircleNonidentityClass_ne_one⟩⟩

noncomputable instance normOneCircleFundamentalGroupNontrivial :
    Nontrivial (FundamentalGroup NormOneCircle (⟨1, by simp⟩ : NormOneCircle)) :=
  ⟨⟨normOneCircleNonidentityClass, 1, normOneCircleNonidentityClass_ne_one⟩⟩

#print axioms nonidentityClass_ne_one_of_homeomorphCircle
#print axioms metricCircleNonidentityClass_ne_one
#print axioms normOneCircleNonidentityClass_ne_one

end ConstructionTargets.CircleMetricFundamentalGroup
