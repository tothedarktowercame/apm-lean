import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

open scoped Manifold
noncomputable section

abbrev apm_t01J06_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01J06_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t01J06_S1 := Metric.sphere (0 : apm_t01J06_E2) 1
abbrev apm_t01J06_S2 := Metric.sphere (0 : apm_t01J06_E3) 1
def apm_t01J06_sphereTangent (q : apm_t01J06_S2) : Submodule ℝ apm_t01J06_E3 :=
  (Submodule.span ℝ ({(q : apm_t01J06_E3)} : Set apm_t01J06_E3)).orthogonal
def apm_t01J06_circleTangent (p : apm_t01J06_S1) : Submodule ℝ apm_t01J06_E2 :=
  (Submodule.span ℝ ({(p : apm_t01J06_E2)} : Set apm_t01J06_E2)).orthogonal
abbrev apm_t01J06_SphereForm2 := ∀ q : apm_t01J06_S2,
  apm_t01J06_sphereTangent q [⋀^Fin 2]→L[ℝ] ℝ
abbrev apm_t01J06_ProductForm2 := ∀ qp : apm_t01J06_S2 × apm_t01J06_S1,
  (apm_t01J06_sphereTangent qp.1 × apm_t01J06_circleTangent qp.2) [⋀^Fin 2]→L[ℝ] ℝ
def apm_t01J06_isJPullback (p : apm_t01J06_S1) (zeta : apm_t01J06_ProductForm2)
    (alpha : apm_t01J06_SphereForm2) : Prop :=
  ∀ q v, zeta (q,p) (fun k ↦ (v k, 0)) = alpha q v
def apm_t01J06_projectionPullback (alpha : apm_t01J06_SphereForm2) :
    apm_t01J06_ProductForm2 := fun qp ↦ (alpha qp.1).compContinuousLinearMap
  (ContinuousLinearMap.fst ℝ _ _)

-- The old part (c) has a witness for every sphere form, without any regularity
-- or closedness assumption.  Thus it cannot encode the requested closed form.
example (alpha : apm_t01J06_SphereForm2) (p : apm_t01J06_S1) :
    ∃ zeta : apm_t01J06_ProductForm2,
      zeta = apm_t01J06_projectionPullback alpha ∧
      apm_t01J06_isJPullback p zeta alpha :=
  ⟨apm_t01J06_projectionPullback alpha, rfl, by intro q v; rfl⟩
