import Mathlib

/-! Genuine alternating coordinate forms on R3, and pullback integration on
an oriented parameter rectangle. The exterior derivative is Mathlib.extDeriv,
not a separately assumed scalar operation. Geometric consumers must identify
the parametrized image and its orientation; this is not an intrinsic arbitrary-
manifold integration library. -/

noncomputable section
namespace ConstructionTargets.CoordinateSurfaceForms
abbrev V := Fin 3 → ℝ
abbrev Parameters := Fin 2 → ℝ
abbrev TwoForm := V → V [⋀^Fin 2]→L[ℝ] ℝ

def coordinateProjection (i j : Fin 3) : V →ₗ[ℝ] Parameters where
  toFun x := ![x i, x j]
  map_add' x y := by ext k; fin_cases k <;> rfl
  map_smul' c x := by ext k; fin_cases k <;> rfl

/-- dx_i wedge dx_j, including the zero form when i=j. -/
def coordinateWedge (i j : Fin 3) : V [⋀^Fin 2]→L[ℝ] ℝ where
  toAlternatingMap := Matrix.detRowAlternating.compLinearMap (coordinateProjection i j)
  cont := by
    change Continuous (fun v : Fin 2 → V => Matrix.det (fun k => coordinateProjection i j (v k)))
    unfold coordinateProjection
    fun_prop

def volumeForm : V [⋀^Fin 3]→L[ℝ] ℝ where
  toAlternatingMap := Matrix.detRowAlternating
  cont := by change Continuous (fun v : Fin 3 → V => Matrix.det v); fun_prop

def pullbackCoefficient (ω : TwoForm) (φ : Parameters → V) (p : Parameters) : ℝ :=
  ω (φ p) ![fderiv ℝ φ p (Pi.single 0 1), fderiv ℝ φ p (Pi.single 1 1)]

/-- Parameter orientation is dθ wedge dz, with θ the first coordinate. -/
def rectangleIntegral (ω : TwoForm) (φ : Parameters → V)
    (θ₀ θ₁ z₀ z₁ : ℝ) : ℝ :=
  ∫ z in z₀..z₁, ∫ θ in θ₀..θ₁, pullbackCoefficient ω φ ![θ, z]

end ConstructionTargets.CoordinateSurfaceForms
