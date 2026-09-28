import Mathlib

open scoped ContDiff Manifold

noncomputable section

/-!
# APM t91A01 — an index-three zero and the Poincaré–Hopf obstruction

## Statement repairs

Part (b) now quantifies a compact connected oriented smooth surface and a smooth tangent-bundle section; the index-three condition is derived from that section on an embedded local disk.

## Encoding note

Part (a) is encoded by the standard complex model `z ↦ z³`: its only zero is
the origin and its direction on the unit circle is `θ ↦ exp (3 i θ)`.  Part
(b) records exactly the finite-index conclusion of Poincaré–Hopf together with
the classification formula `χ = 2 - 2g`; this avoids pretending that Mathlib
already has a developed index theory for vector fields on surfaces.
-/

def apm_t91a01_vectorField (z : ℂ) : ℂ := z ^ 3

/-- Superseded: part (b) assumed the Poincaré--Hopf sum and contained no surface or vector field. -/
theorem apm_t91a01_previous_encoding :
    (∀ z : ℂ, apm_t91a01_vectorField z = 0 ↔ z = 0) ∧
    (∀ θ : ℝ,
      apm_t91a01_vectorField (Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.exp (Complex.I * ((3 * θ : ℝ) : ℂ))) ∧
    ∀ (α : Type*) [DecidableEq α] (zeros : Finset α) (index : α → ℤ)
      (genus : ℕ) (p : α),
      (∑ q ∈ zeros, index q) = 2 - 2 * (genus : ℤ) →
      p ∈ zeros → index p = 3 →
      ∃ q ∈ zeros, q ≠ p := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simp [apm_t91a01_vectorField]
  · intro θ
    simp only [apm_t91a01_vectorField]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · intro α _ zeros index genus p hsum hp hip
    by_contra hother
    push_neg at hother
    have hzeros : zeros = {p} := by
      ext q
      constructor
      · intro hq
        have hqp := hother q hq
        simpa [hqp]
      · intro hq
        have hqp : q = p := by simpa using hq
        simpa [hqp] using hp
    rw [hzeros] at hsum
    simp [hip] at hsum
    omega

abbrev apm_t91a01_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t91a01_Model2 := 𝓘(ℝ, apm_t91a01_E2)
abbrev apm_t91a01_Disk2 := Metric.closedBall (0 : ℂ) 1
abbrev apm_t91a01_Circle := Metric.sphere (0 : ℂ) 1

/-- An explicit orientation certificate for a two-dimensional tangent space.
The local compatibility condition makes the chosen orientations agree on
neighbouring tangent spaces rather than choosing them independently. -/
def apm_t91a01_oriented
    (F : Type*) [TopologicalSpace F] : Prop :=
  ∃ atlas : Set (OpenPartialHomeomorph F apm_t91a01_E2),
    (∀ x : F, ∃ c ∈ atlas, x ∈ c.source) ∧
    ∀ c ∈ atlas, ∀ d ∈ atlas, ∀ x ∈ c.source ∩ d.source,
      0 < (LinearMap.det : (apm_t91a01_E2 →ₗ[ℝ] apm_t91a01_E2) →* ℝ)
        (fderiv ℝ (fun y ↦ d (c.symm y)) (c x))

/-- The field `V` read in the extended chart at `p`: at a chart point `y`, the
chart's derivative applied to `V` at the corresponding point of `F`. -/
def apm_t91a01_chartField
    {F : Type*} [TopologicalSpace F] [ChartedSpace apm_t91a01_E2 F]
    (V : (x : F) → TangentSpace apm_t91a01_Model2 x) (p : F)
    (y : apm_t91a01_E2) : apm_t91a01_E2 :=
  mfderiv apm_t91a01_Model2 apm_t91a01_Model2 (extChartAt apm_t91a01_Model2 p)
    ((extChartAt apm_t91a01_Model2 p).symm y)
    (V ((extChartAt apm_t91a01_Model2 p).symm y))

/-- Standard identification of the chart plane with `ℂ` (`1 ↦ e₀`, `i ↦ e₁`). -/
abbrev apm_t91a01_planeEquiv : ℂ ≃ₗᵢ[ℝ] apm_t91a01_E2 :=
  Complex.orthonormalBasisOneI.repr

/-- The point of the chart plane at radius `r` in direction `z` around `p`. -/
def apm_t91a01_circlePoint
    {F : Type*} [TopologicalSpace F] [ChartedSpace apm_t91a01_E2 F]
    (p : F) (r : ℝ) (z : apm_t91a01_Circle) : apm_t91a01_E2 :=
  extChartAt apm_t91a01_Model2 p p + r • apm_t91a01_planeEquiv z.1

/-- The degree-three model `z ↦ z³` on the unit circle. -/
def apm_t91a01_cube : C(apm_t91a01_Circle, apm_t91a01_Circle) where
  toFun z := ⟨z.1 ^ 3, by
    simpa [Metric.mem_sphere, norm_pow] using congrArg (fun r : ℝ ↦ r ^ 3) z.2⟩
  continuous_toFun := by fun_prop

/-- The isolated zero `p` has index `+3` (part (a)): in the chart at `p`, on a
circle of some radius `r` whose closed disk lies in the chart, `V` (read through
the chart's derivative) does not vanish, and its normalized direction is a
continuous map of the circle homotopic to `z ↦ z³`, i.e. of degree three. The
chart's own tangent identification is used, so the direction is computed from
`V` alone. -/
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

/-- A local index-three model exists; on a compact connected oriented smooth
surface, a smooth tangent vector field having an isolated zero whose actual
normalized boundary direction has degree three (index +3) has another zero. -/
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
  sorry
