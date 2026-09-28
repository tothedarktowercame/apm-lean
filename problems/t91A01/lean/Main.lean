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

/-- The normalized direction of the actual tangent vector field on the
boundary of an embedded coordinate disk. -/
def apm_t91a01_localDirection
    {F : Type*} [TopologicalSpace F] [ChartedSpace apm_t91a01_E2 F]
    (V : (x : F) → TangentSpace apm_t91a01_Model2 x)
    (φ : apm_t91a01_Disk2 → F)
    (τ : ∀ z : apm_t91a01_Circle,
      TangentSpace apm_t91a01_Model2
        (φ ⟨z.1, by simpa [Metric.mem_closedBall] using le_of_eq z.2⟩) ≃L[ℝ] ℂ)
    (hnz : ∀ z, τ z (V (φ ⟨z.1,
      by simpa [Metric.mem_closedBall] using le_of_eq z.2⟩)) ≠ 0)
    (z : apm_t91a01_Circle) : apm_t91a01_Circle :=
  let w := τ z (V (φ ⟨z.1,
    by simpa [Metric.mem_closedBall] using le_of_eq z.2⟩))
  ⟨w / (‖w‖ : ℂ), by
    have hw : w ≠ 0 := hnz z
    simpa [Metric.mem_sphere, norm_div, hw]⟩

/-- The isolated zero `p` has index `+3`: an embedded coordinate disk
centred at `p` trivializes the tangent field along its boundary, and the
normalized direction of that very field is the degree-three map. -/
def apm_t91a01_hasIndexThreeZero
    {F : Type*} [TopologicalSpace F] [ChartedSpace apm_t91a01_E2 F]
    (V : (x : F) → TangentSpace apm_t91a01_Model2 x) (p : F) : Prop :=
  ∃ (φ : apm_t91a01_Disk2 → F) (hφ : Topology.IsEmbedding φ),
    φ ⟨0, by simp⟩ = p ∧
    ∃ (τ : ∀ z : apm_t91a01_Circle,
      TangentSpace apm_t91a01_Model2
        (φ ⟨z.1, by simpa [Metric.mem_closedBall] using le_of_eq z.2⟩) ≃L[ℝ] ℂ)
      (hnz : ∀ z, τ z (V (φ ⟨z.1,
        by simpa [Metric.mem_closedBall] using le_of_eq z.2⟩)) ≠ 0)
      (link : C(apm_t91a01_Circle, apm_t91a01_Circle)),
      (∀ z, link z = apm_t91a01_localDirection V φ τ hnz z) ∧
      ∀ z, link z = ⟨z.1 ^ 3, by
        simpa [Metric.mem_sphere, norm_pow] using
          congrArg (fun r : ℝ ↦ r ^ 3) z.2⟩

/-- A local index-three model exists; on a compact connected oriented smooth
surface, a smooth tangent vector field having an isolated zero whose actual
normalized boundary direction is `z ↦ z³` has another zero. -/
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
