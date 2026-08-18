import Mathlib

/-!
# Finite signed transverse intersections

This file isolates the algebraic core of an intersection number.  At an intersection of
complementary-dimensional submanifolds, the direct sum of their tangent inclusions is an
isomorphism onto the ambient tangent space.  After oriented identifications of source and
target with the same model vector space, this is an automorphism.  Its determinant gives the
local sign.  A finite intersection number is the sum of these signs.

The missing geometric input in the current Mathlib snapshot is a theory connecting embedded
submanifolds and their tangent spaces to this datum; no singular homology is used here.
-/

namespace Intersection

open scoped BigOperators

/-- The tangent-sum map is transverse exactly when it is bijective.  In a geometric client,
this map is `(u, v) ↦ di₁ u + di₂ v` after identifying the complementary-dimensional direct
sum with `E`. -/
def IsTransverse {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E →ₗ[ℝ] E) : Prop :=
  Function.Bijective f

theorem isTransverse_refl (E : Type*) [AddCommGroup E] [Module ℝ E] :
    IsTransverse (LinearMap.id (R := ℝ) (M := E)) := by
  exact Function.bijective_id

theorem not_isTransverse_zero_real :
    ¬ IsTransverse (0 : ℝ →ₗ[ℝ] ℝ) := by
  intro h
  have hz : (0 : ℝ →ₗ[ℝ] ℝ) 0 = (0 : ℝ →ₗ[ℝ] ℝ) 1 := by simp
  have := h.1 hz
  norm_num at this

/-- The local linear data at a transverse intersection point.  `sourceFrame` is the product
orientation on the two tangent spaces, `ambientFrame` is the ambient orientation, and
`tangentSum` is the (invertible) sum of the two tangent inclusions. -/
structure PointDatum (E : Type*) [AddCommGroup E] [Module ℝ E] where
  sourceFrame : E ≃ₗ[ℝ] E
  ambientFrame : E ≃ₗ[ℝ] E
  tangentSum : E ≃ₗ[ℝ] E

/-- The comparison automorphism from the oriented source frame to the oriented ambient
frame. -/
def PointDatum.comparison {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : PointDatum E) : E ≃ₗ[ℝ] E :=
  (d.sourceFrame.trans d.tangentSum).trans d.ambientFrame.symm

/-- The determinant sign of the tangent-sum comparison.  Since `comparison` is an
equivalence, its determinant cannot vanish, so the two branches really are `+1` and `-1`. -/
noncomputable def localSign {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Free ℝ E]
    [Module.Finite ℝ E] (d : PointDatum E) : ℤ :=
  if 0 < (↑(LinearEquiv.det d.comparison) : ℝ) then 1 else -1

theorem localSign_eq_one_or_neg_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Free ℝ E] [Module.Finite ℝ E] (d : PointDatum E) :
    localSign d = 1 ∨ localSign d = -1 := by
  unfold localSign
  split <;> simp_all

theorem localSign_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Free ℝ E] [Module.Finite ℝ E] (d : PointDatum E) : localSign d ≠ 0 := by
  rcases localSign_eq_one_or_neg_one d with h | h <;> omega

/-- Signed intersection number of a finite transverse intersection. -/
noncomputable def intersectionNumber {P E : Type*} [Fintype P] [AddCommGroup E] [Module ℝ E]
    [Module.Free ℝ E] [Module.Finite ℝ E] (atPoint : P → PointDatum E) : ℤ :=
  ∑ p, localSign (atPoint p)

def positivePoint : PointDatum ℝ where
  sourceFrame := LinearEquiv.refl ℝ ℝ
  ambientFrame := LinearEquiv.refl ℝ ℝ
  tangentSum := LinearEquiv.refl ℝ ℝ

def negativePoint : PointDatum ℝ where
  sourceFrame := LinearEquiv.refl ℝ ℝ
  ambientFrame := LinearEquiv.refl ℝ ℝ
  tangentSum := LinearEquiv.neg ℝ

theorem localSign_positivePoint : localSign positivePoint = 1 := by
  simp [localSign, PointDatum.comparison, positivePoint]

theorem localSign_negativePoint : localSign negativePoint = -1 := by
  simp [localSign, PointDatum.comparison, negativePoint]

/-- A single positively oriented transverse point has nonzero intersection number. -/
theorem intersectionNumber_singleton_positive :
    intersectionNumber (fun _ : Fin 1 ↦ positivePoint) = 1 := by
  simp [intersectionNumber, localSign_positivePoint]

/-- Reversing the one-dimensional tangent-sum orientation flips the concrete signed count. -/
theorem intersectionNumber_singleton_orientation_reversed :
    intersectionNumber (fun _ : Fin 1 ↦ negativePoint) =
      -intersectionNumber (fun _ : Fin 1 ↦ positivePoint) := by
  simp [intersectionNumber, localSign_positivePoint, localSign_negativePoint]

theorem intersectionNumber_singleton_negative :
    intersectionNumber (fun _ : Fin 1 ↦ negativePoint) = -1 := by
  simp [intersectionNumber, localSign_negativePoint]

#print axioms isTransverse_refl
#print axioms not_isTransverse_zero_real
#print axioms localSign_ne_zero
#print axioms intersectionNumber_singleton_positive
#print axioms intersectionNumber_singleton_orientation_reversed
#print axioms intersectionNumber_singleton_negative

end Intersection
