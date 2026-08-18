import Mathlib
import ConstructionTargets.OrientedIntegration

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

/-! ## Hypothesis-driven geometric adapter -/

abbrev Model (n : ℕ) := OrientedIntegration.Model n

/-- The orientation attached to a frame, using Mathlib's `Orientation`. -/
noncomputable def orientationOfFrame {n : ℕ} (frame : Model n ≃ₗ[ℝ] Model n) :
    Orientation ℝ (Model n) (Fin n) :=
  ((Pi.basisFun ℝ (Fin n)).map frame).orientation

/-- A client-supplied oriented frame together with the proof that it represents the client's
Mathlib orientation.  This is the precise bridge between the frame used by `localSign` and
`Orientation`; it does not silently choose an unrelated representative. -/
structure OrientedFrame (n : ℕ) where
  orientation : Orientation ℝ (Model n) (Fin n)
  frame : Model n ≃ₗ[ℝ] Model n
  frame_represents : orientationOfFrame frame = orientation

noncomputable def standardOrientedFrame (n : ℕ) : OrientedFrame n where
  orientation := OrientedIntegration.standardOrientation n
  frame := LinearEquiv.refl ℝ (Model n)
  frame_represents := by
    unfold orientationOfFrame OrientedIntegration.standardOrientation
    congr 1

theorem standardOrientedFrame_satisfiable (n : ℕ) :
    (standardOrientedFrame n).orientation = OrientedIntegration.standardOrientation n := rfl

/-- The actual coincidence locus of two parameterized embedded submanifolds. -/
def Coincidence {A B M : Type*} (left : A → M) (right : B → M) :=
  {z : A × B // left z.1 = right z.2}

/-- Hypotheses required to turn a pair of parameterized embedded submanifolds into the finite
algebraic signed count.  Mathlib currently lacks an embedded-submanifold tangent API, so a
client supplies:

* injectivity of both parameterizations (the set-level embedding component);
* an exact finite enumeration of their coincidence locus;
* the tangent-sum linear map at each enumerated point and its transversality/bijectivity;
* source-product and ambient orientations, each tied to an explicit frame.

Topological embedding and smoothness hypotheses belong in the geometric client's notion of
embedded submanifold; this adapter only consumes the data relevant to the signed count. -/
structure Adapter (n : ℕ) {A B M P : Type*} [Fintype P]
    (left : A → M) (right : B → M) where
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  enumerate : P ≃ Coincidence left right
  tangentSum : P → Model n →ₗ[ℝ] Model n
  transverse : ∀ p, IsTransverse (tangentSum p)
  tangentSumEquiv : P → Model n ≃ₗ[ℝ] Model n
  tangentSumEquiv_agrees : ∀ p, (tangentSumEquiv p).toLinearMap = tangentSum p
  sourceOrientation : P → OrientedFrame n
  ambientOrientation : P → OrientedFrame n

/-- Convert the client-supplied bijective tangent-sum map and compatible orientation frames
to the algebraic local datum. -/
noncomputable def Adapter.pointDatum {n : ℕ} {A B M P : Type*} [Fintype P]
    {left : A → M} {right : B → M} (g : Adapter n (P := P) left right) (p : P) :
    PointDatum (Model n) where
  sourceFrame := (g.sourceOrientation p).frame
  ambientFrame := (g.ambientOrientation p).frame
  tangentSum := g.tangentSumEquiv p

/-- The intersection number supplied by an embedded-submanifold client satisfying `Adapter`.
The exact enumeration makes the finiteness hypothesis explicit and prevents omitted points. -/
noncomputable def Adapter.signedCount {n : ℕ} {A B M P : Type*} [Fintype P]
    {left : A → M} {right : B → M} (g : Adapter n (P := P) left right) : ℤ :=
  intersectionNumber (fun p : P ↦ g.pointDatum p)

/-- The adapter hypotheses are jointly satisfiable: two one-point embedded parameter spaces,
with identity tangent sum and standard orientations, produce signed count `+1`. -/
noncomputable def singletonAdapter :
    Adapter 1 (P := Fin 1) (fun _ : PUnit ↦ PUnit.unit) (fun _ : PUnit ↦ PUnit.unit) where
  left_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  right_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  enumerate :=
    { toFun := fun _ ↦ ⟨(PUnit.unit, PUnit.unit), rfl⟩
      invFun := fun _ ↦ 0
      left_inv := fun x ↦ Subsingleton.elim _ _
      right_inv := fun x ↦ by
        rcases x with ⟨⟨a, b⟩, h⟩
        congr }
  tangentSum := fun _ ↦ LinearMap.id
  transverse := fun _ ↦ isTransverse_refl _
  tangentSumEquiv := fun _ ↦ LinearEquiv.refl ℝ (Model 1)
  tangentSumEquiv_agrees := fun _ ↦ rfl
  sourceOrientation := fun _ ↦ standardOrientedFrame 1
  ambientOrientation := fun _ ↦ standardOrientedFrame 1

theorem singletonAdapter_signedCount : singletonAdapter.signedCount = 1 := by
  simp [Adapter.signedCount, Adapter.pointDatum, intersectionNumber, localSign,
    PointDatum.comparison, singletonAdapter, standardOrientedFrame]

/-- The same realizable geometric hypotheses admit a negative local model when the supplied
tangent-sum map reverses orientation. -/
noncomputable def singletonReversedAdapter :
    Adapter 1 (P := Fin 1) (fun _ : PUnit ↦ PUnit.unit) (fun _ : PUnit ↦ PUnit.unit) where
  left_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  right_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  enumerate :=
    { toFun := fun _ ↦ ⟨(PUnit.unit, PUnit.unit), rfl⟩
      invFun := fun _ ↦ 0
      left_inv := fun x ↦ Subsingleton.elim _ _
      right_inv := fun x ↦ by
        rcases x with ⟨⟨a, b⟩, h⟩
        congr }
  tangentSum := fun _ ↦ (LinearEquiv.neg ℝ : Model 1 ≃ₗ[ℝ] Model 1).toLinearMap
  transverse := fun _ ↦ (LinearEquiv.neg ℝ : Model 1 ≃ₗ[ℝ] Model 1).bijective
  tangentSumEquiv := fun _ ↦ LinearEquiv.neg ℝ
  tangentSumEquiv_agrees := fun _ ↦ rfl
  sourceOrientation := fun _ ↦ standardOrientedFrame 1
  ambientOrientation := fun _ ↦ standardOrientedFrame 1

theorem singletonReversedAdapter_signedCount : singletonReversedAdapter.signedCount = -1 := by
  have hdet : LinearMap.det
      ((LinearEquiv.neg ℝ : Model 1 ≃ₗ[ℝ] Model 1).toLinearMap) = -1 := by
    rw [show (LinearEquiv.neg ℝ : Model 1 ≃ₗ[ℝ] Model 1).toLinearMap =
      (-1 : ℝ) • LinearMap.id by ext x i; simp]
    rw [LinearMap.det_smul]
    simp
  simp [Adapter.signedCount, Adapter.pointDatum, intersectionNumber, localSign,
    PointDatum.comparison, singletonReversedAdapter, standardOrientedFrame, hdet]

#print axioms isTransverse_refl
#print axioms not_isTransverse_zero_real
#print axioms localSign_ne_zero
#print axioms intersectionNumber_singleton_positive
#print axioms intersectionNumber_singleton_orientation_reversed
#print axioms intersectionNumber_singleton_negative
#print axioms standardOrientedFrame_satisfiable
#print axioms singletonAdapter_signedCount
#print axioms singletonReversedAdapter_signedCount

end Intersection
