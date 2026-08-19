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

/-! ## Complementary tangent maps

This is the shape needed by geometric clients: separate derivatives for the two
submanifolds, rather than a preassembled endomorphism of the ambient model.
-/

/-- Split the standard `(p + q)`-dimensional model into its first `p` and last `q`
coordinates.  Fixing this order also fixes the intersection-sign convention. -/
def modelSplit (p q : ℕ) : Model (p + q) ≃ₗ[ℝ] Model p × Model q where
  toFun x := (fun i ↦ x (Fin.castAdd q i), fun j ↦ x (Fin.natAdd p j))
  invFun x := Fin.addCases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp
  map_add' x y := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' c x := by
    apply Prod.ext <;> funext i <;> rfl

/-- Separate tangent inclusions for complementary dimensions.  Transversality says
their sum `(u,v) ↦ left u + right v` is a bijection onto the ambient tangent model. -/
structure ComplementaryTangents (p q : ℕ) where
  left : Model p →ₗ[ℝ] Model (p + q)
  right : Model q →ₗ[ℝ] Model (p + q)
  transverse : Function.Bijective (LinearMap.coprod left right)

/-- The tangent-sum equivalence produced by complementary transversality. -/
noncomputable def ComplementaryTangents.sumEquiv {p q : ℕ}
    (t : ComplementaryTangents p q) :
    (Model p × Model q) ≃ₗ[ℝ] Model (p + q) :=
  LinearEquiv.ofBijective (LinearMap.coprod t.left t.right) t.transverse

/-- The ordered tangent-sum comparison as an automorphism of the standard ambient
model.  Its determinant is the local intersection sign before orientation-frame
adjustment. -/
noncomputable def ComplementaryTangents.comparison {p q : ℕ}
    (t : ComplementaryTangents p q) : Model (p + q) ≃ₗ[ℝ] Model (p + q) :=
  (modelSplit p q).trans t.sumEquiv

/-- Coordinate inclusions give a satisfiable complementary-transversality model. -/
noncomputable def standardComplementaryTangents (p q : ℕ) :
    ComplementaryTangents p q where
  left := (modelSplit p q).symm.toLinearMap.comp (LinearMap.inl ℝ (Model p) (Model q))
  right := (modelSplit p q).symm.toLinearMap.comp (LinearMap.inr ℝ (Model p) (Model q))
  transverse := by
    have hmap : LinearMap.coprod
        ((modelSplit p q).symm.toLinearMap.comp (LinearMap.inl ℝ (Model p) (Model q)))
        ((modelSplit p q).symm.toLinearMap.comp (LinearMap.inr ℝ (Model p) (Model q))) =
        (modelSplit p q).symm.toLinearMap := by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change (modelSplit p q).symm (x, 0) + (modelSplit p q).symm (0, y) =
        (modelSplit p q).symm (x, y)
      rw [← map_add]
      congr 1
      ext <;> simp
    rw [hmap]
    exact (modelSplit p q).symm.bijective

theorem standardComplementaryTangents_sumEquiv (p q : ℕ) :
    (standardComplementaryTangents p q).sumEquiv = (modelSplit p q).symm := by
  apply LinearEquiv.ext
  rintro ⟨x, y⟩
  change (modelSplit p q).symm (x, 0) + (modelSplit p q).symm (0, y) =
    (modelSplit p q).symm (x, y)
  rw [← map_add]
  congr 1
  ext <;> simp

theorem standardComplementaryTangents_comparison_apply (p q : ℕ)
    (x : Model (p + q)) :
    (standardComplementaryTangents p q).comparison x = x := by
  rw [ComplementaryTangents.comparison, standardComplementaryTangents_sumEquiv]
  exact (modelSplit p q).symm_apply_apply x

theorem standardComplementaryTangents_comparison (p q : ℕ) :
    (standardComplementaryTangents p q).comparison = LinearEquiv.refl ℝ (Model (p + q)) := by
  apply LinearEquiv.ext
  intro x
  exact standardComplementaryTangents_comparison_apply p q x

/-- Postcomposing the coordinate tangent inclusions by any ambient automorphism
realizes that automorphism as the ordered tangent comparison. -/
noncomputable def complementaryTangentsOfEquiv {p q : ℕ}
    (e : Model (p + q) ≃ₗ[ℝ] Model (p + q)) : ComplementaryTangents p q where
  left := e.toLinearMap.comp (standardComplementaryTangents p q).left
  right := e.toLinearMap.comp (standardComplementaryTangents p q).right
  transverse := by
    have hmap : LinearMap.coprod
        (e.toLinearMap.comp (standardComplementaryTangents p q).left)
        (e.toLinearMap.comp (standardComplementaryTangents p q).right) =
        e.toLinearMap.comp (LinearMap.coprod
          (standardComplementaryTangents p q).left
          (standardComplementaryTangents p q).right) := by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      simp [LinearMap.coprod_apply]
    rw [hmap]
    exact e.bijective.comp (standardComplementaryTangents p q).transverse

theorem complementaryTangentsOfEquiv_comparison {p q : ℕ}
    (e : Model (p + q) ≃ₗ[ℝ] Model (p + q)) :
    (complementaryTangentsOfEquiv e).comparison = e := by
  unfold ComplementaryTangents.comparison ComplementaryTangents.sumEquiv
  apply LinearEquiv.ext
  intro x
  simp only [complementaryTangentsOfEquiv, standardComplementaryTangents,
    LinearMap.coprod_apply, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply]
  rw [← map_add]
  apply e.injective
  rw [← map_add]
  simp

/-- A direct-sum datum converted to the existing oriented local-sign core. -/
noncomputable def ComplementaryTangents.pointDatum {p q : ℕ}
    (t : ComplementaryTangents p q) (source ambient : OrientedFrame (p + q)) :
    PointDatum (Model (p + q)) where
  sourceFrame := source.frame
  ambientFrame := ambient.frame
  tangentSum := t.comparison

/-- The direct-sum API can exhibit a negative local sign: in dimension one,
postcomposition by negation reverses the ambient tangent direction. -/
theorem complementaryTangents_negative_witness :
    localSign ((complementaryTangentsOfEquiv (p := 1) (q := 0)
      (LinearEquiv.neg ℝ : Model 1 ≃ₗ[ℝ] Model 1)).pointDatum
        (standardOrientedFrame 1) (standardOrientedFrame 1)) = -1 := by
  have hdet : LinearMap.det
      ((LinearEquiv.neg ℝ : Model 1 ≃ₗ[ℝ] Model 1).toLinearMap) = -1 := by
    rw [show (LinearEquiv.neg ℝ : Model 1 ≃ₗ[ℝ] Model 1).toLinearMap =
      (-1 : ℝ) • LinearMap.id by ext x i; simp]
    rw [LinearMap.det_smul]
    simp
  rw [ComplementaryTangents.pointDatum, complementaryTangentsOfEquiv_comparison]
  simp [localSign, PointDatum.comparison, standardOrientedFrame, hdet]

/-! ## Coordinate and frame independence -/

/-- Change source and ambient tangent coordinates coherently.  The tangent map is
transported contravariantly in the source and covariantly in the ambient space;
changing frames without transporting this map would describe different geometric data. -/
def PointDatum.reframe {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : PointDatum E) (sourceChange ambientChange : E ≃ₗ[ℝ] E) : PointDatum E where
  sourceFrame := d.sourceFrame.trans sourceChange
  ambientFrame := d.ambientFrame.trans ambientChange
  tangentSum := (sourceChange.symm.trans d.tangentSum).trans ambientChange

/-- A coherent coordinate change leaves the actual oriented tangent comparison unchanged. -/
theorem PointDatum.reframe_comparison {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : PointDatum E) (sourceChange ambientChange : E ≃ₗ[ℝ] E) :
    (d.reframe sourceChange ambientChange).comparison = d.comparison := by
  apply LinearEquiv.ext
  intro x
  simp [PointDatum.reframe, PointDatum.comparison]

/-- Local intersection sign is intrinsic under simultaneous changes of tangent coordinates
and their representing frames. -/
theorem localSign_reframe {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Free ℝ E] [Module.Finite ℝ E] (d : PointDatum E)
    (sourceChange ambientChange : E ≃ₗ[ℝ] E) :
    localSign (d.reframe sourceChange ambientChange) = localSign d := by
  simp only [localSign, PointDatum.reframe_comparison]

/-- Anti-vacuity: frame independence preserves the already exhibited negative local sign,
even after nontrivial source and ambient coordinate reversals. -/
theorem negativePoint_reframe_witness :
    localSign (negativePoint.reframe (LinearEquiv.neg ℝ) (LinearEquiv.neg ℝ)) = -1 := by
  rw [localSign_reframe]
  exact localSign_negativePoint

/-! ## Ordered product orientations -/

/-- The frame on the ordered direct sum obtained from frames on its two factors. -/
noncomputable def productFrame {p q : ℕ} (left : OrientedFrame p) (right : OrientedFrame q) :
    Model (p + q) ≃ₗ[ℝ] Model (p + q) :=
  ((modelSplit p q).trans (left.frame.prodCongr right.frame)).trans (modelSplit p q).symm

/-- Mathlib orientation carried by the ordered product frame.  The order is deliberately
part of the definition; exchanging the factors is not definitionally harmless. -/
noncomputable def productOrientation {p q : ℕ}
    (left : OrientedFrame p) (right : OrientedFrame q) :
    Orientation ℝ (Model (p + q)) (Fin (p + q)) :=
  orientationOfFrame (productFrame left right)

/-- Package two separately oriented tangent models as the ordered source orientation used
by the complementary-tangent comparison. -/
noncomputable def productOrientedFrame {p q : ℕ}
    (left : OrientedFrame p) (right : OrientedFrame q) : OrientedFrame (p + q) where
  orientation := productOrientation left right
  frame := productFrame left right
  frame_represents := rfl

theorem productOrientedFrame_represents {p q : ℕ}
    (left : OrientedFrame p) (right : OrientedFrame q) :
    orientationOfFrame (productOrientedFrame left right).frame =
      productOrientation left right := rfl

theorem productFrame_standard (p q : ℕ) :
    productFrame (standardOrientedFrame p) (standardOrientedFrame q) =
      LinearEquiv.refl ℝ (Model (p + q)) := by
  apply LinearEquiv.ext
  intro x
  simp [productFrame, standardOrientedFrame]

/-- Anti-vacuity: the product of two standard oriented lines represents the independently
known standard orientation of the plane. -/
theorem productOrientation_standard_lines :
    productOrientation (standardOrientedFrame 1) (standardOrientedFrame 1) =
      OrientedIntegration.standardOrientation 2 := by
  rw [productOrientation, productFrame_standard]
  exact (standardOrientedFrame 2).frame_represents

/-- Transporting the orientation represented by one frame along the transition to another
frame gives the orientation represented by the latter. -/
theorem orientationOfFrame_transition {n : ℕ} (a b : OrientedFrame n) :
    Orientation.map (Fin n) (a.frame.symm.trans b.frame) (orientationOfFrame a.frame) =
      orientationOfFrame b.frame := by
  unfold orientationOfFrame
  rw [← Module.Basis.orientation_map]
  congr 1
  ext i
  simp

/-- Two frames representing the same Mathlib orientation differ by a positive-determinant
transition.  This is the intrinsic content missing from mere frame packaging. -/
theorem OrientedFrame.transition_det_pos {n : ℕ} (a b : OrientedFrame n)
    (h : a.orientation = b.orientation) :
    0 < LinearMap.det (a.frame.symm.trans b.frame : Model n →ₗ[ℝ] Model n) := by
  apply (Orientation.map_eq_iff_det_pos (orientationOfFrame a.frame)
    (a.frame.symm.trans b.frame) (by simp)).mp
  rw [orientationOfFrame_transition]
  rw [a.frame_represents, b.frame_represents, h]

theorem productFrame_transition_det {p q : ℕ}
    (a₁ b₁ : OrientedFrame p) (a₂ b₂ : OrientedFrame q) :
    LinearMap.det ((productFrame a₁ a₂).symm.trans (productFrame b₁ b₂) :
      Model (p + q) →ₗ[ℝ] Model (p + q)) =
      LinearMap.det (a₁.frame.symm.trans b₁.frame : Model p →ₗ[ℝ] Model p) *
      LinearMap.det (a₂.frame.symm.trans b₂.frame : Model q →ₗ[ℝ] Model q) := by
  have heq : (productFrame a₁ a₂).symm.trans (productFrame b₁ b₂) =
      ((modelSplit p q).trans
        ((a₁.frame.symm.trans b₁.frame).prodCongr
          (a₂.frame.symm.trans b₂.frame))).trans (modelSplit p q).symm := by
    apply LinearEquiv.ext
    intro x
    simp [productFrame, LinearEquiv.prodCongr_symm]
  have hprod : LinearEquiv.det ((a₁.frame.symm.trans b₁.frame).prodCongr
      (a₂.frame.symm.trans b₂.frame)) =
      LinearEquiv.det (a₁.frame.symm.trans b₁.frame) *
      LinearEquiv.det (a₂.frame.symm.trans b₂.frame) := by
    apply Units.ext
    simp only [LinearEquiv.coe_det, Units.val_mul, LinearEquiv.coe_prodCongr]
    exact LinearMap.det_prodMap _ _
  rw [heq, ← LinearEquiv.coe_det]
  have hc := LinearEquiv.det_conj
    ((a₁.frame.symm.trans b₁.frame).prodCongr
      (a₂.frame.symm.trans b₂.frame)) (modelSplit p q).symm
  have hc' : LinearEquiv.det
      (((modelSplit p q).trans
        ((a₁.frame.symm.trans b₁.frame).prodCongr
          (a₂.frame.symm.trans b₂.frame))).trans (modelSplit p q).symm) =
      LinearEquiv.det ((a₁.frame.symm.trans b₁.frame).prodCongr
        (a₂.frame.symm.trans b₂.frame)) := by
    simpa using hc
  rw [hc', hprod]
  simp only [Units.val_mul, LinearEquiv.coe_det]

/-- The ordered product orientation depends only on the two input orientations, not on the
chosen frames representing them. -/
theorem productOrientation_eq_of_orientation_eq {p q : ℕ}
    (a₁ b₁ : OrientedFrame p) (a₂ b₂ : OrientedFrame q)
    (h₁ : a₁.orientation = b₁.orientation) (h₂ : a₂.orientation = b₂.orientation) :
    productOrientation a₁ a₂ = productOrientation b₁ b₂ := by
  have hdet : 0 < LinearMap.det
      ((productFrame a₁ a₂).symm.trans (productFrame b₁ b₂) :
        Model (p + q) →ₗ[ℝ] Model (p + q)) := by
    rw [productFrame_transition_det]
    exact mul_pos (a₁.transition_det_pos b₁ h₁) (a₂.transition_det_pos b₂ h₂)
  have hmap := (Orientation.map_eq_iff_det_pos (productOrientation a₁ a₂)
    ((productFrame a₁ a₂).symm.trans (productFrame b₁ b₂)) (by simp)).mpr hdet
  have htransition := orientationOfFrame_transition (productOrientedFrame a₁ a₂)
    (productOrientedFrame b₁ b₂)
  rw [productOrientedFrame_represents, productOrientedFrame_represents] at htransition
  have ht : (Orientation.map (Fin (p + q))
      ((productFrame a₁ a₂).symm.trans (productFrame b₁ b₂)))
      (productOrientation a₁ a₂) = productOrientation b₁ b₂ := by
    simpa [productOrientedFrame] using htransition
  exact hmap.symm.trans ht

/-! ## Swapping complementary tangent factors -/

/-- Reindex standard coordinates by a finite permutation. -/
noncomputable def coordinatePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Model n ≃ₗ[ℝ] Model n :=
  LinearEquiv.piCongrLeft ℝ (fun _ : Fin n ↦ ℝ) σ

theorem coordinatePermutation_det {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (coordinatePermutation σ).toLinearMap = ((σ.sign : ℤˣ) : ℝ) := by
  rw [← LinearMap.det_toMatrix']
  calc
    _ = Matrix.det ((σ⁻¹).permMatrix ℝ) := by
      congr 1
      ext i j
      classical
      by_cases h : σ.symm i = j <;>
        simp [coordinatePermutation, LinearEquiv.piCongrLeft,
          LinearEquiv.piCongrLeft', Equiv.Perm.permMatrix,
          PEquiv.toMatrix_apply, Pi.single_apply, h]
    _ = (((σ⁻¹).sign : ℤˣ) : ℝ) := Matrix.det_permutation (σ⁻¹)
    _ = ((σ.sign : ℤˣ) : ℝ) := by simp

/-- Moving the final `q` coordinates in front of the first `p` coordinates is
the `q`-th power of cyclic rotation. -/
def factorSwapPermutation (p q : ℕ) : Equiv.Perm (Fin (p + q)) :=
  finRotate (p + q) ^ q

/-- The block permutation has the Koszul sign `(-1)^(p*q)`.  The proof reduces
cyclic rotation to its known sign and checks the parity identity
`(p+q-1)q ≡ pq (mod 2)` using the evenness of `q(q-1)`. -/
theorem factorSwapPermutation_sign (p q : ℕ) :
    (((factorSwapPermutation p q).sign : ℤˣ) : ℝ) = (-1 : ℝ) ^ (p * q) := by
  by_cases h : p + q = 0
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    simp [factorSwapPermutation]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    change (((Equiv.Perm.sign ((finRotate (p + q)) ^ q) : ℤˣ)) : ℝ) = _
    rw [map_pow, hk, sign_finRotate]
    norm_num
    rw [← pow_mul]
    have hmod : k * q % 2 = p * q % 2 := by
      cases q with
      | zero => simp
      | succ r =>
        have hk' : k = p + r := by omega
        subst k
        rw [Nat.add_mul, Nat.add_mod]
        have he : Even (r * (r + 1)) := Nat.even_mul_succ_self r
        rw [Nat.even_iff] at he
        rw [show r * (r + 1) % 2 = 0 by omega]
        simp
    calc
      (-1 : ℝ) ^ (k * q) = (-1) ^ (k * q % 2) := neg_one_pow_eq_pow_mod_two _
      _ = (-1) ^ (p * q % 2) := by rw [hmod]
      _ = (-1) ^ (p * q) := (neg_one_pow_eq_pow_mod_two _).symm

/-- Linear block swap on the ordered `(p+q)`-dimensional source model. -/
noncomputable def factorSwap (p q : ℕ) : Model (p + q) ≃ₗ[ℝ] Model (p + q) :=
  coordinatePermutation (factorSwapPermutation p q)

/-- Determinant form of the factor-swap law. -/
theorem factorSwap_det (p q : ℕ) :
    LinearMap.det (factorSwap p q).toLinearMap = (-1 : ℝ) ^ (p * q) := by
  rw [factorSwap, coordinatePermutation_det, factorSwapPermutation_sign]

theorem factorSwap_det_of_even (p q : ℕ) (h : Even (p * q)) :
    LinearMap.det (factorSwap p q).toLinearMap = 1 := by
  rw [factorSwap_det, h.neg_one_pow]

theorem factorSwap_det_of_odd (p q : ℕ) (h : Odd (p * q)) :
    LinearMap.det (factorSwap p q).toLinearMap = -1 := by
  rw [factorSwap_det, h.neg_one_pow]

/-- Anti-vacuity in the first nontrivial case: exchanging two oriented lines
reverses the orientation of their plane. -/
theorem factorSwap_lines_det :
    LinearMap.det (factorSwap 1 1).toLinearMap = -1 := by
  simpa using factorSwap_det_of_odd 1 1 (by norm_num)

/-- Precompose the ordered source tangent coordinates by the block swap. -/
noncomputable def PointDatum.swapSourceFactors {p q : ℕ}
    (d : PointDatum (Model (p + q))) : PointDatum (Model (p + q)) where
  sourceFrame := d.sourceFrame
  ambientFrame := d.ambientFrame
  tangentSum := (factorSwap p q).trans d.tangentSum

theorem PointDatum.swapSourceFactors_comparison_det {p q : ℕ}
    (d : PointDatum (Model (p + q))) :
    LinearMap.det (d.swapSourceFactors.comparison : Model (p + q) →ₗ[ℝ] Model (p + q)) =
      (-1 : ℝ) ^ (p * q) *
        LinearMap.det (d.comparison : Model (p + q) →ₗ[ℝ] Model (p + q)) := by
  simp only [← LinearEquiv.coe_det, PointDatum.swapSourceFactors,
    PointDatum.comparison, LinearEquiv.det_trans, Units.val_mul]
  rw [LinearEquiv.coe_det (factorSwap p q), factorSwap_det]
  ring

/-- Swapping complementary tangent factors changes the local intersection sign by the
Koszul factor `(-1)^(p*q)`. -/
theorem localSign_swapSourceFactors {p q : ℕ}
    (d : PointDatum (Model (p + q))) :
    localSign d.swapSourceFactors = (-1 : ℤ) ^ (p * q) * localSign d := by
  have hdet_ne :
      LinearMap.det (d.comparison : Model (p + q) →ₗ[ℝ] Model (p + q)) ≠ 0 :=
    by
      rw [← LinearEquiv.coe_det]
      exact Units.ne_zero _
  rw [localSign, localSign, LinearEquiv.coe_det, LinearEquiv.coe_det,
    PointDatum.swapSourceFactors_comparison_det]
  rcases Nat.even_or_odd (p * q) with heven | hodd
  · rw [heven.neg_one_pow, heven.neg_one_pow]
    simp
  · rw [hodd.neg_one_pow, hodd.neg_one_pow]
    by_cases hpos : 0 < LinearMap.det
        (d.comparison : Model (p + q) →ₗ[ℝ] Model (p + q))
    · simp [hpos, not_lt.mpr hpos.le]
    · have hneg : LinearMap.det
          (d.comparison : Model (p + q) →ₗ[ℝ] Model (p + q)) < 0 :=
        lt_of_le_of_ne (not_lt.mp hpos) hdet_ne
      simp [hpos, neg_pos.mpr hneg]

/-- The exact cancellation pattern shared by `t01A07` and the antipodal pair in
`t02A06`.  It is stated for independently computed signs, not for a fabricated
intersection-number constant. -/
theorem signedCount_finTwo_eq_zero_of_opposite (sign : Fin 2 → ℤ)
    (h : sign 0 = -sign 1) : (∑ i, sign i) = 0 := by
  rw [Fin.sum_univ_two, h]
  omega

/-- Anti-vacuity for the new direct-sum API: the standard line-plane model is
transverse and its ordered comparison is genuinely the identity. -/
theorem standard_lines_in_plane_nonvacuous :
    (standardComplementaryTangents 1 1).comparison =
      LinearEquiv.refl ℝ (Model 2) :=
  standardComplementaryTangents_comparison 1 1

#print axioms isTransverse_refl
#print axioms not_isTransverse_zero_real
#print axioms localSign_ne_zero
#print axioms intersectionNumber_singleton_positive
#print axioms intersectionNumber_singleton_orientation_reversed
#print axioms intersectionNumber_singleton_negative
#print axioms standardOrientedFrame_satisfiable
#print axioms singletonAdapter_signedCount
#print axioms singletonReversedAdapter_signedCount
#print axioms standardComplementaryTangents_comparison
#print axioms signedCount_finTwo_eq_zero_of_opposite
#print axioms standard_lines_in_plane_nonvacuous
#print axioms complementaryTangentsOfEquiv_comparison
#print axioms complementaryTangents_negative_witness
#print axioms PointDatum.reframe_comparison
#print axioms localSign_reframe
#print axioms negativePoint_reframe_witness
#print axioms productOrientedFrame_represents
#print axioms productFrame_standard
#print axioms productOrientation_standard_lines
#print axioms OrientedFrame.transition_det_pos
#print axioms productFrame_transition_det
#print axioms productOrientation_eq_of_orientation_eq
#print axioms coordinatePermutation_det
#print axioms factorSwapPermutation_sign
#print axioms factorSwap_det
#print axioms factorSwap_lines_det
#print axioms PointDatum.swapSourceFactors_comparison_det
#print axioms localSign_swapSourceFactors

end Intersection
