import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.t97A03Closure
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.PolygonCellPiOne
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.ThreeCirclesFundamentalGroup
import ConstructionTargets.SphereHomology
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.CoveringLiftRestriction
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# APM t97A03

## Statement repairs

None.

## Encoding questions

The base and both pictured covers are concrete adjunction-space quotients.
The base glues two marked circle points to the poles of `S²`. The cover
pictures glue two sphere sheets to either one lifted circle at four points or
two lifted circles at two points each. Homology is Mathlib integral singular
homology, and the fundamental group is the actual based fundamental group.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97A03_R3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t97A03_S2 := Metric.sphere (0 : apm_t97A03_R3) 1

def apm_t97A03_north : apm_t97A03_S2 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp⟩

def apm_t97A03_south : apm_t97A03_S2 :=
  ⟨EuclideanSpace.single (2 : Fin 3) (-1), by simp⟩

/-- The two specified identifications in `S¹ ⊔ S²`. -/
inductive apm_t97A03_BaseRel (A B : Circle) :
    Sum Circle apm_t97A03_S2 → Sum Circle apm_t97A03_S2 → Prop
  | north : apm_t97A03_BaseRel A B (.inl A) (.inr apm_t97A03_north)
  | south : apm_t97A03_BaseRel A B (.inl B) (.inr apm_t97A03_south)

def apm_t97A03_BaseSpace (A B : Circle) :=
  Quotient (Relation.EqvGen.setoid (apm_t97A03_BaseRel A B))

noncomputable instance (A B : Circle) :
    TopologicalSpace (apm_t97A03_BaseSpace A B) :=
  TopologicalSpace.coinduced (fun x : Sum Circle apm_t97A03_S2 ↦
    Quotient.mk _ x) inferInstance

/-- The literal circle summand in the base adjunction quotient. -/
def apm_t97A03_baseCircle (A B : Circle) (z : Circle) :
    apm_t97A03_BaseSpace A B :=
  Quotient.mk _ (.inl z)

/-- The literal sphere summand in the base adjunction quotient. -/
def apm_t97A03_baseSphere (A B : Circle) (z : apm_t97A03_S2) :
    apm_t97A03_BaseSpace A B :=
  Quotient.mk _ (.inr z)

lemma apm_t97A03_continuous_baseCircle (A B : Circle) :
    Continuous (apm_t97A03_baseCircle A B) := by
  exact continuous_coinduced_rng.comp continuous_inl

lemma apm_t97A03_continuous_baseSphere (A B : Circle) :
    Continuous (apm_t97A03_baseSphere A B) := by
  exact continuous_coinduced_rng.comp continuous_inr

/-- Every point of the literal base is represented by one of its two
summands.  This is the elimination interface used when comparing the
adjunction quotient with the two-circle wedge normal form. -/
lemma apm_t97A03_baseCircle_or_baseSphere (A B : Circle)
    (x : apm_t97A03_BaseSpace A B) :
    (∃ z : Circle, x = apm_t97A03_baseCircle A B z) ∨
      ∃ z : apm_t97A03_S2, x = apm_t97A03_baseSphere A B z := by
  refine Quotient.inductionOn x ?_
  rintro (z | z)
  · exact Or.inl ⟨z, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

/-- The first marked circle point is attached to the north pole in the base. -/
lemma apm_t97A03_base_north_eq (A B : Circle) :
    (Quotient.mk _ (.inl A) : apm_t97A03_BaseSpace A B) =
      Quotient.mk _ (.inr apm_t97A03_north) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _
      (apm_t97A03_BaseRel.north (A := A) (B := B)))

/-- The second marked circle point is attached to the south pole in the base. -/
lemma apm_t97A03_base_south_eq (A B : Circle) :
    (Quotient.mk _ (.inl B) : apm_t97A03_BaseSpace A B) =
      Quotient.mk _ (.inr apm_t97A03_south) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _
      (apm_t97A03_BaseRel.south (A := A) (B := B)))

@[simp] lemma apm_t97A03_baseCircle_A (A B : Circle) :
    apm_t97A03_baseCircle A B A =
      apm_t97A03_baseSphere A B apm_t97A03_north := by
  exact apm_t97A03_base_north_eq A B

@[simp] lemma apm_t97A03_baseCircle_B (A B : Circle) :
    apm_t97A03_baseCircle A B B =
      apm_t97A03_baseSphere A B apm_t97A03_south := by
  exact apm_t97A03_base_south_eq A B

/-- The circle quotient obtained by identifying the two attachment points.
For distinct points this is the literal two-circle graph underlying the base. -/
inductive apm_t97A03_CutCircleRel (A B : Circle) : Circle → Circle → Prop
  | glue : apm_t97A03_CutCircleRel A B A B

def apm_t97A03_CutCircle (A B : Circle) :=
  Quotient (Relation.EqvGen.setoid (apm_t97A03_CutCircleRel A B))

noncomputable instance (A B : Circle) :
    TopologicalSpace (apm_t97A03_CutCircle A B) :=
  TopologicalSpace.coinduced (fun z : Circle ↦ Quotient.mk _ z) inferInstance

def apm_t97A03_cutCircleMap (A B : Circle) (z : Circle) :
    apm_t97A03_CutCircle A B := Quotient.mk _ z

lemma apm_t97A03_continuous_cutCircleMap (A B : Circle) :
    Continuous (apm_t97A03_cutCircleMap A B) := continuous_coinduced_rng

/-- Collapse the sphere summand of the literal base to its north attachment,
leaving the circle summand as the quotient identifying `A` and `B`. -/
def apm_t97A03_collapseToCutCircle (A B : Circle) :
    apm_t97A03_BaseSpace A B → apm_t97A03_CutCircle A B :=
  Quotient.lift
    (fun x : Sum Circle apm_t97A03_S2 ↦
      match x with
      | Sum.inl z => apm_t97A03_cutCircleMap A B z
      | Sum.inr _ => apm_t97A03_cutCircleMap A B A)
    (by
      intro x y hxy
      exact Relation.EqvGen.rec
        (fun _ _ h => by
          cases h with
          | north => rfl
          | south =>
              exact Quotient.sound
                (Relation.EqvGen.symm _ _
                  (Relation.EqvGen.rel _ _
                    (apm_t97A03_CutCircleRel.glue (A := A) (B := B)))))
        (fun _ => rfl)
        (fun _ _ _ ih => ih.symm)
        (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
        hxy)

@[simp] lemma apm_t97A03_collapseToCutCircle_circle (A B z : Circle) :
    apm_t97A03_collapseToCutCircle A B (apm_t97A03_baseCircle A B z) =
      apm_t97A03_cutCircleMap A B z := rfl

@[simp] lemma apm_t97A03_collapseToCutCircle_sphere
    (A B : Circle) (z : apm_t97A03_S2) :
    apm_t97A03_collapseToCutCircle A B (apm_t97A03_baseSphere A B z) =
      apm_t97A03_cutCircleMap A B A := rfl

lemma apm_t97A03_continuous_collapseToCutCircle (A B : Circle) :
    Continuous (apm_t97A03_collapseToCutCircle A B) := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.mpr
  exact ⟨apm_t97A03_continuous_cutCircleMap A B, continuous_const⟩

/-- The collapse reaches every point of the cut-circle quotient through the
literal circle summand. -/
lemma apm_t97A03_surjective_collapseToCutCircle (A B : Circle) :
    Function.Surjective (apm_t97A03_collapseToCutCircle A B) := by
  intro z
  refine Quotient.inductionOn z ?_
  intro w
  exact ⟨apm_t97A03_baseCircle A B w, rfl⟩

/-- The two marked endpoints are the same point in the cut-circle quotient. -/
lemma apm_t97A03_cutCircleMap_A_eq_B (A B : Circle) :
    apm_t97A03_cutCircleMap A B A = apm_t97A03_cutCircleMap A B B := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _
      (apm_t97A03_CutCircleRel.glue (A := A) (B := B)))

/-- The closed-form relation generated by identifying the two marked circle
points.  Keeping this relation explicit is the representation boundary needed
to construct and prove injective a geometric decoder for the cut quotient. -/
def apm_t97A03_CutCircleClosedRel (A B : Circle) (x y : Circle) : Prop :=
  x = y ∨ (x = A ∧ y = B) ∨ (x = B ∧ y = A)

lemma apm_t97A03_cutCircleClosedRel_trans (A B : Circle) {x y z : Circle}
    (hxy : apm_t97A03_CutCircleClosedRel A B x y)
    (hyz : apm_t97A03_CutCircleClosedRel A B y z) :
    apm_t97A03_CutCircleClosedRel A B x z := by
  rcases hxy with hxy | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · subst y
    exact hyz
  · rcases hyz with hyz | ⟨hy', hz⟩ | ⟨hy', hz⟩
    · subst z
      exact Or.inr (Or.inl ⟨hx, hy⟩)
    · subst y
      exact Or.inr (Or.inl ⟨hx, hz⟩)
    · subst y
      exact Or.inl (hx.trans hz.symm)
  · rcases hyz with hyz | ⟨hy', hz⟩ | ⟨hy', hz⟩
    · subst z
      exact Or.inr (Or.inr ⟨hx, hy⟩)
    · subst y
      exact Or.inl (hx.trans hz.symm)
    · subst y
      exact Or.inr (Or.inr ⟨hx, hz⟩)

/-- Exact normal form for the equivalence closure of the genuine two-point
cut relation: no circle points other than the marked pair are collapsed. -/
lemma apm_t97A03_eqvGen_cutCircleRel_iff (A B x y : Circle) :
    Relation.EqvGen (apm_t97A03_CutCircleRel A B) x y ↔
      apm_t97A03_CutCircleClosedRel A B x y := by
  constructor
  · intro h
    exact Relation.EqvGen.rec
      (fun _ _ h => by
        cases h
        exact Or.inr (Or.inl ⟨rfl, rfl⟩))
      (fun _ => Or.inl rfl)
      (fun _ _ h ih => by
        rcases ih with ih | ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inl ih.symm
        · exact Or.inr (Or.inr ⟨hy, hx⟩)
        · exact Or.inr (Or.inl ⟨hy, hx⟩))
      (fun _ _ _ _ _ ih₁ ih₂ =>
        apm_t97A03_cutCircleClosedRel_trans A B ih₁ ih₂)
      h
  · intro h
    rcases h with h | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · subst y
      exact Relation.EqvGen.refl x
    · subst x
      subst y
      exact Relation.EqvGen.rel _ _
        (apm_t97A03_CutCircleRel.glue (A := A) (B := B))
    · subst x
      subst y
      exact Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _
          (apm_t97A03_CutCircleRel.glue (A := A) (B := B)))

/-- Rotate the literal cut-circle quotient so that its first marked point is
one.  This is an actual quotient map, not an abstract pi1 coordinate choice. -/
def apm_t97A03_normalizeCutCircle (A B : Circle) :
    apm_t97A03_CutCircle A B →
      apm_t97A03_CutCircle 1 (A⁻¹ * B) :=
  Quotient.lift
    (fun z => apm_t97A03_cutCircleMap 1 (A⁻¹ * B) (A⁻¹ * z))
    (by
      intro x y hxy
      exact Relation.EqvGen.rec
        (fun _ _ h => by
          cases h
          simpa using Quotient.sound
            (Relation.EqvGen.rel _ _
              (apm_t97A03_CutCircleRel.glue
                (A := (1 : Circle)) (B := A⁻¹ * B))))
        (fun _ => rfl)
        (fun _ _ _ ih => ih.symm)
        (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
        hxy)

/-- Undo the normalization rotation on the literal quotient. -/
def apm_t97A03_denormalizeCutCircle (A B : Circle) :
    apm_t97A03_CutCircle 1 (A⁻¹ * B) →
      apm_t97A03_CutCircle A B :=
  Quotient.lift
    (fun z => apm_t97A03_cutCircleMap A B (A * z))
    (by
      intro x y hxy
      exact Relation.EqvGen.rec
        (fun _ _ h => by
          cases h
          simpa using Quotient.sound
            (Relation.EqvGen.rel _ _
              (apm_t97A03_CutCircleRel.glue (A := A) (B := B))))
        (fun _ => rfl)
        (fun _ _ _ ih => ih.symm)
        (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
        hxy)

lemma apm_t97A03_continuous_normalizeCutCircle (A B : Circle) :
    Continuous (apm_t97A03_normalizeCutCircle A B) := by
  apply continuous_coinduced_dom.mpr
  exact (apm_t97A03_continuous_cutCircleMap 1 (A⁻¹ * B)).comp
    (continuous_const.mul continuous_id)

lemma apm_t97A03_continuous_denormalizeCutCircle (A B : Circle) :
    Continuous (apm_t97A03_denormalizeCutCircle A B) := by
  apply continuous_coinduced_dom.mpr
  exact (apm_t97A03_continuous_cutCircleMap A B).comp
    (continuous_const.mul continuous_id)

/-- Identifying arbitrary marked points is geometrically equivalent to
identifying one with their relative displacement. -/
noncomputable def apm_t97A03_cutCircleNormalizeHomeomorph (A B : Circle) :
    apm_t97A03_CutCircle A B ≃ₜ apm_t97A03_CutCircle 1 (A⁻¹ * B) where
  toFun := apm_t97A03_normalizeCutCircle A B
  invFun := apm_t97A03_denormalizeCutCircle A B
  left_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro z
    change apm_t97A03_cutCircleMap A B (A * (A⁻¹ * z)) =
      apm_t97A03_cutCircleMap A B z
    congr 1
    simp
  right_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro z
    change apm_t97A03_cutCircleMap 1 (A⁻¹ * B) (A⁻¹ * (A * z)) =
      apm_t97A03_cutCircleMap 1 (A⁻¹ * B) z
    congr 1
    simp
  continuous_toFun := apm_t97A03_continuous_normalizeCutCircle A B
  continuous_invFun := apm_t97A03_continuous_denormalizeCutCircle A B

/-- A fixed path in the literal sphere summand from the north attachment to
the south attachment. -/
noncomputable def apm_t97A03_sphereReturn :
    Path apm_t97A03_north apm_t97A03_south := by
  letI : PathConnectedSpace apm_t97A03_S2 :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (E := apm_t97A03_R3)
        (by rw [← Module.finrank_eq_rank]; norm_num [apm_t97A03_R3])
        0 (by norm_num))
  exact PathConnectedSpace.somePath _ _

/-- The actual return path in the base quotient, obtained from the sphere
summand rather than from an abstract loop selector. -/
noncomputable def apm_t97A03_baseSphereReturn (A B : Circle) :
    Path (apm_t97A03_baseSphere A B apm_t97A03_north)
      (apm_t97A03_baseSphere A B apm_t97A03_south) :=
  apm_t97A03_sphereReturn.map (apm_t97A03_continuous_baseSphere A B)

/-- The sphere return is sent pointwise to the wedge point by the literal
collapse map. -/
lemma apm_t97A03_collapse_baseSphereReturn (A B : Circle) (t : unitInterval) :
    apm_t97A03_collapseToCutCircle A B
        (apm_t97A03_baseSphereReturn A B t) =
      apm_t97A03_cutCircleMap A B A := by
  rfl

@[simp] lemma apm_t97A03_baseSphereReturn_zero (A B : Circle) :
    apm_t97A03_baseSphereReturn A B 0 = apm_t97A03_baseCircle A B A := by
  rw [(apm_t97A03_baseSphereReturn A B).source,
    ← apm_t97A03_baseCircle_A]

@[simp] lemma apm_t97A03_baseSphereReturn_one (A B : Circle) :
    apm_t97A03_baseSphereReturn A B 1 = apm_t97A03_baseCircle A B B := by
  rw [(apm_t97A03_baseSphereReturn A B).target,
    ← apm_t97A03_baseCircle_B]

/-- A literal circle-summand path between the two marked points.  The second,
complementary arc will be obtained from a cut-circle normal form rather than
by reusing this path or its reverse. -/
noncomputable def apm_t97A03_circleArc (A B : Circle) : Path A B :=
  Path.ofLine (f := fun t : ℝ ↦
      Circle.exp ((1 - t) * Complex.arg A + t * Complex.arg B))
    (by fun_prop) (by simp) (by simp)

/-- The full turn added to the endpoint of the second arc: `-2π` when
`arg A < arg B` and `+2π` otherwise, so that the second arc runs the other way
round the circle from the first and the two arcs together cover it exactly once. -/
noncomputable def apm_t97A03_arcShift (A B : Circle) : ℝ :=
  if Complex.arg A < Complex.arg B then -(2 * Real.pi) else 2 * Real.pi

lemma apm_t97A03_exp_arg_add_arcShift (A B : Circle) :
    Circle.exp (Complex.arg B + apm_t97A03_arcShift A B) = B := by
  unfold apm_t97A03_arcShift
  split_ifs
  · rw [← sub_eq_add_neg, Circle.exp_sub_two_pi]; simp
  · simp

/-- The opposite lifted interval from `A` to `B`.  Its endpoint differs in
the real lift by one full turn in the direction opposite to the first arc, so
this is the complementary circle arc and not a second choice of an arbitrary
path. -/
noncomputable def apm_t97A03_complementaryCircleArc (A B : Circle) : Path A B :=
  Path.ofLine (f := fun t : ℝ ↦
      Circle.exp ((1 - t) * Complex.arg A +
        t * (Complex.arg B + apm_t97A03_arcShift A B)))
    (by fun_prop) (by simp) (by simpa using apm_t97A03_exp_arg_add_arcShift A B)

lemma apm_t97A03_circleArcs_ne (A B : Circle) :
    apm_t97A03_circleArc A B ≠ apm_t97A03_complementaryCircleArc A B := by
  intro h
  have hm := congrArg (fun p : Path A B ↦ p ⟨(1 / 2 : ℝ), by norm_num⟩) h
  simp [apm_t97A03_circleArc, apm_t97A03_complementaryCircleArc,
    Path.ofLine] at hm
  have hshift : (2 : ℝ)⁻¹ * apm_t97A03_arcShift A B = Real.pi ∨
      (2 : ℝ)⁻¹ * apm_t97A03_arcShift A B = -Real.pi := by
    unfold apm_t97A03_arcShift; split_ifs
    · right; ring
    · left; ring
  rw [show (2 : ℝ)⁻¹ * (Complex.arg B + apm_t97A03_arcShift A B) =
      2⁻¹ * Complex.arg B + 2⁻¹ * apm_t97A03_arcShift A B by ring,
    Circle.exp_add] at hm
  have hone : Circle.exp ((2 : ℝ)⁻¹ * apm_t97A03_arcShift A B) = 1 := by
    apply mul_left_cancel (a := Circle.exp (2⁻¹ * Complex.arg B))
    simpa using hm.symm
  rcases hshift with h' | h' <;> rw [h'] at hone
  · exact Circle.exp_pi_ne_one hone
  · rw [Circle.exp_neg, inv_eq_one] at hone; exact Circle.exp_pi_ne_one hone

/-- Rotation by `A⁻¹` sends the first genuine complementary arc to an arc
from the normalized point `1` to the relative marked point `A⁻¹ * B`. -/
noncomputable def apm_t97A03_normalizedCircleArc (A B : Circle) :
    Path (1 : Circle) (A⁻¹ * B) :=
  ((apm_t97A03_circleArc A B).map
    (continuous_const.mul continuous_id)).cast (by simp) rfl

/-- The other genuine complementary arc in the same normalized coordinates. -/
noncomputable def apm_t97A03_normalizedComplementaryCircleArc (A B : Circle) :
    Path (1 : Circle) (A⁻¹ * B) :=
  ((apm_t97A03_complementaryCircleArc A B).map
    (continuous_const.mul continuous_id)).cast (by simp) rfl

/-- Normalization preserves the fact that the two literal arcs are genuinely
different; it does not replace one of them by a constant path. -/
lemma apm_t97A03_normalizedCircleArcs_ne (A B : Circle) :
    apm_t97A03_normalizedCircleArc A B ≠
      apm_t97A03_normalizedComplementaryCircleArc A B := by
  intro h
  apply apm_t97A03_circleArcs_ne A B
  ext t
  have ht := congrArg (fun p : Path (1 : Circle) (A⁻¹ * B) ↦ p t) h
  change A⁻¹ * apm_t97A03_circleArc A B t =
    A⁻¹ * apm_t97A03_complementaryCircleArc A B t at ht
  have ht' := congrArg (fun z : Circle ↦ A * z) ht
  simpa [mul_assoc] using ht'

/-- The quotient normalization carries the first literal arc pointwise to
its normalized representative. -/
lemma apm_t97A03_normalize_firstArc (A B : Circle) (t : unitInterval) :
    apm_t97A03_normalizeCutCircle A B
        (apm_t97A03_cutCircleMap A B (apm_t97A03_circleArc A B t)) =
      apm_t97A03_cutCircleMap 1 (A⁻¹ * B)
        (apm_t97A03_normalizedCircleArc A B t) := by
  rfl

/-- The same literal quotient map carries the complementary arc pointwise;
both normalized generators therefore come from the actual gluing circle. -/
lemma apm_t97A03_normalize_complementaryArc
    (A B : Circle) (t : unitInterval) :
    apm_t97A03_normalizeCutCircle A B
        (apm_t97A03_cutCircleMap A B
          (apm_t97A03_complementaryCircleArc A B t)) =
      apm_t97A03_cutCircleMap 1 (A⁻¹ * B)
        (apm_t97A03_normalizedComplementaryCircleArc A B t) := by
  rfl

/-- The chosen literal circle arc mapped into the adjunction quotient. -/
noncomputable def apm_t97A03_baseCircleArc (A B : Circle) :
    Path (apm_t97A03_baseCircle A B A) (apm_t97A03_baseCircle A B B) :=
  (apm_t97A03_circleArc A B).map (apm_t97A03_continuous_baseCircle A B)

noncomputable def apm_t97A03_baseComplementaryCircleArc (A B : Circle) :
    Path (apm_t97A03_baseCircle A B A) (apm_t97A03_baseCircle A B B) :=
  (apm_t97A03_complementaryCircleArc A B).map
    (apm_t97A03_continuous_baseCircle A B)

/-- On the first literal arc, collapse is exactly the quotient projection of
the original circle arc. -/
lemma apm_t97A03_collapse_baseCircleArc (A B : Circle) (t : unitInterval) :
    apm_t97A03_collapseToCutCircle A B (apm_t97A03_baseCircleArc A B t) =
      apm_t97A03_cutCircleMap A B (apm_t97A03_circleArc A B t) := by
  rfl

/-- The same exact comparison holds for the genuinely complementary arc. -/
lemma apm_t97A03_collapse_baseComplementaryCircleArc
    (A B : Circle) (t : unitInterval) :
    apm_t97A03_collapseToCutCircle A B
        (apm_t97A03_baseComplementaryCircleArc A B t) =
      apm_t97A03_cutCircleMap A B
        (apm_t97A03_complementaryCircleArc A B t) := by
  rfl

/-- The first actual complementary arc, closed at the identified cut point. -/
noncomputable def apm_t97A03_firstCutCircleLoop (A B : Circle) :
    Path (apm_t97A03_cutCircleMap A B A)
      (apm_t97A03_cutCircleMap A B A) :=
  ((apm_t97A03_circleArc A B).map
      (apm_t97A03_continuous_cutCircleMap A B)).cast rfl
    (apm_t97A03_cutCircleMap_A_eq_B A B)

/-- The second actual complementary arc, closed at the same cut point. -/
noncomputable def apm_t97A03_secondCutCircleLoop (A B : Circle) :
    Path (apm_t97A03_cutCircleMap A B A)
      (apm_t97A03_cutCircleMap A B A) :=
  ((apm_t97A03_complementaryCircleArc A B).map
      (apm_t97A03_continuous_cutCircleMap A B)).cast rfl
    (apm_t97A03_cutCircleMap_A_eq_B A B)

/-- The first genuine loop after normalizing the marked pair. -/
noncomputable def apm_t97A03_normalizedFirstCutCircleLoop (A B : Circle) :
    Path (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1)
      (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  ((apm_t97A03_normalizedCircleArc A B).map
      (apm_t97A03_continuous_cutCircleMap 1 (A⁻¹ * B))).cast rfl
    (apm_t97A03_cutCircleMap_A_eq_B 1 (A⁻¹ * B))

/-- The complementary genuine loop after the same normalization. -/
noncomputable def apm_t97A03_normalizedSecondCutCircleLoop (A B : Circle) :
    Path (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1)
      (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  ((apm_t97A03_normalizedComplementaryCircleArc A B).map
      (apm_t97A03_continuous_cutCircleMap 1 (A⁻¹ * B))).cast rfl
    (apm_t97A03_cutCircleMap_A_eq_B 1 (A⁻¹ * B))

/-- Normalization sends the first original based loop pointwise to its
normalized based-loop representative. -/
lemma apm_t97A03_normalize_firstCutCircleLoop
    (A B : Circle) (t : unitInterval) :
    apm_t97A03_normalizeCutCircle A B
        (apm_t97A03_firstCutCircleLoop A B t) =
      apm_t97A03_normalizedFirstCutCircleLoop A B t := by
  rfl

/-- Normalization sends the complementary original based loop pointwise to
the complementary normalized representative. -/
lemma apm_t97A03_normalize_secondCutCircleLoop
    (A B : Circle) (t : unitInterval) :
    apm_t97A03_normalizeCutCircle A B
        (apm_t97A03_secondCutCircleLoop A B t) =
      apm_t97A03_normalizedSecondCutCircleLoop A B t := by
  rfl

lemma apm_t97A03_normalize_cutCircleBasepoint (A B : Circle) :
    apm_t97A03_normalizeCutCircle A B
        (apm_t97A03_cutCircleMap A B A) =
      apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1 := by
  change apm_t97A03_cutCircleMap 1 (A⁻¹ * B) (A⁻¹ * A) = _
  congr 1
  simp

/-- The typed based-path image of the first generator under normalization. -/
noncomputable def apm_t97A03_normalizedImageFirstCutCircleLoop
    (A B : Circle) :
    Path (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1)
      (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  ((apm_t97A03_firstCutCircleLoop A B).map
    (apm_t97A03_continuous_normalizeCutCircle A B)).cast
      (apm_t97A03_normalize_cutCircleBasepoint A B).symm
      (apm_t97A03_normalize_cutCircleBasepoint A B).symm

/-- The typed based-path image of the complementary generator. -/
noncomputable def apm_t97A03_normalizedImageSecondCutCircleLoop
    (A B : Circle) :
    Path (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1)
      (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  ((apm_t97A03_secondCutCircleLoop A B).map
    (apm_t97A03_continuous_normalizeCutCircle A B)).cast
      (apm_t97A03_normalize_cutCircleBasepoint A B).symm
      (apm_t97A03_normalize_cutCircleBasepoint A B).symm

theorem apm_t97A03_normalizedImageFirstCutCircleLoop_eq (A B : Circle) :
    apm_t97A03_normalizedImageFirstCutCircleLoop A B =
      apm_t97A03_normalizedFirstCutCircleLoop A B := by
  ext t
  rfl

theorem apm_t97A03_normalizedImageSecondCutCircleLoop_eq (A B : Circle) :
    apm_t97A03_normalizedImageSecondCutCircleLoop A B =
      apm_t97A03_normalizedSecondCutCircleLoop A B := by
  ext t
  rfl

/-- The homomorphism on based fundamental groups induced by the literal
sphere-collapse map. -/
noncomputable def apm_t97A03_collapsePiOneHom (A B : Circle) :
    FundamentalGroup (apm_t97A03_BaseSpace A B)
        (apm_t97A03_baseCircle A B A) →*
      FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) :=
  FundamentalGroup.map
    ⟨apm_t97A03_collapseToCutCircle A B,
      apm_t97A03_continuous_collapseToCutCircle A B⟩
    (apm_t97A03_baseCircle A B A)

/-- The first fixed cut-circle generator as an actual fundamental-group
element. -/
noncomputable def apm_t97A03_firstCutCircleGenerator (A B : Circle) :
    FundamentalGroup (apm_t97A03_CutCircle A B)
      (apm_t97A03_cutCircleMap A B A) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (apm_t97A03_firstCutCircleLoop A B))

/-- The complementary fixed cut-circle generator. -/
noncomputable def apm_t97A03_secondCutCircleGenerator (A B : Circle) :
    FundamentalGroup (apm_t97A03_CutCircle A B)
      (apm_t97A03_cutCircleMap A B A) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (apm_t97A03_secondCutCircleLoop A B))

/-- The first normalized class is represented by the genuine normalized
arc-built loop, not by a selected abstract element. -/
noncomputable def apm_t97A03_normalizedFirstCutCircleGenerator
    (A B : Circle) :
    FundamentalGroup (apm_t97A03_CutCircle 1 (A⁻¹ * B))
      (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      (apm_t97A03_normalizedFirstCutCircleLoop A B))

/-- The complementary normalized class retains the second literal arc. -/
noncomputable def apm_t97A03_normalizedSecondCutCircleGenerator
    (A B : Circle) :
    FundamentalGroup (apm_t97A03_CutCircle 1 (A⁻¹ * B))
      (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      (apm_t97A03_normalizedSecondCutCircleLoop A B))

theorem apm_t97A03_normalizedImageFirstGenerator_eq (A B : Circle) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (apm_t97A03_normalizedImageFirstCutCircleLoop A B)) =
      apm_t97A03_normalizedFirstCutCircleGenerator A B := by
  rw [apm_t97A03_normalizedImageFirstCutCircleLoop_eq]
  rfl

theorem apm_t97A03_normalizedImageSecondGenerator_eq (A B : Circle) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (apm_t97A03_normalizedImageSecondCutCircleLoop A B)) =
      apm_t97A03_normalizedSecondCutCircleGenerator A B := by
  rw [apm_t97A03_normalizedImageSecondCutCircleLoop_eq]
  rfl

/-- The geometric normalization homeomorphism transports the based
fundamental group at the literal cut point. -/
noncomputable def apm_t97A03_cutCircleNormalizePiOneHom (A B : Circle) :
    FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) →*
      FundamentalGroup (apm_t97A03_CutCircle 1 (A⁻¹ * B))
        (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  FundamentalGroup.mapOfEq
    ⟨apm_t97A03_normalizeCutCircle A B,
      apm_t97A03_continuous_normalizeCutCircle A B⟩
    (apm_t97A03_normalize_cutCircleBasepoint A B)

/-- Normalization carries the first genuine cut generator to the first
normalized arc class. -/
theorem apm_t97A03_cutCircleNormalizePiOneHom_first (A B : Circle) :
    apm_t97A03_cutCircleNormalizePiOneHom A B
        (apm_t97A03_firstCutCircleGenerator A B) =
      apm_t97A03_normalizedFirstCutCircleGenerator A B := by
  simp only [apm_t97A03_cutCircleNormalizePiOneHom,
    apm_t97A03_firstCutCircleGenerator,
    FundamentalGroup.mapOfEq_apply]
  exact apm_t97A03_normalizedImageFirstGenerator_eq A B

/-- Normalization carries the complementary genuine cut generator to the
complementary normalized arc class. -/
theorem apm_t97A03_cutCircleNormalizePiOneHom_second (A B : Circle) :
    apm_t97A03_cutCircleNormalizePiOneHom A B
        (apm_t97A03_secondCutCircleGenerator A B) =
      apm_t97A03_normalizedSecondCutCircleGenerator A B := by
  simp only [apm_t97A03_cutCircleNormalizePiOneHom,
    apm_t97A03_secondCutCircleGenerator,
    FundamentalGroup.mapOfEq_apply]
  exact apm_t97A03_normalizedImageSecondGenerator_eq A B

lemma apm_t97A03_denormalize_cutCircleBasepoint (A B : Circle) :
    apm_t97A03_denormalizeCutCircle A B
        (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) =
      apm_t97A03_cutCircleMap A B A := by
  change apm_t97A03_cutCircleMap A B (A * 1) = _
  simp

/-- The inverse geometric transport on based fundamental groups. -/
noncomputable def apm_t97A03_cutCircleDenormalizePiOneHom (A B : Circle) :
    FundamentalGroup (apm_t97A03_CutCircle 1 (A⁻¹ * B))
        (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) →*
      FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) :=
  FundamentalGroup.mapOfEq
    ⟨apm_t97A03_denormalizeCutCircle A B,
      apm_t97A03_continuous_denormalizeCutCircle A B⟩
    (apm_t97A03_denormalize_cutCircleBasepoint A B)

/-- The two literal quotient rotations induce mutually inverse maps on pi1. -/
theorem apm_t97A03_cutCircleNormalizePiOneHom_bijective (A B : Circle) :
    Function.Bijective (apm_t97A03_cutCircleNormalizePiOneHom A B) := by
  let e := ConstructionTargets.PolygonSurfaceHomology.fundamentalGroupEquivOfHomeomorphEq
    (apm_t97A03_cutCircleNormalizeHomeomorph A B)
    (apm_t97A03_cutCircleMap A B A)
    (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1)
    (apm_t97A03_normalize_cutCircleBasepoint A B)
  have he : (e : FundamentalGroup (apm_t97A03_CutCircle A B)
      (apm_t97A03_cutCircleMap A B A) →
      FundamentalGroup (apm_t97A03_CutCircle 1 (A⁻¹ * B))
        (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1)) =
      apm_t97A03_cutCircleNormalizePiOneHom A B := rfl
  rw [← he]
  exact e.bijective

/-- On a represented loop, the induced homomorphism is represented by its
literal image under collapse. -/
lemma apm_t97A03_collapsePiOneHom_apply (A B : Circle)
    (q : Path (apm_t97A03_baseCircle A B A)
      (apm_t97A03_baseCircle A B A)) :
    apm_t97A03_collapsePiOneHom A B
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (q.map (apm_t97A03_continuous_collapseToCutCircle A B))) := by
  rfl

/-- The collapsed sphere-return segment, rebased at the identified cut point. -/
noncomputable def apm_t97A03_collapsedSphereReturnLoop (A B : Circle) :
    Path (apm_t97A03_cutCircleMap A B A)
      (apm_t97A03_cutCircleMap A B A) :=
  ((((apm_t97A03_baseSphereReturn A B).cast
      (apm_t97A03_baseCircle_A A B)
      (apm_t97A03_baseCircle_B A B)).symm).map
        (apm_t97A03_continuous_collapseToCutCircle A B)).cast
    (apm_t97A03_cutCircleMap_A_eq_B A B) rfl

/-- The literal sphere return contributes the identity after collapse, not a
synthetic second generator. -/
lemma apm_t97A03_collapsedSphereReturnLoop_eq_refl (A B : Circle) :
    apm_t97A03_collapsedSphereReturnLoop A B =
      Path.refl (apm_t97A03_cutCircleMap A B A) := by
  ext t
  rfl

lemma apm_t97A03_collapsedSphereReturnClass_eq_one (A B : Circle) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (apm_t97A03_collapsedSphereReturnLoop A B)) = 1 := by
  rw [apm_t97A03_collapsedSphereReturnLoop_eq_refl]
  rfl

/-- The collapsed first literal circle arc, rebased at the cut point. -/
noncomputable def apm_t97A03_collapsedFirstArcLoop (A B : Circle) :
    Path (apm_t97A03_cutCircleMap A B A)
      (apm_t97A03_cutCircleMap A B A) :=
  ((apm_t97A03_baseCircleArc A B).map
      (apm_t97A03_continuous_collapseToCutCircle A B)).cast rfl
    (apm_t97A03_cutCircleMap_A_eq_B A B)

/-- The collapsed complementary literal arc, rebased at the cut point. -/
noncomputable def apm_t97A03_collapsedSecondArcLoop (A B : Circle) :
    Path (apm_t97A03_cutCircleMap A B A)
      (apm_t97A03_cutCircleMap A B A) :=
  ((apm_t97A03_baseComplementaryCircleArc A B).map
      (apm_t97A03_continuous_collapseToCutCircle A B)).cast rfl
    (apm_t97A03_cutCircleMap_A_eq_B A B)

lemma apm_t97A03_collapsedFirstArcLoop_eq (A B : Circle) :
    apm_t97A03_collapsedFirstArcLoop A B =
      apm_t97A03_firstCutCircleLoop A B := by
  rfl

lemma apm_t97A03_collapsedSecondArcLoop_eq (A B : Circle) :
    apm_t97A03_collapsedSecondArcLoop A B =
      apm_t97A03_secondCutCircleLoop A B := by
  rfl

lemma apm_t97A03_collapsedFirstArcClass_eq_generator (A B : Circle) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (apm_t97A03_collapsedFirstArcLoop A B)) =
      apm_t97A03_firstCutCircleGenerator A B := by
  rw [apm_t97A03_collapsedFirstArcLoop_eq]
  rfl

lemma apm_t97A03_collapsedSecondArcClass_eq_generator (A B : Circle) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (apm_t97A03_collapsedSecondArcLoop A B)) =
      apm_t97A03_secondCutCircleGenerator A B := by
  rw [apm_t97A03_collapsedSecondArcLoop_eq]
  rfl

/-- A genuine based loop in the frozen base: traverse the literal circle
summand from `A` to `B`, then return through the literal sphere summand. -/
noncomputable def apm_t97A03_firstLiteralLoop (A B : Circle) :
    Path (apm_t97A03_baseCircle A B A) (apm_t97A03_baseCircle A B A) :=
  (apm_t97A03_baseCircleArc A B).trans
    ((apm_t97A03_baseSphereReturn A B).cast
      (apm_t97A03_baseCircle_A A B) (apm_t97A03_baseCircle_B A B)).symm

/-- The based loop obtained from the genuinely complementary lifted circle
arc and the same literal sphere return. -/
noncomputable def apm_t97A03_secondLiteralLoop (A B : Circle) :
    Path (apm_t97A03_baseCircle A B A) (apm_t97A03_baseCircle A B A) :=
  (apm_t97A03_baseComplementaryCircleArc A B).trans
    ((apm_t97A03_baseSphereReturn A B).cast
      (apm_t97A03_baseCircle_A A B) (apm_t97A03_baseCircle_B A B)).symm

lemma apm_t97A03_collapse_firstLiteralLoop_path (A B : Circle) :
    (apm_t97A03_firstLiteralLoop A B).map
        (apm_t97A03_continuous_collapseToCutCircle A B) =
      (apm_t97A03_collapsedFirstArcLoop A B).trans
        (apm_t97A03_collapsedSphereReturnLoop A B) := by
  rw [apm_t97A03_firstLiteralLoop, Path.map_trans]
  unfold apm_t97A03_collapsedFirstArcLoop
  unfold apm_t97A03_collapsedSphereReturnLoop
  rw [← Path.cast_trans]
  rfl

lemma apm_t97A03_collapse_secondLiteralLoop_path (A B : Circle) :
    (apm_t97A03_secondLiteralLoop A B).map
        (apm_t97A03_continuous_collapseToCutCircle A B) =
      (apm_t97A03_collapsedSecondArcLoop A B).trans
        (apm_t97A03_collapsedSphereReturnLoop A B) := by
  rw [apm_t97A03_secondLiteralLoop, Path.map_trans]
  unfold apm_t97A03_collapsedSecondArcLoop
  unfold apm_t97A03_collapsedSphereReturnLoop
  rw [← Path.cast_trans]
  rfl

/-- The first fixed arc followed by the actual collapsed sphere return is the
first quotient generator. -/
lemma apm_t97A03_collapsedFirstLiteralClass_eq_generator (A B : Circle) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((apm_t97A03_collapsedFirstArcLoop A B).trans
            (apm_t97A03_collapsedSphereReturnLoop A B))) =
      apm_t97A03_firstCutCircleGenerator A B := by
  rw [apm_t97A03_collapsedSphereReturnLoop_eq_refl]
  exact (congrArg FundamentalGroup.fromPath
    (Quotient.sound ⟨Path.Homotopy.transRefl
      (apm_t97A03_collapsedFirstArcLoop A B)⟩)).trans
        (apm_t97A03_collapsedFirstArcClass_eq_generator A B)

/-- The complementary fixed arc followed by the same actual collapsed return
is the second quotient generator. -/
lemma apm_t97A03_collapsedSecondLiteralClass_eq_generator (A B : Circle) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((apm_t97A03_collapsedSecondArcLoop A B).trans
            (apm_t97A03_collapsedSphereReturnLoop A B))) =
      apm_t97A03_secondCutCircleGenerator A B := by
  rw [apm_t97A03_collapsedSphereReturnLoop_eq_refl]
  exact (congrArg FundamentalGroup.fromPath
    (Quotient.sound ⟨Path.Homotopy.transRefl
      (apm_t97A03_collapsedSecondArcLoop A B)⟩)).trans
        (apm_t97A03_collapsedSecondArcClass_eq_generator A B)

/-- The induced map sends the first literal base loop to the first fixed
generator of the cut-circle quotient. -/
lemma apm_t97A03_collapsePiOneHom_firstLiteralLoop (A B : Circle) :
    apm_t97A03_collapsePiOneHom A B
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            (apm_t97A03_firstLiteralLoop A B))) =
      apm_t97A03_firstCutCircleGenerator A B := by
  rw [apm_t97A03_collapsePiOneHom_apply,
    apm_t97A03_collapse_firstLiteralLoop_path]
  exact apm_t97A03_collapsedFirstLiteralClass_eq_generator A B

/-- The induced map sends the complementary literal base loop to the second
fixed generator of the cut-circle quotient. -/
lemma apm_t97A03_collapsePiOneHom_secondLiteralLoop (A B : Circle) :
    apm_t97A03_collapsePiOneHom A B
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            (apm_t97A03_secondLiteralLoop A B))) =
      apm_t97A03_secondCutCircleGenerator A B := by
  rw [apm_t97A03_collapsePiOneHom_apply,
    apm_t97A03_collapse_secondLiteralLoop_path]
  exact apm_t97A03_collapsedSecondLiteralClass_eq_generator A B

@[simp] lemma apm_t97A03_firstLiteralLoop_zero (A B : Circle) :
    apm_t97A03_firstLiteralLoop A B 0 = apm_t97A03_baseCircle A B A :=
  (apm_t97A03_firstLiteralLoop A B).source

@[simp] lemma apm_t97A03_firstLiteralLoop_one (A B : Circle) :
    apm_t97A03_firstLiteralLoop A B 1 = apm_t97A03_baseCircle A B A :=
  (apm_t97A03_firstLiteralLoop A B).target

@[simp] lemma apm_t97A03_secondLiteralLoop_zero (A B : Circle) :
    apm_t97A03_secondLiteralLoop A B 0 = apm_t97A03_baseCircle A B A :=
  (apm_t97A03_secondLiteralLoop A B).source

@[simp] lemma apm_t97A03_secondLiteralLoop_one (A B : Circle) :
    apm_t97A03_secondLiteralLoop A B 1 = apm_t97A03_baseCircle A B A :=
  (apm_t97A03_secondLiteralLoop A B).target

/-- Fiber transport along the first fixed literal quotient loop. -/
noncomputable def apm_t97A03_firstLiteralTransport
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p) :
    Equiv.Perm (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) :=
  ConstructionTargets.t97A03Closure.coveringPathFiberEquiv p hp
    (Quotient.mk'' (apm_t97A03_firstLiteralLoop A B))

/-- Fiber transport along the second fixed literal quotient loop. -/
noncomputable def apm_t97A03_secondLiteralTransport
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p) :
    Equiv.Perm (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) :=
  ConstructionTargets.t97A03Closure.coveringPathFiberEquiv p hp
    (Quotient.mk'' (apm_t97A03_secondLiteralLoop A B))

/-- Once literal-loop generation supplies a moved endpoint, the existing
finite classifier applies to precisely the two geometric arc transports. -/
theorem apm_t97A03_literal_transports_select_model
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (hmoved : (∃ e, apm_t97A03_firstLiteralTransport p hp e ≠ e) ∨
      ∃ e, apm_t97A03_secondLiteralTransport p hp e ≠ e) :
    ∃ label : (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) ≃ Fin 2,
      ∃ firstSwaps secondSwaps model,
        ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
            (apm_t97A03_firstLiteralTransport p hp) =
          (if firstSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
            (apm_t97A03_secondLiteralTransport p hp) =
          (if secondSwaps then Equiv.swap 0 1 else Equiv.refl (Fin 2)) ∧
        ((model = ConstructionTargets.t97A03Closure.DoubleCoverModel.oneCircle ∧
            ∃ swapArcs : Bool,
              (if swapArcs then (secondSwaps, firstSwaps)
                else (firstSwaps, secondSwaps)) = (true, false)) ∨
          (model = ConstructionTargets.t97A03Closure.DoubleCoverModel.twoCircle ∧
            firstSwaps = true ∧ secondSwaps = true)) := by
  exact ConstructionTargets.t97A03Closure.twoArcModel_exists_of_moved_covering_loop
    p hp hdegree _ _ _ hmoved

/-- The exact algebraic consequence required from geometric generation: a
moved loop whose labeled transport is a signed word in the two fixed literal
loop transports forces one of those actual transports to be nonidentity. -/
theorem apm_t97A03_literal_transport_nontrivial_of_generated
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (label : (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) ≃ Fin 2)
    (transport : Equiv.Perm
      (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)))
    (hgenerated : ∃ word,
      ConstructionTargets.t97A03Closure.labeledFiberMonodromy label transport =
        ConstructionTargets.t97A03Closure.twoArcSignedTransportWord
          (ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
            (apm_t97A03_firstLiteralTransport p hp))
          (ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
            (apm_t97A03_secondLiteralTransport p hp)) word)
    (hne : transport ≠ Equiv.refl _) :
    apm_t97A03_firstLiteralTransport p hp ≠ Equiv.refl _ ∨
      apm_t97A03_secondLiteralTransport p hp ≠ Equiv.refl _ := by
  have htransport :=
    (ConstructionTargets.t97A03Closure.labeledFiberMonodromy_ne_refl_iff
      label transport).2 hne
  rcases ConstructionTargets.t97A03Closure.twoArcTransport_nontrivial_of_signed_generated
      _ _ _ hgenerated htransport with hfirst | hsecond
  · exact Or.inl
      ((ConstructionTargets.t97A03Closure.labeledFiberMonodromy_ne_refl_iff
        label _).1 hfirst)
  · exact Or.inr
      ((ConstructionTargets.t97A03Closure.labeledFiberMonodromy_ne_refl_iff
        label _).1 hsecond)

theorem apm_t97A03_literal_transport_moved_of_generated
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (label : (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) ≃ Fin 2)
    (transport : Equiv.Perm
      (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)))
    (hgenerated : ∃ word,
      ConstructionTargets.t97A03Closure.labeledFiberMonodromy label transport =
        ConstructionTargets.t97A03Closure.twoArcSignedTransportWord
          (ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
            (apm_t97A03_firstLiteralTransport p hp))
          (ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
            (apm_t97A03_secondLiteralTransport p hp)) word)
    (hne : transport ≠ Equiv.refl _) :
    (∃ e, apm_t97A03_firstLiteralTransport p hp e ≠ e) ∨
      ∃ e, apm_t97A03_secondLiteralTransport p hp e ≠ e := by
  rcases apm_t97A03_literal_transport_nontrivial_of_generated
      p hp label transport hgenerated hne with hfirst | hsecond
  · exact Or.inl
      ((ConstructionTargets.t97A03Closure.fiberTransport_ne_refl_iff_exists_moved
        _).1 hfirst)
  · exact Or.inr
      ((ConstructionTargets.t97A03Closure.fiberTransport_ne_refl_iff_exists_moved
        _).1 hsecond)

/-- The shared polygon-surface foundation already proves the exact signed-word
normal form needed on the target of the geometric comparison: every based
loop in the two-circle wedge is a word in its two fixed positive leg loops.
This specialization prevents the literal-base comparison from rebuilding a
second, problem-local van Kampen calculation. -/
theorem apm_t97A03_twoCircleWedge_exists_signedGeneratorWord
    (g : FundamentalGroup
      (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (Fin 2))
      (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (0 : Fin 2) 1)) :
    ∃ w : ConstructionTargets.PolygonSurfaceHomology.FiniteWedgeFinGeneratorWord 1,
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinGeneratorWordValue
          1 w = g := by
  exact
    ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFin_exists_generatorWord
      1 g

/-- Evaluate an integer-exponent word in two distinguished elements. -/
def apm_t97A03_twoGeneratorWord {G : Type*} [Group G]
    (first second : G) (w : List (Fin 2 × ℤ)) : G :=
  (w.map fun q ↦ (if q.1 = 0 then first else second) ^ q.2).prod

lemma apm_t97A03_twoGeneratorWord_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (first second : G) (w : List (Fin 2 × ℤ)) :
    f (apm_t97A03_twoGeneratorWord first second w) =
      apm_t97A03_twoGeneratorWord (f first) (f second) w := by
  simp only [apm_t97A03_twoGeneratorWord, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨i, z⟩ hi
  fin_cases i <;> simp [map_zpow]

/-- Signed generation for the normalized literal quotient transports back
to the original marked quotient through the geometric rotation. -/
theorem apm_t97A03_cutCircle_signed_generation_of_normalized
    (A B : Circle)
    (hnormalized : ∀ g : FundamentalGroup
        (apm_t97A03_CutCircle 1 (A⁻¹ * B))
        (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (apm_t97A03_normalizedFirstCutCircleGenerator A B)
          (apm_t97A03_normalizedSecondCutCircleGenerator A B) w = g) :
    ∀ g : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (apm_t97A03_firstCutCircleGenerator A B)
          (apm_t97A03_secondCutCircleGenerator A B) w = g := by
  intro g
  rcases hnormalized (apm_t97A03_cutCircleNormalizePiOneHom A B g) with
    ⟨w, hw⟩
  refine ⟨w, (apm_t97A03_cutCircleNormalizePiOneHom_bijective A B).1 ?_⟩
  rw [apm_t97A03_twoGeneratorWord_map,
    apm_t97A03_cutCircleNormalizePiOneHom_first,
    apm_t97A03_cutCircleNormalizePiOneHom_second]
  exact hw

/-- The concrete free-group evaluation map determined by the two geometric
arcs of the cut-circle quotient.  Proving this map bijective is now the exact
remaining van Kampen calculation for the cut representation. -/
noncomputable def apm_t97A03_cutGeneratorFreeGroupMap (A B : Circle) :
    FreeGroup (Fin 2) →*
      FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) :=
  FreeGroup.lift (fun i => if i = 0 then
    apm_t97A03_firstCutCircleGenerator A B else
    apm_t97A03_secondCutCircleGenerator A B)

/-- Free-word evaluation on the two genuine arcs of the normalized literal
cut quotient. -/
noncomputable def apm_t97A03_normalizedCutGeneratorFreeGroupMap
    (A B : Circle) :
    FreeGroup (Fin 2) →*
      FundamentalGroup (apm_t97A03_CutCircle 1 (A⁻¹ * B))
        (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1) :=
  FreeGroup.lift (fun i => if i = 0 then
    apm_t97A03_normalizedFirstCutCircleGenerator A B else
    apm_t97A03_normalizedSecondCutCircleGenerator A B)

/-- The geometric normalization square commutes on every free word, not only
on the two generators. -/
theorem apm_t97A03_normalize_comp_cutGeneratorFreeGroupMap (A B : Circle) :
    (apm_t97A03_cutCircleNormalizePiOneHom A B).comp
        (apm_t97A03_cutGeneratorFreeGroupMap A B) =
      apm_t97A03_normalizedCutGeneratorFreeGroupMap A B := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i
  · simp [apm_t97A03_cutGeneratorFreeGroupMap,
      apm_t97A03_normalizedCutGeneratorFreeGroupMap,
      apm_t97A03_cutCircleNormalizePiOneHom_first]
  · simp [apm_t97A03_cutGeneratorFreeGroupMap,
      apm_t97A03_normalizedCutGeneratorFreeGroupMap,
      apm_t97A03_cutCircleNormalizePiOneHom_second]

/-- The normalized free-word calculation is exactly equivalent to the
original one, because the vertical geometric normalization is bijective. -/
theorem apm_t97A03_cutGenerator_bijective_iff_normalized (A B : Circle) :
    Function.Bijective (apm_t97A03_cutGeneratorFreeGroupMap A B) ↔
      Function.Bijective
        (apm_t97A03_normalizedCutGeneratorFreeGroupMap A B) := by
  let n := apm_t97A03_cutCircleNormalizePiOneHom A B
  have hn := apm_t97A03_cutCircleNormalizePiOneHom_bijective A B
  have hs : n.comp (apm_t97A03_cutGeneratorFreeGroupMap A B) =
      apm_t97A03_normalizedCutGeneratorFreeGroupMap A B :=
    apm_t97A03_normalize_comp_cutGeneratorFreeGroupMap A B
  constructor
  · rintro ⟨hi, hsurr⟩
    constructor
    · intro x y hxy
      apply hi
      apply hn.1
      simpa only [← hs, MonoidHom.comp_apply] using hxy
    · intro y
      rcases hn.2 y with ⟨g, rfl⟩
      rcases hsurr g with ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      rw [← hs]
      rfl
  · rintro ⟨hi, hsurr⟩
    constructor
    · intro x y hxy
      apply hi
      simpa only [← hs, MonoidHom.comp_apply, hxy]
    · intro g
      rcases hsurr (n g) with ⟨x, hx⟩
      refine ⟨x, hn.1 ?_⟩
      simpa only [← hs, MonoidHom.comp_apply] using hx

@[simp] lemma apm_t97A03_cutGeneratorFreeGroupMap_zero (A B : Circle) :
    apm_t97A03_cutGeneratorFreeGroupMap A B (FreeGroup.of (0 : Fin 2)) =
      apm_t97A03_firstCutCircleGenerator A B := by
  simp [apm_t97A03_cutGeneratorFreeGroupMap]

@[simp] lemma apm_t97A03_cutGeneratorFreeGroupMap_one (A B : Circle) :
    apm_t97A03_cutGeneratorFreeGroupMap A B (FreeGroup.of (1 : Fin 2)) =
      apm_t97A03_secondCutCircleGenerator A B := by
  simp [apm_t97A03_cutGeneratorFreeGroupMap]

/-- A decoder with the correct values on the two genuine cut arcs is a left
inverse to their free-group evaluation map. -/
theorem apm_t97A03_cutGeneratorFreeGroupMap_leftInverse_of_decoder
    (A B : Circle)
    (decode : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) →* FreeGroup (Fin 2))
    (hfirst : decode (apm_t97A03_firstCutCircleGenerator A B) =
      FreeGroup.of (0 : Fin 2))
    (hsecond : decode (apm_t97A03_secondCutCircleGenerator A B) =
      FreeGroup.of (1 : Fin 2)) :
    Function.LeftInverse decode (apm_t97A03_cutGeneratorFreeGroupMap A B) := by
  have hcomp : decode.comp (apm_t97A03_cutGeneratorFreeGroupMap A B) =
      MonoidHom.id (FreeGroup (Fin 2)) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i <;> simp [hfirst, hsecond]
  intro x
  change (decode.comp (apm_t97A03_cutGeneratorFreeGroupMap A B)) x = x
  rw [hcomp]
  rfl

/-- Thus the geometric decoder equations prove freeness of the two concrete
cut generators, rather than merely postulating injectivity. -/
theorem apm_t97A03_cutGeneratorFreeGroupMap_injective_of_decoder
    (A B : Circle)
    (decode : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) →* FreeGroup (Fin 2))
    (hfirst : decode (apm_t97A03_firstCutCircleGenerator A B) =
      FreeGroup.of (0 : Fin 2))
    (hsecond : decode (apm_t97A03_secondCutCircleGenerator A B) =
      FreeGroup.of (1 : Fin 2)) :
    Function.Injective (apm_t97A03_cutGeneratorFreeGroupMap A B) :=
  (apm_t97A03_cutGeneratorFreeGroupMap_leftInverse_of_decoder
    A B decode hfirst hsecond).injective

/-- Free-group evaluation on the two actual literal loops in the uncollapsed
base quotient. -/
noncomputable def apm_t97A03_literalGeneratorFreeGroupMap (A B : Circle) :
    FreeGroup (Fin 2) →*
      FundamentalGroup (apm_t97A03_BaseSpace A B)
        (apm_t97A03_baseCircle A B A) :=
  FreeGroup.lift (fun i => if i = 0 then
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (apm_t97A03_firstLiteralLoop A B)) else
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (apm_t97A03_secondLiteralLoop A B)))

/-- Collapse intertwines the two concrete free evaluations generator by
generator; this is the representation-level square needed for injectivity. -/
theorem apm_t97A03_collapse_comp_literalGeneratorFreeGroupMap (A B : Circle) :
    (apm_t97A03_collapsePiOneHom A B).comp
        (apm_t97A03_literalGeneratorFreeGroupMap A B) =
      apm_t97A03_cutGeneratorFreeGroupMap A B := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i
  · simp [apm_t97A03_literalGeneratorFreeGroupMap,
      apm_t97A03_collapsePiOneHom_firstLiteralLoop]
  · simp [apm_t97A03_literalGeneratorFreeGroupMap,
      apm_t97A03_collapsePiOneHom_secondLiteralLoop]

/-- If the two literal loops generate the source and the corresponding cut
generators are free, the actual collapse map is injective. -/
theorem apm_t97A03_collapsePiOneHom_injective_of_literal_surjective_cut_injective
    (A B : Circle)
    (hliteral : Function.Surjective
      (apm_t97A03_literalGeneratorFreeGroupMap A B))
    (hcut : Function.Injective
      (apm_t97A03_cutGeneratorFreeGroupMap A B)) :
    Function.Injective (apm_t97A03_collapsePiOneHom A B) := by
  intro x y hxy
  rcases hliteral x with ⟨u, rfl⟩
  rcases hliteral y with ⟨v, rfl⟩
  apply congrArg (apm_t97A03_literalGeneratorFreeGroupMap A B)
  apply hcut
  simpa only [← apm_t97A03_collapse_comp_literalGeneratorFreeGroupMap A B,
    MonoidHom.comp_apply] using hxy

/-- The free-group element spelling a signed word in the two cut arcs. -/
def apm_t97A03_cutFreeGroupWord (w : List (Fin 2 × ℤ)) : FreeGroup (Fin 2) :=
  (w.map fun q => FreeGroup.of q.1 ^ q.2).prod

/-- Every element of the free group has an explicit signed-list spelling in
the same format used by the two geometric arc calculations. -/
theorem apm_t97A03_exists_cutFreeGroupWord (x : FreeGroup (Fin 2)) :
    ∃ w : List (Fin 2 × ℤ), apm_t97A03_cutFreeGroupWord w = x := by
  induction x using FreeGroup.induction_on with
  | C1 => exact ⟨[], by simp [apm_t97A03_cutFreeGroupWord]⟩
  | of i => exact ⟨[(i, 1)], by simp [apm_t97A03_cutFreeGroupWord]⟩
  | inv_of i hi =>
      exact ⟨[(i, -1)], by simp [apm_t97A03_cutFreeGroupWord]⟩
  | mul x y hx hy =>
      rcases hx with ⟨wx, rfl⟩
      rcases hy with ⟨wy, rfl⟩
      exact ⟨wx ++ wy, by simp [apm_t97A03_cutFreeGroupWord,
        List.map_append, List.prod_append]⟩

/-- The explicit free word evaluates to the corresponding signed word in the
two actual literal loops. -/
lemma apm_t97A03_literalGeneratorFreeGroupMap_word (A B : Circle)
    (w : List (Fin 2 × ℤ)) :
    apm_t97A03_literalGeneratorFreeGroupMap A B
        (apm_t97A03_cutFreeGroupWord w) =
      apm_t97A03_twoGeneratorWord
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (apm_t97A03_firstLiteralLoop A B)))
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (apm_t97A03_secondLiteralLoop A B))) w := by
  simp only [apm_t97A03_cutFreeGroupWord, apm_t97A03_twoGeneratorWord,
    map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨i, z⟩ hi
  fin_cases i <;> simp [apm_t97A03_literalGeneratorFreeGroupMap, map_zpow]

/-- Signed generation by the two literal quotient loops gives surjectivity of
their concrete free-group evaluation. -/
theorem apm_t97A03_literalGeneratorFreeGroupMap_surjective_of_signed_generation
    (A B : Circle)
    (hgenerated : ∀ g : FundamentalGroup (apm_t97A03_BaseSpace A B)
        (apm_t97A03_baseCircle A B A),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (apm_t97A03_firstLiteralLoop A B)))
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (apm_t97A03_secondLiteralLoop A B))) w = g) :
    Function.Surjective (apm_t97A03_literalGeneratorFreeGroupMap A B) := by
  intro g
  rcases hgenerated g with ⟨w, hw⟩
  exact ⟨apm_t97A03_cutFreeGroupWord w,
    (apm_t97A03_literalGeneratorFreeGroupMap_word A B w).trans hw⟩

/-- Literal signed generation and cut freeness discharge the injectivity of
the concrete collapse map. -/
theorem apm_t97A03_collapsePiOneHom_injective_of_literal_signed_generation
    (A B : Circle)
    (hgenerated : ∀ g : FundamentalGroup (apm_t97A03_BaseSpace A B)
        (apm_t97A03_baseCircle A B A),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (apm_t97A03_firstLiteralLoop A B)))
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (apm_t97A03_secondLiteralLoop A B))) w = g)
    (hcut : Function.Injective (apm_t97A03_cutGeneratorFreeGroupMap A B)) :
    Function.Injective (apm_t97A03_collapsePiOneHom A B) :=
  apm_t97A03_collapsePiOneHom_injective_of_literal_surjective_cut_injective
    A B
    (apm_t97A03_literalGeneratorFreeGroupMap_surjective_of_signed_generation
      A B hgenerated)
    hcut

/-- Evaluation of the explicit free word is exactly the corresponding signed
word in the two geometric cut generators. -/
lemma apm_t97A03_cutGeneratorFreeGroupMap_word (A B : Circle)
    (w : List (Fin 2 × ℤ)) :
    apm_t97A03_cutGeneratorFreeGroupMap A B
        (apm_t97A03_cutFreeGroupWord w) =
      apm_t97A03_twoGeneratorWord
        (apm_t97A03_firstCutCircleGenerator A B)
        (apm_t97A03_secondCutCircleGenerator A B) w := by
  simp only [apm_t97A03_cutFreeGroupWord, apm_t97A03_twoGeneratorWord,
    map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨i, z⟩ hi
  fin_cases i <;> simp [map_zpow]

/-- The explicit list word evaluates to the corresponding signed word in the
two genuine normalized arc classes.  This is the computational half of the
pending normalized generation theorem, with no abstract generator selector. -/
lemma apm_t97A03_normalizedCutGeneratorFreeGroupMap_word
    (A B : Circle) (w : List (Fin 2 × ℤ)) :
    apm_t97A03_normalizedCutGeneratorFreeGroupMap A B
        (apm_t97A03_cutFreeGroupWord w) =
      apm_t97A03_twoGeneratorWord
        (apm_t97A03_normalizedFirstCutCircleGenerator A B)
        (apm_t97A03_normalizedSecondCutCircleGenerator A B) w := by
  simp only [apm_t97A03_cutFreeGroupWord, apm_t97A03_twoGeneratorWord,
    map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨i, z⟩ hi
  fin_cases i <;>
    simp [apm_t97A03_normalizedCutGeneratorFreeGroupMap, map_zpow]

/-- Surjectivity of the concrete normalized evaluation is exactly signed
generation by the two genuine complementary arcs; the reverse direction uses
the explicit free-group spelling above. -/
theorem apm_t97A03_normalized_signed_generation_iff_surjective (A B : Circle) :
    (∀ g : FundamentalGroup
        (apm_t97A03_CutCircle 1 (A⁻¹ * B))
        (apm_t97A03_cutCircleMap 1 (A⁻¹ * B) 1),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (apm_t97A03_normalizedFirstCutCircleGenerator A B)
          (apm_t97A03_normalizedSecondCutCircleGenerator A B) w = g) ↔
      Function.Surjective
        (apm_t97A03_normalizedCutGeneratorFreeGroupMap A B) := by
  constructor
  · intro h g
    rcases h g with ⟨w, hw⟩
    exact ⟨apm_t97A03_cutFreeGroupWord w,
      (apm_t97A03_normalizedCutGeneratorFreeGroupMap_word A B w).trans hw⟩
  · intro h g
    rcases h g with ⟨x, rfl⟩
    rcases apm_t97A03_exists_cutFreeGroupWord x with ⟨w, rfl⟩
    exact ⟨w, (apm_t97A03_normalizedCutGeneratorFreeGroupMap_word A B w).symm⟩

/-- Signed-word generation by the two concrete cut arcs is precisely enough
for surjectivity of their free-group evaluation map. -/
theorem apm_t97A03_cutGeneratorFreeGroupMap_surjective_of_signed_generation
    (A B : Circle)
    (hgenerated : ∀ g : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (apm_t97A03_firstCutCircleGenerator A B)
          (apm_t97A03_secondCutCircleGenerator A B) w = g) :
    Function.Surjective (apm_t97A03_cutGeneratorFreeGroupMap A B) := by
  intro g
  rcases hgenerated g with ⟨w, hw⟩
  exact ⟨apm_t97A03_cutFreeGroupWord w,
    (apm_t97A03_cutGeneratorFreeGroupMap_word A B w).trans hw⟩

/-- Bijectivity of the explicit cut-generator evaluation map produces the
required cut-to-standard-wedge equivalence with both generator alignments,
so no arbitrary abstract equivalence may be substituted at this boundary. -/
theorem apm_t97A03_exists_aligned_cut_piOneEquiv_of_generator_bijective
    (A B : Circle)
    (hbij : Function.Bijective (apm_t97A03_cutGeneratorFreeGroupMap A B)) :
    ∃ e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1),
      e (apm_t97A03_firstCutCircleGenerator A B) =
          ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass ∧
        e (apm_t97A03_secondCutCircleGenerator A B) =
          ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass := by
  let cutFree : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) ≃* FreeGroup (Fin 2) :=
    (MulEquiv.ofBijective (apm_t97A03_cutGeneratorFreeGroupMap A B) hbij).symm
  let freeWedge : FreeGroup (Fin 2) ≃*
      FundamentalGroup
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (Fin 2))
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin 2) 1) :=
    MulEquiv.ofBijective
      (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap 1)
      ⟨ConstructionTargets.PolygonCellPiOne.finiteWedgeFinLegFreeGroupMap_injective 1,
        ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap_surjective 1⟩
  refine ⟨cutFree.trans freeWedge, ?_, ?_⟩
  · have hz : cutFree (apm_t97A03_firstCutCircleGenerator A B) =
        FreeGroup.of (0 : Fin 2) := by
      apply cutFree.symm.injective
      simp [cutFree]
    change freeWedge (cutFree (apm_t97A03_firstCutCircleGenerator A B)) = _
    rw [hz]
    simp [freeWedge,
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap]
  · have ho : cutFree (apm_t97A03_secondCutCircleGenerator A B) =
        FreeGroup.of (1 : Fin 2) := by
      apply cutFree.symm.injective
      simp [cutFree]
    change freeWedge (cutFree (apm_t97A03_secondCutCircleGenerator A B)) = _
    rw [ho]
    simp [freeWedge,
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap]

/-- The remaining cut-circle calculation can therefore be stated without an
opaque bijectivity hypothesis: freeness plus geometric signed generation. -/
theorem apm_t97A03_exists_aligned_cut_piOneEquiv_of_free_and_generated
    (A B : Circle)
    (hinj : Function.Injective (apm_t97A03_cutGeneratorFreeGroupMap A B))
    (hgenerated : ∀ g : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (apm_t97A03_firstCutCircleGenerator A B)
          (apm_t97A03_secondCutCircleGenerator A B) w = g) :
    ∃ e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1),
      e (apm_t97A03_firstCutCircleGenerator A B) =
          ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass ∧
        e (apm_t97A03_secondCutCircleGenerator A B) =
          ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass := by
  apply apm_t97A03_exists_aligned_cut_piOneEquiv_of_generator_bijective
  exact ⟨hinj,
    apm_t97A03_cutGeneratorFreeGroupMap_surjective_of_signed_generation
      A B hgenerated⟩

/-- A geometric decoder and signed generation together discharge the whole
cut-circle representation boundary, including both literal arc alignments. -/
theorem apm_t97A03_exists_aligned_cut_piOneEquiv_of_decoder_and_generated
    (A B : Circle)
    (decode : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A) →* FreeGroup (Fin 2))
    (hfirst : decode (apm_t97A03_firstCutCircleGenerator A B) =
      FreeGroup.of (0 : Fin 2))
    (hsecond : decode (apm_t97A03_secondCutCircleGenerator A B) =
      FreeGroup.of (1 : Fin 2))
    (hgenerated : ∀ g : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (apm_t97A03_firstCutCircleGenerator A B)
          (apm_t97A03_secondCutCircleGenerator A B) w = g) :
    ∃ e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1),
      e (apm_t97A03_firstCutCircleGenerator A B) =
          ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass ∧
        e (apm_t97A03_secondCutCircleGenerator A B) =
          ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass := by
  exact apm_t97A03_exists_aligned_cut_piOneEquiv_of_free_and_generated A B
    (apm_t97A03_cutGeneratorFreeGroupMap_injective_of_decoder
      A B decode hfirst hsecond) hgenerated

/-- Exact algebraic contract for the pending geometric comparison.  Once an
equivalence identifies the literal base fundamental group with the finite
two-circle wedge, every literal loop is a signed word in the inverse images
of the two genuine wedge-leg generators. -/
theorem apm_t97A03_signed_generation_of_piOneEquiv
    {G : Type*} [Group G]
    (e : G ≃*
      FundamentalGroup
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (Fin 2))
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin 2) 1)) (g : G) :
    ∃ w : List (Fin 2 × ℤ),
      apm_t97A03_twoGeneratorWord
        (e.symm (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
          1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass))
        (e.symm (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
          1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass))
        w = g := by
  rcases apm_t97A03_twoCircleWedge_exists_signedGeneratorWord (e g) with ⟨w, hw⟩
  refine ⟨w, e.injective ?_⟩
  change e ((w.map fun q ↦
    (if q.1 = 0 then
      e.symm (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    else
      e.symm (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)) ^ q.2).prod) = e g
  rw [map_list_prod]
  have hword :
      (w.map fun q ↦ e
        ((if q.1 = 0 then
          e.symm (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
        else
          e.symm (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
            1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)) ^ q.2)).prod =
        ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinGeneratorWordValue
          1 w := by
    rw [ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinGeneratorWordValue]
    apply congrArg List.prod
    apply List.map_congr_left
    rintro ⟨i, z⟩ hi
    fin_cases i <;> simp [map_zpow]
  simpa [List.map_map, Function.comp_def] using hword.trans hw

/-- A cut-circle pi1 equivalence aligned with the two literal cut generators
turns the abstract wedge normal form into a word in those exact generators. -/
theorem apm_t97A03_cutCircle_signed_generation_of_aligned_piOneEquiv
    (A B : Circle)
    (e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1))
    (hfirst : e (apm_t97A03_firstCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hsecond : e (apm_t97A03_secondCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (g : FundamentalGroup (apm_t97A03_CutCircle A B)
      (apm_t97A03_cutCircleMap A B A)) :
    ∃ w : List (Fin 2 × ℤ),
      apm_t97A03_twoGeneratorWord
        (apm_t97A03_firstCutCircleGenerator A B)
        (apm_t97A03_secondCutCircleGenerator A B) w = g := by
  rcases apm_t97A03_signed_generation_of_piOneEquiv e g with ⟨w, hw⟩
  have hf : e.symm
      (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass) =
      apm_t97A03_firstCutCircleGenerator A B := by
    rw [← hfirst, e.symm_apply_apply]
  have hs : e.symm
      (ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass) =
      apm_t97A03_secondCutCircleGenerator A B := by
    rw [← hsecond, e.symm_apply_apply]
  exact ⟨w, by simpa [hf, hs] using hw⟩

/-- Generation by the two fixed cut classes makes the literal collapse
surjective on pi1, because both generators have the compiled literal lifts. -/
theorem apm_t97A03_collapsePiOneHom_surjective_of_cut_generation
    (A B : Circle)
    (hgenerated : ∀ g : FundamentalGroup (apm_t97A03_CutCircle A B)
        (apm_t97A03_cutCircleMap A B A),
      ∃ w : List (Fin 2 × ℤ),
        apm_t97A03_twoGeneratorWord
          (apm_t97A03_firstCutCircleGenerator A B)
          (apm_t97A03_secondCutCircleGenerator A B) w = g) :
    Function.Surjective (apm_t97A03_collapsePiOneHom A B) := by
  intro g
  rcases hgenerated g with ⟨w, hw⟩
  refine ⟨apm_t97A03_twoGeneratorWord
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (apm_t97A03_firstLiteralLoop A B)))
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (apm_t97A03_secondLiteralLoop A B))) w, ?_⟩
  rw [apm_t97A03_twoGeneratorWord_map,
    apm_t97A03_collapsePiOneHom_firstLiteralLoop,
    apm_t97A03_collapsePiOneHom_secondLiteralLoop]
  exact hw

theorem apm_t97A03_collapsePiOneHom_surjective_of_aligned_piOneEquiv
    (A B : Circle)
    (e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1))
    (hfirst : e (apm_t97A03_firstCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hsecond : e (apm_t97A03_secondCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass) :
    Function.Surjective (apm_t97A03_collapsePiOneHom A B) := by
  apply apm_t97A03_collapsePiOneHom_surjective_of_cut_generation
  exact apm_t97A03_cutCircle_signed_generation_of_aligned_piOneEquiv
    A B e hfirst hsecond

/-- Injectivity of the literal collapse, together with the aligned cut-circle
normal form, reduces every literal pi1 class to a signed word in the two
actual literal loops. -/
theorem apm_t97A03_literal_signed_generation_of_collapse_injective
    (A B : Circle)
    (e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1))
    (hfirst : e (apm_t97A03_firstCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hsecond : e (apm_t97A03_secondCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hinj : Function.Injective (apm_t97A03_collapsePiOneHom A B))
    (g : FundamentalGroup (apm_t97A03_BaseSpace A B)
      (apm_t97A03_baseCircle A B A)) :
    ∃ w : List (Fin 2 × ℤ),
      apm_t97A03_twoGeneratorWord
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (apm_t97A03_firstLiteralLoop A B)))
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (apm_t97A03_secondLiteralLoop A B))) w = g := by
  rcases apm_t97A03_cutCircle_signed_generation_of_aligned_piOneEquiv
      A B e hfirst hsecond (apm_t97A03_collapsePiOneHom A B g) with ⟨w, hw⟩
  refine ⟨w, hinj ?_⟩
  rw [apm_t97A03_twoGeneratorWord_map,
    apm_t97A03_collapsePiOneHom_firstLiteralLoop,
    apm_t97A03_collapsePiOneHom_secondLiteralLoop]
  exact hw

/-- An injective collapse, together with an aligned computation of the cut
circle fundamental group, identifies the literal base fundamental group with
the fixed two-circle wedge group. -/
noncomputable def apm_t97A03_literalPiOneEquiv_of_collapse_injective
    (A B : Circle)
    (e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1))
    (hfirst : e (apm_t97A03_firstCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hsecond : e (apm_t97A03_secondCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hinj : Function.Injective (apm_t97A03_collapsePiOneHom A B)) :
    FundamentalGroup (apm_t97A03_BaseSpace A B)
        (apm_t97A03_baseCircle A B A) ≃*
      FundamentalGroup
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (Fin 2))
        (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin 2) 1) :=
  (MulEquiv.ofBijective (apm_t97A03_collapsePiOneHom A B)
    ⟨hinj, apm_t97A03_collapsePiOneHom_surjective_of_aligned_piOneEquiv
      A B e hfirst hsecond⟩).trans e

/-- The resulting equivalence is genuinely aligned with the two literal arc
loops, rather than with a synthetic moved loop and a constant loop. -/
theorem apm_t97A03_literalPiOneEquiv_literalLoops
    (A B : Circle)
    (e : FundamentalGroup (apm_t97A03_CutCircle A B)
          (apm_t97A03_cutCircleMap A B A) ≃*
        FundamentalGroup
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (Fin 2))
          (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin 2) 1))
    (hfirst : e (apm_t97A03_firstCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hsecond : e (apm_t97A03_secondCutCircleGenerator A B) =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
        1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass)
    (hinj : Function.Injective (apm_t97A03_collapsePiOneHom A B)) :
    let E := apm_t97A03_literalPiOneEquiv_of_collapse_injective
      A B e hfirst hsecond hinj
    E (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (apm_t97A03_firstLiteralLoop A B))) =
        ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
          1 0 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass ∧
      E (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (apm_t97A03_secondLiteralLoop A B))) =
        ConstructionTargets.PolygonSurfaceHomology.finiteWedgeFinLegMap
          1 1 ConstructionTargets.PolygonSurfaceHomology.circlePositiveFundamentalClass := by
  dsimp [apm_t97A03_literalPiOneEquiv_of_collapse_injective]
  constructor
  · rw [apm_t97A03_collapsePiOneHom_firstLiteralLoop, hfirst]
  · rw [apm_t97A03_collapsePiOneHom_secondLiteralLoop, hsecond]

def apm_t97A03_circleOne : Circle := ⟨1, by simp⟩
def apm_t97A03_circleNegOne : Circle := ⟨-1, by
  exact mem_sphere_zero_iff_norm.mpr (by norm_num)⟩
def apm_t97A03_circleI : Circle := ⟨Complex.I, by
  exact mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
def apm_t97A03_circleNegI : Circle := ⟨-Complex.I, by
  exact mem_sphere_zero_iff_norm.mpr (by rw [norm_neg, Complex.norm_I])⟩

abbrev apm_t97A03_TwoSpheres := Fin 2 × apm_t97A03_S2

/-- One lifted circle, cut by four attachment points, threading through the
two sphere sheets. -/
inductive apm_t97A03_OneCircleRel :
    Sum apm_t97A03_TwoSpheres Circle →
      Sum apm_t97A03_TwoSpheres Circle → Prop
  | n0 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleOne) (.inl (0, apm_t97A03_north))
  | s0 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleI) (.inl (0, apm_t97A03_south))
  | n1 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleNegOne) (.inl (1, apm_t97A03_north))
  | s1 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleNegI) (.inl (1, apm_t97A03_south))

def apm_t97A03_OneCircleCover :=
  Quotient (Relation.EqvGen.setoid apm_t97A03_OneCircleRel)

noncomputable instance : TopologicalSpace apm_t97A03_OneCircleCover :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres Circle ↦ Quotient.mk _ x) inferInstance

/-- Two lifted circles joining the two sphere sheets. -/
inductive apm_t97A03_TwoCircleRel :
    Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) →
      Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) → Prop
  | c0n : apm_t97A03_TwoCircleRel
      (.inr (0, apm_t97A03_circleOne)) (.inl (0, apm_t97A03_north))
  | c0s : apm_t97A03_TwoCircleRel
      (.inr (0, apm_t97A03_circleNegOne)) (.inl (1, apm_t97A03_south))
  | c1n : apm_t97A03_TwoCircleRel
      (.inr (1, apm_t97A03_circleOne)) (.inl (1, apm_t97A03_north))
  | c1s : apm_t97A03_TwoCircleRel
      (.inr (1, apm_t97A03_circleNegOne)) (.inl (0, apm_t97A03_south))

def apm_t97A03_TwoCircleCover :=
  Quotient (Relation.EqvGen.setoid apm_t97A03_TwoCircleRel)

noncomputable instance : TopologicalSpace apm_t97A03_TwoCircleCover :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) ↦ Quotient.mk _ x)
    inferInstance

inductive apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfRel :
    Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) →
      Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) → Prop
  | c0n : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfRel
      (.inr (0, apm_t97A03_circleOne)) (.inl (0, apm_t97A03_north))
  | c0s : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfRel
      (.inr (0, apm_t97A03_circleNegOne)) (.inl (1, apm_t97A03_south))
  | c1n : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfRel
      (.inr (1, apm_t97A03_circleOne)) (.inl (1, apm_t97A03_north))
  | c1s : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfRel
      (.inr (1, apm_t97A03_circleNegOne)) (.inl (0, apm_t97A03_north))

abbrev apm_t97A03_Homology (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- The frozen two-sheet fiber count forces the covering map to be onto. -/
lemma apm_t97A03_surjective_of_fiber_card_two
    {A B : Circle} {Y : Type} (p : Y → apm_t97A03_BaseSpace A B)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    Function.Surjective p := by
  intro x
  by_contra hx
  push_neg at hx
  have hempty : p ⁻¹' ({x} : Set _) = ∅ := by
    ext y
    simp [hx y]
  have h := hdegree x
  rw [hempty] at h
  simp at h

/-- The cardinality hypothesis gives each fiber an actual equivalence with a
two-element type, not merely a nonemptiness consequence. -/
lemma apm_t97A03_fiber_equiv_fin_two
    {A B : Circle} {Y : Type} (p : Y → apm_t97A03_BaseSpace A B)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (x : apm_t97A03_BaseSpace A B) :
    Nonempty ((p ⁻¹' ({x} : Set _)) ≃ Fin 2) := by
  have hcard0 : Nat.card (p ⁻¹' ({x} : Set _)) ≠ 0 := by
    rw [hdegree x]
    norm_num
  letI : Finite (p ⁻¹' ({x} : Set _)) := Nat.finite_of_card_ne_zero hcard0
  letI := Fintype.ofFinite (p ⁻¹' ({x} : Set _))
  exact ⟨Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using hdegree x)⟩

def apm_t97A03_OneCircleMonodromy
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p) : Prop :=
  ∃ label : (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) ≃ Fin 2,
    ∃ swapArcs : Bool,
      let first := ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
        (apm_t97A03_firstLiteralTransport p hp)
      let second := ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
        (apm_t97A03_secondLiteralTransport p hp)
      (if swapArcs then (second, first) else (first, second)) =
        (Equiv.swap 0 1, Equiv.refl (Fin 2))

def apm_t97A03_TwoCircleMonodromy
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p) : Prop :=
  ∃ label : (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) ≃ Fin 2,
    ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
        (apm_t97A03_firstLiteralTransport p hp) = Equiv.swap 0 1 ∧
      ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
        (apm_t97A03_secondLiteralTransport p hp) = Equiv.swap 0 1

/-- The common geometric input for the two model comparisons.  The map
`sphere` labels the two sheets above the literal sphere, while `first` and
`second` are the lifts of the two complementary circle arcs starting on the
corresponding north-pole sheet.  Recording the endpoint permutations here
keeps all later quotient gluing arguments independent of choices made by the
covering-lift API. -/
structure apm_t97A03_ClassifySheetData
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) where
  sphere : Fin 2 → apm_t97A03_S2 → Y
  continuous_sphere : Continuous (fun q : Fin 2 × apm_t97A03_S2 ↦ sphere q.1 q.2)
  sphere_lifts : ∀ i z, p (sphere i z) = apm_t97A03_baseSphere A B z
  sphere_unique : ∀ {y z}, p y = apm_t97A03_baseSphere A B z →
    ∃! i : Fin 2, sphere i z = y
  first : Fin 2 → Set.Icc (0 : ℝ) 1 → Y
  second : Fin 2 → Set.Icc (0 : ℝ) 1 → Y
  continuous_first : ∀ i, Continuous (first i)
  continuous_second : ∀ i, Continuous (second i)
  first_lifts : ∀ i t, p (first i t) = apm_t97A03_baseCircleArc A B t
  second_lifts : ∀ i t, p (second i t) = apm_t97A03_baseComplementaryCircleArc A B t
  first_zero : ∀ i, first i 0 = sphere i apm_t97A03_north
  second_zero : ∀ i, second i 0 = sphere i apm_t97A03_north
  firstPerm : Equiv.Perm (Fin 2)
  secondPerm : Equiv.Perm (Fin 2)
  first_one : ∀ i, first i 1 = sphere (firstPerm i) apm_t97A03_south
  second_one : ∀ i, second i 1 = sphere (secondPerm i) apm_t97A03_south

/-- Triviality of a two-sheeted covering over the simply connected literal
two-sphere.  This is the precise sphere-only use of simple connectedness. -/
theorem apm_t97A03_classify_aux_sheetData_aux_sphereTrivialization
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    ∃ sphere : Fin 2 → apm_t97A03_S2 → Y,
      Continuous (fun q : Fin 2 × apm_t97A03_S2 ↦ sphere q.1 q.2) ∧
      (∀ i z, p (sphere i z) = apm_t97A03_baseSphere A B z) ∧
      ∀ {y z}, p y = apm_t97A03_baseSphere A B z →
        ∃! i : Fin 2, sphere i z = y := by
  letI : SimplyConnectedSpace apm_t97A03_S2 :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
      2 (by norm_num)
  letI : LocPathConnectedSpace apm_t97A03_S2 :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) apm_t97A03_S2
  let f : C(apm_t97A03_S2, apm_t97A03_BaseSpace A B) :=
    ⟨apm_t97A03_baseSphere A B, apm_t97A03_continuous_baseSphere A B⟩
  let L := ConstructionTargets.CoveringLiftRestriction.Lifts p f
  let ev (z : apm_t97A03_S2) : L ≃ {y : Y // p y = f z} :=
    ConstructionTargets.CoveringLiftRestriction.evaluationEquiv hp f z
  obtain ⟨label⟩ := apm_t97A03_fiber_equiv_fin_two p hdegree (f apm_t97A03_north)
  let lifts : Fin 2 → L := fun i ↦
    (ev apm_t97A03_north).symm (label.symm i)
  let sphere : Fin 2 → apm_t97A03_S2 → Y := fun i z ↦ (lifts i).1 z
  refine ⟨sphere, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro q
    apply ContinuousAt.congr_of_eventuallyEq
      ((lifts q.1).1.continuous.continuousAt.comp continuousAt_snd)
    filter_upwards [continuousAt_fst.eventually
      ((isOpen_discrete ({q.1} : Set (Fin 2))).mem_nhds (by simp))] with x hx
    change x.1 = q.1 at hx
    simp [sphere, hx]
  · intro i z
    exact congrFun (lifts i).2 z
  · intro y z hy
    let ly : L := (ev z).symm ⟨y, by simpa [f] using hy⟩
    let i : Fin 2 := label ((ev apm_t97A03_north) ly)
    have hli : lifts i = ly := by
      apply (ev apm_t97A03_north).injective
      simp [lifts, i]
    refine ⟨i, ?_, ?_⟩
    · change (lifts i).1 z = y
      rw [hli]
      exact congrArg Subtype.val ((ev z).apply_symm_apply ⟨y, by simpa [f] using hy⟩)
    · intro j hj
      have hlj : lifts j = ly := by
        apply (ev z).injective
        apply Subtype.ext
        change (lifts j).1 z = ly.1 z
        change (lifts j).1 z = y at hj
        rw [hj]
        exact (congrArg Subtype.val
          ((ev z).apply_symm_apply ⟨y, by simpa [f] using hy⟩)).symm
      have h := congrArg (fun l : L ↦ label ((ev apm_t97A03_north) l))
        (hlj.trans hli.symm)
      simpa [lifts] using h

theorem apm_t97A03_classify_aux_sheetData_aux_arcEndpoints_aux_path
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (sphere : Fin 2 → apm_t97A03_S2 → Y)
    (sphere_lifts : ∀ i z, p (sphere i z) = apm_t97A03_baseSphere A B z)
    (sphere_unique : ∀ {y z}, p y = apm_t97A03_baseSphere A B z →
      ∃! i : Fin 2, sphere i z = y)
    (γ : Path (apm_t97A03_baseCircle A B A) (apm_t97A03_baseCircle A B B)) :
    ∃ (lift : Fin 2 → Set.Icc (0 : ℝ) 1 → Y) (perm : Equiv.Perm (Fin 2)),
      (∀ i, Continuous (lift i)) ∧
      (∀ i t, p (lift i t) = γ t) ∧
      (∀ i, lift i 0 = sphere i apm_t97A03_north) ∧
      (∀ i, lift i 1 = sphere (perm i) apm_t97A03_south) := by
  have hzero (i : Fin 2) : γ 0 = p (sphere i apm_t97A03_north) := by
    rw [γ.source, sphere_lifts]
    exact apm_t97A03_baseCircle_A A B
  let lift : Fin 2 → C(Set.Icc (0 : ℝ) 1, Y) := fun i ↦
    hp.liftPath γ (sphere i apm_t97A03_north) (hzero i)
  have hlifts (i : Fin 2) (t : Set.Icc (0 : ℝ) 1) : p (lift i t) = γ t := by
    exact congr_fun (hp.liftPath_lifts γ (sphere i apm_t97A03_north) (hzero i)) t
  have hone (i : Fin 2) :
      p (lift i 1) = apm_t97A03_baseSphere A B apm_t97A03_south := by
    rw [hlifts, γ.target]
    exact apm_t97A03_baseCircle_B A B
  choose endpoint hendpoint _ using fun i ↦ sphere_unique (hone i)
  have endpoint_injective : Function.Injective endpoint := by
    intro i j hij
    have hatone : lift i (1 : Set.Icc (0 : ℝ) 1) = lift j 1 := by
      rw [← hendpoint i, ← hendpoint j, hij]
    have heqfun : (lift i : Set.Icc (0 : ℝ) 1 → Y) = lift j := by
      apply hp.eq_of_comp_eq (lift i).continuous (lift j).continuous
      · funext t
        rw [Function.comp_apply, Function.comp_apply, hlifts, hlifts]
      · exact hatone
    have heq : lift i = lift j := ContinuousMap.coe_injective heqfun
    have hnorth : sphere i apm_t97A03_north = sphere j apm_t97A03_north := by
      rw [← hp.liftPath_zero γ (sphere i apm_t97A03_north) (hzero i),
        ← hp.liftPath_zero γ (sphere j apm_t97A03_north) (hzero j)]
      exact congrFun (congrArg DFunLike.coe heq) 0
    obtain ⟨k, _, hk⟩ := sphere_unique (sphere_lifts i apm_t97A03_north)
    exact (hk i rfl).trans (hk j hnorth.symm).symm
  let perm : Equiv.Perm (Fin 2) :=
    Equiv.ofBijective endpoint (Finite.injective_iff_bijective.mp endpoint_injective)
  refine ⟨fun i ↦ lift i, perm, fun i ↦ (lift i).continuous, hlifts, ?_, ?_⟩
  · intro i
    exact hp.liftPath_zero γ (sphere i apm_t97A03_north) (hzero i)
  · intro i
    exact (hendpoint i).symm

/-- Once the sphere sheets are labelled, path lifting supplies both arc
lifts, and the two-point south fibre turns their endpoints into permutations. -/
theorem apm_t97A03_classify_aux_sheetData_aux_arcEndpoints
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (sphere : Fin 2 → apm_t97A03_S2 → Y)
    (sphere_lifts : ∀ i z, p (sphere i z) = apm_t97A03_baseSphere A B z)
    (sphere_unique : ∀ {y z}, p y = apm_t97A03_baseSphere A B z →
      ∃! i : Fin 2, sphere i z = y) :
    ∃ (first second : Fin 2 → Set.Icc (0 : ℝ) 1 → Y)
        (firstPerm secondPerm : Equiv.Perm (Fin 2)),
      (∀ i, Continuous (first i)) ∧
      (∀ i, Continuous (second i)) ∧
      (∀ i t, p (first i t) = apm_t97A03_baseCircleArc A B t) ∧
      (∀ i t, p (second i t) = apm_t97A03_baseComplementaryCircleArc A B t) ∧
      (∀ i, first i 0 = sphere i apm_t97A03_north) ∧
      (∀ i, second i 0 = sphere i apm_t97A03_north) ∧
      (∀ i, first i 1 = sphere (firstPerm i) apm_t97A03_south) ∧
      (∀ i, second i 1 = sphere (secondPerm i) apm_t97A03_south) := by
  obtain ⟨first, firstPerm, hfirstcont, hfirstlift, hfirstzero, hfirstone⟩ :=
    apm_t97A03_classify_aux_sheetData_aux_arcEndpoints_aux_path
      A B Y p hp sphere sphere_lifts sphere_unique (apm_t97A03_baseCircleArc A B)
  obtain ⟨second, secondPerm, hsecondcont, hsecondlift, hsecondzero, hsecondone⟩ :=
    apm_t97A03_classify_aux_sheetData_aux_arcEndpoints_aux_path
      A B Y p hp sphere sphere_lifts sphere_unique
        (apm_t97A03_baseComplementaryCircleArc A B)
  exact ⟨first, second, firstPerm, secondPerm, hfirstcont, hsecondcont,
    hfirstlift, hsecondlift, hfirstzero, hsecondzero, hfirstone, hsecondone⟩

/-- Sheet data shared by the nontriviality argument and both quotient-model
homeomorphisms. -/
theorem apm_t97A03_classify_aux_sheetData
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    Nonempty (apm_t97A03_ClassifySheetData A B Y p) := by
  obtain ⟨sphere, hscont, hslift, hsunique⟩ :=
    apm_t97A03_classify_aux_sheetData_aux_sphereTrivialization A B Y p hp hdegree
  obtain ⟨first, second, firstPerm, secondPerm, hfcont, hscont', hflift, hsecondlift,
      hfzero, hszero, hfone, hsone⟩ :=
    apm_t97A03_classify_aux_sheetData_aux_arcEndpoints
      A B Y p hp sphere hslift hsunique
  exact ⟨⟨sphere, hscont, hslift, hsunique, first, second, hfcont, hscont', hflift,
    hsecondlift, hfzero, hszero, firstPerm, secondPerm, hfone, hsone⟩⟩

/-- The endpoint permutations of the sheet data are the literal transports:
the first literal loop is the first arc followed by the reversed sphere
return, so from the north point of sheet `i` it ends at the north point of
sheet `firstPerm i`, and likewise for the second. -/
theorem apm_t97A03_classify_aux_sheetData_aux_transport
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p) (i : Fin 2) :
    ((apm_t97A03_firstLiteralTransport p hp
        ⟨d.sphere i apm_t97A03_north, by simp [d.sphere_lifts]⟩ : Y) =
        d.sphere (d.firstPerm i) apm_t97A03_north) ∧
    ((apm_t97A03_secondLiteralTransport p hp
        ⟨d.sphere i apm_t97A03_north, by simp [d.sphere_lifts]⟩ : Y) =
        d.sphere (d.secondPerm i) apm_t97A03_north) := by
  constructor
  · let σ : Path (d.sphere (d.firstPerm i) apm_t97A03_north)
        (d.sphere (d.firstPerm i) apm_t97A03_south) :=
      apm_t97A03_sphereReturn.map
        (d.continuous_sphere.comp (continuous_const.prodMk continuous_id))
    let Γ : Path (d.sphere i apm_t97A03_north)
        (d.sphere (d.firstPerm i) apm_t97A03_north) :=
      ({ toFun := d.first i
         continuous_toFun := d.continuous_first i
         source' := d.first_zero i
         target' := d.first_one i } : Path _ _).trans σ.symm
    have hmap : p ∘ Γ = apm_t97A03_firstLiteralLoop A B := by
      rw [apm_t97A03_firstLiteralLoop]
      funext t
      simp only [Function.comp_apply, Γ, Path.trans_apply]
      split_ifs
      · exact d.first_lifts i _
      · simp [σ, d.sphere_lifts, apm_t97A03_baseSphereReturn]
    have hzero : apm_t97A03_firstLiteralLoop A B 0 =
        p (d.sphere i apm_t97A03_north) :=
      (congrFun hmap 0).symm.trans (congrArg p Γ.source)
    change hp.liftPath (apm_t97A03_firstLiteralLoop A B)
      (d.sphere i apm_t97A03_north) hzero 1 = _
    have hlift : (Γ : unitInterval → Y) = hp.liftPath
        (apm_t97A03_firstLiteralLoop A B) (d.sphere i apm_t97A03_north) hzero :=
      (hp.eq_liftPath_iff hzero).2 ⟨Γ.continuous, hmap, Γ.source⟩
    rw [← hlift]
    exact Γ.target
  · let σ : Path (d.sphere (d.secondPerm i) apm_t97A03_north)
        (d.sphere (d.secondPerm i) apm_t97A03_south) :=
      apm_t97A03_sphereReturn.map
        (d.continuous_sphere.comp (continuous_const.prodMk continuous_id))
    let Γ : Path (d.sphere i apm_t97A03_north)
        (d.sphere (d.secondPerm i) apm_t97A03_north) :=
      ({ toFun := d.second i
         continuous_toFun := d.continuous_second i
         source' := d.second_zero i
         target' := d.second_one i } : Path _ _).trans σ.symm
    have hmap : p ∘ Γ = apm_t97A03_secondLiteralLoop A B := by
      rw [apm_t97A03_secondLiteralLoop]
      funext t
      simp only [Function.comp_apply, Γ, Path.trans_apply]
      split_ifs
      · exact d.second_lifts i _
      · simp [σ, d.sphere_lifts, apm_t97A03_baseSphereReturn]
    have hzero : apm_t97A03_secondLiteralLoop A B 0 =
        p (d.sphere i apm_t97A03_north) :=
      (congrFun hmap 0).symm.trans (congrArg p Γ.source)
    change hp.liftPath (apm_t97A03_secondLiteralLoop A B)
      (d.sphere i apm_t97A03_north) hzero 1 = _
    have hlift : (Γ : unitInterval → Y) = hp.liftPath
        (apm_t97A03_secondLiteralLoop A B) (d.sphere i apm_t97A03_north) hzero :=
      (hp.eq_liftPath_iff hzero).2 ⟨Γ.continuous, hmap, Γ.source⟩
    rw [← hlift]
    exact Γ.target

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_perms
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : apm_t97A03_firstLiteralTransport p hp = Equiv.refl _)
    (hsecond : apm_t97A03_secondLiteralTransport p hp = Equiv.refl _) :
    d.firstPerm = Equiv.refl _ ∧ d.secondPerm = Equiv.refl _ := by
  constructor <;> apply Equiv.ext <;> intro i
  · have ht :=
      (apm_t97A03_classify_aux_sheetData_aux_transport A B Y p hp d i).1
    have hr := congrArg
      (fun e : Equiv.Perm (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) =>
        ((e ⟨d.sphere i apm_t97A03_north, by simp [d.sphere_lifts]⟩ :
          p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) : Y)) hfirst
    have hsphere : d.sphere (d.firstPerm i) apm_t97A03_north =
        d.sphere i apm_t97A03_north := by
      exact ht.symm.trans (by simpa using hr)
    obtain ⟨j, hj, hjunique⟩ := d.sphere_unique
      (d.sphere_lifts (d.firstPerm i) apm_t97A03_north)
    exact (hjunique _ rfl).trans (hjunique _ hsphere.symm).symm
  · have ht :=
      (apm_t97A03_classify_aux_sheetData_aux_transport A B Y p hp d i).2
    have hr := congrArg
      (fun e : Equiv.Perm (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) =>
        ((e ⟨d.sphere i apm_t97A03_north, by simp [d.sphere_lifts]⟩ :
          p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) : Y)) hsecond
    have hsphere : d.sphere (d.secondPerm i) apm_t97A03_north =
        d.sphere i apm_t97A03_north := by
      exact ht.symm.trans (by simpa using hr)
    obtain ⟨j, hj, hjunique⟩ := d.sphere_unique
      (d.sphere_lifts (d.secondPerm i) apm_t97A03_north)
    exact (hjunique _ rfl).trans (hjunique _ hsphere.symm).symm

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_quotient
    {X Z W : Type} [TopologicalSpace X] [TopologicalSpace Z] [TopologicalSpace W]
    (q : X → Z) (g : X → W) (hq : Topology.IsQuotientMap q) (hg : Continuous g)
    (hcompat : ∀ x y, q x = q y → g x = g y) :
    ∃ s : Z → W, Continuous s ∧ ∀ x, s (q x) = g x := by
  let r : Z → X := Function.surjInv hq.surjective
  let s : Z → W := g ∘ r
  have hr : Function.RightInverse r q :=
    Function.rightInverse_surjInv hq.surjective
  have hsq : s ∘ q = g := by
    funext x
    exact hcompat (r (q x)) x (hr (q x))
  refine ⟨s, hq.continuous_iff.mpr ?_, fun x ↦ congrFun hsq x⟩
  simpa [hsq] using hg

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
    (A B : Circle) (hAB : A ≠ B) :
    Function.Surjective (fun x : Sum (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ↦
      match x with
      | .inl t => apm_t97A03_circleArc A B t
      | .inr t => apm_t97A03_complementaryCircleArc A B t) := by
  sorry

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_fibres
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (first second : Set.Icc (0 : ℝ) 1 → Y)
    (hzero : first 0 = second 0) (hone : first 1 = second 1) :
    ∀ x y : Sum (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1),
      (match x with
        | .inl t => apm_t97A03_circleArc A B t
        | .inr t => apm_t97A03_complementaryCircleArc A B t) =
      (match y with
        | .inl t => apm_t97A03_circleArc A B t
        | .inr t => apm_t97A03_complementaryCircleArc A B t) →
      (match x with | .inl t => first t | .inr t => second t) =
      (match y with | .inl t => first t | .inr t => second t) := by
  sorry

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (first second : Set.Icc (0 : ℝ) 1 → Y)
    (hfirst : Continuous first) (hsecond : Continuous second)
    (hzero : first 0 = second 0) (hone : first 1 = second 1) :
    ∃ s : Circle → Y,
      Continuous s ∧
      (∀ t, s (apm_t97A03_circleArc A B t) = first t) ∧
      (∀ t, s (apm_t97A03_complementaryCircleArc A B t) = second t) := by
  let q : Sum (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) → Circle := fun x ↦
    match x with
    | .inl t => apm_t97A03_circleArc A B t
    | .inr t => apm_t97A03_complementaryCircleArc A B t
  let g : Sum (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) → Y := fun x ↦
    match x with | .inl t => first t | .inr t => second t
  have hqcont : Continuous q := by
    apply continuous_sum_dom.mpr
    exact ⟨(apm_t97A03_circleArc A B).continuous,
      (apm_t97A03_complementaryCircleArc A B).continuous⟩
  have hqsurj : Function.Surjective q :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
      A B hAB
  have hq : Topology.IsQuotientMap q :=
    hqcont.isClosedMap.isQuotientMap hqcont hqsurj
  have hg : Continuous g := continuous_sum_dom.mpr ⟨hfirst, hsecond⟩
  have hcompat : ∀ x y, q x = q y → g x = g y :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_fibres
      A B hAB Y first second hzero hone
  obtain ⟨s, hs, hsq⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_quotient
      q g hq hg hcompat
  exact ⟨s, hs, fun t ↦ hsq (.inl t), fun t ↦ hsq (.inr t)⟩

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_endpoints
    (A B : Circle)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hperms : d.firstPerm = Equiv.refl _ ∧ d.secondPerm = Equiv.refl _) :
    d.first 0 0 = d.second 0 0 ∧ d.first 0 1 = d.second 0 1 := by
  constructor
  · rw [d.first_zero, d.second_zero]
  · rw [d.first_one, d.second_one, hperms.1, hperms.2]

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_lifts
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (s : Circle → Y)
    (hsfirst : ∀ t, s (apm_t97A03_circleArc A B t) = d.first 0 t)
    (hssecond : ∀ t,
      s (apm_t97A03_complementaryCircleArc A B t) = d.second 0 t) :
    ∀ z, p (s z) = apm_t97A03_baseCircle A B z := by
  intro z
  obtain ⟨t | t, ht⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
      A B hAB z
  · rw [← ht, hsfirst, d.first_lifts]
    rfl
  · rw [← ht, hssecond, d.second_lifts]
    rfl

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hperms : d.firstPerm = Equiv.refl _ ∧ d.secondPerm = Equiv.refl _) :
    ∃ s : Circle → Y,
      Continuous s ∧
      (∀ z, p (s z) = apm_t97A03_baseCircle A B z) ∧
      s A = d.sphere 0 apm_t97A03_north ∧
      s B = d.sphere 0 apm_t97A03_south := by
  obtain ⟨hzero, hone⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_endpoints
      A B Y p d hperms
  obtain ⟨s, hscont, hsfirst, hssecond⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste
      A B hAB Y (d.first 0) (d.second 0) (d.continuous_first 0)
        (d.continuous_second 0) hzero hone
  refine ⟨s, hscont, ?_, ?_, ?_⟩
  · exact
      apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_lifts
        A B hAB Y p d s hsfirst hssecond
  · simpa [d.first_zero] using hsfirst 0
  · simpa [d.first_one, hperms.1] using hsfirst 1

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hperms : d.firstPerm = Equiv.refl _ ∧ d.secondPerm = Equiv.refl _) :
    ∃ σ : apm_t97A03_BaseSpace A B → Y,
      Continuous σ ∧ Function.RightInverse σ p := by
  obtain ⟨s, hscont, hslift, hsA, hsB⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle
      A B hAB Y p hp d hperms
  let f : Sum Circle apm_t97A03_S2 → Y := fun x ↦
    match x with
    | Sum.inl z => s z
    | Sum.inr z => d.sphere 0 z
  have hfrel : ∀ x y, apm_t97A03_BaseRel A B x y → f x = f y := by
    intro x y hxy
    cases hxy with
    | north => exact hsA
    | south => exact hsB
  have hfeqv : ∀ x y, Relation.EqvGen (apm_t97A03_BaseRel A B) x y →
      f x = f y := by
    intro x y hxy
    exact Relation.EqvGen.rec
      hfrel
      (fun _ => rfl)
      (fun _ _ _ ih => ih.symm)
      (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
      hxy
  let σ : apm_t97A03_BaseSpace A B → Y := Quotient.lift f hfeqv
  refine ⟨σ, ?_, ?_⟩
  · apply continuous_coinduced_dom.mpr
    apply continuous_sum_dom.mpr
    exact ⟨hscont,
      d.continuous_sphere.comp (continuous_const.prodMk continuous_id)⟩
  · intro x
    refine Quotient.inductionOn x ?_
    rintro (z | z)
    · exact hslift z
    · exact d.sphere_lifts 0 z

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_contra
    (A B : Circle) (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (σ : apm_t97A03_BaseSpace A B → Y)
    (hσcont : Continuous σ) (hσ : Function.RightInverse σ p) : False := by
  let U : Set Y := {y | σ (p y) = y}
  have hcomp : p ∘ (σ ∘ p) = p ∘ id := by
    funext y
    exact hσ (p y)
  have hUclosed : IsClosed U := by
    exact hp.isSeparatedMap.isClosed_eqLocus
      (hσcont.comp hp.continuous) continuous_id hcomp
  have hUopen : IsOpen U := by
    exact hp.isLocalHomeomorph.isLocallyInjective.isOpen_eqLocus
      (hσcont.comp hp.continuous) continuous_id hcomp
  let x : apm_t97A03_BaseSpace A B := apm_t97A03_baseCircle A B A
  have hUnonempty : U.Nonempty := by
    refine ⟨σ x, ?_⟩
    change σ (p (σ x)) = σ x
    rw [hσ x]
  have hU : U = Set.univ := IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUnonempty
  have hall (y : Y) : σ (p y) = y := by
    have : y ∈ U := hU.symm ▸ Set.mem_univ y
    exact this
  let F := p ⁻¹' ({x} : Set (apm_t97A03_BaseSpace A B))
  have hFnonempty : Nonempty F := by
    refine ⟨⟨σ x, ?_⟩⟩
    change p (σ x) = x
    exact hσ x
  have hFsubsingleton : Subsingleton F := by
    constructor
    intro a b
    apply Subtype.ext
    have ha : p a = x := by
      simpa only [F, Set.mem_preimage, Set.mem_singleton_iff] using a.property
    have hb : p b = x := by
      simpa only [F, Set.mem_preimage, Set.mem_singleton_iff] using b.property
    calc
      (a : Y) = σ (p a) := (hall a).symm
      _ = σ x := congrArg σ ha
      _ = σ (p b) := (congrArg σ hb).symm
      _ = (b : Y) := hall b
  letI : Nonempty F := hFnonempty
  letI : Subsingleton F := hFsubsingleton
  have hone : Nat.card F = 1 := Nat.card_unique
  have htwo : Nat.card F = 2 := hdegree x
  omega

/-- If both literal transports fix both north sheets, the sheet-zero sphere
lift and its two arc lifts descend to a global section.  Its image is clopen
by covering uniqueness and closedness of the diagonal; connectedness then
contradicts the second point in every fibre. -/
theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : apm_t97A03_firstLiteralTransport p hp = Equiv.refl _)
    (hsecond : apm_t97A03_secondLiteralTransport p hp = Equiv.refl _) : False := by
  have hperms :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_perms
      A B Y p hp d hfirst hsecond
  obtain ⟨σ, hσcont, hσ⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section
      A B hAB Y p hp d hperms
  exact
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_contra
      A B Y p hp hdegree σ hσcont hσ

/-- Use connected-cover monodromy, the proved literal `F₂` generators, and
`apm_t97A03_literal_transport_moved_of_generated` to show that one of the two
fixed complementary-arc transports moves a sheet.  Tools:
`exists_moved_covering_loop_over_connected` and the aligned literal
fundamental-group equivalence already proved above. -/
theorem apm_t97A03_classify_aux_literal_transport_nontrivial
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    apm_t97A03_firstLiteralTransport p hp ≠ Equiv.refl _ ∨
      apm_t97A03_secondLiteralTransport p hp ≠ Equiv.refl _ := by
  obtain ⟨d⟩ := apm_t97A03_classify_aux_sheetData A B hAB Y p hp hdegree
  by_contra h
  push_neg at h
  exact apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection
    A B hAB Y p hp hdegree d h.1 h.2

/-- Convert the finite selector's one-swap case into the exact normalized
one-circle predicate.  This is finite `Fin 2` permutation algebra using
`finTwoPerm_bool_normalForm`; no topology remains. -/
theorem apm_t97A03_classify_aux_oneCircleMonodromy
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (hnontrivial : apm_t97A03_firstLiteralTransport p hp ≠ Equiv.refl _ ∨
      apm_t97A03_secondLiteralTransport p hp ≠ Equiv.refl _)
    (hnotBoth : ¬ apm_t97A03_TwoCircleMonodromy p hp) :
    apm_t97A03_OneCircleMonodromy p hp := by
  obtain ⟨label⟩ := apm_t97A03_fiber_equiv_fin_two p hdegree
    (apm_t97A03_baseCircle A B A)
  let first := ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
    (apm_t97A03_firstLiteralTransport p hp)
  let second := ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
    (apm_t97A03_secondLiteralTransport p hp)
  have hnontrivial' : first ≠ Equiv.refl (Fin 2) ∨
      second ≠ Equiv.refl (Fin 2) := by
    rcases hnontrivial with hfirst | hsecond
    · exact Or.inl
        ((ConstructionTargets.t97A03Closure.labeledFiberMonodromy_ne_refl_iff
          label (apm_t97A03_firstLiteralTransport p hp)).2 hfirst)
    · exact Or.inr
        ((ConstructionTargets.t97A03Closure.labeledFiberMonodromy_ne_refl_iff
          label (apm_t97A03_secondLiteralTransport p hp)).2 hsecond)
  rcases ConstructionTargets.t97A03Closure.finTwoPerm_eq_id_or_swap first with
    hfirst | hfirst <;>
    rcases ConstructionTargets.t97A03Closure.finTwoPerm_eq_id_or_swap second with
      hsecond | hsecond
  · exact False.elim (hnontrivial'.elim (fun h ↦ h hfirst) (fun h ↦ h hsecond))
  · refine ⟨label, true, ?_⟩
    simp only [if_pos]
    exact Prod.ext hsecond hfirst
  · refine ⟨label, false, ?_⟩
    exact Prod.ext hfirst hsecond
  · exfalso
    apply hnotBoth
    exact ⟨label, hfirst, hsecond⟩

/-- In the both-swap case, trivialize the sphere restriction into its two
sheets, lift the two fixed arcs, and descend the sheetwise maps through the
two `EqvGen` quotients.  The inverse is obtained by the same lifted pieces;
use `Continuous.quotient_lift`, covering uniqueness, and
`Homeomorph.homeomorphOfContinuousOpen`. -/
theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_perms
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hmono : apm_t97A03_TwoCircleMonodromy p hp) :
    d.firstPerm = Equiv.swap 0 1 ∧ d.secondPerm = Equiv.swap 0 1 := by
  obtain ⟨label, hfirst, hsecond⟩ := hmono
  have transport_ne_refl
      (transport : Equiv.Perm
        (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)))
      (htransport :
        ConstructionTargets.t97A03Closure.labeledFiberMonodromy label transport =
          Equiv.swap 0 1) : transport ≠ Equiv.refl _ := by
    rw [← ConstructionTargets.t97A03Closure.labeledFiberMonodromy_ne_refl_iff]
    rw [htransport]
    intro h
    have := Equiv.congr_fun h (0 : Fin 2)
    simpa using this
  have perm_ne_refl
      (transport : Equiv.Perm
        (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)))
      (perm : Equiv.Perm (Fin 2))
      (hendpoint : ∀ i,
        ((transport
          ⟨d.sphere i apm_t97A03_north, by simp [d.sphere_lifts]⟩ : Y) =
          d.sphere (perm i) apm_t97A03_north))
      (hne : transport ≠ Equiv.refl _) : perm ≠ Equiv.refl _ := by
    intro hperm
    apply hne
    apply Equiv.ext
    intro x
    obtain ⟨i, hi, hi_unique⟩ := d.sphere_unique (by simpa using x.property)
    have hx : x =
        ⟨d.sphere i apm_t97A03_north, by simp [d.sphere_lifts]⟩ := by
      apply Subtype.ext
      exact hi.symm
    subst x
    apply Subtype.ext
    rw [hendpoint, hperm]
    simp
  constructor
  · rcases ConstructionTargets.t97A03Closure.finTwoPerm_eq_id_or_swap d.firstPerm with
      h | h
    · exact False.elim ((perm_ne_refl _ _
        (fun i ↦
          (apm_t97A03_classify_aux_sheetData_aux_transport A B Y p hp d i).1)
        (transport_ne_refl _ hfirst)) h)
    · exact h
  · rcases ConstructionTargets.t97A03Closure.finTwoPerm_eq_id_or_swap d.secondPerm with
      h | h
    · exact False.elim ((perm_ne_refl _ _
        (fun i ↦
          (apm_t97A03_classify_aux_sheetData_aux_transport A B Y p hp d i).2)
        (transport_ne_refl _ hsecond)) h)
    · exact h

/-- The two lifted closed arcs, pasted at their endpoints, give the two
literal circle sheets.  The parametrisation `q` records the corresponding
homeomorphism from the standard circle (with marked points `1,-1`) to the
base circle (with marked points `A,B`). -/
theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle
    (A B : Circle) (hAB : A ≠ B) :
    ∃ q : Circle ≃ₜ Circle,
      q 1 = A ∧ q apm_t97A03_circleNegOne = B := by
  sorry

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.swap 0 1)
    (hsecond : d.secondPerm = Equiv.swap 0 1)
    (q : Circle ≃ₜ Circle) (hq1 : q 1 = A)
    (hqn : q apm_t97A03_circleNegOne = B) :
    ∃ c : Fin 2 → Circle → Y,
      Continuous (fun w : Fin 2 × Circle ↦ c w.1 w.2) ∧
      (∀ i w, p (c i w) = apm_t97A03_baseCircle A B (q w)) ∧
      (∀ i, c i 1 = d.sphere i apm_t97A03_north) ∧
      (∀ i, c i apm_t97A03_circleNegOne =
        d.sphere (Equiv.swap 0 1 i) apm_t97A03_south) := by
  sorry

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.swap 0 1)
    (hsecond : d.secondPerm = Equiv.swap 0 1) :
    ∃ (q : Circle ≃ₜ Circle) (c : Fin 2 → Circle → Y),
      q 1 = A ∧ q apm_t97A03_circleNegOne = B ∧
      Continuous (fun w : Fin 2 × Circle ↦ c w.1 w.2) ∧
      (∀ i w, p (c i w) = apm_t97A03_baseCircle A B (q w)) ∧
      (∀ i, c i 1 = d.sphere i apm_t97A03_north) ∧
      (∀ i, c i apm_t97A03_circleNegOne =
        d.sphere (Equiv.swap 0 1 i) apm_t97A03_south) := by
  obtain ⟨q, hq1, hqn⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle
      A B hAB
  obtain ⟨c, hc, hlift, hn, hs⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts
      A B Y p d hfirst hsecond q hq1 hqn
  exact ⟨q, c, hq1, hqn, hc, hlift, hn, hs⟩

/-- A pair of continuous lifts of a circle parametrisation which starts at
the two different north-pole sheets exhausts every fibre.  This is covering
path lifting uniqueness, applied along a path from `1` to the requested
circle point; the two possible initial points are supplied by
`sphere_unique`. -/
theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_fiberUnique
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (q : Circle ≃ₜ Circle) (c : Fin 2 → Circle → Y)
    (hq1 : q 1 = A)
    (hc : Continuous (fun w : Fin 2 × Circle ↦ c w.1 w.2))
    (hlift : ∀ i w, p (c i w) = apm_t97A03_baseCircle A B (q w))
    (hn : ∀ i, c i 1 = d.sphere i apm_t97A03_north) :
    ∀ {y w}, p y = apm_t97A03_baseCircle A B (q w) →
      ∃! i : Fin 2, c i w = y := by
  have hc_i (i : Fin 2) : Continuous (c i) := by
    have hpair : Continuous (fun w : Circle ↦ ((i, w) : Fin 2 × Circle)) :=
      Continuous.prodMk continuous_const continuous_id
    exact hc.comp hpair
  intro y w hy
  let γ : Path w 1 := PathConnectedSpace.somePath w 1
  let β : Path (apm_t97A03_baseCircle A B (q w))
      (apm_t97A03_baseCircle A B (q 1)) :=
    (γ.map q.continuous).map (apm_t97A03_continuous_baseCircle A B)
  have hzero : β 0 = p y := by
    change apm_t97A03_baseCircle A B (q (γ 0)) = p y
    rw [γ.source]
    exact hy.symm
  let l : C(Set.Icc (0 : ℝ) 1, Y) := hp.liftPath β y hzero
  have hl (t : Set.Icc (0 : ℝ) 1) : p (l t) = β t := by
    exact congr_fun (hp.liftPath_lifts β y hzero) t
  have hlone : p (l 1) = apm_t97A03_baseSphere A B apm_t97A03_north := by
    rw [hl]
    change apm_t97A03_baseCircle A B (q (γ 1)) = _
    rw [γ.target, hq1]
    exact apm_t97A03_baseCircle_A A B
  obtain ⟨i, hi, hi_unique⟩ := d.sphere_unique hlone
  have hpath : (l : Set.Icc (0 : ℝ) 1 → Y) = fun t ↦ c i (γ t) := by
    apply hp.eq_of_comp_eq l.continuous ((hc_i i).comp γ.continuous)
    · funext t
      simp only [Function.comp_apply]
      rw [hl, hlift]
      rfl
    · change l (1 : Set.Icc (0 : ℝ) 1) = c i (γ 1)
      rw [← hi, γ.target, hn]
  refine ⟨i, ?_, ?_⟩
  · have hz := congrFun hpath 0
    rw [hp.liftPath_zero β y hzero, γ.source] at hz
    exact hz.symm
  · intro j hj
    have hciw : c i w = y := by
      have hz := congrFun hpath 0
      rw [hp.liftPath_zero β y hzero, γ.source] at hz
      exact hz.symm
    have heq : c j = c i := by
      apply hp.eq_of_comp_eq (hc_i j) (hc_i i)
      · funext z
        simp only [Function.comp_apply]
        rw [hlift, hlift]
      · exact hj.trans hciw.symm
    obtain ⟨k, _, hk⟩ := d.sphere_unique (d.sphere_lifts i apm_t97A03_north)
    apply (hk j ?_).trans (hk i rfl).symm
    rw [← hn j, ← hn i, heq]

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.swap 0 1)
    (hsecond : d.secondPerm = Equiv.swap 0 1) :
    ∃ (q : Circle ≃ₜ Circle) (c : Fin 2 → Circle → Y),
      q 1 = A ∧ q apm_t97A03_circleNegOne = B ∧
      Continuous (fun w : Fin 2 × Circle ↦ c w.1 w.2) ∧
      (∀ i w, p (c i w) = apm_t97A03_baseCircle A B (q w)) ∧
      (∀ i, c i 1 = d.sphere i apm_t97A03_north) ∧
      (∀ i, c i apm_t97A03_circleNegOne =
        d.sphere (Equiv.swap 0 1 i) apm_t97A03_south) ∧
      ∀ {y w}, p y = apm_t97A03_baseCircle A B (q w) →
        ∃! i : Fin 2, c i w = y := by
  obtain ⟨q, c, hq1, hqn, hc, hlift, hn, hs⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste
      A B hAB Y p hp d hfirst hsecond
  refine ⟨q, c, hq1, hqn, hc, hlift, hn, hs, ?_⟩
  exact
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_fiberUnique
      A B Y p hp d q c hq1 hc hlift hn

/-- The concrete map on representatives used by the two-circle decoder. -/
noncomputable def apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    {p : Y → apm_t97A03_BaseSpace A B}
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Fin 2 → Circle → Y) :
    Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) → Y
  | .inl iz => d.sphere iz.1 iz.2
  | .inr iw => c iw.1 iw.2

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw_sound
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    {p : Y → apm_t97A03_BaseSpace A B}
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Fin 2 → Circle → Y)
    (hn : ∀ i, c i 1 = d.sphere i apm_t97A03_north)
    (hs : ∀ i, c i apm_t97A03_circleNegOne =
      d.sphere (Equiv.swap 0 1 i) apm_t97A03_south) :
    ∀ x y, apm_t97A03_TwoCircleRel x y →
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw d c x =
        apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw d c y := by
  intro x y h
  cases h with
  | c0n => exact hn 0
  | c0s => simpa using hs 0
  | c1n => exact hn 1
  | c1s => simpa using hs 1

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw_continuous
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    {p : Y → apm_t97A03_BaseSpace A B}
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Fin 2 → Circle → Y)
    (hc : Continuous (fun w : Fin 2 × Circle ↦ c w.1 w.2)) :
    Continuous
      (apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw d c) := by
  apply continuous_sum_dom.mpr
  exact ⟨d.continuous_sphere, hc⟩

noncomputable def apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_map
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    {p : Y → apm_t97A03_BaseSpace A B}
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Fin 2 → Circle → Y)
    (hn : ∀ i, c i 1 = d.sphere i apm_t97A03_north)
    (hs : ∀ i, c i apm_t97A03_circleNegOne =
      d.sphere (Equiv.swap 0 1 i) apm_t97A03_south) :
    apm_t97A03_TwoCircleCover → Y := by
  refine Quotient.lift
    (apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw d c) ?_
  intro x y hxy
  exact Relation.EqvGen.rec
    (fun x y h =>
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw_sound
        d c hn hs x y h)
    (fun _ => rfl)
    (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
    hxy

/-- Exactness of the concrete representative decoder.  Equality over the
sphere is decided by `sphere_unique`; equality over a circle point is decided
by the pasted-circle uniqueness, while the two attachment fibres are exactly
the four generators of `TwoCircleRel`. -/
noncomputable def
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize
    (A B : Circle) : Sum Circle apm_t97A03_S2 → Sum Circle apm_t97A03_S2 := by
  classical
  exact fun x => match x with
    | .inl z => if z = A then .inr apm_t97A03_north
        else if z = B then .inr apm_t97A03_south else .inl z
    | .inr z => .inr z

theorem
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize_eq
    (A B : Circle) (hAB : A ≠ B) {x y : Sum Circle apm_t97A03_S2}
    (h : (Quotient.mk _ x : apm_t97A03_BaseSpace A B) = Quotient.mk _ y) :
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize
        A B x =
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize
        A B y := by
  exact Relation.EqvGen.rec
    (fun _ _ hrel => by
      cases hrel with
      | north => simp [apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
      | south => simp [apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize,
          hAB, hAB.symm])
    (fun _ => rfl)
    (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂)
    (Quotient.exact h)


theorem
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_injective
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (q : Circle ≃ₜ Circle) (c : Fin 2 → Circle → Y)
    (hq1 : q 1 = A) (hqn : q apm_t97A03_circleNegOne = B)
    (hlift : ∀ i w, p (c i w) = apm_t97A03_baseCircle A B (q w))
    (hn : ∀ i, c i 1 = d.sphere i apm_t97A03_north)
    (hs : ∀ i, c i apm_t97A03_circleNegOne =
      d.sphere (Equiv.swap 0 1 i) apm_t97A03_south)
    (hunique : ∀ {y w}, p y = apm_t97A03_baseCircle A B (q w) →
      ∃! i : Fin 2, c i w = y) :
    Function.Injective
      (apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_map
        d c hn hs) := by
  sorry

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (q : Circle ≃ₜ Circle) (c : Fin 2 → Circle → Y)
    (hq1 : q 1 = A) (hqn : q apm_t97A03_circleNegOne = B)
    (hlift : ∀ i w, p (c i w) = apm_t97A03_baseCircle A B (q w))
    (hn : ∀ i, c i 1 = d.sphere i apm_t97A03_north)
    (hs : ∀ i, c i apm_t97A03_circleNegOne =
      d.sphere (Equiv.swap 0 1 i) apm_t97A03_south)
    (hunique : ∀ {y w}, p y = apm_t97A03_baseCircle A B (q w) →
      ∃! i : Fin 2, c i w = y) :
    Function.Bijective
      (apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_map
        d c hn hs) := by
  constructor
  · exact
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_injective
        A B Y p d q c hq1 hqn hlift hn hs hunique
  · intro y
    rcases apm_t97A03_baseCircle_or_baseSphere A B (p y) with ⟨z, hz⟩ | ⟨z, hz⟩
    · obtain ⟨w, rfl⟩ := q.surjective z
      obtain ⟨i, hi, -⟩ := hunique hz
      exact ⟨Quotient.mk _ (.inr (i, w)), hi⟩
    · obtain ⟨i, hi, -⟩ := d.sphere_unique hz
      exact ⟨Quotient.mk _ (.inl (i, z)), hi⟩

/-- With both endpoint permutations normalized to the transposition, the
sphere trivialization and the two pairs of arc lifts glue to a continuous
bijective decoder from the literal two-circle quotient. -/
theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.swap 0 1)
    (hsecond : d.secondPerm = Equiv.swap 0 1) :
    ∃ f : apm_t97A03_TwoCircleCover → Y,
      Continuous f ∧ Function.Bijective f := by
  obtain ⟨q, c, hq1, hqn, hc, hlift, hn, hs, hu⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste
      A B hAB Y p hp d hfirst hsecond
  let f :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_map
      d c hn hs
  refine ⟨f, ?_, ?_⟩
  · apply continuous_coinduced_dom.mpr
    simpa [f,
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_map]
      using
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw_continuous
        d c hc
  · exact
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact
        A B Y p d q c hq1 hqn hlift hn hs hu

/-- The total space of this covering is Hausdorff: the literal base quotient
is Hausdorff, and distinct points in one fibre are separated in an evenly
covered neighbourhood. -/
def apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel
    (A B : Circle) (x y : Sum Circle apm_t97A03_S2) : Prop :=
  x = y ∨
  (x = .inl A ∧ y = .inr apm_t97A03_north) ∨
  (x = .inr apm_t97A03_north ∧ y = .inl A) ∨
  (x = .inl B ∧ y = .inr apm_t97A03_south) ∨
  (x = .inr apm_t97A03_south ∧ y = .inl B)

lemma apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_poles_ne :
    apm_t97A03_north ≠ apm_t97A03_south := by
  intro h
  have h' := congrArg (fun z : apm_t97A03_S2 => (z : apm_t97A03_R3) 2) h
  norm_num [apm_t97A03_north, apm_t97A03_south,
    EuclideanSpace.single_apply] at h'

lemma apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_trans
    (A B : Circle) (hAB : A ≠ B) {x y z : Sum Circle apm_t97A03_S2}
    (hxy : apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel A B x y)
    (hyz : apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel A B y z) :
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel A B x z := by
  rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hyz with h | h | h | h | h <;>
    simp_all [apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel,
      hAB,
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_poles_ne,
      Ne.symm apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_poles_ne]

lemma apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_eqv
    (A B : Circle) (hAB : A ≠ B) (x y : Sum Circle apm_t97A03_S2) :
    Relation.EqvGen (apm_t97A03_BaseRel A B) x y ↔
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel A B x y := by
  constructor
  · intro h
    exact Relation.EqvGen.rec
      (fun _ _ h => by cases h <;> simp [apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel])
      (fun _ => Or.inl rfl)
      (fun _ _ _ ih => by
        rcases ih with h | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
        · exact Or.inr (Or.inl ⟨hy, hx⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hy, hx⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))))
      (fun _ _ _ _ _ ih₁ ih₂ =>
        apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_trans
          A B hAB ih₁ ih₂) h
  · intro h
    rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .refl _
    · exact .rel _ _ (.north)
    · exact .symm _ _ (.rel _ _ (.north))
    · exact .rel _ _ (.south)
    · exact .symm _ _ (.rel _ _ (.south))

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p) :
    T2Space Y := by
  letI : T2Space (apm_t97A03_BaseSpace A B) :=
    ConstructionTargets.compact_closed_equivalence_quotient_t2
      (Relation.EqvGen.setoid (apm_t97A03_BaseRel A B)) (by
        have hdiag : IsClosed {q : (Sum Circle apm_t97A03_S2) ×
            (Sum Circle apm_t97A03_S2) | q.1 = q.2} :=
          isClosed_eq continuous_fst continuous_snd
        have hsingle (x y : Sum Circle apm_t97A03_S2) :
            IsClosed ({(x, y)} : Set ((Sum Circle apm_t97A03_S2) ×
              (Sum Circle apm_t97A03_S2))) := isClosed_singleton
        rw [show {q | (Relation.EqvGen.setoid (apm_t97A03_BaseRel A B)).r q.1 q.2} =
            {q | q.1 = q.2} ∪ {(.inl A, .inr apm_t97A03_north)} ∪
              {(.inr apm_t97A03_north, .inl A)} ∪
              {(.inl B, .inr apm_t97A03_south)} ∪
              {(.inr apm_t97A03_south, .inl B)} by
          ext q
          change Relation.EqvGen (apm_t97A03_BaseRel A B) q.1 q.2 ↔ _
          rw [apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_eqv A B hAB]
          simp only [apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2_aux_rel,
            Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
          aesop]
        exact ((((hdiag.union (hsingle _ _)).union (hsingle _ _)).union
          (hsingle _ _)).union (hsingle _ _)))
  refine ⟨fun x y hxy ↦ ?_⟩
  by_cases h : p x = p y
  · exact hp.isSeparatedMap x y h hxy
  · obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation h
    exact ⟨p ⁻¹' u, p ⁻¹' v, hu.preimage hp.continuous,
      hv.preimage hp.continuous, hxu, hyv, huv.preimage _⟩

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hmono : apm_t97A03_TwoCircleMonodromy p hp) :
    Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover) := by
  obtain ⟨hfirst, hsecond⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_perms
      A B Y p hp d hmono
  obtain ⟨f, hf, hfb⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder
      A B hAB Y p hp hdegree d hfirst hsecond
  letI : CompactSpace apm_t97A03_TwoCircleCover := Quotient.compactSpace
  letI : T2Space Y :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2
      A B hAB Y p hp
  exact ⟨(Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f hfb) hf).symm⟩

theorem apm_t97A03_classify_aux_twoCircle_homeomorph
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (hmono : apm_t97A03_TwoCircleMonodromy p hp) :
    Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover) := by
  obtain ⟨d⟩ := apm_t97A03_classify_aux_sheetData A B hAB Y p hp hdegree
  exact apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend
    A B hAB Y p hp hdegree d hmono

/-- In the exactly-one-swap case, trivialize the sphere restriction, lift the
two complementary arcs with the normalized endpoint labels, and descend the
piecewise inverse maps through `apm_t97A03_OneCircleRel`.  Use covering lift
uniqueness and the quotient universal property to prove the inverse laws. -/
theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_normalize_aux_conj
    (e q r : Equiv.Perm (Fin 2))
    (h : ∀ i, q (e i) = e (r i)) : q = r := by
  rcases ConstructionTargets.t97A03Closure.finTwoPerm_eq_id_or_swap e with
    rfl | rfl
  · apply Equiv.ext
    exact h
  · rcases ConstructionTargets.t97A03Closure.finTwoPerm_eq_id_or_swap q with
      rfl | rfl <;>
      rcases ConstructionTargets.t97A03Closure.finTwoPerm_eq_id_or_swap r with
        rfl | rfl
    · rfl
    · have := h 0
      norm_num at this
    · have := h 0
      norm_num at this
    · rfl

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_normalize
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hmono : apm_t97A03_OneCircleMonodromy p hp) :
    (d.firstPerm = Equiv.swap 0 1 ∧ d.secondPerm = Equiv.refl _) ∨
      (d.firstPerm = Equiv.refl _ ∧ d.secondPerm = Equiv.swap 0 1) := by
  rcases hmono with ⟨label, swapArcs, hmono⟩
  let sheetToFiber : Fin 2 →
      (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) := fun i ↦
    ⟨d.sphere i apm_t97A03_north, by simp [d.sphere_lifts]⟩
  have hinj : Function.Injective sheetToFiber := by
    intro i j hij
    obtain ⟨k, hk, hkunique⟩ := d.sphere_unique
      (d.sphere_lifts i apm_t97A03_north)
    exact (hkunique i rfl).trans
      (hkunique j (congrArg Subtype.val hij).symm).symm
  have hsurj : Function.Surjective sheetToFiber := by
    intro y
    have hy : p y = apm_t97A03_baseSphere A B apm_t97A03_north := by
      rw [← apm_t97A03_baseCircle_A A B]
      simpa using y.property
    obtain ⟨i, hi, -⟩ := d.sphere_unique hy
    exact ⟨i, Subtype.ext hi⟩
  have hbij : Function.Bijective sheetToFiber := ⟨hinj, hsurj⟩
  let sheetEquiv : Fin 2 ≃
      (p ⁻¹' ({apm_t97A03_baseCircle A B A} : Set _)) :=
    Equiv.ofBijective sheetToFiber hbij
  let e : Equiv.Perm (Fin 2) := sheetEquiv.trans label
  let first := ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
    (apm_t97A03_firstLiteralTransport p hp)
  let second := ConstructionTargets.t97A03Closure.labeledFiberMonodromy label
    (apm_t97A03_secondLiteralTransport p hp)
  have hfirst_conj : ∀ i, first (e i) = e (d.firstPerm i) := by
    intro i
    simp only [first, e,
      ConstructionTargets.t97A03Closure.labeledFiberMonodromy,
      Equiv.trans_apply, Equiv.symm_apply_apply]
    apply congrArg label
    apply Subtype.ext
    change ((apm_t97A03_firstLiteralTransport p hp
      ⟨d.sphere i apm_t97A03_north, _⟩ : _) : Y) =
        d.sphere (d.firstPerm i) apm_t97A03_north
    exact (apm_t97A03_classify_aux_sheetData_aux_transport A B Y p hp d i).1
  have hsecond_conj : ∀ i, second (e i) = e (d.secondPerm i) := by
    intro i
    simp only [second, e,
      ConstructionTargets.t97A03Closure.labeledFiberMonodromy,
      Equiv.trans_apply, Equiv.symm_apply_apply]
    apply congrArg label
    apply Subtype.ext
    change ((apm_t97A03_secondLiteralTransport p hp
      ⟨d.sphere i apm_t97A03_north, _⟩ : _) : Y) =
        d.sphere (d.secondPerm i) apm_t97A03_north
    exact (apm_t97A03_classify_aux_sheetData_aux_transport A B Y p hp d i).2
  have hfirst : first = d.firstPerm :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_normalize_aux_conj
      e first d.firstPerm hfirst_conj
  have hsecond : second = d.secondPerm :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_normalize_aux_conj
      e second d.secondPerm hsecond_conj
  change (if swapArcs then (second, first) else (first, second)) =
    (Equiv.swap 0 1, Equiv.refl (Fin 2)) at hmono
  cases swapArcs <;> simp only [Bool.false_eq_true, if_false, if_true] at hmono
  · left
    exact ⟨hfirst.symm.trans (by simpa using congrArg Prod.fst hmono),
      hsecond.symm.trans (by simpa using congrArg Prod.snd hmono)⟩
  · right
    exact ⟨hfirst.symm.trans (by simpa using congrArg Prod.snd hmono),
      hsecond.symm.trans (by simpa using congrArg Prod.fst hmono)⟩

/-- The fixed geometric descent when the first complementary arc changes
sheets and the second one preserves them.  There is no finite permutation
algebra left in this statement: the four endpoint equalities are exactly the
four generators of `apm_t97A03_OneCircleRel`, in cyclic order. -/
theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_endpoints
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.swap 0 1)
    (hsecond : d.secondPerm = Equiv.refl _) :
    d.first 0 0 = d.sphere 0 apm_t97A03_north ∧
    d.first 0 1 = d.sphere 1 apm_t97A03_south ∧
    d.first 1 0 = d.sphere 1 apm_t97A03_north ∧
    d.first 1 1 = d.sphere 0 apm_t97A03_south ∧
    d.second 0 0 = d.sphere 0 apm_t97A03_north ∧
    d.second 0 1 = d.sphere 0 apm_t97A03_south ∧
    d.second 1 0 = d.sphere 1 apm_t97A03_north ∧
    d.second 1 1 = d.sphere 1 apm_t97A03_south := by
  constructor
  · exact d.first_zero 0
  constructor
  · rw [d.first_one, hfirst]
    rfl
  constructor
  · exact d.first_zero 1
  constructor
  · rw [d.first_one, hfirst]
    rfl
  constructor
  · exact d.second_zero 0
  constructor
  · rw [d.second_one, hsecond]
    rfl
  constructor
  · exact d.second_zero 1
  · rw [d.second_one, hsecond]
    rfl

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hendpoints :
      d.first 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.first 0 1 = d.sphere 1 apm_t97A03_south ∧
      d.first 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.first 1 1 = d.sphere 0 apm_t97A03_south ∧
      d.second 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.second 0 1 = d.sphere 0 apm_t97A03_south ∧
      d.second 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.second 1 1 = d.sphere 1 apm_t97A03_south) :
    ∃ c : Circle → Y, Continuous c ∧ Function.Injective c ∧
      c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north ∧
      c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south ∧
      c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north ∧
      c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south ∧
      (∀ w, ∃ z, p (c w) = apm_t97A03_baseCircle A B z) ∧
      (∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y) := by
  sorry

noncomputable def apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    {p : Y → apm_t97A03_BaseSpace A B}
    (d : apm_t97A03_ClassifySheetData A B Y p) (c : Circle → Y) :
    Sum apm_t97A03_TwoSpheres Circle → Y
  | .inl iz => d.sphere iz.1 iz.2
  | .inr w => c w

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw_sound
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    {p : Y → apm_t97A03_BaseSpace A B}
    (d : apm_t97A03_ClassifySheetData A B Y p) (c : Circle → Y)
    (hn0 : c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north)
    (hs0 : c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south)
    (hn1 : c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north)
    (hs1 : c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south) :
    ∀ x y, apm_t97A03_OneCircleRel x y →
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw d c x =
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw d c y := by
  intro x y h
  cases h with
  | n0 => exact hn0
  | s0 => exact hs0
  | n1 => exact hn1
  | s1 => exact hs1

noncomputable def apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_map
    {A B : Circle} {Y : Type} [TopologicalSpace Y]
    {p : Y → apm_t97A03_BaseSpace A B}
    (d : apm_t97A03_ClassifySheetData A B Y p) (c : Circle → Y)
    (hn0 : c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north)
    (hs0 : c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south)
    (hn1 : c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north)
    (hs1 : c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south) :
    apm_t97A03_OneCircleCover → Y := by
  refine Quotient.lift
    (apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw d c) ?_
  intro x y hxy
  exact Relation.EqvGen.rec
    (fun x y h =>
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw_sound
        d c hn0 hs0 hn1 hs1 x y h)
    (fun _ => rfl) (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂) hxy

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_exact
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p) (c : Circle → Y)
    (hn0 : c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north)
    (hs0 : c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south)
    (hn1 : c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north)
    (hs1 : c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south)
    (hcinj : Function.Injective c)
    (hcrange : ∀ w, ∃ z, p (c w) = apm_t97A03_baseCircle A B z)
    (hcover : ∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y) :
    Function.Bijective
      (apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_map
        d c hn0 hs0 hn1 hs1) := by
  sorry

/-- The concrete geometric content of the first-swap case.  The decoder uses
`d.sphere` on the two sphere summands.  On the four successive closed quarter
arcs `1→i`, `i→-1`, `-1→-i`, and `-i→1`, it uses respectively
`d.second 0`, the reverse of `d.first 1`, `d.second 1`, and the reverse of
`d.first 0`.  The endpoint hypotheses are precisely what makes these pieces
descend through `apm_t97A03_OneCircleRel`.

This statement deliberately fixes the decoder by its construction data rather
than quantifying over an arbitrary map: its proof is the remaining pasting and
covering-lift uniqueness argument. -/
theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hendpoints :
      d.first 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.first 0 1 = d.sphere 1 apm_t97A03_south ∧
      d.first 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.first 1 1 = d.sphere 0 apm_t97A03_south ∧
      d.second 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.second 0 1 = d.sphere 0 apm_t97A03_south ∧
      d.second 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.second 1 1 = d.sphere 1 apm_t97A03_south) :
    ∃ f : apm_t97A03_OneCircleCover → Y,
      Continuous f ∧ Function.Bijective f := by
  obtain ⟨c, hc, hcinj, hn0, hs0, hn1, hs1, hcrange, hcover⟩ :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste
      A B hAB Y p hp hdegree d hendpoints
  let f :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_map
      d c hn0 hs0 hn1 hs1
  refine ⟨f, ?_, ?_⟩
  · apply continuous_coinduced_dom.mpr
    apply continuous_sum_dom.mpr
    exact ⟨d.continuous_sphere, hc⟩
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_exact
        A B Y p d c hn0 hs0 hn1 hs1 hcinj hcrange hcover

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hendpoints :
      d.first 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.first 0 1 = d.sphere 1 apm_t97A03_south ∧
      d.first 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.first 1 1 = d.sphere 0 apm_t97A03_south ∧
      d.second 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.second 0 1 = d.sphere 0 apm_t97A03_south ∧
      d.second 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.second 1 1 = d.sphere 1 apm_t97A03_south) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) := by
  obtain ⟨f, hf, hfb⟩ :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder
      A B hAB Y p hp hdegree d hendpoints
  letI : CompactSpace apm_t97A03_OneCircleCover := Quotient.compactSpace
  letI : T2Space Y :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2
      A B hAB Y p hp
  exact ⟨(Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f hfb) hf).symm⟩

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.swap 0 1)
    (hsecond : d.secondPerm = Equiv.refl _) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) := by
  apply apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric
    A B hAB Y p hp hdegree d
  exact
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_endpoints
      A B Y p d hfirst hsecond

/-- The fixed geometric descent when the second complementary arc changes
sheets and the first one preserves them.  This is the preceding construction
with the two circle arcs interchanged (and hence the circle parametrisation
reversed/rotated to retain the four marked model points). -/
theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_endpoints
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.refl _)
    (hsecond : d.secondPerm = Equiv.swap 0 1) :
    d.second 0 0 = d.sphere 0 apm_t97A03_north ∧
    d.second 0 1 = d.sphere 1 apm_t97A03_south ∧
    d.second 1 0 = d.sphere 1 apm_t97A03_north ∧
    d.second 1 1 = d.sphere 0 apm_t97A03_south ∧
    d.first 0 0 = d.sphere 0 apm_t97A03_north ∧
    d.first 0 1 = d.sphere 0 apm_t97A03_south ∧
    d.first 1 0 = d.sphere 1 apm_t97A03_north ∧
    d.first 1 1 = d.sphere 1 apm_t97A03_south := by
  constructor
  · exact d.second_zero 0
  constructor
  · rw [d.second_one, hsecond]
    rfl
  constructor
  · exact d.second_zero 1
  constructor
  · rw [d.second_one, hsecond]
    rfl
  constructor
  · exact d.first_zero 0
  constructor
  · rw [d.first_one, hfirst]
    rfl
  constructor
  · exact d.first_zero 1
  · rw [d.first_one, hfirst]
    rfl

/-- The concrete decoder for the second-swap case.  This is the first-swap
decoder with `d.first` and `d.second` exchanged: the four closed quarter arcs
of the model circle are pasted from the two lifts in the opposite order.  The
listed endpoint equalities are exactly the generators needed for descent
through `apm_t97A03_OneCircleRel`. -/
theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hendpoints :
      d.second 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.second 0 1 = d.sphere 1 apm_t97A03_south ∧
      d.second 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.second 1 1 = d.sphere 0 apm_t97A03_south ∧
      d.first 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.first 0 1 = d.sphere 0 apm_t97A03_south ∧
      d.first 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.first 1 1 = d.sphere 1 apm_t97A03_south) :
    ∃ f : apm_t97A03_OneCircleCover → Y,
      Continuous f ∧ Function.Bijective f := by
  sorry

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hendpoints :
      d.second 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.second 0 1 = d.sphere 1 apm_t97A03_south ∧
      d.second 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.second 1 1 = d.sphere 0 apm_t97A03_south ∧
      d.first 0 0 = d.sphere 0 apm_t97A03_north ∧
      d.first 0 1 = d.sphere 0 apm_t97A03_south ∧
      d.first 1 0 = d.sphere 1 apm_t97A03_north ∧
      d.first 1 1 = d.sphere 1 apm_t97A03_south) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) := by
  obtain ⟨f, hf, hfb⟩ :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder
      A B hAB Y p hp hdegree d hendpoints
  letI : CompactSpace apm_t97A03_OneCircleCover := Quotient.compactSpace
  letI : T2Space Y :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_t2
      A B hAB Y p hp
  exact ⟨(Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f hfb) hf).symm⟩

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.refl _)
    (hsecond : d.secondPerm = Equiv.swap 0 1) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) := by
  apply apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric
    A B hAB Y p hp hdegree d
  exact
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_endpoints
      A B Y p d hfirst hsecond

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hmono : apm_t97A03_OneCircleMonodromy p hp) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) := by
  rcases apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_normalize
      A B Y p hp d hmono with h | h
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap
        A B hAB Y p hp hdegree d h.1 h.2
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap
        A B hAB Y p hp hdegree d h.1 h.2

theorem apm_t97A03_classify_aux_oneCircle_homeomorph
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (hmono : apm_t97A03_OneCircleMonodromy p hp) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) := by
  obtain ⟨d⟩ := apm_t97A03_classify_aux_sheetData A B hAB Y p hp hdegree
  exact apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend
    A B hAB Y p hp hdegree d hmono

open ConstructionTargets.PointWedgeQuotient

abbrev apm_t97A03_ThreeCircles :=
  ConstructionTargets.StatementSurfaceModels.ThreeCircles

abbrev apm_t97A03_twoSphereWedge :=
  Wedge apm_t97A03_north apm_t97A03_north

def apm_t97A03_twoSphereBase : apm_t97A03_twoSphereWedge :=
  quotientMap apm_t97A03_north apm_t97A03_north (.inl apm_t97A03_north)

abbrev apm_t97A03_modelWedge :=
  Wedge apm_t97A03_twoSphereBase
    ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase

def apm_t97A03_modelWedgeBase : apm_t97A03_modelWedge :=
  quotientMap apm_t97A03_twoSphereBase
    ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
    (.inl apm_t97A03_twoSphereBase)

/-- Generic attaching relation: the point `w` of the circles is glued to
`z` whenever `a w = some z`. -/
inductive apm_t97A03_invariants_aux_slide_GenRel {ι Z : Type}
    (a : ι × Circle → Option Z) : Sum Z (ι × Circle) → Sum Z (ι × Circle) → Prop
  | att (w : ι × Circle) (z : Z) (h : a w = some z) :
      apm_t97A03_invariants_aux_slide_GenRel a (.inr w) (.inl z)

/-- Sliding one attaching point along a path in `Z` does not change the
homotopy type of the adjunction space, provided only finitely many points
are attached (so a small arc around the moved point carries no other
attachment).  Proof plan: choose an arc of circle `w₀.1` around `w₀.2`
containing no other marked point; `Φ` is the identity off that arc and on it
runs `γ` from `z` to `z'` and then back out along the arc; `Ψ` is the same with
`γ.symm`; both composites differ from the identity only on the arc, by a
reparametrised `γ.symm.trans γ` (resp. `γ.trans γ.symm`), contracted by the
standard path homotopy. -/
private theorem apm_t97A03_invariants_aux_slide_generic_aux_isolate
    {ι : Type} [TopologicalSpace ι] [DiscreteTopology ι]
    (S : Set (ι × Circle)) (hS : S.Finite) (w₀ : ι × Circle) :
    ∃ U : Set (ι × Circle), IsOpen U ∧ w₀ ∈ U ∧ U ∩ S ⊆ {w₀} := by
  let T : Set (ι × Circle) := S \ {w₀}
  have hT : T.Finite := hS.subset (diff_subset)
  have hTc : IsClosed T := hT.isClosed
  refine ⟨Tᶜ, hTc.isOpen_compl, ?_, ?_⟩
  · simp [T]
  · intro w hw
    have hwS : w ∈ S := hw.2
    by_contra hwne
    have hwT : w ∈ T := ⟨hwS, by simpa [Set.mem_singleton_iff] using hwne⟩
    exact hw.1 hwT

/-- Angle of `c` seen from `c₀`, in `(-π, π]`. -/
noncomputable def apm_t97A03_invariants_aux_slide_aux_angle (c₀ c : Circle) : ℝ :=
  Complex.arg ((c₀⁻¹ * c : Circle) : ℂ)

/-- The detour, on representatives.  Off the closed arc of angular radius `ε`
about `w₀` it is the quotient map.  On the arc, at angle `θ` from `w₀`: for
`|θ| ≤ ε/2` it runs `γ` (from `z` at `θ = 0` to `z'` at `|θ| = ε/2`) in `Z`; for
`ε/2 ≤ |θ| ≤ ε` it re-enters the circle at `w₀` and stretches back out to the
arc's ends.  In the target `w₀` is glued to `z'`, so the two halves agree at
`|θ| = ε/2`. -/
noncomputable def apm_t97A03_invariants_aux_slide_aux_detourRaw
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a' : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z} (γ : Path z z') (ε : ℝ) :
    Sum Z (ι × Circle) → _root_.Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a')) := by
  classical
  exact fun x => match x with
    | .inl y => _root_.Quotient.mk _ (.inl y)
    | .inr w =>
      if w.1 = w₀.1 ∧ |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε then
        (if |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε / 2 then
          _root_.Quotient.mk _ (.inl (γ.extend
            (2 * |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| / ε)))
        else
          _root_.Quotient.mk _ (.inr (w.1, w₀.2 * Circle.exp
            (Real.sign (apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2) *
              (2 * |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| - ε)))))
      else _root_.Quotient.mk _ (.inr w)

/-- A small closed arc about `w₀` lies in the isolating neighbourhood. -/
theorem apm_t97A03_invariants_aux_slide_aux_eps
    {ι : Type} [TopologicalSpace ι] [DiscreteTopology ι]
    (w₀ : ι × Circle) (U : Set (ι × Circle)) (hUopen : IsOpen U) (hwU : w₀ ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi / 2 ∧
      ∀ w : ι × Circle, w.1 = w₀.1 →
        |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε → w ∈ U := by
  sorry

/-- The detour respects the source gluing: at `w₀` it gives `γ 0 = z`, and every
other marked point lies off the arc, where the gluing is unchanged. -/
theorem apm_t97A03_invariants_aux_slide_aux_detourRaw_respects
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a a' : ι × Circle → Option Z) (w₀ : ι × Circle) (hsame : ∀ w, w ≠ w₀ → a w = a' w)
    (z z' : Z) (hz : a w₀ = some z) (γ : Path z z') (ε : ℝ) (hε : 0 < ε)
    (harc : ∀ w : ι × Circle, w.1 = w₀.1 →
      |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε → (a w).isSome → w = w₀) :
    ∀ x y, apm_t97A03_invariants_aux_slide_GenRel a x y →
      apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε x =
        apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε y := by
  sorry

/-- Continuity of the detour: the pieces agree at `|θ| = ε/2` (because `w₀` is
glued to `z'` in the target) and at `|θ| = ε`; the arc avoids the cut of `arg`. -/
theorem apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a' : ι × Circle → Option Z) (w₀ : ι × Circle) (z z' : Z) (hz' : a' w₀ = some z')
    (γ : Path z z') (ε : ℝ) (hε : 0 < ε) (hεπ : ε < Real.pi / 2) :
    Continuous (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε) := by
  sorry

/-- The descended detour. -/
noncomputable def apm_t97A03_invariants_aux_slide_aux_detour
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a a' : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z} (γ : Path z z') (ε : ℝ)
    (hresp : ∀ x y, apm_t97A03_invariants_aux_slide_GenRel a x y →
      apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε x =
        apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε y)
    (hcont : Continuous (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε)) :
    C(_root_.Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)), _root_.Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a'))) :=
  ⟨_root_.Quotient.lift (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε)
      (fun x y hxy => Relation.EqvGen.rec hresp (fun _ => rfl)
        (fun _ _ _ ih => ih.symm) (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂) hxy),
    hcont.quotient_lift _⟩

/-- Going out along `γ` and back along `δ = γ.symm` is homotopic to the identity:
first contract the inserted loop `γ.trans γ.symm` in `Z` (Path.Homotopy.reflTransSymm,
with the arc's outer stretch held fixed), then shrink the constant inner region of
the circle reparametrisation linearly to the point `w₀`. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a a' : ι × Circle → Option Z) (w₀ : ι × Circle) (hsame : ∀ w, w ≠ w₀ → a w = a' w)
    (z z' : Z) (hz : a w₀ = some z) (hz' : a' w₀ = some z')
    (γ : Path z z') (δ : Path z' z) (hδ : δ = γ.symm) (ε : ℝ) (hε : 0 < ε)
    (hεπ : ε < Real.pi / 2)
    (harc : ∀ w : ι × Circle, w.1 = w₀.1 →
      |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε → (a w).isSome → w = w₀)
    (hresp : ∀ x y, apm_t97A03_invariants_aux_slide_GenRel a x y →
      apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε x =
        apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε y)
    (hcont : Continuous (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε))
    (hresp' : ∀ x y, apm_t97A03_invariants_aux_slide_GenRel a' x y →
      apm_t97A03_invariants_aux_slide_aux_detourRaw a w₀ δ ε x =
        apm_t97A03_invariants_aux_slide_aux_detourRaw a w₀ δ ε y)
    (hcont' : Continuous (apm_t97A03_invariants_aux_slide_aux_detourRaw a w₀ δ ε)) :
    ((apm_t97A03_invariants_aux_slide_aux_detour a' a w₀ δ ε hresp' hcont').comp
      (apm_t97A03_invariants_aux_slide_aux_detour a a' w₀ γ ε hresp hcont)).Homotopic
      (ContinuousMap.id _) := by
  sorry

/-- Assembly of the slide from the concrete detours. -/
private theorem apm_t97A03_invariants_aux_slide_generic_aux_realize
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a a' : ι × Circle → Option Z)
    (w₀ : ι × Circle) (hsame : ∀ w, w ≠ w₀ → a w = a' w)
    (z z' : Z) (hz : a w₀ = some z) (hz' : a' w₀ = some z') (γ : Path z z')
    (U : Set (ι × Circle)) (hUopen : IsOpen U) (hwU : w₀ ∈ U)
    (hUmarked : U ∩ {w | (a w).isSome} ⊆ {w₀}) :
    Nonempty (ContinuousMap.HomotopyEquiv (_root_.Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a))) (_root_.Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a')))) := by
  obtain ⟨ε, hε, hεπ, hU⟩ := apm_t97A03_invariants_aux_slide_aux_eps w₀ U hUopen hwU
  have harc : ∀ w : ι × Circle, w.1 = w₀.1 →
      |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε → (a w).isSome → w = w₀ :=
    fun w h1 h2 h3 => hUmarked ⟨hU w h1 h2, h3⟩
  have harc' : ∀ w : ι × Circle, w.1 = w₀.1 →
      |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε → (a' w).isSome → w = w₀ := by
    intro w h1 h2 h3
    by_contra hne
    exact hne (harc w h1 h2 (by rwa [hsame w hne]))
  have hsame' : ∀ w, w ≠ w₀ → a' w = a w := fun w hw => (hsame w hw).symm
  have hresp := apm_t97A03_invariants_aux_slide_aux_detourRaw_respects
    a a' w₀ hsame z z' hz γ ε hε harc
  have hcont := apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous
    a' w₀ z z' hz' γ ε hε hεπ
  have hresp' := apm_t97A03_invariants_aux_slide_aux_detourRaw_respects
    a' a w₀ hsame' z' z hz' γ.symm ε hε harc'
  have hcont' := apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous
    a w₀ z' z hz γ.symm ε hε hεπ
  refine ⟨⟨apm_t97A03_invariants_aux_slide_aux_detour a a' w₀ γ ε hresp hcont,
    apm_t97A03_invariants_aux_slide_aux_detour a' a w₀ γ.symm ε hresp' hcont', ?_, ?_⟩⟩
  · exact apm_t97A03_invariants_aux_slide_aux_detour_comp a a' w₀ hsame z z' hz hz'
      γ γ.symm rfl ε hε hεπ harc hresp hcont hresp' hcont'
  · have h := apm_t97A03_invariants_aux_slide_aux_detour_comp a' a w₀ hsame' z' z hz' hz
      γ.symm γ (Path.symm_symm γ).symm ε hε hεπ harc' hresp' hcont' hresp hcont
    exact h

theorem apm_t97A03_invariants_aux_slide_generic {ι Z : Type} [TopologicalSpace ι]
    [DiscreteTopology ι] [TopologicalSpace Z]
    (a a' : ι × Circle → Option Z) (hfin : {w | (a w).isSome}.Finite)
    (w₀ : ι × Circle) (hsame : ∀ w, w ≠ w₀ → a w = a' w)
    (z z' : Z) (hz : a w₀ = some z) (hz' : a' w₀ = some z') (γ : Path z z') :
    Nonempty (ContinuousMap.HomotopyEquiv
      (Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)))
      (Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a')))) := by
  obtain ⟨U, hUopen, hwU, hUmarked⟩ :=
    apm_t97A03_invariants_aux_slide_generic_aux_isolate
      {w | (a w).isSome} hfin w₀
  exact apm_t97A03_invariants_aux_slide_generic_aux_realize
    a a' w₀ hsame z z' hz hz' γ U hUopen hwU hUmarked

/-- The one-circle model after sliding, on each sphere sheet, the south
attachment to the north attachment.  The four marked points of the circle
are unchanged; only their attaching maps into the sphere sheets have been
homotoped. -/
inductive apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel :
    Sum apm_t97A03_TwoSpheres Circle →
      Sum apm_t97A03_TwoSpheres Circle → Prop
  | p0 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel
      (.inr apm_t97A03_circleOne) (.inl (0, apm_t97A03_north))
  | p1 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel
      (.inr apm_t97A03_circleI) (.inl (0, apm_t97A03_north))
  | p2 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel
      (.inr apm_t97A03_circleNegOne) (.inl (1, apm_t97A03_north))
  | p3 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel
      (.inr apm_t97A03_circleNegI) (.inl (1, apm_t97A03_north))

def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover :=
  Quotient (Relation.EqvGen.setoid
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel)

noncomputable instance : TopologicalSpace
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres Circle ↦ Quotient.mk _ x) inferInstance

private noncomputable def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0
    (w : Unit × Circle) : Option apm_t97A03_TwoSpheres := by
  classical
  exact if w.2 = apm_t97A03_circleOne then some (0, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleI then some (0, apm_t97A03_south)
  else if w.2 = apm_t97A03_circleNegOne then some (1, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleNegI then some (1, apm_t97A03_south)
  else none

private noncomputable def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1
    (w : Unit × Circle) : Option apm_t97A03_TwoSpheres := by
  classical
  exact if w.2 = apm_t97A03_circleOne then some (0, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleI then some (0, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleNegOne then some (1, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleNegI then some (1, apm_t97A03_south)
  else none

private noncomputable def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2
    (w : Unit × Circle) : Option apm_t97A03_TwoSpheres := by
  classical
  exact if w.2 = apm_t97A03_circleOne then some (0, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleI then some (0, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleNegOne then some (1, apm_t97A03_north)
  else if w.2 = apm_t97A03_circleNegI then some (1, apm_t97A03_north)
  else none

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97A03_OneCircleCover
      (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0)))) := by
  sorry
/-
  let h : Sum apm_t97A03_TwoSpheres (Unit × Circle) ≃ₜ
      Sum apm_t97A03_TwoSpheres Circle :=
    Homeomorph.sumCongr (Homeomorph.refl _) (Homeomorph.punitProd Circle)
  let f : (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0))) →
      apm_t97A03_OneCircleCover :=
    Quotient.lift (fun x => Quotient.mk _ (h x)) (by
      intro x y hxy
      apply Quotient.sound
      exact Relation.EqvGen.rec
        (fun _ _ hr => by
          cases hr with
          | att w z hz =>
            simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0]
              at hz
            split_ifs at hz with h1 hI hn1 hnI
            · subst w; cases hz
              exact Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.n0
            · subst w; cases hz
              exact Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.s0
            · subst w; cases hz
              exact Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.n1
            · subst w; cases hz
              exact Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.s1)
        (fun x => Relation.EqvGen.refl (h x))
        (fun _ _ _ ih => Relation.EqvGen.symm _ _ ih)
        (fun _ _ _ _ _ ih₁ ih₂ => Relation.EqvGen.trans _ _ _ ih₁ ih₂)
        hxy)
  let g : apm_t97A03_OneCircleCover →
      Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0)) :=
    Quotient.lift (fun x => Quotient.mk _ (h.symm x)) (by
      intro x y hxy
      apply Quotient.sound
      exact Relation.EqvGen.rec
        (fun _ _ hr => by
          cases hr with
          | n0 => exact Relation.EqvGen.rel _ _ (.att _ _ (by simp
              [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0]))
          | s0 => exact Relation.EqvGen.rel _ _ (.att _ _ (by norm_num
              [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0,
                apm_t97A03_circleI, apm_t97A03_circleOne,
                Subtype.ext_iff, Complex.ext_iff]))
          | n1 => exact Relation.EqvGen.rel _ _ (.att _ _ (by norm_num
              [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0,
                apm_t97A03_circleNegOne, apm_t97A03_circleOne,
                apm_t97A03_circleI, Subtype.ext_iff, Complex.ext_iff]))
          | s1 => exact Relation.EqvGen.rel _ _ (.att _ _ (by norm_num
              [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0,
                apm_t97A03_circleNegI, apm_t97A03_circleOne,
                apm_t97A03_circleI, apm_t97A03_circleNegOne,
                Subtype.ext_iff, Complex.ext_iff])))
        (fun x => Relation.EqvGen.refl (h.symm x))
        (fun _ _ _ ih => Relation.EqvGen.symm _ _ ih)
        (fun _ _ _ _ _ ih₁ ih₂ => Relation.EqvGen.trans _ _ _ ih₁ ih₂)
        hxy)
  have hf : Continuous f := by
    apply continuous_coinduced_dom.mpr
    exact continuous_coinduced_rng.comp h.continuous
  have hg : Continuous g := by
    apply continuous_coinduced_dom.mpr
    exact continuous_coinduced_rng.comp h.symm.continuous
  let e : (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0))) ≃ₜ
      apm_t97A03_OneCircleCover :=
    { toFun := f
      invFun := g
      left_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro x
        exact congrArg (Quotient.mk _)
          (h.symm_apply_apply x)
      right_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        intro x
        exact congrArg (Quotient.mk _)
          (h.apply_symm_apply x)
      continuous_toFun := hf
      continuous_invFun := hg }
  exact ⟨e.symm.toHomotopyEquiv⟩
-/

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first_aux_finite :
    {w | (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0 w).isSome}.Finite := by
  apply Set.Finite.subset (Set.toFinite
    ({((), apm_t97A03_circleOne), ((), apm_t97A03_circleI),
      ((), apm_t97A03_circleNegOne), ((), apm_t97A03_circleNegI)} : Set _))
  intro w hw
  simp only [Set.mem_setOf_eq,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0] at hw
  split_ifs at hw with h1 hI hn1 hnI
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleOne at h1
    subst w
    simp
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleI at hI
    subst w
    simp
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleNegOne at hn1
    subst w
    simp
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleNegI at hnI
    subst w
    simp
  · simp at hw

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second_aux_finite :
    {w | (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1 w).isSome}.Finite := by
  apply Set.Finite.subset (Set.toFinite
    ({((), apm_t97A03_circleOne), ((), apm_t97A03_circleI),
      ((), apm_t97A03_circleNegOne), ((), apm_t97A03_circleNegI)} : Set _))
  intro w hw
  simp only [Set.mem_setOf_eq,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1] at hw
  split_ifs at hw with h1 hI hn1 hnI
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleOne at h1
    subst w
    simp
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleI at hI
    subst w
    simp
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleNegOne at hn1
    subst w
    simp
  · rcases w with ⟨u, w⟩
    change w = apm_t97A03_circleNegI at hnI
    subst w
    simp
  · simp at hw

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first_aux_at_source :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0
      ((), apm_t97A03_circleI) = some (0, apm_t97A03_south) := by
  have hne : apm_t97A03_circleI ≠ apm_t97A03_circleOne := by
    intro h
    have hi := congrArg (fun z : Circle => z.1.im) h
    norm_num [apm_t97A03_circleI, apm_t97A03_circleOne] at hi
  simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0, hne]

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first_aux_at_target :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1
      ((), apm_t97A03_circleI) = some (0, apm_t97A03_north) := by
  have hne : apm_t97A03_circleI ≠ apm_t97A03_circleOne := by
    intro h
    have hi := congrArg (fun z : Circle => z.1.im) h
    norm_num [apm_t97A03_circleI, apm_t97A03_circleOne] at hi
  simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1, hne]

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second_aux_at_source :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1
      ((), apm_t97A03_circleNegI) = some (1, apm_t97A03_south) := by
  have h1 : apm_t97A03_circleNegI ≠ apm_t97A03_circleOne := by
    intro h; have := congrArg (fun z : Circle => z.1.im) h
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleOne] at this
  have hI : apm_t97A03_circleNegI ≠ apm_t97A03_circleI := by
    intro h; have := congrArg (fun z : Circle => z.1.im) h
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleI] at this
  have hn1 : apm_t97A03_circleNegI ≠ apm_t97A03_circleNegOne := by
    intro h; have := congrArg (fun z : Circle => z.1.re) h
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleNegOne] at this
  simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1,
    h1, hI, hn1]

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second_aux_at_target :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2
      ((), apm_t97A03_circleNegI) = some (1, apm_t97A03_north) := by
  have h1 : apm_t97A03_circleNegI ≠ apm_t97A03_circleOne := by
    intro h; have := congrArg (fun z : Circle => z.1.im) h
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleOne] at this
  have hI : apm_t97A03_circleNegI ≠ apm_t97A03_circleI := by
    intro h; have := congrArg (fun z : Circle => z.1.im) h
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleI] at this
  have hn1 : apm_t97A03_circleNegI ≠ apm_t97A03_circleNegOne := by
    intro h; have := congrArg (fun z : Circle => z.1.re) h
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleNegOne] at this
  simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2,
    h1, hI, hn1]

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first :
    Nonempty (ContinuousMap.HomotopyEquiv
      (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0)))
      (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1)))) := by
  apply apm_t97A03_invariants_aux_slide_generic
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1
    (w₀ := ((), apm_t97A03_circleI))
    (z := (0, apm_t97A03_south)) (z' := (0, apm_t97A03_north))
    (γ := apm_t97A03_sphereReturn.symm.map (continuous_const.prodMk continuous_id))
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first_aux_finite
  · intro w hw
    simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0,
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1]
    split_ifs with h1 hI hn1 hnI <;> try rfl
    exact (hw (Prod.ext (Subsingleton.elim _ _) hI)).elim
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first_aux_at_source
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first_aux_at_target

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second :
    Nonempty (ContinuousMap.HomotopyEquiv
      (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1)))
      (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2)))) := by
  apply apm_t97A03_invariants_aux_slide_generic
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2
    (w₀ := ((), apm_t97A03_circleNegI))
    (z := (1, apm_t97A03_south)) (z' := (1, apm_t97A03_north))
    (γ := apm_t97A03_sphereReturn.symm.map (continuous_const.prodMk continuous_id))
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second_aux_finite
  · intro w hw
    simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a1,
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2]
    split_ifs with h1 hI hn1 hnI <;> try rfl
    exact (hw (Prod.ext (Subsingleton.elim _ _) hnI)).elim
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second_aux_at_source
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second_aux_at_target

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_target :
    Nonempty (ContinuousMap.HomotopyEquiv (Quotient (Relation.EqvGen.setoid
      (apm_t97A03_invariants_aux_slide_GenRel
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2)))
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover) := by
  sorry
/-
  have hrel :
      apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2 =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel := by
    funext x y
    apply propext
    constructor
    · rintro ⟨w, z, hz⟩
      simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2]
        at hz
      split_ifs at hz with h1 hI hn1 hnI
      · subst w; cases hz; exact .p0
      · subst w; cases hz; exact .p1
      · subst w; cases hz; exact .p2
      · subst w; cases hz; exact .p3
    · intro hr
      cases hr with
      | p0 => exact .att _ _ (by simp
          [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2])
      | p1 => exact .att _ _ (by norm_num
          [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2,
            apm_t97A03_circleI, apm_t97A03_circleOne,
            Subtype.ext_iff, Complex.ext_iff])
      | p2 => exact .att _ _ (by norm_num
          [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2,
            apm_t97A03_circleNegOne, apm_t97A03_circleOne,
            apm_t97A03_circleI, Subtype.ext_iff, Complex.ext_iff])
      | p3 => exact .att _ _ (by norm_num
          [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2,
            apm_t97A03_circleNegI, apm_t97A03_circleOne,
            apm_t97A03_circleI, apm_t97A03_circleNegOne,
            Subtype.ext_iff, Complex.ext_iff])
  rw [hrel]
  exact ⟨ContinuousMap.HomotopyEquiv.refl _⟩
-/

/-- Homotopy invariance of this concrete adjunction space: slide each south
attaching point to north along a meridian in its sphere sheet. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97A03_OneCircleCover
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover) := by
  obtain ⟨source⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source
  obtain ⟨first⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_first
  obtain ⟨second⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_second
  obtain ⟨target⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_target
  exact ⟨source.trans first |>.trans second |>.trans target⟩

/-- The closed counterclockwise quarter arc from `i` to `-1`.  In Cartesian
coordinates this is exactly the part of the unit circle in the closed
upper-left quadrant. -/
def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc :
    Set Circle :=
  {z | z.1.re ≤ 0 ∧ 0 ≤ z.1.im}

/-- The quotient relation after contracting the whole connecting quarter arc,
not merely identifying its endpoints.  The four original attaching relations
are retained, and every point of the contracted arc is sent to sheet zero's
north point. -/
inductive apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel :
    Sum apm_t97A03_TwoSpheres Circle →
      Sum apm_t97A03_TwoSpheres Circle → Prop
  | p0 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr apm_t97A03_circleOne) (.inl (0, apm_t97A03_north))
  | p1 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr apm_t97A03_circleI) (.inl (0, apm_t97A03_north))
  | p2 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr apm_t97A03_circleNegOne) (.inl (1, apm_t97A03_north))
  | p3 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr apm_t97A03_circleNegI) (.inl (1, apm_t97A03_north))
  | arc (z : Circle)
      (hz : z ∈ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc) :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
        (.inr z) (.inl (0, apm_t97A03_north))

def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space :=
  Quotient (Relation.EqvGen.setoid
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel)

noncomputable instance : TopologicalSpace
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres Circle ↦ Quotient.mk _ x) inferInstance

private def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover →
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space :=
  Quotient.lift
    (fun x ↦ Quotient.mk _ x)
    (by
      intro x y hxy
      apply Quotient.sound
      exact Relation.EqvGen.rec
        (fun _ _ h ↦ by
          cases h with
          | p0 =>
              exact Relation.EqvGen.rel _ _
                apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p0
          | p1 =>
              exact Relation.EqvGen.rel _ _
                apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p1
          | p2 =>
              exact Relation.EqvGen.rel _ _
                apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p2
          | p3 =>
              exact Relation.EqvGen.rel _ _
                apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p3)
        (fun x ↦ Relation.EqvGen.refl x)
        (fun _ _ _ ih ↦ Relation.EqvGen.symm _ _ ih)
        (fun _ _ _ _ _ ih₁ ih₂ ↦ Relation.EqvGen.trans _ _ _ ih₁ ih₂)
        hxy)

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q_continuous :
    Continuous
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q := by
  apply continuous_coinduced_dom.mpr
  exact continuous_coinduced_rng

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies :
    ∃ s : ContinuousMap
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover,
      (s.comp (ContinuousMap.mk
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q_continuous)).Homotopic
          (ContinuousMap.id _) ∧
      ((ContinuousMap.mk
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q_continuous).comp s).Homotopic
        (ContinuousMap.id _) := by
  sorry

/-- Contracting the upper-left quarter arc is a homotopy equivalence.  A
proof can descend the linear contraction of that closed arc, and use the
circle reparametrisation which is constant on the arc as a homotopy inverse. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract :
    Nonempty (ContinuousMap.HomotopyEquiv
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space) := by
  let q : ContinuousMap
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space :=
    ⟨apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q,
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q_continuous⟩
  obtain ⟨s, left, right⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies
  exact ⟨⟨q, s, left, right⟩⟩

/-- In the contracted quotient there is one vertex: the contracted arc joins
the two north points.  The other three quarter arcs are the three loop legs,
so the quotient is homeomorphic to the fixed wedge of two spheres and three
circles. -/
private def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_circlePow4
    (z : Circle) : Circle :=
  z ^ 4

private def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere
    (w : apm_t97A03_TwoSpheres) : apm_t97A03_modelWedge :=
  quotientMap apm_t97A03_twoSphereBase
    ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
    (.inl (quotientMap apm_t97A03_north apm_t97A03_north
      (if w.1 = 0 then .inl w.2 else .inr w.2)))

private def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg
    (j : Fin 3) (z : Circle) : apm_t97A03_modelWedge :=
  let z4 :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_circlePow4 z
  quotientMap apm_t97A03_twoSphereBase
    ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
    (.inr (match j with
      | ⟨0, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld
          (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft z4)
      | ⟨1, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld
          (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight z4)
      | ⟨2, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew z4))

private noncomputable def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw
    (x : Sum apm_t97A03_TwoSpheres Circle) : apm_t97A03_modelWedge := by
  classical
  exact match x with
  | .inl w =>
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere w
  | .inr z =>
      if z.1.re ≤ 0 ∧ 0 ≤ z.1.im then apm_t97A03_modelWedgeBase
      else if 0 ≤ z.1.re ∧ 0 ≤ z.1.im then
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 0 z
      else if z.1.re ≤ 0 ∧ z.1.im ≤ 0 then
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 1 z
      else
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 2 z

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_continuous_aux_sphere :
    Continuous
      (fun w : apm_t97A03_TwoSpheres ↦
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw
          (.inl w)) := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_continuous_aux_circle :
    Continuous
      (fun z : Circle ↦
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw
          (.inr z)) := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_continuous :
    Continuous
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw := by
  apply continuous_sum_dom.mpr
  exact ⟨
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_continuous_aux_sphere,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_continuous_aux_circle⟩

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator
    {x y : Sum apm_t97A03_TwoSpheres Circle}
    (h : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw x =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw y := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects
    {x y : Sum apm_t97A03_TwoSpheres Circle}
    (h : Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw x =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw y := by
  exact Relation.EqvGen.rec
    (fun _ _ h ↦
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator h)
    (fun _ ↦ rfl)
    (fun _ _ _ ih ↦ ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ ↦ ih₁.trans ih₂)
    h

private noncomputable def
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space →
      apm_t97A03_modelWedge :=
  Quotient.lift
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw
    (fun _ _ h =>
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects h)

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_continuous :
    Continuous
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map := by
  apply Continuous.quotient_lift
  exact
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_continuous

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_surjective_aux_raw :
    Function.Surjective
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_surjective :
    Function.Surjective
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map := by
  intro z
  obtain ⟨x, hx⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_surjective_aux_raw z
  exact ⟨Quotient.mk _ x, hx⟩

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_sphere
    (x y : apm_t97A03_TwoSpheres)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel (.inl x) (.inl y) := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle
    (x : apm_t97A03_TwoSpheres) (y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel (.inl x) (.inr y) := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_sphere
    (x : Circle) (y : apm_t97A03_TwoSpheres)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) (.inl y) := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_circle
    (x y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) (.inr y) := by
  sorry

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel
    {x y : Sum apm_t97A03_TwoSpheres Circle}
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw x =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw y) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel x y := by
  rcases x with x | x <;> rcases y with y | y
  · exact
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_sphere
        x y h
  · exact
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle
        x y h
  · exact
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_sphere
        x y h
  · exact
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_circle
        x y h

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_injective :
    Function.Injective
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map := by
  rintro ⟨x⟩ ⟨y⟩ h
  exact Quotient.sound
    (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel h)

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv :
    ∃ e :
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space ≃
          apm_t97A03_modelWedge,
      Continuous e := by
  let f :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map
  let e :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space ≃
        apm_t97A03_modelWedge :=
    Equiv.ofBijective f ⟨
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_injective,
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_surjective⟩
  exact ⟨e,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_continuous⟩

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_wedge
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    (x₀ : X) (y₀ : Y) : T2Space (Wedge x₀ y₀) := by
  apply ConstructionTargets.compact_closed_equivalence_quotient_t2
    (WedgeSetoid x₀ y₀)
  have hclosed : IsClosed (Set.diagonal (Sum X Y) ∪
      {(.inl x₀, .inr y₀), (.inr y₀, .inl x₀)}) :=
    isClosed_diagonal.union (isClosed_singleton.union isClosed_singleton)
  convert hclosed using 1
  apply Set.ext
  rintro ⟨a, b⟩
  change Relation.EqvGen (Rel x₀ y₀) a b ↔ _
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_diagonal_iff]
  constructor
  · intro h
    induction h with
    | rel a b h => cases h; aesop
    | refl => aesop
    | symm _ _ _ ih => rcases ih with h | h | h <;> aesop
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with h | h | h <;> rcases ih₂ with h' | h' | h' <;>
          simp_all
  · rintro (h | h | h)
    · exact h ▸ Relation.EqvGen.refl _
    · rcases h with ⟨rfl, rfl⟩
      exact Relation.EqvGen.rel _ _ (.base : Rel x₀ y₀ (.inl x₀) (.inr y₀))
    · rcases h with ⟨rfl, rfl⟩
      exact (Relation.EqvGen.rel _ _
        (.base : Rel x₀ y₀ (.inl x₀) (.inr y₀))).symm

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_compactWedge
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] (x₀ : X) (y₀ : Y) :
    CompactSpace (Wedge x₀ y₀) := by
  constructor
  rw [← Set.range_eq_univ.mpr (surjective_quotientMap x₀ y₀)]
  simpa only [Set.image_univ] using
    isCompact_univ.image (continuous_quotientMap x₀ y₀)

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2 :
    T2Space apm_t97A03_modelWedge := by
  letI : CompactSpace apm_t97A03_twoSphereWedge :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_compactWedge
      apm_t97A03_north apm_t97A03_north
  letI : T2Space apm_t97A03_twoSphereWedge :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_wedge
      apm_t97A03_north apm_t97A03_north
  letI : CompactSpace ConstructionTargets.StatementSurfaceModels.TwoCircles :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_compactWedge
      (1 : Circle) (1 : Circle)
  letI : T2Space ConstructionTargets.StatementSurfaceModels.TwoCircles :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_wedge
      (1 : Circle) (1 : Circle)
  letI : CompactSpace apm_t97A03_ThreeCircles :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_compactWedge
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint (1 : Circle)
  letI : T2Space apm_t97A03_ThreeCircles :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_wedge
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint (1 : Circle)
  exact
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2_aux_wedge
      apm_t97A03_twoSphereBase
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_compact :
    CompactSpace
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space := by
  let q : Sum apm_t97A03_TwoSpheres Circle →
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space :=
    fun x ↦ Quotient.mk _ x
  have hq : Function.Surjective q := Quotient.mk_surjective
  have hcomp : IsCompact
      (Set.univ : Set
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space) := by
    rw [← Set.range_eq_univ.mpr hq]
    have h := isCompact_univ.image (continuous_coinduced_rng : Continuous q)
    rwa [Set.image_univ] at h
  exact isCompact_univ_iff.mp hcomp

theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm :
    Nonempty
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space ≃ₜ
        apm_t97A03_modelWedge) := by
  letI : T2Space apm_t97A03_modelWedge :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2
  letI : CompactSpace
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_compact
  obtain ⟨e, he⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) he⟩

theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse :
    Nonempty (ContinuousMap.HomotopyEquiv
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover
      apm_t97A03_modelWedge) := by
  obtain ⟨contract⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract
  obtain ⟨normalForm⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm
  exact ⟨contract.trans normalForm.toHomotopyEquiv⟩

/-- Collapse the contractible connecting arc in the one-circle quotient.
The quotient homotopies leave two sphere summands and three circle loops,
giving the fixed `modelWedge`.  Use `PointWedgePointedContractionDescent` and
the existing generic point-wedge comparison. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97A03_OneCircleCover apm_t97A03_modelWedge) := by
  obtain ⟨slide⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide
  obtain ⟨collapse⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse
  exact ⟨slide.trans collapse⟩

/-- The two-circle model after sliding the two south attachments to north on
their respective sphere sheets. -/
inductive apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel :
    Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) →
      Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) → Prop
  | c0a : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel
      (.inr (0, apm_t97A03_circleOne)) (.inl (0, apm_t97A03_north))
  | c0b : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel
      (.inr (0, apm_t97A03_circleNegOne)) (.inl (1, apm_t97A03_north))
  | c1a : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel
      (.inr (1, apm_t97A03_circleOne)) (.inl (1, apm_t97A03_north))
  | c1b : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel
      (.inr (1, apm_t97A03_circleNegOne)) (.inl (0, apm_t97A03_north))

def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover :=
  Quotient (Relation.EqvGen.setoid
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel)

noncomputable instance : TopologicalSpace
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) ↦ Quotient.mk _ x)
    inferInstance

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a
    (w : Fin 2 × Circle) : Option apm_t97A03_TwoSpheres := by
  classical
  exact if w = (0, apm_t97A03_circleOne) then some (0, apm_t97A03_north)
  else if w = (0, apm_t97A03_circleNegOne) then some (1, apm_t97A03_south)
  else if w = (1, apm_t97A03_circleOne) then some (1, apm_t97A03_north)
  else if w = (1, apm_t97A03_circleNegOne) then some (0, apm_t97A03_south)
  else none

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf
    (w : Fin 2 × Circle) : Option apm_t97A03_TwoSpheres := by
  classical
  exact if w = (0, apm_t97A03_circleOne) then some (0, apm_t97A03_north)
  else if w = (0, apm_t97A03_circleNegOne) then some (1, apm_t97A03_south)
  else if w = (1, apm_t97A03_circleOne) then some (1, apm_t97A03_north)
  else if w = (1, apm_t97A03_circleNegOne) then some (0, apm_t97A03_north)
  else none

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid
    (w : Fin 2 × Circle) : Option apm_t97A03_TwoSpheres := by
  classical
  exact if w = (0, apm_t97A03_circleOne) then some (0, apm_t97A03_north)
  else if w = (0, apm_t97A03_circleNegOne) then some (1, apm_t97A03_north)
  else if w = (1, apm_t97A03_circleOne) then some (1, apm_t97A03_north)
  else if w = (1, apm_t97A03_circleNegOne) then some (0, apm_t97A03_north)
  else none

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne :
    apm_t97A03_circleOne ≠ apm_t97A03_circleNegOne := by
  intro h
  have := congrArg Subtype.val h
  norm_num [apm_t97A03_circleOne, apm_t97A03_circleNegOne] at this

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne' :
    apm_t97A03_circleNegOne ≠ apm_t97A03_circleOne :=
  apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne.symm

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_rel_a :
    apm_t97A03_invariants_aux_slide_GenRel
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a =
      apm_t97A03_TwoCircleRel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨w, z, hz⟩
    simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a]
      at hz
    split_ifs at hz with h₀ h₁ h₂ h₃
    · subst w; cases hz; exact apm_t97A03_TwoCircleRel.c0n
    · subst w; cases hz; exact apm_t97A03_TwoCircleRel.c0s
    · subst w; cases hz; exact apm_t97A03_TwoCircleRel.c1n
    · subst w; cases hz; exact apm_t97A03_TwoCircleRel.c1s
  · intro h
    cases h with
    | c0n => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a])
    | c0s => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a,
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])
    | c1n => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a])
    | c1s => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a,
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_rel_half :
    apm_t97A03_invariants_aux_slide_GenRel
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf =
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfRel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨w, z, hz⟩
    simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf] at hz
    split_ifs at hz with h₀ h₁ h₂ h₃
    · subst w; cases hz; exact .c0n
    · subst w; cases hz; exact .c0s
    · subst w; cases hz; exact .c1n
    · subst w; cases hz; exact .c1s
  · intro h
    cases h with
    | c0n => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf])
    | c0s => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf,
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])
    | c1n => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf])
    | c1s => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf,
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_rel_slid :
    apm_t97A03_invariants_aux_slide_GenRel
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid =
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨w, z, hz⟩
    simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid] at hz
    split_ifs at hz with h₀ h₁ h₂ h₃
    · subst w; cases hz; exact .c0a
    · subst w; cases hz; exact .c0b
    · subst w; cases hz; exact .c1a
    · subst w; cases hz; exact .c1b
  · intro h
    cases h with
    | c0a => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid])
    | c0b => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid,
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])
    | c1a => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid])
    | c1b => exact .att _ _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid,
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])

/-- Intermediate quotient in which only the south attachment on sphere sheet
zero has been slid to north.  Keeping the other south attachment unchanged
lets the two-circle slide be assembled from two independent one-attachment
slides. -/
def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfCover :=
  Quotient (Relation.EqvGen.setoid
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfRel)

noncomputable instance : TopologicalSpace
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfCover :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) ↦ Quotient.mk _ x)
    inferInstance

/-- Sliding the attachment on sphere sheet zero along the reverse of
`apm_t97A03_sphereReturn` gives the half-slid quotient.  All other summand
maps and attachments remain fixed. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_first :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97A03_TwoCircleCover
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfCover) := by
  let a := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a
  let a' := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf
  have hfin : {w | (a w).isSome}.Finite := by
    classical
    have hf : ({((1 : Fin 2), apm_t97A03_circleNegOne)} : Set (Fin 2 × Circle)).Finite :=
      Set.finite_singleton _
    refine Set.Finite.subset
      (((hf.insert ((1 : Fin 2), apm_t97A03_circleOne)).insert
        ((0 : Fin 2), apm_t97A03_circleNegOne)).insert
          ((0 : Fin 2), apm_t97A03_circleOne)) ?_
    intro w hw
    simp only [Set.mem_setOf_eq, Option.isSome_iff_ne_none] at hw
    simp only [a, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a] at hw
    split_ifs at hw with h₀ h₁ h₂ h₃ <;> simp_all
  have hsame : ∀ w, w ≠ (1, apm_t97A03_circleNegOne) → a w = a' w := by
    classical
    intro w hw
    simp only [a, a',
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf]
    split_ifs <;> simp_all
  let γ : Path ((0 : Fin 2), apm_t97A03_south) ((0 : Fin 2), apm_t97A03_north) :=
    apm_t97A03_sphereReturn.symm.map
      (continuous_const.prodMk continuous_id)
  have h := apm_t97A03_invariants_aux_slide_generic a a' hfin
    (1, apm_t97A03_circleNegOne) hsame
    (0, apm_t97A03_south) (0, apm_t97A03_north)
    (by simp [a, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_a,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])
    (by simp [a', apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])
    γ
  rw [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_rel_a,
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_rel_half] at h
  exact h

/-- Sliding the remaining attachment, on sphere sheet one, along the same
north--south meridian gives the fully slid quotient.  All other summand maps
and attachments remain fixed. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_second :
    Nonempty (ContinuousMap.HomotopyEquiv
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_HalfCover
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover) := by
  let a := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf
  let a' := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid
  have hfin : {w | (a w).isSome}.Finite := by
    classical
    have hf : ({((1 : Fin 2), apm_t97A03_circleNegOne)} : Set (Fin 2 × Circle)).Finite :=
      Set.finite_singleton _
    refine Set.Finite.subset
      (((hf.insert ((1 : Fin 2), apm_t97A03_circleOne)).insert
        ((0 : Fin 2), apm_t97A03_circleNegOne)).insert
          ((0 : Fin 2), apm_t97A03_circleOne)) ?_
    intro w hw
    simp only [Set.mem_setOf_eq, Option.isSome_iff_ne_none] at hw
    simp only [a, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf] at hw
    split_ifs at hw with h₀ h₁ h₂ h₃ <;> simp_all
  have hsame : ∀ w, w ≠ (0, apm_t97A03_circleNegOne) → a w = a' w := by
    classical
    intro w hw
    simp only [a, a',
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid]
    split_ifs <;> simp_all
  let γ : Path ((1 : Fin 2), apm_t97A03_south) ((1 : Fin 2), apm_t97A03_north) :=
    apm_t97A03_sphereReturn.symm.map
      (continuous_const.prodMk continuous_id)
  have h := apm_t97A03_invariants_aux_slide_generic a a' hfin
    (0, apm_t97A03_circleNegOne) hsame
    (1, apm_t97A03_south) (1, apm_t97A03_north)
    (by simp [a, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aHalf,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])
    (by simp [a', apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_aSlid,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_points_ne'])
    γ
  rw [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_rel_half,
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_rel_slid] at h
  exact h

/-- Homotopy invariance for the two-circle adjunction space, sliding the two
south attaching points to north along sphere meridians. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97A03_TwoCircleCover
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover) := by
  obtain ⟨first⟩ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_first
  obtain ⟨second⟩ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide_aux_second
  exact ⟨first.trans second⟩

/-- The closed upper semicircle on circle zero is a spanning tree edge
from the north point of sheet zero to the north point of sheet one. -/
def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc : Set Circle :=
  {z | 0 ≤ z.1.im}

/-- Retain the four slid attachments and collapse every point of the upper
semicircle of circle zero to the north point of sheet zero. -/
inductive apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel :
    Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) →
      Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) → Prop
  | c0a : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr (0, apm_t97A03_circleOne)) (.inl (0, apm_t97A03_north))
  | c0b : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr (0, apm_t97A03_circleNegOne)) (.inl (1, apm_t97A03_north))
  | c1a : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr (1, apm_t97A03_circleOne)) (.inl (1, apm_t97A03_north))
  | c1b : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr (1, apm_t97A03_circleNegOne)) (.inl (0, apm_t97A03_north))
  | arc (z : Circle) (hz : z ∈ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc) :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
        (.inr (0, z)) (.inl (0, apm_t97A03_north))

def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space :=
  Quotient (Relation.EqvGen.setoid apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel)

noncomputable instance : TopologicalSpace apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) ↦ Quotient.mk _ x)
    inferInstance

/-- The canonical continuous map to the edge-collapse quotient. -/
noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q :
    ContinuousMap apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space where
  toFun := Quotient.lift (fun x => Quotient.mk _ x) (by
    intro x y h
    apply Quotient.sound
    induction h with
    | rel x y h =>
      apply Relation.EqvGen.rel
      cases h with
      | c0a => exact .c0a
      | c0b => exact .c0b
      | c1a => exact .c1a
      | c1b => exact .c1b
    | refl x => exact Relation.EqvGen.refl x
    | symm x y h ih => exact Relation.EqvGen.symm x y ih
    | trans x y z h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans x y z ih₁ ih₂)
  continuous_toFun := continuous_coinduced_rng.quotient_lift _

/-- Squaring a real point on the unit circle gives the basepoint. -/
lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_square_boundary (z : Circle) (h : z.1.im = 0) :
    z * z = 1 := by
  apply Circle.ext
  apply Complex.ext
  · have hn := Circle.normSq_coe z
    rw [Complex.normSq_apply] at hn
    simp only [Circle.coe_mul, Complex.mul_re, Circle.coe_one, Complex.one_re]
    nlinarith
  · simp [h, Complex.mul_im]

/-- Collapse the upper semicircle and run once around the circle on the lower one. -/
noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle : ContinuousMap Circle Circle where
  toFun z := if 0 ≤ z.1.im then 1 else z * z
  continuous_toFun := by
    apply Continuous.if_le continuous_const (continuous_id.mul continuous_id)
      continuous_const (Complex.continuous_im.comp continuous_subtype_val)
    intro z hz
    exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_square_boundary z hz.symm).symm

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle_arc (z : Circle)
    (hz : z ∈ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle z = 1 := by
  exact if_pos hz

section
local notation "SC" => apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover
local notation "N₀" => (Quotient.mk _ (Sum.inl (0, apm_t97A03_north)) : SC)
local notation "N₁" => (Quotient.mk _ (Sum.inl (1, apm_t97A03_north)) : SC)

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge : Path N₀ N₁ :=
  ((apm_t97A03_circleArc apm_t97A03_circleOne apm_t97A03_circleNegOne).map
    (show Continuous (fun z : Circle => (Quotient.mk _ (.inr (0, z)) : SC)) from
      continuous_coinduced_rng.comp (continuous_inr.comp (continuous_const.prodMk continuous_id)))).cast
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c0a)).symm
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c0b)).symm

/-- Polynomial double-angle map; its restriction to the lower hemisphere
stretches that hemisphere over the whole sphere. -/
noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold : ContinuousMap apm_t97A03_S2 apm_t97A03_S2 where
  toFun x := ⟨WithLp.toLp 2 ![-2 * x.1 2 * x.1 0,
      -2 * x.1 2 * x.1 1, 1 - 2 * (x.1 2)^2], by
    rw [Metric.mem_sphere, dist_zero_right]
    have hx : (x.1 0)^2 + (x.1 1)^2 + (x.1 2)^2 = 1 := by
      have hn : ‖x.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.2
      have hs := EuclideanSpace.real_norm_sq_eq x.1
      simp [Fin.sum_univ_succ, hn] at hs
      linarith
    have hs := EuclideanSpace.real_norm_sq_eq
      (WithLp.toLp 2 ![-2 * x.1 2 * x.1 0, -2 * x.1 2 * x.1 1, 1 - 2 * (x.1 2)^2])
    simp [Fin.sum_univ_succ] at hs
    have hn := norm_nonneg (WithLp.toLp 2 ![-2 * x.1 2 * x.1 0,
      -2 * x.1 2 * x.1 1, 1 - 2 * (x.1 2)^2])
    simp only [neg_mul] at *
    nlinarith [congrArg (fun t : ℝ => 4 * (x.1 2)^2 * t) hx]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold_equator (x : apm_t97A03_S2) (hx : x.1 2 = 0) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold x = apm_t97A03_north := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold, apm_t97A03_north, hx]

/-- Pinch the upper hemisphere onto the tree edge, with the pole at N₀. -/
noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap : ContinuousMap apm_t97A03_S2 SC where
  toFun x := if 0 ≤ x.1 2 then
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge (Set.projIcc 0 1 (by norm_num) (1 - x.1 2))
    else Quotient.mk _ (.inl (1, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold x))
  continuous_toFun := by
    apply Continuous.if_le
      (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge.continuous.comp (continuous_projIcc.comp (by fun_prop)))
      (continuous_coinduced_rng.comp (continuous_inl.comp
        (continuous_const.prodMk apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold.continuous)))
      continuous_const (by fun_prop)
    intro x hx
    simp only [Function.comp_apply]
    rw [show 1 - x.1 2 = 1 by linarith]
    simp only [Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)]
    rw [show (⟨(1 : ℝ), by norm_num⟩ : unitInterval) = 1 from rfl,
      Path.target, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold_equator x hx.symm]

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_upperOne : Path N₁ N₀ :=
  ((apm_t97A03_circleArc apm_t97A03_circleOne apm_t97A03_circleNegOne).map
    (show Continuous (fun z : Circle => (Quotient.mk _ (.inr (1, z)) : SC)) from
      continuous_coinduced_rng.comp (continuous_inr.comp (continuous_const.prodMk continuous_id)))).cast
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c1a)).symm
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c1b)).symm

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_lowerCircle :
    Path apm_t97A03_circleNegOne apm_t97A03_circleOne :=
  ((apm_t97A03_circleArc apm_t97A03_circleOne apm_t97A03_circleNegOne).map
    (show Continuous (fun z : Circle => z⁻¹) from continuous_inv)).symm.cast
    (by apply Circle.ext; simp [apm_t97A03_circleNegOne])
    (by apply Circle.ext; simp [apm_t97A03_circleOne])

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_lowerOne : Path N₀ N₁ :=
  (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_lowerCircle.map
    (show Continuous (fun z : Circle => (Quotient.mk _ (.inr (1, z)) : SC)) from
      continuous_coinduced_rng.comp (continuous_inr.comp (continuous_const.prodMk continuous_id)))).cast
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c1b)).symm
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c1a)).symm

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle : ContinuousMap Circle unitInterval where
  toFun z := Set.projIcc 0 1 (by norm_num) (Real.arccos z.1.re / Real.pi)
  continuous_toFun := (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := by norm_num)).comp (by fun_prop)

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_real (z : Circle) (h : z.1.im = 0) :
    z = apm_t97A03_circleOne ∨ z = apm_t97A03_circleNegOne := by
  have hn := Circle.normSq_coe z
  rw [Complex.normSq_apply] at hn
  have hr : z.1.re = 1 ∨ z.1.re = -1 := by
    have : (z.1.re - 1) * (z.1.re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hr with hr | hr
  · left; apply Circle.ext; apply Complex.ext <;> simp [apm_t97A03_circleOne, hr, h]
  · right; apply Circle.ext; apply Complex.ext <;> simp [apm_t97A03_circleNegOne, hr, h]

/-- Circle one includes the necessary edge detour at its moved vertex. -/
noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne : ContinuousMap Circle SC where
  toFun z := if 0 ≤ z.1.im then
      (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge.trans apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_upperOne) (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle z)
    else (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_lowerOne.trans apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge.symm) (unitInterval.symm (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle z))
  continuous_toFun := by
    apply Continuous.if_le
      ((apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge.trans apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_upperOne).continuous.comp apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle.continuous)
      ((apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_lowerOne.trans apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge.symm).continuous.comp
        (unitInterval.continuous_symm.comp apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle.continuous))
      continuous_const (Complex.continuous_im.comp continuous_subtype_val)
    intro z hz
    simp only [Function.comp_apply]
    rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_real z hz.symm with rfl | rfl
    · have ha : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle apm_t97A03_circleOne = 0 := by
        apply Subtype.ext
        simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle, apm_t97A03_circleOne, Set.projIcc]
      rw [ha]; simp
    · have ha : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle apm_t97A03_circleNegOne = 1 := by
        apply Subtype.ext
        simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle, apm_t97A03_circleNegOne, Set.projIcc, Real.pi_ne_zero]
      rw [ha]; simp

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap_north : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap apm_t97A03_north = N₀ := by
  simpa [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap, apm_t97A03_north, Set.projIcc] using apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge.source

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne_endpoints :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne apm_t97A03_circleOne = N₀ ∧
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne apm_t97A03_circleNegOne = N₀ := by
  constructor <;>
    simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle,
      apm_t97A03_circleOne, apm_t97A03_circleNegOne, Set.projIcc, Real.pi_ne_zero]

noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw :
    ContinuousMap (Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)) SC where
  toFun := Sum.elim
    (fun w => if w.1 = 0 then Quotient.mk _ (.inl (0, w.2)) else apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap w.2)
    (fun w => if w.1 = 0 then Quotient.mk _ (.inr (0, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle w.2))
      else apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne w.2)
  continuous_toFun := by
    rw [continuous_sum_dom]
    constructor <;> rw [continuous_prod_of_discrete_left] <;> intro i <;> fin_cases i
    · change Continuous (fun x : apm_t97A03_S2 => (Quotient.mk _ (.inl (0, x)) : SC))
      apply Continuous.comp continuous_coinduced_rng
      exact continuous_inl.comp (continuous_const.prodMk continuous_id)
    · exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap.continuous
    · change Continuous (fun z : Circle => (Quotient.mk _ (.inr (0, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle z)) : SC))
      apply Continuous.comp continuous_coinduced_rng
      exact continuous_inr.comp (continuous_const.prodMk apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle.continuous)
    · exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne.continuous

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw_arc (z : Circle)
    (hz : z ∈ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw (.inr (0, z)) = N₀ := by
  change (if (0 : Fin 2) = 0 then Quotient.mk _ (.inr (0, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle z))
    else apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne z) = N₀
  rw [if_pos rfl, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle_arc z hz]
  exact Quotient.sound (Relation.EqvGen.rel _ _
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c0a)

lemma apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_respects (x y : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle))
    (h : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw x = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw y := by
  have h0 : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw (.inl (0, apm_t97A03_north)) = N₀ := rfl
  have h1 : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw (.inl (1, apm_t97A03_north)) = N₀ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap_north
  cases h with
  | c0a => rw [h0]; apply apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw_arc; simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc, apm_t97A03_circleOne]
  | c0b => rw [h1]; apply apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw_arc; simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc, apm_t97A03_circleNegOne]
  | c1a => exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne_endpoints.1.trans h1.symm
  | c1b => exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne_endpoints.2.trans h0.symm
  | arc z hz => exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw_arc z hz).trans h0.symm

/-- The explicit inverse candidate: fix sheet zero, pinch sheet one, and
insert the tree-edge detours into the two circles. -/
noncomputable def apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s :
    ContinuousMap apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space SC where
  toFun := Quotient.lift apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw (by
    intro x y h
    induction h with
    | rel x y h => exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_respects x y h
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂)
  continuous_toFun := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw.continuous.quotient_lift _


local notation "CC" => apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space
local notation "CQ" => apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q
local notation "CR" => apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_raw
local notation "CV" => (Quotient.mk _ (Sum.inl (0, apm_t97A03_north)) : CC)

/-- The spanning edge is constant after projection to the collapsed space. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_edge (t : unitInterval) : CQ (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge t) = CV := by
  change (Quotient.mk _ (.inr (0,
    apm_t97A03_circleArc apm_t97A03_circleOne apm_t97A03_circleNegOne t)) : CC) = CV
  apply Quotient.sound
  apply Relation.EqvGen.rel
  apply apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
  change 0 ≤ (apm_t97A03_circleArc apm_t97A03_circleOne apm_t97A03_circleNegOne t).1.im
  simp only [apm_t97A03_circleArc, Path.ofLine, apm_t97A03_circleOne,
    apm_t97A03_circleNegOne, Circle.coe_one, Complex.arg_one,
    Complex.arg_neg_one, mul_zero, zero_add]
  change 0 ≤ (Circle.exp ((t : ℝ) * Real.pi) : ℂ).im
  simpa [Circle.coe_exp, Complex.exp_im] using Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg t.2.1 Real.pi_pos.le)
    (by nlinarith [t.2.2, Real.pi_pos])

/-- Shrink the cap while its north pole moves along the spanning edge.
An explicit polar formula uses `θ = arccos x₂`, `a = (1-t)π/2`.
For `θ ≤ a`, use `edge (t + (1-t)(1-cos θ)/(1-cos a))`;
for `θ ≥ a`, use sphere sheet one at polar angle `π(θ-a)/(π-a)`,
retaining the longitude. At `t=1` use the identity. The formulas agree
at `θ=a` at the north pole of sheet one; the shrinking cap tends to that
pole at the terminal corner. At `t=0` the lower formula is exactly `fold`. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere :
    ∃ H : C(apm_t97A03_S2, C(unitInterval, SC)),
      (∀ x, H x 0 = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap x) ∧
      (∀ x, H x 1 = Quotient.mk _ (.inl (1, x))) ∧
      (∀ t, H apm_t97A03_north t = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge t) := by
  sorry

/-- Grow the upper arc and shorten the lower detour; the upper arc remains
inside the spanning edge throughout the motion. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_circleZero :
    ∃ H : C(Circle, C(unitInterval, SC)),
      (∀ z, H z 0 = CR (.inr (0, z))) ∧
      (∀ z, H z 1 = Quotient.mk _ (.inr (0, z))) ∧
      (∀ t, H apm_t97A03_circleOne t = N₀) ∧
      (∀ t, H apm_t97A03_circleNegOne t = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge t) ∧
      (∀ z, z ∈ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc →
        ∀ t, CQ (H z t) = CV) := by
  have hu (z : Circle) (hz : 0 ≤ z.1.im) :
      Circle.exp (Real.arccos z.1.re) = z := by
    have ha := Complex.arg_of_im_nonneg_of_ne_zero hz (Circle.coe_ne_zero z)
    simp only [Circle.norm_coe, div_one] at ha
    rw [← ha]
    exact Circle.exp_arg z
  let g (z : Circle) (t : unitInterval) : Circle :=
    z * Circle.exp (-(1 - (t : ℝ)) * Real.arccos z.1.re)
  have hg0 (z : Circle) : g z 0 = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle z := by
    dsimp [g, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle]
    split_ifs with hz
    · simp only [sub_zero, neg_mul, one_mul, Circle.exp_neg]
      rw [hu z hz, mul_inv_cancel]
    · have ha := Complex.arg_of_im_neg (lt_of_not_ge hz)
      simp only [Circle.norm_coe, div_one] at ha
      simp only [sub_zero, neg_mul, one_mul]
      rw [← ha, Circle.exp_arg]
  have hgA (z : Circle) (hz : 0 ≤ z.1.im) (t : unitInterval) :
      g z t = Circle.exp ((t : ℝ) * Real.arccos z.1.re) := by
    dsimp [g]
    conv_lhs => lhs; rw [← hu z hz]
    rw [← Circle.exp_add]
    congr 1
    ring
  let H : C(Circle, C(unitInterval, SC)) := ContinuousMap.curry
    ⟨fun p : Circle × unitInterval => Quotient.mk _ (.inr (0, g p.1 p.2)), by
      apply continuous_coinduced_rng.comp
      apply continuous_inr.comp
      apply continuous_const.prodMk
      dsimp [g]
      fun_prop⟩
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    change (Quotient.mk _ (.inr (0, g z 0)) : SC) =
      Quotient.mk _ (.inr (0, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circle z))
    rw [hg0]
  · intro z
    change (Quotient.mk _ (.inr (0, g z 1)) : SC) = Quotient.mk _ (.inr (0, z))
    simp [g]
  · intro t
    change (Quotient.mk _ (.inr (0, g apm_t97A03_circleOne t)) : SC) = N₀
    have hg : g apm_t97A03_circleOne t = apm_t97A03_circleOne := by
      simp [g, apm_t97A03_circleOne]
    rw [hg]
    exact Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel.c0a)
  · intro t
    change (Quotient.mk _ (.inr (0, g apm_t97A03_circleNegOne t)) : SC) =
      Quotient.mk _ (.inr (0, apm_t97A03_circleArc
        apm_t97A03_circleOne apm_t97A03_circleNegOne t))
    congr 3
    rw [hgA _ (by simp [apm_t97A03_circleNegOne])]
    simp [apm_t97A03_circleArc, Path.ofLine, apm_t97A03_circleOne,
      apm_t97A03_circleNegOne]
    rfl
  · intro z hz t
    change (Quotient.mk _ (.inr (0, g z t)) : CC) = CV
    apply Quotient.sound
    apply Relation.EqvGen.rel
    apply apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
    change 0 ≤ (g z t).1.im
    rw [hgA z hz t]
    simpa [Circle.coe_exp, Complex.exp_im] using Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg t.2.1 (Real.arccos_nonneg z.1.re))
      ((mul_le_of_le_one_left (Real.arccos_nonneg _) t.2.2).trans (Real.arccos_le_pi _))

/-- Shorten the edge detours with the moving circle-one endpoint.
On the upper arc with parameter `u=angle z`, use `edge(t+2u)` when
`2u+t ≤ 1`, otherwise `upperOne((2u+t-1)/(1+t))`.
On the lower arc with parameter `u=1-angle z`, use `lowerOne(2u/(1+t))`
when `2u ≤ 1+t`, otherwise `edge(2+t-2u)`. Clamp interval arguments
outside their active pieces. At the switching points the path endpoints
agree; the two semicircle formulas agree at both real circle points. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_circleOne :
    ∃ H : C(Circle, C(unitInterval, SC)),
      (∀ z, H z 0 = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne z) ∧
      (∀ z, H z 1 = Quotient.mk _ (.inr (1, z))) ∧
      (∀ t, H apm_t97A03_circleOne t = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge t) ∧
      (∀ t, H apm_t97A03_circleNegOne t = N₀) := by
  sorry

/-- Undo the pinch and edge detours in the original slid cover.  The moving
north pole follows `edge` from N₀ to N₁.  Extend that motion across the cap
by shrinking its radius, interpolate the polar angle on its complement,
and shorten the detours on circle one.  On circle zero the upper arc grows
from the constant path and the lower arc loses its initial edge traversal.
These motions agree at the four attaching points. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy :
    (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s.comp apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q).Homotopic (ContinuousMap.id SC) := by
  obtain ⟨HS, hS0, hS1, hSN⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere
  obtain ⟨H0, h00, h01, h0N, h0S, h0A⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_circleZero
  obtain ⟨H1, h10, h11, h1N, h1S⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_circleOne
  let H : C(Sum apm_t97A03_TwoSpheres (Fin 2 × Circle), C(unitInterval, SC)) :=
    ⟨Sum.elim
      (fun w => if w.1 = 0 then ContinuousMap.const _ (Quotient.mk _ (.inl (0, w.2)))
        else HS w.2)
      (fun w => if w.1 = 0 then H0 w.2 else H1 w.2), by
      rw [continuous_sum_dom]
      constructor <;> rw [continuous_prod_of_discrete_left] <;> intro i <;> fin_cases i
      · exact ContinuousMap.continuous_const'.comp
          (continuous_coinduced_rng.comp (continuous_inl.comp (continuous_const.prodMk continuous_id)))
      · exact HS.continuous
      · exact H0.continuous
      · exact H1.continuous⟩
  have hrel : ∀ x y,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidRel x y →
      H x = H y := by
    intro x y h
    ext t
    cases h with
    | c0a => exact h0N t
    | c0b => exact (h0S t).trans (hSN t).symm
    | c1a => exact (h1N t).trans (hSN t).symm
    | c1b => exact h1S t
  let F : C(SC, C(unitInterval, SC)) :=
    ⟨Quotient.lift H (by
      intro x y h
      induction h with
      | rel x y h => exact hrel x y h
      | refl x => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz),
      H.continuous.quotient_lift _⟩
  refine ⟨{ toFun := fun p => F p.2 p.1
            continuous_toFun := (F.continuous.comp continuous_snd).eval continuous_fst
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    refine Quotient.inductionOn x ?_
    rintro (⟨i, x⟩ | ⟨i, z⟩) <;> fin_cases i
    · rfl
    · exact hS0 x
    · exact h00 z
    · exact h10 z
  · intro x
    refine Quotient.inductionOn x ?_
    rintro (⟨i, x⟩ | ⟨i, z⟩) <;> fin_cases i
    · rfl
    · exact hS1 x
    · exact h01 z
    · exact h11 z


/-- Polar interpolation of the pinched sphere, fixing the north pole. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy_aux_sphere :
    ∃ H : C(apm_t97A03_S2, C(unitInterval, CC)),
      (∀ x, H x 0 = CQ (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap x)) ∧
      (∀ x, H x 1 = Quotient.mk _ (.inl (1, x))) ∧
      (∀ t, H apm_t97A03_north t = CV) := by
  obtain ⟨H, h0, h1, hN⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere
  refine ⟨⟨fun x => (CQ).comp (H x), (ContinuousMap.continuous_postcomp CQ).comp H.continuous⟩,
    ?_, ?_, ?_⟩
  · intro x; exact congrArg CQ (h0 x)
  · intro x; exact congrArg CQ (h1 x)
  · intro t; exact (congrArg CQ (hN t)).trans (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_edge t)

/-- Remove the extra traversal of the collapsed upper arc on circle zero. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy_aux_circleZero :
    ∃ H : C(Circle, C(unitInterval, CC)),
      (∀ z, H z 0 = CQ (CR (.inr (0, z)))) ∧
      (∀ z, H z 1 = Quotient.mk _ (.inr (0, z))) ∧
      (∀ z, z ∈ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc →
        ∀ t, H z t = CV) := by
  obtain ⟨H, h0, h1, hN, hS, hA⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_circleZero
  refine ⟨⟨fun x => (CQ).comp (H x), (ContinuousMap.continuous_postcomp CQ).comp H.continuous⟩,
    ?_, ?_, ?_⟩
  · intro x; exact congrArg CQ (h0 x)
  · intro x; exact congrArg CQ (h1 x)
  · exact hA

/-- Shorten the constant edge detours on circle one, relative to its endpoints. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy_aux_circleOne :
    ∃ H : C(Circle, C(unitInterval, CC)),
      (∀ z, H z 0 = CQ (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne z)) ∧
      (∀ z, H z 1 = Quotient.mk _ (.inr (1, z))) ∧
      (∀ t, H apm_t97A03_circleOne t = CV) ∧
      (∀ t, H apm_t97A03_circleNegOne t = CV) := by
  obtain ⟨H, h0, h1, hN, hS⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_circleOne
  refine ⟨⟨fun x => (CQ).comp (H x), (ContinuousMap.continuous_postcomp CQ).comp H.continuous⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x; exact congrArg CQ (h0 x)
  · intro x; exact congrArg CQ (h1 x)
  · intro t; exact (congrArg CQ (hN t)).trans (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_edge t)
  · intro t; exact congrArg CQ (hS t)

/-- After projection the entire edge is constant.  On sheet one the cap
pinch is a degree-one polar reparametrisation, homotopic relative to the
north pole to the identity by interpolation of the polar angle.  On the
three surviving arcs, remove the constant edge segments by interval
reparametrisation.  All four pieces fix the collapsed vertex, so the
homotopies descend through the collapse relation. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy :
    (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q.comp apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s).Homotopic
      (ContinuousMap.id apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space) := by
  obtain ⟨HS, hS0, hS1, hSN⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy_aux_sphere
  obtain ⟨H0, h00, h01, h0A⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy_aux_circleZero
  obtain ⟨H1, h10, h11, h1N, h1S⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy_aux_circleOne
  let H : C(Sum apm_t97A03_TwoSpheres (Fin 2 × Circle), C(unitInterval, CC)) :=
    ⟨Sum.elim
      (fun w => if w.1 = 0 then ContinuousMap.const _ (Quotient.mk _ (.inl (0, w.2)))
        else HS w.2)
      (fun w => if w.1 = 0 then H0 w.2 else H1 w.2), by
      rw [continuous_sum_dom]
      constructor <;> rw [continuous_prod_of_discrete_left] <;> intro i <;> fin_cases i
      · exact ContinuousMap.continuous_const'.comp
          (continuous_coinduced_rng.comp (continuous_inl.comp (continuous_const.prodMk continuous_id)))
      · exact HS.continuous
      · exact H0.continuous
      · exact H1.continuous⟩
  have hrel : ∀ x y,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel x y →
      H x = H y := by
    intro x y h
    ext t
    cases h with
    | c0a => exact h0A _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc, apm_t97A03_circleOne]) t
    | c0b => exact (h0A _ (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc, apm_t97A03_circleNegOne]) t).trans (hSN t).symm
    | c1a => exact (h1N t).trans (hSN t).symm
    | c1b => exact h1S t
    | arc z hz => exact h0A z hz t
  let F : C(CC, C(unitInterval, CC)) :=
    ⟨Quotient.lift H (by
      intro x y h
      induction h with
      | rel x y h => exact hrel x y h
      | refl x => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz),
      H.continuous.quotient_lift _⟩
  refine ⟨{ toFun := fun p => F p.2 p.1
            continuous_toFun := (F.continuous.comp continuous_snd).eval continuous_fst
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    refine Quotient.inductionOn x ?_
    rintro (⟨i, x⟩ | ⟨i, z⟩) <;> fin_cases i
    · rfl
    · exact hS0 x
    · exact h00 z
    · exact h10 z
  · intro x
    refine Quotient.inductionOn x ?_
    rintro (⟨i, x⟩ | ⟨i, z⟩) <;> fin_cases i
    · rfl
    · exact hS1 x
    · exact h01 z
    · exact h11 z

end

/-- Collapsing the closed tree edge preserves homotopy type.  Construct the
inverse by pinching a polar cap of one sphere sheet onto the connecting arc;
a circle-only reparametrisation cannot separate the two north points that
have become one.  The cap contraction and edge reparametrisations give the
inverse homotopies by quotient descent. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract :
    Nonempty (ContinuousMap.HomotopyEquiv
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space) := by
  exact ⟨{ toFun := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q
           invFun := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s
           left_inv := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy
           right_inv := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_right_homotopy }⟩

/-- After contraction both north points coincide.  The lower semicircle of
circle zero and the two semicircles of circle one are three loops at that
point.  Parametrising each closed semicircle modulo its endpoints gives the
three circle summands, while the two sphere sheets give the sphere wedge. -/
private noncomputable def
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw
    (x : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)) : apm_t97A03_modelWedge :=
  match x with
  | .inl w =>
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere w
  | .inr (i, z) =>
      if i = 0 then
        if 0 ≤ z.1.im then apm_t97A03_modelWedgeBase
        else
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg
            0 (z ^ 2)
      else if 0 ≤ z.1.im then
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg
          1 (z ^ 2)
      else
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg
          2 (z ^ 2)

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous :
    Continuous
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw := by
  sorry

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects
    {x y : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)}
    (h : Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw x =
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw y := by
  sorry

private noncomputable def
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space →
      apm_t97A03_modelWedge :=
  Quotient.lift
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw
    (fun _ _ h =>
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects h)

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_continuous :
    Continuous
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map := by
  apply Continuous.quotient_lift
  exact
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_surjective :
    Function.Surjective
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map := by
  sorry

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel
    {x y : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)}
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw x =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw y) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel x y := by
  sorry

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_injective :
    Function.Injective
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map := by
  rintro ⟨x⟩ ⟨y⟩ h
  exact Quotient.sound
    (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel h)

theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv :
    ∃ e : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space ≃
        apm_t97A03_modelWedge,
      Continuous e := by
  let f :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map
  let e : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space ≃
      apm_t97A03_modelWedge :=
    Equiv.ofBijective f ⟨
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_injective,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_surjective⟩
  exact ⟨e,
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_continuous⟩

theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_compact :
    CompactSpace
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space := by
  constructor
  let q : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) →
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space :=
    fun x ↦ Quotient.mk _ x
  have hc : Continuous q := continuous_coinduced_rng
  have hsurj : Function.Surjective q := by
    intro y
    refine Quotient.inductionOn y ?_
    intro x
    exact ⟨x, rfl⟩
  have hq := (isCompact_univ : IsCompact
    (Set.univ : Set (Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)))).image hc
  rw [Set.image_univ, Set.range_eq_univ.mpr hsurj] at hq
  exact hq

theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2 :
    T2Space apm_t97A03_modelWedge :=
  apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2

theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm :
    Nonempty (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space ≃ₜ apm_t97A03_modelWedge) := by
  letI : CompactSpace
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_space :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_compact
  letI : T2Space apm_t97A03_modelWedge :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_t2
  obtain ⟨e, he⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) he⟩

/-- The slid two-circle graph has four edges between two sphere vertices;
collapsing one spanning edge leaves the three-circle wedge. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse :
    Nonempty (ContinuousMap.HomotopyEquiv
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_SlidCover
      apm_t97A03_modelWedge) := by
  obtain ⟨contract⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract
  obtain ⟨normalForm⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm
  exact ⟨contract.trans normalForm.toHomotopyEquiv⟩

/-- Collapse one spanning arc in the two-circle quotient.  The remaining
three independent arcs and two sphere sheets identify the result with the
same `modelWedge`; use quotient homotopy descent and the explicit attachment
equalities of `apm_t97A03_TwoCircleRel`. -/
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97A03_TwoCircleCover apm_t97A03_modelWedge) := by
  obtain ⟨slide⟩ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_slide
  obtain ⟨collapse⟩ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse
  exact ⟨slide.trans collapse⟩

/-- Degree zero of the connected nested point wedge is `ℤ`.  Apply the H₀
point-wedge Mayer--Vietoris comparison, or `CoefficientH0.h0Iso` after proving
path connectedness from the sphere and three-circle summands. -/
theorem apm_t97A03_invariants_aux_modelWedge_h0 :
    Nonempty (apm_t97A03_Homology apm_t97A03_modelWedge 0 ≅
      ModuleCat.of ℤ ℤ) := by
  letI : PathConnectedSpace apm_t97A03_S2 :=
    ConstructionTargets.SphereHomology.spherePathConnectedSpace 2
  letI : PathConnectedSpace apm_t97A03_ThreeCircles :=
    ConstructionTargets.PointWedgeVanKampen.threeCircles_pathConnected
  exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℤ apm_t97A03_modelWedgeBase⟩

/-- Seat: degree one of a point wedge of path-connected spaces. Follow the proof of
`PolygonSurfaceHomology.pointWedgeHigherHomologyIsZero`, using its cover package. Mayer–Vietoris
(`IntegralMV.integralMayerVietoris`): `H₁(U ∩ V) = 0` because the overlap is contractible, and `H₀(U ∩ V) → H₀ U ⊕ H₀ V` is
injective because `H₀` of the contractible overlap is `ℤ` and maps isomorphically to `H₀ U` for path-connected `U`
(`CoefficientH0`). So `H₁ U ⊕ H₁ V ≅ H₁` of the wedge, and `U`, `V` are homotopy equivalent to `X`, `Y`. -/
noncomputable def apm_t97A03_pointWedge_h1_aux_h0GroupIso
    {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] (z : Z) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 0 (TopCat.of Z) ≅
      AddCommGrpCat.of ℤ :=
  (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Z) 0).symm ≪≫
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (ConstructionTargets.CoefficientH0.h0Iso ℤ z)

theorem apm_t97A03_pointWedge_h1 {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (x₀ : X) (y₀ : Y)
    (PX : ConstructionTargets.PolygonSurfaceHomology.PointedContractibleNeighborhood X x₀)
    (PY : ConstructionTargets.PolygonSurfaceHomology.PointedContractibleNeighborhood Y y₀) :
    Nonempty (apm_t97A03_Homology (ConstructionTargets.PointWedgeQuotient.Wedge x₀ y₀) 1 ≅
      (apm_t97A03_Homology X 1 ⊞ apm_t97A03_Homology Y 1)) := by
  let p := ConstructionTargets.GenericPointWedgeOpenCoverComparison.genericPointWedgeCoverPackage
    x₀ y₀ PY.carrier PX.carrier PY.isOpen PX.isOpen PY.mem PX.mem
      PY.contraction PX.contraction
  let U := ConstructionTargets.PointWedgeQuotient.leftOpen x₀ y₀ PY.carrier
  let V := ConstructionTargets.PointWedgeQuotient.rightOpen x₀ y₀ PX.carrier
  letI : Nonempty U := ⟨p.leftEquiv.symm x₀⟩
  letI : Nonempty V := ⟨p.rightEquiv.symm y₀⟩
  letI : Nonempty (U ∩ V : Set _) := ⟨p.intersectionEquiv.symm ()⟩
  let eI :=
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      p.intersectionEquiv 0 ≪≫
      ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt
  let eU :=
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      p.leftEquiv 0 ≪≫ apm_t97A03_pointWedge_h1_aux_h0GroupIso x₀
  let eV :=
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      p.rightEquiv 0 ≪≫ apm_t97A03_pointWedge_h1_aux_h0GroupIso y₀
  have hI : Limits.IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of (U ∩ V : Set _))) :=
    (ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
      Unit 1 (by omega)).of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        p.intersectionEquiv 1)
  letI : Mono
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow U V 0) :=
    ConstructionTargets.T00A01MayerVietorisAdapters.productionIntersectionArrow_mono_zero_of_coordinates
      U V eI eU
  have hconn :
      ConstructionTargets.ProductionOpenCoverMayerVietoris.productionConnecting
        U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ 0 = 0 :=
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_intersection
      U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ 0).mono_g_iff.mp
        (by infer_instance)
  letI : Mono
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V 1) :=
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_pieces
      U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ 1).mono_g_iff.mpr
        (hI.eq_of_src _ _)
  letI : Epi
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V 1) :=
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union
      U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ 0).epi_f_iff.mpr hconn
  letI : IsIso
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V 1) :=
    isIso_of_mono_of_epi _
  exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of (ConstructionTargets.PointWedgeQuotient.Wedge x₀ y₀)) 1 _
    ((asIso
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V 1)).symm ≪≫
      CategoryTheory.Limits.biprod.mapIso
        (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          p.leftEquiv 1)
        (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          p.rightEquiv 1) ≪≫
      CategoryTheory.Limits.biprod.mapIso
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of X) 1).symm
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of Y) 1).symm ≪≫
      AddCommGrpCat.biprodIsoProd _ _ ≪≫
      (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
        (ModuleCat.biprodIsoProd (apm_t97A03_Homology X 1)
          (apm_t97A03_Homology Y 1))).symm)⟩

/-- Degree one is supplied entirely by the three-circle summand. Apply `apm_t97A03_pointWedge_h1` to `modelWedge` and to
`twoSphereWedge` (`H₁(S²) = 0`), and for `ThreeCircles` iterate it over circles or use the finite-wedge `H₁` results,
to obtain the fixed `Fin 3` basis. -/
noncomputable def apm_t97A03_invariants_aux_modelWedge_h1_aux_sphereNeighborhood :
    ConstructionTargets.PolygonSurfaceHomology.PointedContractibleNeighborhood
      apm_t97A03_S2 apm_t97A03_north := by
  let south : apm_t97A03_S2 := -apm_t97A03_north
  have hsouth : ‖(south : apm_t97A03_R3)‖ = 1 := norm_eq_of_mem_sphere south
  let e0 := stereographic hsouth
  let e : e0.source ≃ₜ Submodule.orthogonal (ℝ ∙ (south : apm_t97A03_R3)) :=
    e0.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (by simp [e0, stereographic_target])).trans (Homeomorph.Set.univ _))
  have hnorth : apm_t97A03_north ∈ e0.source := by
    rw [stereographic_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h2 := congrArg (fun x : apm_t97A03_R3 ↦ x (2 : Fin 3)) (congrArg Subtype.val h)
    norm_num [south, apm_t97A03_north, EuclideanSpace.single_apply] at h2
  have he_base : e ⟨apm_t97A03_north, hnorth⟩ = 0 := by
    change e0 apm_t97A03_north = 0
    simpa [south, e0] using stereographic_apply_neg south
  let h : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      (Submodule.orthogonal (ℝ ∙ (south : apm_t97A03_R3))) 0 :=
    { homotopy :=
        { toFun := fun p ↦ (1 - (p.1 : ℝ)) • p.2
          continuous_toFun := (continuous_const.sub
            (continuous_subtype_val.comp continuous_fst)).smul continuous_snd
          map_zero_left := by intro x; simp
          map_one_left := by intro x; simp }
      fixed := by
        intro t
        change (1 - (t : ℝ)) • (0 : Submodule.orthogonal
          (ℝ ∙ (south : apm_t97A03_R3))) = 0
        simp }
  rw [← he_base] at h
  exact
    { carrier := e0.source
      isOpen := e0.open_source
      mem := hnorth
      contraction :=
        ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm e h }

noncomputable def apm_t97A03_invariants_aux_modelWedge_h1_aux_finThreeLinearEquiv :
    ((Fin 2 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) where
  toFun p := Fin.lastCases p.2 p.1
  invFun g := (fun i ↦ g i.castSucc, g (Fin.last 2))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp
    · simp only [Fin.lastCases_last]
  right_inv g := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc]
  map_add' p q := by
    funext i
    fin_cases i <;> rfl
  map_smul' z p := by
    funext i
    fin_cases i <;> rfl

theorem apm_t97A03_invariants_aux_modelWedge_h1 :
    Nonempty (apm_t97A03_Homology apm_t97A03_modelWedge 1 ≅
      ModuleCat.of ℤ (Fin 3 → ℤ)) := by
  open ConstructionTargets.PolygonSurfaceHomology in
    letI : PathConnectedSpace apm_t97A03_S2 :=
      ConstructionTargets.SphereHomology.spherePathConnectedSpace 2
    letI : PathConnectedSpace apm_t97A03_ThreeCircles := by infer_instance
    let PS := apm_t97A03_invariants_aux_modelWedge_h1_aux_sphereNeighborhood
    let PC := circlePointedContractibleNeighborhood
    let PtwoSphere := pointWedgePointedContractibleNeighborhood PS PS
    let PtwoCircle := pointWedgePointedContractibleNeighborhood PC PC
    let PthreeCircle := pointWedgePointedContractibleNeighborhood PtwoCircle PC
    obtain ⟨eTwoSphere⟩ := apm_t97A03_pointWedge_h1
      apm_t97A03_north apm_t97A03_north PS PS
    obtain ⟨eTwoCircle⟩ := apm_t97A03_pointWedge_h1 (1 : Circle) (1 : Circle) PC PC
    obtain ⟨eThreeCircle⟩ := apm_t97A03_pointWedge_h1
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint (1 : Circle) PtwoCircle PC
    have hOuter : Nonempty
        (apm_t97A03_Homology apm_t97A03_modelWedge 1 ≅
          (apm_t97A03_Homology apm_t97A03_twoSphereWedge 1 ⊞
            apm_t97A03_Homology apm_t97A03_ThreeCircles 1)) :=
      apm_t97A03_pointWedge_h1 apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
        PtwoSphere PthreeCircle
    obtain ⟨eOuter⟩ := hOuter
    have hSphere : Limits.IsZero (apm_t97A03_Homology apm_t97A03_S2 1) :=
      ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
        2 1 (by omega) (by omega)
    have hTwoSphere : Limits.IsZero
        (apm_t97A03_Homology apm_t97A03_twoSphereWedge 1) :=
      ((Limits.biprod_isZero_iff _ _).2 ⟨hSphere, hSphere⟩).of_iso eTwoSphere
    let eCircle := ConstructionTargets.CircleHomology.circleH1IsoInt
    let eTwoCoordinates := (eTwoCircle ≪≫
      CategoryTheory.Limits.biprod.mapIso eCircle eCircle ≪≫
      ModuleCat.biprodIsoProd _ _ ≪≫
      (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 ↦ ℤ)).symm.toModuleIso)
    let eThreeCoordinates := (eThreeCircle ≪≫
      CategoryTheory.Limits.biprod.mapIso eTwoCoordinates eCircle ≪≫
      ModuleCat.biprodIsoProd _ _ ≪≫
      apm_t97A03_invariants_aux_modelWedge_h1_aux_finThreeLinearEquiv.toModuleIso)
    letI : IsIso (CategoryTheory.Limits.biprod.inl :
        apm_t97A03_Homology apm_t97A03_ThreeCircles 1 ⟶
          (apm_t97A03_Homology apm_t97A03_ThreeCircles 1 ⊞
            apm_t97A03_Homology apm_t97A03_twoSphereWedge 1)) :=
      (CategoryTheory.Biprod.isIso_inl_iff_isZero _ _).2 hTwoSphere
    exact ⟨eOuter ≪≫
      CategoryTheory.Limits.biprod.braiding _ _ ≪≫
      (asIso (CategoryTheory.Limits.biprod.inl :
        apm_t97A03_Homology apm_t97A03_ThreeCircles 1 ⟶
          (apm_t97A03_Homology apm_t97A03_ThreeCircles 1 ⊞
            apm_t97A03_Homology apm_t97A03_twoSphereWedge 1))).symm ≪≫
      eThreeCoordinates⟩

/-- Degree two is the biproduct of the top homology of the two sphere
summands.  Use `SphereHomology.sphereModuleTopHomologyIsoInt` twice and
`IntegralOpenCoverMayerVietoris` for the two successive point wedges. -/
noncomputable def apm_t97A03_invariants_aux_modelWedge_h2_aux_wedgeIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (PX : ConstructionTargets.PolygonSurfaceHomology.PointedContractibleNeighborhood X x₀)
    (PY : ConstructionTargets.PolygonSurfaceHomology.PointedContractibleNeighborhood Y y₀)
    (n : ℕ) (hn : 2 ≤ n) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology n
        (TopCat.of (Wedge x₀ y₀)) ≅
      Limits.biprod
        (ConstructionTargets.SingularHomologyConcrete.SingularHomology n (TopCat.of X))
        (ConstructionTargets.SingularHomologyConcrete.SingularHomology n (TopCat.of Y)) := by
  let p := ConstructionTargets.GenericPointWedgeOpenCoverComparison.genericPointWedgeCoverPackage
    x₀ y₀ PY.carrier PX.carrier PY.isOpen PX.isOpen PY.mem PX.mem
      PY.contraction PX.contraction
  let U := ConstructionTargets.PointWedgeQuotient.leftOpen x₀ y₀ PY.carrier
  let V := ConstructionTargets.PointWedgeQuotient.rightOpen x₀ y₀ PX.carrier
  let GH (k : ℕ) (Z : Type) [TopologicalSpace Z] :=
    ConstructionTargets.SingularHomologyConcrete.SingularHomology k (TopCat.of Z)
  have hI (k : ℕ) (hk : k ≠ 0) : Limits.IsZero (GH k (U ∩ V : Set _)) :=
    (ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
      Unit k hk).of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        p.intersectionEquiv k)
  have hIso : IsIso
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V n) := by
    have hm : Mono
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V n) :=
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_pieces
        U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ n).mono_g_iff.mpr
          ((hI n (by omega)).eq_of_src _ _)
    have heq : n - 1 + 1 = n := by omega
    have he : Epi
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V n) := by
      rw [← heq]
      exact
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union
          U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ (n - 1)).epi_f_iff.mpr
            ((hI (n - 1) (by omega)).eq_of_tgt _ _)
    letI := hm
    letI := he
    exact isIso_of_mono_of_epi _
  letI := hIso
  let eX : GH n U ≅ GH n X :=
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      p.leftEquiv n
  let eY : GH n V ≅ GH n Y :=
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      p.rightEquiv n
  exact (asIso (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
      U V n)).symm ≪≫ CategoryTheory.Limits.biprod.mapIso eX eY

noncomputable def apm_t97A03_invariants_aux_modelWedge_h2_aux_sphereNeighborhood :
    ConstructionTargets.PolygonSurfaceHomology.PointedContractibleNeighborhood
      apm_t97A03_S2 apm_t97A03_north := by
  let south : apm_t97A03_S2 := -apm_t97A03_north
  have hsouth : ‖(south : apm_t97A03_R3)‖ = 1 := norm_eq_of_mem_sphere south
  let e0 := stereographic hsouth
  let e : e0.source ≃ₜ Submodule.orthogonal (ℝ ∙ (south : apm_t97A03_R3)) :=
    e0.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (by simp [e0, stereographic_target])).trans (Homeomorph.Set.univ _))
  have hnorth : apm_t97A03_north ∈ e0.source := by
    rw [stereographic_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h2 := congrArg (fun x : apm_t97A03_R3 ↦ x (2 : Fin 3)) (congrArg Subtype.val h)
    norm_num [south, apm_t97A03_north, EuclideanSpace.single_apply] at h2
  have he_base : e ⟨apm_t97A03_north, hnorth⟩ = 0 := by
    change e0 apm_t97A03_north = 0
    simpa [south, e0] using stereographic_apply_neg south
  let h : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      (Submodule.orthogonal (ℝ ∙ (south : apm_t97A03_R3))) 0 :=
    { homotopy :=
        { toFun := fun p ↦ (1 - (p.1 : ℝ)) • p.2
          continuous_toFun := (continuous_const.sub
            (continuous_subtype_val.comp continuous_fst)).smul continuous_snd
          map_zero_left := by intro x; simp
          map_one_left := by intro x; simp }
      fixed := by
        intro t
        change (1 - (t : ℝ)) • (0 : Submodule.orthogonal
          (ℝ ∙ (south : apm_t97A03_R3))) = 0
        simp }
  rw [← he_base] at h
  exact
    { carrier := e0.source
      isOpen := e0.open_source
      mem := hnorth
      contraction :=
        ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm e h }

theorem apm_t97A03_invariants_aux_modelWedge_h2 :
    Nonempty (apm_t97A03_Homology apm_t97A03_modelWedge 2 ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  open ConstructionTargets.PolygonSurfaceHomology in
    let PS := apm_t97A03_invariants_aux_modelWedge_h2_aux_sphereNeighborhood
    let PC := circlePointedContractibleNeighborhood
    let PtwoSphere := pointWedgePointedContractibleNeighborhood PS PS
    let PtwoCircle := pointWedgePointedContractibleNeighborhood PC PC
    let PthreeCircle := pointWedgePointedContractibleNeighborhood PtwoCircle PC
    let eSphere := ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 2 (by omega)
    let eTwo := apm_t97A03_invariants_aux_modelWedge_h2_aux_wedgeIso
      apm_t97A03_north apm_t97A03_north PS PS 2 (by omega)
    let eOuter := apm_t97A03_invariants_aux_modelWedge_h2_aux_wedgeIso
      apm_t97A03_twoSphereBase
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
      PtwoSphere PthreeCircle 2 (by omega)
    have hcircle : Limits.IsZero (apm_t97A03_Homology Circle 2) :=
      ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
        (TopCat.of Circle) 2
        (ConstructionTargets.BoundaryTorusMayerVietoris.circleHomology_isZero_of_one_lt
          2 (by omega))
    have htwoCircle : Limits.IsZero
        (apm_t97A03_Homology (Wedge (1 : Circle) (1 : Circle)) 2) :=
      pointWedgeHigherHomologyIsZero (1 : Circle) (1 : Circle)
        PC PC 2 (by omega) hcircle hcircle
    have hthree : Limits.IsZero (apm_t97A03_Homology apm_t97A03_ThreeCircles 2) :=
      pointWedgeHigherHomologyIsZero
        ConstructionTargets.StatementSurfaceModels.twoCirclesPoint (1 : Circle)
        PtwoCircle PC 2 (by omega) htwoCircle hcircle
    have underlyingIsZero {A : ModuleCat ℤ} (hA : Limits.IsZero A) :
        Limits.IsZero
          (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.obj A) := by
      rw [Limits.IsZero.iff_id_eq_zero]
      rw [← ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_id,
        ← ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_zero]
      exact congrArg
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (hA.eq_of_src _ _)
    have hthreeRaw : Limits.IsZero
        (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
          (TopCat.of apm_t97A03_ThreeCircles)) :=
      (underlyingIsZero hthree).of_iso
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of apm_t97A03_ThreeCircles) 2).symm
    letI : IsIso (CategoryTheory.Limits.biprod.inl :
        ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
            (TopCat.of apm_t97A03_twoSphereWedge) ⟶
          Limits.biprod
            (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
              (TopCat.of apm_t97A03_twoSphereWedge))
            (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
              (TopCat.of apm_t97A03_ThreeCircles))) :=
      (CategoryTheory.Biprod.isIso_inl_iff_isZero _ _).2 hthreeRaw
    exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of apm_t97A03_modelWedge) 2 _
      (eOuter ≪≫ (asIso (CategoryTheory.Limits.biprod.inl :
          ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
              (TopCat.of apm_t97A03_twoSphereWedge) ⟶
            Limits.biprod
              (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
                (TopCat.of apm_t97A03_twoSphereWedge))
              (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
                (TopCat.of apm_t97A03_ThreeCircles)))).symm ≪≫
        eTwo ≪≫ CategoryTheory.Limits.biprod.mapIso eSphere eSphere ≪≫
        AddCommGrpCat.biprodIsoProd _ _ ≪≫
        (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 ↦ ℤ)).symm.toAddEquiv.toAddCommGrpIso)⟩

/-- Above degree two, both spheres and all three circles vanish.  Apply
`PolygonSurfaceHomology.pointWedgeHigherHomologyIsZero` successively with
`SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top` and the finite
circle-wedge vanishing theorem. -/
def apm_t97A03_invariants_aux_modelWedge_high_sphereNeighborhood :
    ConstructionTargets.PolygonSurfaceHomology.PointedContractibleNeighborhood
      apm_t97A03_S2 apm_t97A03_north := by
  let south : apm_t97A03_S2 := -apm_t97A03_north
  have hsouth : ‖(south : apm_t97A03_R3)‖ = 1 :=
    norm_eq_of_mem_sphere south
  let e0 := stereographic hsouth
  let e : e0.source ≃ₜ Submodule.orthogonal (ℝ ∙ (south : apm_t97A03_R3)) :=
    e0.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (by simp [e0, stereographic_target])).trans
        (Homeomorph.Set.univ _))
  have hnorth : apm_t97A03_north ∈ e0.source := by
    rw [stereographic_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hv := congrArg Subtype.val h
    have h2 := congrArg (fun x : apm_t97A03_R3 => x (2 : Fin 3)) hv
    norm_num [south, apm_t97A03_north, EuclideanSpace.single_apply] at h2
  have he_base : e ⟨apm_t97A03_north, hnorth⟩ = 0 := by
    change e0 apm_t97A03_north = 0
    simpa [south, e0] using stereographic_apply_neg south
  let h :
      ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
        (Submodule.orthogonal (ℝ ∙ (south : apm_t97A03_R3))) 0 :=
    { homotopy :=
        { toFun := fun p => (1 - (p.1 : ℝ)) • p.2
          continuous_toFun := (continuous_const.sub
            (continuous_subtype_val.comp continuous_fst)).smul continuous_snd
          map_zero_left := by intro x; simp
          map_one_left := by intro x; simp }
      fixed := by
        intro t
        change (1 - (t : ℝ)) • (0 : Submodule.orthogonal
          (ℝ ∙ (south : apm_t97A03_R3))) = 0
        simp }
  rw [← he_base] at h
  exact
    { carrier := e0.source
      isOpen := e0.open_source
      mem := hnorth
      contraction :=
        ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm e h }

theorem apm_t97A03_invariants_aux_modelWedge_high (n : ℕ) (hn : 3 ≤ n) :
    Limits.IsZero (apm_t97A03_Homology apm_t97A03_modelWedge n) := by
  open ConstructionTargets.PolygonSurfaceHomology in
    have hsphere : Limits.IsZero (apm_t97A03_Homology apm_t97A03_S2 n) :=
      ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
        2 n (by omega) (by omega)
    have hcircle : Limits.IsZero (apm_t97A03_Homology Circle n) :=
      ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
        (TopCat.of Circle) n
        (ConstructionTargets.BoundaryTorusMayerVietoris.circleHomology_isZero_of_one_lt
          n (by omega))
    let PS := apm_t97A03_invariants_aux_modelWedge_high_sphereNeighborhood
    let PC := circlePointedContractibleNeighborhood
    have htwoSphere :
        Limits.IsZero (apm_t97A03_Homology apm_t97A03_twoSphereWedge n) :=
      pointWedgeHigherHomologyIsZero apm_t97A03_north apm_t97A03_north
        PS PS n (by omega) hsphere hsphere
    let PtwoSphere := pointWedgePointedContractibleNeighborhood PS PS
    have htwoCircle : Limits.IsZero
        (apm_t97A03_Homology
          (Wedge (1 : Circle) (1 : Circle)) n) :=
      pointWedgeHigherHomologyIsZero (1 : Circle) (1 : Circle)
        PC PC n (by omega) hcircle hcircle
    let PtwoCircle := pointWedgePointedContractibleNeighborhood PC PC
    have hthreeCircle :
        Limits.IsZero (apm_t97A03_Homology apm_t97A03_ThreeCircles n) :=
      pointWedgeHigherHomologyIsZero
        ConstructionTargets.StatementSurfaceModels.twoCirclesPoint (1 : Circle)
        PtwoCircle PC n (by omega) htwoCircle hcircle
    let PthreeCircle := pointWedgePointedContractibleNeighborhood PtwoCircle PC
    exact pointWedgeHigherHomologyIsZero apm_t97A03_twoSphereBase
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
      PtwoSphere PthreeCircle n (by omega) htwoSphere hthreeCircle

/-- Van Kampen turns the nested point wedge into the free product of two
trivial sphere groups and the rank-three circle-wedge group.  Use
`PointWedgeVanKampen.genericPointWedgeLegCoordinatesEquiv`,
`threeCirclesFundamentalGroupEquiv`, and basepoint change along path
connectedness. -/
/- The fundamental group of a simply connected sphere leg, in rank-zero
free-group coordinates. -/
noncomputable def apm_t97A03_invariants_aux_modelWedge_piOne_aux_spherePiOne :
    FundamentalGroup apm_t97A03_S2 apm_t97A03_north ≃* FreeGroup (Fin 0) := by
  haveI : SimplyConnectedSpace apm_t97A03_S2 :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
      2 (by norm_num)
  haveI : Subsingleton (FundamentalGroup apm_t97A03_S2 apm_t97A03_north) :=
    inferInstanceAs
      (Subsingleton (Path.Homotopic.Quotient apm_t97A03_north apm_t97A03_north))
  exact
    { toFun := fun _ => 1
      invFun := fun _ => 1
      map_mul' := fun _ _ => by simp
      left_inv := fun a => (Subsingleton.elim a 1).symm
      right_inv := fun a => by
        have : a = 1 := Subsingleton.elim a 1
        subst this
        rfl }

/- Van Kampen reduces the two-sphere wedge to the free product of two trivial
groups, i.e. the rank-zero free group. -/
noncomputable def apm_t97A03_invariants_aux_modelWedge_piOne_aux_twoSphereWedgePiOne :
    FundamentalGroup apm_t97A03_twoSphereWedge apm_t97A03_twoSphereBase ≃*
      FreeGroup (Fin 0) := by
  letI : PathConnectedSpace apm_t97A03_S2 :=
    ConstructionTargets.SphereHomology.spherePathConnectedSpace 2
  let PS := apm_t97A03_invariants_aux_modelWedge_high_sphereNeighborhood
  have leg : FundamentalGroup apm_t97A03_twoSphereWedge apm_t97A03_twoSphereBase ≃*
      Monoid.Coprod (FundamentalGroup apm_t97A03_S2 apm_t97A03_north)
        (FundamentalGroup apm_t97A03_S2 apm_t97A03_north) :=
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLegCoordinatesEquiv
      apm_t97A03_north apm_t97A03_north
      PS.carrier PS.carrier PS.isOpen PS.isOpen PS.mem PS.mem
      PS.contraction PS.contraction
  let e : Fin 0 ⊕ Fin 0 ≃ Fin 0 := finSumFinEquiv (m := 0) (n := 0)
  exact leg.trans
    ((MulEquiv.coprodCongr
        apm_t97A03_invariants_aux_modelWedge_piOne_aux_spherePiOne
        apm_t97A03_invariants_aux_modelWedge_piOne_aux_spherePiOne).trans
      ((ConstructionTargets.PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum
          (Fin 0) (Fin 0)).trans
        (MulEquiv.ofBijective (FreeGroup.map e)
          ⟨FreeGroup.map_injective e.injective,
            FreeGroup.map_surjective e.surjective⟩)))

/- Van Kampen at the outer wedge: the free product of the rank-zero two-sphere
wedge group and the rank-three three-circle group is the rank-three free
group, computed once at the model wedge basepoint. -/
noncomputable def apm_t97A03_invariants_aux_modelWedge_piOne_aux_modelWedgeBase :
    FundamentalGroup apm_t97A03_modelWedge apm_t97A03_modelWedgeBase ≃*
      FreeGroup (Fin 3) := by
  letI : PathConnectedSpace apm_t97A03_S2 :=
    ConstructionTargets.SphereHomology.spherePathConnectedSpace 2
  haveI : PathConnectedSpace apm_t97A03_twoSphereWedge :=
    ConstructionTargets.PointWedgePathConnected.wedgePathConnectedSpace
      apm_t97A03_north apm_t97A03_north
  haveI : PathConnectedSpace apm_t97A03_ThreeCircles :=
    ConstructionTargets.PointWedgeVanKampen.threeCircles_pathConnected
  let PS := apm_t97A03_invariants_aux_modelWedge_high_sphereNeighborhood
  let PC := ConstructionTargets.PolygonSurfaceHomology.circlePointedContractibleNeighborhood
  let PtwoSphere :=
    ConstructionTargets.PolygonSurfaceHomology.pointWedgePointedContractibleNeighborhood
      PS PS
  let PtwoCircle :=
    ConstructionTargets.PolygonSurfaceHomology.pointWedgePointedContractibleNeighborhood
      PC PC
  let PthreeCircle :=
    ConstructionTargets.PolygonSurfaceHomology.pointWedgePointedContractibleNeighborhood
      PtwoCircle PC
  have leg : FundamentalGroup apm_t97A03_modelWedge apm_t97A03_modelWedgeBase ≃*
      Monoid.Coprod (FundamentalGroup apm_t97A03_twoSphereWedge apm_t97A03_twoSphereBase)
        (FundamentalGroup apm_t97A03_ThreeCircles
          ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase) :=
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLegCoordinatesEquiv
      apm_t97A03_twoSphereBase
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
      PthreeCircle.carrier PtwoSphere.carrier
      PthreeCircle.isOpen PtwoSphere.isOpen PthreeCircle.mem PtwoSphere.mem
      PthreeCircle.contraction PtwoSphere.contraction
  let e : Fin 0 ⊕ Fin 3 ≃ Fin 3 := finSumFinEquiv (m := 0) (n := 3)
  exact leg.trans
    ((MulEquiv.coprodCongr
        apm_t97A03_invariants_aux_modelWedge_piOne_aux_twoSphereWedgePiOne
        ConstructionTargets.PointWedgeVanKampen.threeCirclesFundamentalGroupEquiv).trans
      ((ConstructionTargets.PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum
          (Fin 0) (Fin 3)).trans
        (MulEquiv.ofBijective (FreeGroup.map e)
          ⟨FreeGroup.map_injective e.injective,
            FreeGroup.map_surjective e.surjective⟩)))

theorem apm_t97A03_invariants_aux_modelWedge_piOne
    (z : apm_t97A03_modelWedge) :
    Nonempty (FundamentalGroup apm_t97A03_modelWedge z ≃*
      FreeGroup (Fin 3)) := by
  letI : PathConnectedSpace apm_t97A03_S2 :=
    ConstructionTargets.SphereHomology.spherePathConnectedSpace 2
  haveI : PathConnectedSpace apm_t97A03_twoSphereWedge :=
    ConstructionTargets.PointWedgePathConnected.wedgePathConnectedSpace
      apm_t97A03_north apm_t97A03_north
  haveI : PathConnectedSpace apm_t97A03_ThreeCircles :=
    ConstructionTargets.PointWedgeVanKampen.threeCircles_pathConnected
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected z
      apm_t97A03_modelWedgeBase).trans
    apm_t97A03_invariants_aux_modelWedge_piOne_aux_modelWedgeBase⟩

/-- Transport all four singular-homology calculations and the based
fundamental-group calculation across a supplied homotopy equivalence.  Use
`singularHomologyIsoOfHomotopyEquiv` and the path induced by the homotopy
equivalence's inverse law for basepoint change. -/
theorem apm_t97A03_invariants_aux_transport
    (Y : Type) [TopologicalSpace Y] (y : Y)
    (e : ContinuousMap.HomotopyEquiv Y apm_t97A03_modelWedge)
    (h0 : Nonempty (apm_t97A03_Homology apm_t97A03_modelWedge 0 ≅
      ModuleCat.of ℤ ℤ))
    (h1 : Nonempty (apm_t97A03_Homology apm_t97A03_modelWedge 1 ≅
      ModuleCat.of ℤ (Fin 3 → ℤ)))
    (h2 : Nonempty (apm_t97A03_Homology apm_t97A03_modelWedge 2 ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)))
    (hhigh : ∀ n, 3 ≤ n →
      Limits.IsZero (apm_t97A03_Homology apm_t97A03_modelWedge n))
    (hpi : ∀ z : apm_t97A03_modelWedge,
      Nonempty (FundamentalGroup apm_t97A03_modelWedge z ≃*
        FreeGroup (Fin 3))) :
    Nonempty (apm_t97A03_Homology Y 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97A03_Homology Y 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97A03_Homology Y 2 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ n, 3 ≤ n → Limits.IsZero (apm_t97A03_Homology Y n)) ∧
    Nonempty (FundamentalGroup Y y ≃* FreeGroup (Fin 3)) := by
  obtain ⟨h0⟩ := h0
  obtain ⟨h1⟩ := h1
  obtain ⟨h2⟩ := h2
  let homologyTransport (n : ℕ) :
      apm_t97A03_Homology Y n ≅ apm_t97A03_Homology apm_t97A03_modelWedge n :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of Y) n (apm_t97A03_Homology apm_t97A03_modelWedge n)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        e n ≪≫
       (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of apm_t97A03_modelWedge) n).symm)
  refine ⟨⟨homologyTransport 0 ≪≫ h0⟩,
    ⟨homologyTransport 1 ≪≫ h1⟩,
    ⟨homologyTransport 2 ≪≫ h2⟩, ?_, ?_⟩
  · intro n hn
    exact Limits.IsZero.of_iso (hhigh n hn) (homologyTransport n)
  · obtain ⟨hpi⟩ := hpi (e.toFun y)
    let epi := (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
      (FundamentalGroupoid.mk y)
    exact ⟨epi.trans hpi⟩

/-- Why this unblocks `apm_t97a03`: this is the missing global monodromy
classification of connected two-sheeted covers of the concrete base.  It
identifies the total space with one of the two quotient models appearing in
the frozen conclusion. -/
theorem apm_t97A03_bridge_classify_connected_double_cover
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) ∨
      Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover) := by
  by_cases htwo : apm_t97A03_TwoCircleMonodromy p hp
  · exact Or.inr (apm_t97A03_classify_aux_twoCircle_homeomorph
      A B hAB Y p hp hdegree htwo)
  · have hnontrivial :=
      apm_t97A03_classify_aux_literal_transport_nontrivial
        A B hAB Y p hp hdegree
    have hone := apm_t97A03_classify_aux_oneCircleMonodromy
      p hp hdegree hnontrivial htwo
    exact Or.inl (apm_t97A03_classify_aux_oneCircle_homeomorph
      A B hAB Y p hp hdegree hone)

/-- Why this unblocks `apm_t97a03`: this packages the cellular-to-singular
homology calculation and quantitative Nielsen--Schreier computation for the
two classified models, including transport along the displayed
homeomorphism.  It supplies all five invariant conjuncts of the main theorem. -/
theorem apm_t97A03_bridge_invariants_of_model
    (Y : Type) [TopologicalSpace Y] (y : Y)
    (hmodel : Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) ∨
      Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover)) :
    Nonempty (apm_t97A03_Homology Y 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97A03_Homology Y 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97A03_Homology Y 2 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ n, 3 ≤ n → Limits.IsZero (apm_t97A03_Homology Y n)) ∧
    Nonempty (FundamentalGroup Y y ≃* FreeGroup (Fin 3)) := by
  have h0 := apm_t97A03_invariants_aux_modelWedge_h0
  have h1 := apm_t97A03_invariants_aux_modelWedge_h1
  have h2 := apm_t97A03_invariants_aux_modelWedge_h2
  have hhigh := apm_t97A03_invariants_aux_modelWedge_high
  have hpi := apm_t97A03_invariants_aux_modelWedge_piOne
  rcases hmodel with ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩
  · obtain ⟨eM⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv
    exact apm_t97A03_invariants_aux_transport Y y
      (eY.toHomotopyEquiv.trans eM) h0 h1 h2 hhigh hpi
  · obtain ⟨eM⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv
    exact apm_t97A03_invariants_aux_transport Y y
      (eY.toHomotopyEquiv.trans eM) h0 h1 h2 hhigh hpi

theorem apm_t97a03
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (y : Y) (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    (Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) ∨
      Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover)) ∧
    Nonempty (apm_t97A03_Homology Y 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97A03_Homology Y 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97A03_Homology Y 2 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ n, 3 ≤ n → Limits.IsZero (apm_t97A03_Homology Y n)) ∧
    Nonempty (FundamentalGroup Y y ≃* FreeGroup (Fin 3)) := by
  have hmodel := apm_t97A03_bridge_classify_connected_double_cover
    A B hAB Y p hp hdegree
  exact ⟨hmodel, apm_t97A03_bridge_invariants_of_model Y y hmodel⟩
