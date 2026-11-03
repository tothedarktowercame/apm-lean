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

/-- A function on `[0, 2π]` that is continuous there and has equal values at the
two ends descends to a continuous map on the circle, agreeing with it along
`Circle.exp`.  This is the pasting tool for maps built from arcs: define the
pieces on consecutive subintervals of `[0, 2π]` (e.g. with `Set.IccExtend` and
`Continuous.if_le`) and lift. -/
theorem apm_t97A03_circleLiftIcc {Y : Type} [TopologicalSpace Y] (f : ℝ → Y)
    (hf : f 0 = f (2 * Real.pi)) (hc : ContinuousOn f (Set.Icc 0 (2 * Real.pi))) :
    ∃ g : Circle → Y, Continuous g ∧
      ∀ t ∈ Set.Icc 0 (2 * Real.pi), g (Circle.exp t) = f t := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  refine ⟨fun z => AddCircle.liftIco (2 * Real.pi) 0 f (AddCircle.homeomorphCircle'.symm z), ?_, ?_⟩
  · exact (AddCircle.liftIco_zero_continuous hf hc).comp
      AddCircle.homeomorphCircle'.symm.continuous
  · intro t ht
    have hsymm : AddCircle.homeomorphCircle'.symm (Circle.exp t) = (t : AddCircle (2 * Real.pi)) := by
      rw [← AddCircle.homeomorphCircle'_apply_mk, Homeomorph.symm_apply_apply]
    show AddCircle.liftIco (2 * Real.pi) 0 f (AddCircle.homeomorphCircle'.symm (Circle.exp t)) = f t
    rw [hsymm]
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h
      rw [AddCircle.coe_period, ← hf]
      exact AddCircle.liftIco_zero_coe_apply (x := (0 : ℝ)) ⟨le_rfl, by positivity⟩
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, h⟩

/-- The lift is injective when `f` is injective on `[0, 2π)`. -/
theorem apm_t97A03_circleLiftIcc_injective {Y : Type} (f : ℝ → Y) (g : Circle → Y)
    (hg : ∀ t ∈ Set.Icc 0 (2 * Real.pi), g (Circle.exp t) = f t)
    (hinj : Set.InjOn f (Set.Ico 0 (2 * Real.pi))) : Function.Injective g := by
  have hrep : ∀ z : Circle, ∃ s ∈ Set.Ico 0 (2 * Real.pi), Circle.exp s = z := by
    intro z
    refine ⟨toIcoMod Real.two_pi_pos 0 (Complex.arg (z : ℂ)), by
      simpa using toIcoMod_mem_Ico Real.two_pi_pos 0 (Complex.arg (z : ℂ)), ?_⟩
    have hp : Function.Periodic Circle.exp (2 * Real.pi) := Circle.periodic_exp
    rw [toIcoMod, hp.sub_zsmul_eq, Circle.exp_arg]
  intro z w hzw
  obtain ⟨s, hs, rfl⟩ := hrep z
  obtain ⟨u, hu, rfl⟩ := hrep w
  rw [hg s ⟨hs.1, hs.2.le⟩, hg u ⟨hu.1, hu.2.le⟩] at hzw
  rw [hinj hs hu hzw]

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

/-- The four marked points are `Circle.exp` of `0, π/2, π, 3π/2`. -/
lemma apm_t97A03_exp_zero_eq_circleOne : Circle.exp 0 = apm_t97A03_circleOne := by
  apply Subtype.ext; simp [apm_t97A03_circleOne]

lemma apm_t97A03_exp_pi_div_two_eq_circleI :
    Circle.exp (Real.pi / 2) = apm_t97A03_circleI := by
  apply Subtype.ext
  simp [apm_t97A03_circleI, Circle.coe_exp, Complex.exp_mul_I, Complex.ofReal_div]

lemma apm_t97A03_exp_pi_eq_circleNegOne : Circle.exp Real.pi = apm_t97A03_circleNegOne := by
  apply Subtype.ext
  simp [apm_t97A03_circleNegOne, Circle.coe_exp, Complex.exp_mul_I]

lemma apm_t97A03_exp_three_pi_div_two_eq_circleNegI :
    Circle.exp (3 * Real.pi / 2) = apm_t97A03_circleNegI := by
  apply Subtype.ext
  have : (3 * Real.pi / 2 : ℝ) = Real.pi / 2 + Real.pi := by ring
  simp only [apm_t97A03_circleNegI, Circle.coe_exp, this, Complex.ofReal_add, add_mul,
    Complex.exp_add, Complex.exp_pi_mul_I]
  simp [Complex.exp_mul_I, Complex.ofReal_div]

/-- Four interval maps run in turn over the quarters `[kπ/2, (k+1)π/2]` of
`[0, 2π]`.  Used to paste lifted arcs into a circle. -/
noncomputable def apm_t97A03_quarterPasteRaw {Y : Type}
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (t : ℝ) : Y :=
  if t ≤ Real.pi / 2 then g 0 (Set.projIcc 0 1 zero_le_one (t / (Real.pi / 2)))
  else if t ≤ Real.pi then g 1 (Set.projIcc 0 1 zero_le_one ((t - Real.pi / 2) / (Real.pi / 2)))
  else if t ≤ 3 * Real.pi / 2 then
    g 2 (Set.projIcc 0 1 zero_le_one ((t - Real.pi) / (Real.pi / 2)))
  else g 3 (Set.projIcc 0 1 zero_le_one ((t - 3 * Real.pi / 2) / (Real.pi / 2)))

lemma apm_t97A03_quarterPasteRaw_continuous {Y : Type} [TopologicalSpace Y]
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (hg : ∀ k, Continuous (g k))
    (h01 : g 0 1 = g 1 0) (h12 : g 1 1 = g 2 0) (h23 : g 2 1 = g 3 0) :
    Continuous (apm_t97A03_quarterPasteRaw g) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have piece : ∀ (k : Fin 4) (c : ℝ), Continuous fun t : ℝ =>
      g k (Set.projIcc 0 1 zero_le_one ((t - c) / (Real.pi / 2))) := fun k c =>
    (hg k).comp (continuous_projIcc.comp (by fun_prop))
  unfold apm_t97A03_quarterPasteRaw
  refine Continuous.if_le (by simpa using piece 0 0) ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le (piece 1 _) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (piece 2 _) (piece 3 _) continuous_id continuous_const ?_
      intro t ht; subst ht
      rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 by field_simp; ring,
        show (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2) = 0 by simp]
      simpa using h23
    · intro t ht; subst ht
      have h3 : ¬ (Real.pi ≤ 3 * Real.pi / 2) → False := fun h => h (by linarith)
      rw [if_pos (by linarith : Real.pi ≤ 3 * Real.pi / 2)]
      rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by field_simp; ring,
        show (Real.pi - Real.pi) / (Real.pi / 2) = 0 by simp]
      simpa using h12
  · intro t ht; subst ht
    rw [if_pos (by linarith : Real.pi / 2 ≤ Real.pi)]
    rw [show Real.pi / 2 / (Real.pi / 2) = 1 by field_simp,
      show (Real.pi / 2 - Real.pi / 2) / (Real.pi / 2) = 0 by simp]
    simpa using h01

/-- The pasted circle map: continuous, and equal to the quarter pieces along
`Circle.exp`.  It is determined by these values. -/
lemma apm_t97A03_quarterPaste_exists {Y : Type} [TopologicalSpace Y]
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (hg : ∀ k, Continuous (g k))
    (h01 : g 0 1 = g 1 0) (h12 : g 1 1 = g 2 0) (h23 : g 2 1 = g 3 0)
    (h30 : g 3 1 = g 0 0) :
    ∃ c : Circle → Y, Continuous c ∧
      (∀ t ∈ Set.Icc 0 (2 * Real.pi), c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) ∧
      c apm_t97A03_circleOne = g 0 0 ∧ c apm_t97A03_circleI = g 1 0 ∧
      c apm_t97A03_circleNegOne = g 2 0 ∧ c apm_t97A03_circleNegI = g 3 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc := apm_t97A03_quarterPasteRaw_continuous g hg h01 h12 h23
  have hend : apm_t97A03_quarterPasteRaw g 0 = apm_t97A03_quarterPasteRaw g (2 * Real.pi) := by
    unfold apm_t97A03_quarterPasteRaw
    rw [if_pos (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    rw [show (2 * Real.pi - 3 * Real.pi / 2) / (Real.pi / 2) = 1 by field_simp; ring]
    simpa using h30.symm
  obtain ⟨c, hcc, hcv⟩ := apm_t97A03_circleLiftIcc _ hend hc.continuousOn
  refine ⟨c, hcc, hcv, ?_, ?_, ?_, ?_⟩
  · rw [← apm_t97A03_exp_zero_eq_circleOne, hcv 0 ⟨le_rfl, by linarith⟩]
    unfold apm_t97A03_quarterPasteRaw; rw [if_pos (by linarith)]; simp
  · rw [← apm_t97A03_exp_pi_div_two_eq_circleI, hcv _ ⟨by linarith, by linarith⟩]
    unfold apm_t97A03_quarterPasteRaw; rw [if_pos le_rfl]
    rw [show Real.pi / 2 / (Real.pi / 2) = 1 by field_simp]; simpa using h01
  · rw [← apm_t97A03_exp_pi_eq_circleNegOne, hcv _ ⟨by linarith, by linarith⟩]
    unfold apm_t97A03_quarterPasteRaw; rw [if_neg (by linarith), if_pos le_rfl]
    rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 by field_simp; ring]; simpa using h12
  · rw [← apm_t97A03_exp_three_pi_div_two_eq_circleNegI, hcv _ ⟨by linarith, by linarith⟩]
    unfold apm_t97A03_quarterPasteRaw
    rw [if_neg (by linarith), if_neg (by linarith), if_pos le_rfl]
    rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 by field_simp; ring]; simpa using h23

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

lemma apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_exp_inj
    {x y : ℝ} (hlo : -(2 * Real.pi) < x - y)
    (hhi : x - y < 2 * Real.pi) (h : Circle.exp x = Circle.exp y) : x = y := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hm' : x - y = (m : ℝ) * (2 * Real.pi) := by linarith
  have hml : (-1 : ℝ) < (m : ℝ) := by
    nlinarith [Real.pi_pos]
  have hmu : (m : ℝ) < 1 := by
    nlinarith [Real.pi_pos]
  have hml' : (-1 : ℤ) < m := by exact_mod_cast hml
  have hmu' : m < (1 : ℤ) := by exact_mod_cast hmu
  have : m = 0 := by omega
  subst m
  simpa using hm

lemma apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cross
    (A B : Circle) (hAB : A ≠ B) (t u : Set.Icc (0 : ℝ) 1)
    (h : apm_t97A03_circleArc A B t =
      apm_t97A03_complementaryCircleArc A B u) :
    ((t : ℝ) = 0 ∧ (u : ℝ) = 0) ∨ ((t : ℝ) = 1 ∧ (u : ℝ) = 1) := by
  have hab : Complex.arg A ≠ Complex.arg B := fun e ↦ hAB (Circle.injective_arg e)
  have hAlo := Complex.neg_pi_lt_arg (A : ℂ)
  have hAhi := Complex.arg_le_pi (A : ℂ)
  have hBlo := Complex.neg_pi_lt_arg (B : ℂ)
  have hBhi := Complex.arg_le_pi (B : ℂ)
  have he : Circle.exp
        ((1 - (t : ℝ)) * Complex.arg A + (t : ℝ) * Complex.arg B) =
      Circle.exp ((1 - (u : ℝ)) * Complex.arg A +
        (u : ℝ) * (Complex.arg B + apm_t97A03_arcShift A B)) := by
    simpa [apm_t97A03_circleArc, apm_t97A03_complementaryCircleArc, Path.ofLine] using h
  unfold apm_t97A03_arcShift at he
  split_ifs at he with hlt
  · obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
    have hm' :
        ((1 - (t : ℝ)) * Complex.arg A + (t : ℝ) * Complex.arg B) -
          ((1 - (u : ℝ)) * Complex.arg A +
            (u : ℝ) * (Complex.arg B - 2 * Real.pi)) =
          (m : ℝ) * (2 * Real.pi) := by linarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by
      nlinarith [t.property.1, t.property.2, u.property.1, u.property.2, Real.pi_pos]
    have hm1 : (m : ℝ) ≤ 1 := by
      nlinarith [t.property.1, t.property.2, u.property.1, u.property.2, Real.pi_pos]
    have hm0' : (0 : ℤ) ≤ m := by exact_mod_cast hm0
    have hm1' : m ≤ (1 : ℤ) := by exact_mod_cast hm1
    have hm_cases : m = 0 ∨ m = 1 := by omega
    rcases hm_cases with rfl | rfl
    · left
      simp only [Int.cast_zero, zero_mul] at hm'
      constructor <;> nlinarith [t.property.1, u.property.1, Real.pi_pos]
    · right
      simp only [Int.cast_one, one_mul] at hm'
      constructor <;> nlinarith [t.property.2, u.property.2, Real.pi_pos]
  · have hba : Complex.arg B < Complex.arg A := lt_of_le_of_ne (le_of_not_gt hlt) hab.symm
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
    have hm' :
        ((1 - (t : ℝ)) * Complex.arg A + (t : ℝ) * Complex.arg B) -
          ((1 - (u : ℝ)) * Complex.arg A +
            (u : ℝ) * (Complex.arg B + 2 * Real.pi)) =
          (m : ℝ) * (2 * Real.pi) := by linarith
    have hm0 : (-1 : ℝ) ≤ (m : ℝ) := by
      nlinarith [t.property.1, t.property.2, u.property.1, u.property.2, Real.pi_pos]
    have hm1 : (m : ℝ) ≤ 0 := by
      nlinarith [t.property.1, t.property.2, u.property.1, u.property.2, Real.pi_pos]
    have hm0' : (-1 : ℤ) ≤ m := by exact_mod_cast hm0
    have hm1' : m ≤ (0 : ℤ) := by exact_mod_cast hm1
    have hm_cases : m = -1 ∨ m = 0 := by omega
    rcases hm_cases with rfl | rfl
    · right
      norm_num at hm'
      constructor <;> nlinarith [t.property.2, u.property.2, Real.pi_pos]
    · left
      simp only [Int.cast_zero, zero_mul] at hm'
      constructor <;> nlinarith [t.property.1, u.property.1, Real.pi_pos]

theorem apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
    (A B : Circle) (hAB : A ≠ B) :
    Function.Surjective (fun x : Sum (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ↦
      match x with
      | .inl t => apm_t97A03_circleArc A B t
      | .inr t => apm_t97A03_complementaryCircleArc A B t) := by
  intro z
  have hab : Complex.arg A ≠ Complex.arg B := fun e ↦ hAB (Circle.injective_arg e)
  have hAlo := Complex.neg_pi_lt_arg (A : ℂ)
  have hAhi := Complex.arg_le_pi (A : ℂ)
  have hBlo := Complex.neg_pi_lt_arg (B : ℂ)
  have hBhi := Complex.arg_le_pi (B : ℂ)
  have hzlo := Complex.neg_pi_lt_arg (z : ℂ)
  have hzhi := Complex.arg_le_pi (z : ℂ)
  by_cases hlt : Complex.arg A < Complex.arg B
  · by_cases haz : Complex.arg A ≤ Complex.arg z
    · by_cases hzb : Complex.arg z ≤ Complex.arg B
      · let t : Set.Icc (0 : ℝ) 1 := ⟨(Complex.arg z - Complex.arg A) /
            (Complex.arg B - Complex.arg A), by
              constructor
              · exact div_nonneg (sub_nonneg.mpr haz) (sub_nonneg.mpr hlt.le)
              · exact (div_le_one (sub_pos.mpr hlt)).2 (by linarith)⟩
        refine ⟨.inl t, ?_⟩
        change apm_t97A03_circleArc A B t = z
        rw [← Circle.exp_arg z]
        apply congrArg Circle.exp
        dsimp [apm_t97A03_circleArc, Path.ofLine, t]
        field_simp [sub_ne_zero.mpr hab.symm]
        ring
      · have hbz : Complex.arg B < Complex.arg z := lt_of_not_ge hzb
        have hden : 0 < Complex.arg A - Complex.arg B + 2 * Real.pi := by nlinarith
        let t : Set.Icc (0 : ℝ) 1 := ⟨(Complex.arg A - (Complex.arg z - 2 * Real.pi)) /
              (Complex.arg A - Complex.arg B + 2 * Real.pi), by
                constructor
                · exact div_nonneg (by nlinarith) hden.le
                · exact (div_le_one hden).2 (by nlinarith)⟩
        refine ⟨.inr t, ?_⟩
        change apm_t97A03_complementaryCircleArc A B t = z
        rw [show apm_t97A03_complementaryCircleArc A B t = Circle.exp (Complex.arg z - 2 * Real.pi) by
          apply congrArg Circle.exp
          change (1 - (t : ℝ)) * Complex.arg A +
            (t : ℝ) * (Complex.arg B + apm_t97A03_arcShift A B) = _
          dsimp [t, apm_t97A03_arcShift]
          rw [if_pos hlt]
          field_simp [ne_of_gt hden]
          ring]
        rw [Circle.exp_sub_two_pi, Circle.exp_arg]
    · have hza : Complex.arg z < Complex.arg A := lt_of_not_ge haz
      have hden : 0 < Complex.arg A - Complex.arg B + 2 * Real.pi := by nlinarith
      let t : Set.Icc (0 : ℝ) 1 := ⟨(Complex.arg A - Complex.arg z) /
            (Complex.arg A - Complex.arg B + 2 * Real.pi), by
              constructor
              · exact div_nonneg (sub_nonneg.mpr hza.le) hden.le
              · exact (div_le_one hden).2 (by nlinarith)⟩
      refine ⟨.inr t, ?_⟩
      change apm_t97A03_complementaryCircleArc A B t = z
      rw [← Circle.exp_arg z]
      apply congrArg Circle.exp
      change (1 - (t : ℝ)) * Complex.arg A +
        (t : ℝ) * (Complex.arg B + apm_t97A03_arcShift A B) = _
      dsimp [t, apm_t97A03_arcShift]
      rw [if_pos hlt]
      field_simp [ne_of_gt hden]
      ring
  · have hba : Complex.arg B < Complex.arg A := lt_of_le_of_ne (le_of_not_gt hlt) hab.symm
    by_cases hbz : Complex.arg B ≤ Complex.arg z
    · by_cases hza : Complex.arg z ≤ Complex.arg A
      · let t : Set.Icc (0 : ℝ) 1 := ⟨(Complex.arg A - Complex.arg z) /
            (Complex.arg A - Complex.arg B), by
              constructor
              · exact div_nonneg (sub_nonneg.mpr hza) (sub_nonneg.mpr hba.le)
              · exact (div_le_one (sub_pos.mpr hba)).2 (by linarith)⟩
        refine ⟨.inl t, ?_⟩
        change apm_t97A03_circleArc A B t = z
        rw [← Circle.exp_arg z]
        apply congrArg Circle.exp
        dsimp [apm_t97A03_circleArc, Path.ofLine, t]
        field_simp [sub_ne_zero.mpr hab]
        ring
      · have haz : Complex.arg A < Complex.arg z := lt_of_not_ge hza
        have hden : 0 < Complex.arg B - Complex.arg A + 2 * Real.pi := by nlinarith
        let t : Set.Icc (0 : ℝ) 1 := ⟨(Complex.arg z - Complex.arg A) /
              (Complex.arg B - Complex.arg A + 2 * Real.pi), by
                constructor
                · exact div_nonneg (sub_nonneg.mpr haz.le) hden.le
                · exact (div_le_one hden).2 (by nlinarith)⟩
        refine ⟨.inr t, ?_⟩
        change apm_t97A03_complementaryCircleArc A B t = z
        rw [← Circle.exp_arg z]
        apply congrArg Circle.exp
        change (1 - (t : ℝ)) * Complex.arg A +
          (t : ℝ) * (Complex.arg B + apm_t97A03_arcShift A B) = _
        dsimp [t, apm_t97A03_arcShift]
        rw [if_neg hlt]
        field_simp [ne_of_gt hden]
        ring
    · have hzb : Complex.arg z < Complex.arg B := lt_of_not_ge hbz
      have hden : 0 < Complex.arg B - Complex.arg A + 2 * Real.pi := by nlinarith
      let t : Set.Icc (0 : ℝ) 1 := ⟨(Complex.arg z + 2 * Real.pi - Complex.arg A) /
            (Complex.arg B - Complex.arg A + 2 * Real.pi), by
              constructor
              · exact div_nonneg (by nlinarith) hden.le
              · exact (div_le_one hden).2 (by nlinarith)⟩
      refine ⟨.inr t, ?_⟩
      change apm_t97A03_complementaryCircleArc A B t = z
      rw [show apm_t97A03_complementaryCircleArc A B t = Circle.exp (Complex.arg z + 2 * Real.pi) by
        apply congrArg Circle.exp
        change (1 - (t : ℝ)) * Complex.arg A +
          (t : ℝ) * (Complex.arg B + apm_t97A03_arcShift A B) = _
        dsimp [t, apm_t97A03_arcShift]
        rw [if_neg hlt]
        field_simp [ne_of_gt hden]
        ring]
      rw [Circle.exp_add_two_pi, Circle.exp_arg]

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
  have hab : Complex.arg A ≠ Complex.arg B := by
    intro h
    apply hAB
    exact Circle.injective_arg h
  have hargAlo := Complex.neg_pi_lt_arg (A : ℂ)
  have hargAhi := Complex.arg_le_pi (A : ℂ)
  have hargBlo := Complex.neg_pi_lt_arg (B : ℂ)
  have hargBhi := Complex.arg_le_pi (B : ℂ)
  rintro (t | t) (u | u) h
  · change first t = first u
    congr 1
    apply Subtype.ext
    have he : Circle.exp
          ((1 - (t : ℝ)) * Complex.arg A + (t : ℝ) * Complex.arg B) =
        Circle.exp ((1 - (u : ℝ)) * Complex.arg A + (u : ℝ) * Complex.arg B) := by
      simpa [apm_t97A03_circleArc, Path.ofLine] using h
    have hei :
        (1 - (t : ℝ)) * Complex.arg A + (t : ℝ) * Complex.arg B =
          (1 - (u : ℝ)) * Complex.arg A + (u : ℝ) * Complex.arg B := by
      rcases le_total (t : ℝ) u with htu | hut
      · apply apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_exp_inj
            (h := he) <;>
          nlinarith [t.property.1, t.property.2, u.property.1, u.property.2,
            mul_nonneg (sub_nonneg.mpr htu) (sub_nonneg.mpr (le_of_lt hargBlo)),
            mul_nonneg (sub_nonneg.mpr htu) (sub_nonneg.mpr hargAhi)]
      · apply apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_exp_inj
            (h := he) <;>
          nlinarith [t.property.1, t.property.2, u.property.1, u.property.2,
            mul_nonneg (sub_nonneg.mpr hut) (sub_nonneg.mpr (le_of_lt hargAlo)),
            mul_nonneg (sub_nonneg.mpr hut) (sub_nonneg.mpr hargBhi)]
    have hz : ((t : ℝ) - (u : ℝ)) * (Complex.arg B - Complex.arg A) = 0 := by
      nlinarith [hei]
    rcases mul_eq_zero.mp hz with htu | hba
    · linarith
    · exact (hab (sub_eq_zero.mp hba).symm).elim
  · change first t = second u
    rcases apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cross
        A B hAB t u h with ⟨ht, hu⟩ | ⟨ht, hu⟩
    · have ht' : t = 0 := by apply Subtype.ext; exact ht
      have hu' : u = 0 := by apply Subtype.ext; exact hu
      simpa [ht', hu'] using hzero
    · have ht' : t = 1 := by apply Subtype.ext; exact ht
      have hu' : u = 1 := by apply Subtype.ext; exact hu
      simpa [ht', hu'] using hone
  · change second t = first u
    rcases apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cross
        A B hAB u t h.symm with ⟨hu, ht⟩ | ⟨hu, ht⟩
    · have ht' : t = 0 := by apply Subtype.ext; exact ht
      have hu' : u = 0 := by apply Subtype.ext; exact hu
      simpa [ht', hu'] using hzero.symm
    · have ht' : t = 1 := by apply Subtype.ext; exact ht
      have hu' : u = 1 := by apply Subtype.ext; exact hu
      simpa [ht', hu'] using hone.symm
  · change second t = second u
    congr 1
    apply Subtype.ext
    have hdelta : Complex.arg B + apm_t97A03_arcShift A B ≠ Complex.arg A := by
      unfold apm_t97A03_arcShift
      split_ifs with hlt <;> nlinarith [Real.pi_pos]
    have he : Circle.exp
          ((1 - (t : ℝ)) * Complex.arg A +
            (t : ℝ) * (Complex.arg B + apm_t97A03_arcShift A B)) =
        Circle.exp ((1 - (u : ℝ)) * Complex.arg A +
            (u : ℝ) * (Complex.arg B + apm_t97A03_arcShift A B)) := by
      simpa [apm_t97A03_complementaryCircleArc, Path.ofLine] using h
    simp only [apm_t97A03_arcShift] at he hdelta
    split_ifs at he hdelta ⊢ with hlt
    · have hei :=
        apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_exp_inj
          (x := (1 - (t : ℝ)) * Complex.arg A +
            (t : ℝ) * (Complex.arg B - 2 * Real.pi))
          (y := (1 - (u : ℝ)) * Complex.arg A +
            (u : ℝ) * (Complex.arg B - 2 * Real.pi))
          (by nlinarith [t.property.1, t.property.2, u.property.1, u.property.2])
          (by nlinarith [t.property.1, t.property.2, u.property.1, u.property.2]) (by simpa using he)
      have hz : ((t : ℝ) - (u : ℝ)) *
          (Complex.arg B - 2 * Real.pi - Complex.arg A) = 0 := by nlinarith [hei]
      rcases mul_eq_zero.mp hz with htu | hd
      · linarith
      · exact (hdelta (by linarith)).elim
    · have hba : Complex.arg B < Complex.arg A := lt_of_le_of_ne (le_of_not_gt hlt) hab.symm
      have hei :=
        apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_exp_inj
          (x := (1 - (t : ℝ)) * Complex.arg A +
            (t : ℝ) * (Complex.arg B + 2 * Real.pi))
          (y := (1 - (u : ℝ)) * Complex.arg A +
            (u : ℝ) * (Complex.arg B + 2 * Real.pi))
          (by nlinarith [t.property.1, t.property.2, u.property.1, u.property.2])
          (by nlinarith [t.property.1, t.property.2, u.property.1, u.property.2]) (by simpa using he)
      have hz : ((t : ℝ) - (u : ℝ)) *
          (Complex.arg B + 2 * Real.pi - Complex.arg A) = 0 := by nlinarith [hei]
      rcases mul_eq_zero.mp hz with htu | hd
      · linarith
      · exact (hdelta (by linarith)).elim

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
theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle_aux_homeomorph
    (A B : Circle) (hAB : A ≠ B) :
    ∃ q : Circle ≃ₜ Circle, q 1 = A ∧
      q apm_t97A03_circleNegOne = B := by
  let S := apm_t97A03_circleOne
  let T := apm_t97A03_circleNegOne
  have hST : S ≠ T := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num [S, T, apm_t97A03_circleOne, apm_t97A03_circleNegOne] at hv
  obtain ⟨q, hq, hqfirst, hqsecond⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste
      S T hST Circle (apm_t97A03_circleArc A B)
        (apm_t97A03_complementaryCircleArc A B)
        (apm_t97A03_circleArc A B).continuous
        (apm_t97A03_complementaryCircleArc A B).continuous
        (by simp) (by simp)
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨x, hx⟩ :=
      apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
        A B hAB z
    rcases x with t | t
    · exact ⟨apm_t97A03_circleArc S T t, by simpa [hqfirst] using hx⟩
    · exact ⟨apm_t97A03_complementaryCircleArc S T t, by simpa [hqsecond] using hx⟩
  have hqinj : Function.Injective q := by
    intro x y hxy
    obtain ⟨rx, hrx⟩ :=
      apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
        S T hST x
    obtain ⟨ry, hry⟩ :=
      apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
        S T hST y
    rw [← hrx, ← hry] at hxy ⊢
    apply apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_fibres
      A B hAB Circle (apm_t97A03_circleArc S T)
        (apm_t97A03_complementaryCircleArc S T) (by simp) (by simp) rx ry
    rcases rx with t | t <;> rcases ry with u | u <;>
      simpa [hqfirst, hqsecond] using hxy
  let e : Circle ≃ Circle := Equiv.ofBijective q ⟨hqinj, hqsurj⟩
  have hec : Continuous e := hq
  refine ⟨hec.homeoOfEquivCompactToT2, ?_, ?_⟩
  · simpa [e, S] using hqfirst (0 : Set.Icc (0 : ℝ) 1)
  · simpa [e, S, T] using hqfirst (1 : Set.Icc (0 : ℝ) 1)

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle_aux_normalized_aux_continuousEquiv
    (C : Circle) (hC : C ≠ 1) :
    ∃ e : Circle ≃ Circle, Continuous e ∧ e 1 = 1 ∧
      e apm_t97A03_circleNegOne = C := by
  obtain ⟨e, he1, hen⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle_aux_homeomorph
      1 C (Ne.symm hC)
  exact ⟨e.toEquiv, e.continuous, he1, hen⟩

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle_aux_normalized
    (C : Circle) (hC : C ≠ 1) :
    ∃ e : Circle ≃ₜ Circle, e 1 = 1 ∧
      e apm_t97A03_circleNegOne = C := by
  obtain ⟨e, he, he1, hen⟩ :=
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle_aux_normalized_aux_continuousEquiv
      C hC
  exact ⟨he.homeoOfEquivCompactToT2, he1, hen⟩

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle
    (A B : Circle) (hAB : A ≠ B) :
    ∃ q : Circle ≃ₜ Circle,
      q 1 = A ∧ q apm_t97A03_circleNegOne = B := by
  exact
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_markedCircle_aux_homeomorph
      A B hAB

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts_aux_construct_aux_oneSheet
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (hfirst : d.firstPerm = Equiv.swap 0 1)
    (hsecond : d.secondPerm = Equiv.swap 0 1)
    (q : Circle ≃ₜ Circle) (hq1 : q 1 = A)
    (hqn : q apm_t97A03_circleNegOne = B) (i : Fin 2) :
    ∃ c : Circle → Y, Continuous c ∧
      (∀ w, p (c w) = apm_t97A03_baseCircle A B (q w)) ∧
      c 1 = d.sphere i apm_t97A03_north ∧
      c apm_t97A03_circleNegOne =
        d.sphere (Equiv.swap 0 1 i) apm_t97A03_south := by
  have hzero : d.first i 0 = d.second i 0 := by
    rw [d.first_zero, d.second_zero]
  have hone : d.first i 1 = d.second i 1 := by
    rw [d.first_one, d.second_one, hfirst, hsecond]
  obtain ⟨s, hs, hsfirst, hssecond⟩ :=
    apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste
      A B (by
        intro h
        have := q.injective (hq1.trans (h.trans hqn.symm))
        have hv := congrArg Subtype.val this
        norm_num [apm_t97A03_circleNegOne] at hv)
      Y (d.first i) (d.second i) (d.continuous_first i)
        (d.continuous_second i) hzero hone
  let c : Circle → Y := fun w ↦ s (q w)
  refine ⟨c, hs.comp q.continuous, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨x, hx⟩ :=
      apm_t97A03_classify_aux_literal_transport_nontrivial_aux_clopenSection_aux_section_aux_circle_aux_paste_aux_cover
        A B (by
          intro h
          have := q.injective (hq1.trans (h.trans hqn.symm))
          have hv := congrArg Subtype.val this
          norm_num [apm_t97A03_circleNegOne] at hv) (q w)
    rcases x with t | t
    · change p (s (q w)) = apm_t97A03_baseCircle A B (q w)
      rw [← hx, hsfirst, d.first_lifts]
      rfl
    · change p (s (q w)) = apm_t97A03_baseCircle A B (q w)
      rw [← hx, hssecond, d.second_lifts]
      rfl
  · change s (q 1) = _
    calc
      s (q 1) = s A := congrArg s hq1
      _ = s ((apm_t97A03_circleArc A B) 0) :=
        congrArg s (apm_t97A03_circleArc A B).source.symm
      _ = d.first i 0 := hsfirst 0
      _ = d.sphere i apm_t97A03_north := d.first_zero i
  · change s (q apm_t97A03_circleNegOne) = _
    calc
      s (q apm_t97A03_circleNegOne) = s B := congrArg s hqn
      _ = s ((apm_t97A03_circleArc A B) 1) :=
        congrArg s (apm_t97A03_circleArc A B).target.symm
      _ = d.first i 1 := hsfirst 1
      _ = d.sphere (d.firstPerm i) apm_t97A03_south := d.first_one i
      _ = d.sphere (Equiv.swap 0 1 i) apm_t97A03_south := by rw [hfirst]

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts_aux_construct_aux_continuous
    {Y : Type} [TopologicalSpace Y] (c : Fin 2 → Circle → Y)
    (hc : ∀ i, Continuous (c i)) :
    Continuous (fun w : Fin 2 × Circle ↦ c w.1 w.2) := by
  rw [continuous_iff_continuousAt]
  intro w
  apply ContinuousAt.congr_of_eventuallyEq
    ((hc w.1).continuousAt.comp continuousAt_snd)
  filter_upwards [continuousAt_fst.eventually
    ((isOpen_discrete ({w.1} : Set (Fin 2))).mem_nhds (by simp))] with x hx
  change x.1 = w.1 at hx
  simp [hx]

theorem apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts_aux_construct
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
  choose c hc hlift hn hs using fun i ↦
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts_aux_construct_aux_oneSheet
      A B Y p d hfirst hsecond q hq1 hqn i
  exact ⟨c,
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts_aux_construct_aux_continuous c hc,
    hlift, hn, hs⟩

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
  exact
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_circlePaste_aux_geometricPaste_aux_pasteLifts_aux_construct
      A B Y p d hfirst hsecond q hq1 hqn

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
  classical
  have hAB : A ≠ B := by
    intro h
    have hw : (1 : Circle) = apm_t97A03_circleNegOne := by
      apply q.injective
      rw [hq1, hqn, h]
    have hv := congrArg Subtype.val hw
    norm_num [apm_t97A03_circleNegOne] at hv
  have hNS : apm_t97A03_north ≠ apm_t97A03_south := by
    intro h
    have hv := congrArg (fun z : apm_t97A03_S2 => z.1 (2 : Fin 3)) h
    norm_num [apm_t97A03_north, apm_t97A03_south,
      EuclideanSpace.single_apply] at hv
  have hmix (i : Fin 2) (z : apm_t97A03_S2) (j : Fin 2) (w : Circle)
      (he : d.sphere i z = c j w) :
      (Quotient.mk _ (.inl (i, z)) : apm_t97A03_TwoCircleCover) =
        Quotient.mk _ (.inr (j, w)) := by
    have hb : apm_t97A03_baseSphere A B z =
        apm_t97A03_baseCircle A B (q w) := by
      rw [← d.sphere_lifts i z, ← hlift j w, he]
    have hnrm :=
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize_eq
        A B hAB hb
    by_cases ha : q w = A
    · have hz : z = apm_t97A03_north := by
        simpa [ha,
          apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
          using hnrm
      have hw : w = 1 := q.injective (ha.trans hq1.symm)
      subst z
      subst w
      obtain ⟨k, hk, hku⟩ := d.sphere_unique (d.sphere_lifts i apm_t97A03_north)
      have hej : d.sphere j apm_t97A03_north = d.sphere i apm_t97A03_north :=
        (hn j).symm.trans he.symm
      have hij : i = j := (hku i rfl).trans (hku j hej).symm
      subst j
      fin_cases i
      · exact Quotient.sound
          (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ apm_t97A03_TwoCircleRel.c0n))
      · exact Quotient.sound
          (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ apm_t97A03_TwoCircleRel.c1n))
    · by_cases hb' : q w = B
      · have hz : z = apm_t97A03_south := by
          simpa [ha, hb', hAB.symm,
            apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
            using hnrm
        have hw : w = apm_t97A03_circleNegOne := q.injective (hb'.trans hqn.symm)
        subst z
        subst w
        have hej : d.sphere (Equiv.swap 0 1 j) apm_t97A03_south =
            d.sphere i apm_t97A03_south := (hs j).symm.trans he.symm
        obtain ⟨k, hk, hku⟩ := d.sphere_unique
          (d.sphere_lifts i apm_t97A03_south)
        have hi : i = Equiv.swap 0 1 j := (hku i rfl).trans (hku _ hej).symm
        fin_cases j <;> subst i
        · exact Quotient.sound
            (Relation.EqvGen.symm _ _
              (Relation.EqvGen.rel _ _ apm_t97A03_TwoCircleRel.c0s))
        · exact Quotient.sound
            (Relation.EqvGen.symm _ _
              (Relation.EqvGen.rel _ _ apm_t97A03_TwoCircleRel.c1s))
      · simp [ha, hb',
          apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
          at hnrm
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro x y hxy
  change
    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw d c x =
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_raw d c y
    at hxy
  cases x with
  | inl iz =>
      cases y with
      | inl jz =>
          obtain ⟨i, z⟩ := iz
          obtain ⟨j, z'⟩ := jz
          change d.sphere i z = d.sphere j z' at hxy
          have hb : apm_t97A03_baseSphere A B z =
              apm_t97A03_baseSphere A B z' := by
            rw [← d.sphere_lifts i z, ← d.sphere_lifts j z', hxy]
          have hz : z = z' := by
            have hnrm :=
              apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize_eq
                A B hAB hb
            simpa [apm_t97A03_baseSphere,
              apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
              using hnrm
          subst z'
          obtain ⟨k, hk, hku⟩ := d.sphere_unique (d.sphere_lifts i z)
          have hij : i = j := (hku i rfl).trans (hku j hxy.symm).symm
          subst j
          rfl
      | inr jw =>
          obtain ⟨i, z⟩ := iz
          obtain ⟨j, w⟩ := jw
          change d.sphere i z = c j w at hxy
          exact hmix i z j w hxy
  | inr iw =>
      cases y with
      | inl jz =>
          obtain ⟨i, w⟩ := iw
          obtain ⟨j, z⟩ := jz
          change c i w = d.sphere j z at hxy
          exact (hmix j z i w hxy.symm).symm
      | inr jw =>
          obtain ⟨i, w⟩ := iw
          obtain ⟨j, w'⟩ := jw
          change c i w = c j w' at hxy
          have hb : apm_t97A03_baseCircle A B (q w) =
              apm_t97A03_baseCircle A B (q w') := by
            rw [← hlift i w, ← hlift j w', hxy]
          have hnrm :=
            apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize_eq
              A B hAB hb
          have hq : q w = q w' := by
            by_cases ha : q w = A
            · have ha' : q w' = A := by
                by_cases hwa : q w' = A
                · exact hwa
                · by_cases hwb : q w' = B
                  · simp [ha, hwa, hwb, hAB,
                      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize] at hnrm
                    exact False.elim (hNS (hnrm hAB.symm))
                  · simp [ha, hwa, hwb,
                      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize] at hnrm
              exact ha.trans ha'.symm
            · by_cases hb' : q w = B
              · have hb'' : q w' = B := by
                  by_cases hwa : q w' = A
                  · simp [ha, hb', hwa, hAB.symm,
                      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize] at hnrm
                    exact False.elim (hNS hnrm.symm)
                  · by_cases hwb : q w' = B
                    · exact hwb
                    · simp [ha, hb', hwa, hwb, hAB.symm,
                        apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize] at hnrm
                exact hb'.trans hb''.symm
              · by_cases hwa : q w' = A
                · simp [ha, hb', hwa,
                    apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize] at hnrm
                · by_cases hwb : q w' = B
                  · simp [ha, hb', hwa, hwb, hAB.symm,
                      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize] at hnrm
                  · simpa [ha, hb', hwa, hwb,
                      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
                      using hnrm
          have hw : w = w' := q.injective hq
          subst w'
          obtain ⟨k, hk, hku⟩ := hunique (hlift i w)
          have hij : i = j := (hku i rfl).trans (hku j hxy.symm).symm
          subst j
          rfl

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

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_paste
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
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
    ∃ (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (c : Circle → Y),
      g = ![d.second 0, fun t ↦ d.first 1 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
        d.second 1, fun t ↦ d.first 0 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩] ∧
      Continuous c ∧
      (∀ t ∈ Set.Icc 0 (2 * Real.pi),
        c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) ∧
      c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north ∧
      c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south ∧
      c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north ∧
      c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south := by
  let σ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := fun t ↦
    ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩
  let g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y :=
    ![d.second 0, d.first 1 ∘ σ, d.second 1, d.first 0 ∘ σ]
  have hσ : Continuous σ := by
    exact (continuous_const.sub continuous_subtype_val).subtype_mk _
  have hg : ∀ k, Continuous (g k) := by
    intro k
    fin_cases k
    · exact d.continuous_second 0
    · exact (d.continuous_first 1).comp hσ
    · exact d.continuous_second 1
    · exact (d.continuous_first 0).comp hσ
  have h01 : g 0 1 = g 1 0 := by
    simpa [g, σ] using
      hendpoints.2.2.2.2.2.1.trans hendpoints.2.2.2.1.symm
  have h12 : g 1 1 = g 2 0 := by
    simpa [g, σ] using hendpoints.2.2.1.trans hendpoints.2.2.2.2.2.2.1.symm
  have h23 : g 2 1 = g 3 0 := by
    simpa [g, σ] using hendpoints.2.2.2.2.2.2.2.trans hendpoints.2.1.symm
  have h30 : g 3 1 = g 0 0 := by
    simpa [g, σ] using hendpoints.1.trans hendpoints.2.2.2.2.1.symm
  obtain ⟨c, hc, hraw, hc1, hci, hcn, hcni⟩ :=
    apm_t97A03_quarterPaste_exists g hg h01 h12 h23 h30
  refine ⟨g, c, ?_, hc, hraw, ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa [g] using hc1.trans hendpoints.2.2.2.2.1
  · have hci' : c apm_t97A03_circleI = d.first 1 1 := by
      simpa [g, σ] using hci
    exact hci'.trans hendpoints.2.2.2.1
  · simpa [g] using hcn.trans hendpoints.2.2.2.2.2.2.1
  · have hcni' : c apm_t97A03_circleNegI = d.first 0 1 := by
      simpa [g, σ] using hcni
    exact hcni'.trans hendpoints.2.1

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_injective_aux_raw
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (c : Circle → Y)
    (hg : g = ![d.second 0, fun t ↦ d.first 1 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
      d.second 1, fun t ↦ d.first 0 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩])
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) :
    Set.InjOn (fun t ↦ c (Circle.exp t)) (Set.Ico 0 (2 * Real.pi)) := by
  sorry

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_injective
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (c : Circle → Y)
    (hg : g = ![d.second 0, fun t ↦ d.first 1 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
      d.second 1, fun t ↦ d.first 0 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩])
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) :
    Function.Injective c := by
  apply apm_t97A03_circleLiftIcc_injective (fun t ↦ c (Circle.exp t)) c
  · intro t ht
    rfl
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_injective_aux_raw
        A B hAB Y p hp d g c hg hraw

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_range
    (A B : Circle)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (c : Circle → Y)
    (hg : g = ![d.second 0, fun t ↦ d.first 1 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
      d.second 1, fun t ↦ d.first 0 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩])
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) :
    ∀ w, ∃ z, p (c w) = apm_t97A03_baseCircle A B z := by
  intro w
  let t := toIcoMod Real.two_pi_pos 0 (Complex.arg (w : ℂ))
  have ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    simpa [t] using toIcoMod_mem_Ico Real.two_pi_pos 0 (Complex.arg (w : ℂ))
  have hexp : Circle.exp t = w := by
    have hperiod : Function.Periodic Circle.exp (2 * Real.pi) := Circle.periodic_exp
    change Circle.exp (toIcoMod Real.two_pi_pos 0 (Complex.arg (w : ℂ))) = w
    rw [toIcoMod, hperiod.sub_zsmul_eq, Circle.exp_arg]
  rw [← hexp, hraw t ⟨ht.1, ht.2.le⟩, hg]
  unfold apm_t97A03_quarterPasteRaw
  split_ifs with h0 h1 h2
  · exact ⟨apm_t97A03_complementaryCircleArc A B
        (Set.projIcc 0 1 zero_le_one (t / (Real.pi / 2))), d.second_lifts 0 _⟩
  · exact ⟨apm_t97A03_circleArc A B
        ⟨1 - (Set.projIcc 0 1 zero_le_one
          ((t - Real.pi / 2) / (Real.pi / 2)) : ℝ), by
            constructor <;>
              linarith [(Set.projIcc 0 1 zero_le_one
                ((t - Real.pi / 2) / (Real.pi / 2))).property.1,
                (Set.projIcc 0 1 zero_le_one
                ((t - Real.pi / 2) / (Real.pi / 2))).property.2]⟩,
        d.first_lifts 1 _⟩
  · exact ⟨apm_t97A03_complementaryCircleArc A B
        (Set.projIcc 0 1 zero_le_one ((t - Real.pi) / (Real.pi / 2))),
        d.second_lifts 1 _⟩
  · exact ⟨apm_t97A03_circleArc A B
        ⟨1 - (Set.projIcc 0 1 zero_le_one
          ((t - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ), by
            constructor <;>
              linarith [(Set.projIcc 0 1 zero_le_one
                ((t - 3 * Real.pi / 2) / (Real.pi / 2))).property.1,
                (Set.projIcc 0 1 zero_le_one
                ((t - 3 * Real.pi / 2) / (Real.pi / 2))).property.2]⟩,
        d.first_lifts 0 _⟩

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_cover_aux_two
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (c : Circle → Y)
    (hg : g = ![d.second 0, fun t ↦ d.first 1 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
      d.second 1, fun t ↦ d.first 0 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩])
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) :
    ∀ z, ∃ w₀ w₁, w₀ ≠ w₁ ∧
      p (c w₀) = apm_t97A03_baseCircle A B z ∧
      p (c w₁) = apm_t97A03_baseCircle A B z := by
  sorry

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_cover_aux_card
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (c : Circle → Y) (hinj : Function.Injective c)
    (htwo : ∀ z, ∃ w₀ w₁, w₀ ≠ w₁ ∧
      p (c w₀) = apm_t97A03_baseCircle A B z ∧
      p (c w₁) = apm_t97A03_baseCircle A B z) :
    ∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y := by
  intro y z hy
  obtain ⟨w₀, w₁, hne, h0, h1⟩ := htwo z
  have hc : c w₀ ≠ c w₁ := fun h => hne (hinj h)
  have hcard := hdegree (apm_t97A03_baseCircle A B z)
  rw [Nat.card_coe_set_eq, Set.ncard_eq_two] at hcard
  obtain ⟨a, b, hab, hS⟩ := hcard
  have m0 : c w₀ ∈ ({a, b} : Set Y) := hS ▸ (show c w₀ ∈ p ⁻¹' {apm_t97A03_baseCircle A B z} from h0)
  have m1 : c w₁ ∈ ({a, b} : Set Y) := hS ▸ (show c w₁ ∈ p ⁻¹' {apm_t97A03_baseCircle A B z} from h1)
  have my : y ∈ ({a, b} : Set Y) := hS ▸ (show y ∈ p ⁻¹' {apm_t97A03_baseCircle A B z} from hy)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m0 m1 my
  rcases my with rfl | rfl <;> rcases m0 with h0' | h0' <;> rcases m1 with h1' | h1'
  all_goals first
    | exact ⟨w₀, h0'⟩ | exact ⟨w₁, h1'⟩
    | exact absurd (h0'.trans h1'.symm) hc

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_cover
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (c : Circle → Y)
    (hg : g = ![d.second 0, fun t ↦ d.first 1 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
      d.second 1, fun t ↦ d.first 0 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩])
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) :
    ∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y := by
  apply
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_cover_aux_card
      A B Y p hdegree c
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_injective
        A B hAB Y p hp d g c hg hraw
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_cover_aux_two
        A B hAB Y p hp d g c hg hraw

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y) (c : Circle → Y)
    (hg : g = ![d.second 0, fun t ↦ d.first 1 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩,
      d.second 1, fun t ↦ d.first 0 ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩])
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw g t) :
    Function.Injective c ∧
      (∀ w, ∃ z, p (c w) = apm_t97A03_baseCircle A B z) ∧
      (∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y) := by
  exact ⟨
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_injective
      A B hAB Y p hp d g c hg hraw,
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_range
      A B Y p d g c hg hraw,
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact_aux_cover
      A B hAB Y p hp hdegree d g c hg hraw⟩

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct
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
  obtain ⟨g, c, hg, hc, hraw, hc1, hci, hcn, hcni⟩ :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_paste
      A B Y p d hendpoints
  obtain ⟨hinj, hrange, hcover⟩ :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct_aux_exact
      A B hAB Y p hp hdegree d g c hg hraw
  exact ⟨c, hc, hinj, hc1, hci, hcn, hcni, hrange, hcover⟩

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
  exact
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_construct
      A B hAB Y p hp hdegree d hendpoints

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

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_exact_aux_injective
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p) (c : Circle → Y)
    (hn0 : c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north)
    (hs0 : c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south)
    (hn1 : c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north)
    (hs1 : c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south)
    (hcinj : Function.Injective c)
    (hcrange : ∀ w, ∃ z, p (c w) = apm_t97A03_baseCircle A B z) :
    Function.Injective
      (apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_map
        d c hn0 hs0 hn1 hs1) := by
  classical
  have hAB : A ≠ B := by
    intro hAB
    have hbase : apm_t97A03_baseSphere A B apm_t97A03_north =
        apm_t97A03_baseSphere A B apm_t97A03_south := by
      rw [← apm_t97A03_baseCircle_A, ← apm_t97A03_baseCircle_B, hAB]
    have hp0 : p (c apm_t97A03_circleOne) =
        apm_t97A03_baseSphere A B apm_t97A03_north := by
      rw [hn0, d.sphere_lifts]
    have hpi : p (c apm_t97A03_circleI) =
        apm_t97A03_baseSphere A B apm_t97A03_north := by
      rw [hs0, d.sphere_lifts, ← hbase]
    have hpn : p (c apm_t97A03_circleNegOne) =
        apm_t97A03_baseSphere A B apm_t97A03_north := by
      rw [hn1, d.sphere_lifts]
    obtain ⟨i0, hi0, -⟩ := d.sphere_unique hp0
    obtain ⟨ii, hii, -⟩ := d.sphere_unique hpi
    obtain ⟨ineg, hineg, -⟩ := d.sphere_unique hpn
    have h0i : i0 ≠ ii := by
      intro e
      have hc_eq : c apm_t97A03_circleOne = c apm_t97A03_circleI :=
        hi0.symm.trans (e ▸ hii)
      have heq := hcinj hc_eq
      have hv := congrArg Subtype.val heq
      norm_num [apm_t97A03_circleOne, apm_t97A03_circleI] at hv
      have hv' := congrArg Complex.re hv
      norm_num at hv'
    have h0n : i0 ≠ ineg := by
      intro e
      have hc_eq : c apm_t97A03_circleOne = c apm_t97A03_circleNegOne :=
        hi0.symm.trans (e ▸ hineg)
      have heq := hcinj hc_eq
      have hv := congrArg Subtype.val heq
      norm_num [apm_t97A03_circleOne, apm_t97A03_circleNegOne] at hv
    have hin' : ii = ineg := by
      fin_cases i0 <;> fin_cases ii <;> fin_cases ineg <;> simp_all
    have hc_eq : c apm_t97A03_circleI = c apm_t97A03_circleNegOne :=
      hii.symm.trans (hin' ▸ hineg)
    have heq := hcinj hc_eq
    have hv := congrArg Subtype.val heq
    norm_num [apm_t97A03_circleI, apm_t97A03_circleNegOne] at hv
    have hv' := congrArg Complex.im hv
    norm_num at hv'
  have hNS : apm_t97A03_north ≠ apm_t97A03_south := by
    intro h
    have hv := congrArg (fun z : apm_t97A03_S2 => z.1 (2 : Fin 3)) h
    norm_num [apm_t97A03_north, apm_t97A03_south,
      EuclideanSpace.single_apply] at hv
  have hmix (i : Fin 2) (z : apm_t97A03_S2) (w : Circle)
      (he : d.sphere i z = c w) :
      (Quotient.mk _ (.inl (i, z)) : apm_t97A03_OneCircleCover) =
        Quotient.mk _ (.inr w) := by
    obtain ⟨u, hu⟩ := hcrange w
    have hb : apm_t97A03_baseSphere A B z =
        apm_t97A03_baseCircle A B u := by
      rw [← d.sphere_lifts i z, ← hu, he]
    have hnrm :=
      apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize_eq
        A B hAB hb
    by_cases ha : u = A
    · have hz : z = apm_t97A03_north := by
        simpa [ha,
          apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
          using hnrm
      subst z
      fin_cases i
      · have hw : w = apm_t97A03_circleOne := hcinj (he.symm.trans hn0.symm)
        subst w
        exact Quotient.sound (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.n0))
      · have hw : w = apm_t97A03_circleNegOne := hcinj (he.symm.trans hn1.symm)
        subst w
        exact Quotient.sound (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.n1))
    · by_cases hb' : u = B
      · have hz : z = apm_t97A03_south := by
          simpa [ha, hb', hAB.symm,
            apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
            using hnrm
        subst z
        obtain ⟨k, hk, hku⟩ := d.sphere_unique
          (d.sphere_lifts i apm_t97A03_south)
        fin_cases i
        · have hw : w = apm_t97A03_circleI := hcinj (he.symm.trans hs0.symm)
          subst w
          exact Quotient.sound (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.s0))
        · have hw : w = apm_t97A03_circleNegI := hcinj (he.symm.trans hs1.symm)
          subst w
          exact Quotient.sound (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.s1))
      · simp [ha, hb',
          apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
          at hnrm
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro x y hxy
  change
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw d c x =
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_raw d c y
    at hxy
  cases x with
  | inl iz =>
      cases y with
      | inl jz =>
          obtain ⟨i, z⟩ := iz
          obtain ⟨j, z'⟩ := jz
          change d.sphere i z = d.sphere j z' at hxy
          have hb : apm_t97A03_baseSphere A B z =
              apm_t97A03_baseSphere A B z' := by
            rw [← d.sphere_lifts i z, ← d.sphere_lifts j z', hxy]
          have hnrm :=
            apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize_eq
              A B hAB hb
          have hz : z = z' := by
            simpa [apm_t97A03_baseSphere,
              apm_t97A03_classify_aux_twoCircle_homeomorph_aux_descend_aux_decoder_aux_exact_aux_normalize]
              using hnrm
          subst z'
          obtain ⟨k, hk, hku⟩ := d.sphere_unique (d.sphere_lifts i z)
          have hij : i = j := (hku i rfl).trans (hku j hxy.symm).symm
          subst j
          rfl
      | inr w => exact hmix iz.1 iz.2 w hxy
  | inr w =>
      cases y with
      | inl jz => exact (hmix jz.1 jz.2 w hxy.symm).symm
      | inr w' =>
          change c w = c w' at hxy
          rw [hcinj hxy]

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
  constructor
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_firstSwap_aux_geometric_aux_decoder_aux_exact_aux_injective
        A B Y p d c hn0 hs0 hn1 hs1 hcinj hcrange
  · intro y
    rcases apm_t97A03_baseCircle_or_baseSphere A B (p y) with
      ⟨z, hz⟩ | ⟨z, hz⟩
    · obtain ⟨w, hw⟩ := hcover y z hz
      exact ⟨Quotient.mk _ (.inr w), hw⟩
    · obtain ⟨i, hi, -⟩ := d.sphere_unique hz
      exact ⟨Quotient.mk _ (.inl (i, z)), hi⟩

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
theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_paste
    (A B : Circle)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
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
    ∃ c : Circle → Y, Continuous c ∧
      (∀ t ∈ Set.Icc 0 (2 * Real.pi),
        c (Circle.exp t) = apm_t97A03_quarterPasteRaw
          ![d.first 0, fun s ↦ d.second 1 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩,
            d.first 1, fun s ↦ d.second 0 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩] t) ∧
      c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north ∧
      c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south ∧
      c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north ∧
      c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south := by
  let σ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩
  let g : Fin 4 → Set.Icc (0 : ℝ) 1 → Y :=
    ![d.first 0, d.second 1 ∘ σ, d.first 1, d.second 0 ∘ σ]
  have hσ : Continuous σ := by
    apply Continuous.subtype_mk
    fun_prop
  have hg : ∀ k, Continuous (g k) := by
    intro k
    fin_cases k
    · simpa [g] using d.continuous_first 0
    · simpa [g] using (d.continuous_second 1).comp hσ
    · simpa [g] using d.continuous_first 1
    · simpa [g] using (d.continuous_second 0).comp hσ
  rcases hendpoints with ⟨hs00, hs01, hs10, hs11, hf00, hf01, hf10, hf11⟩
  have h01 : g 0 1 = g 1 0 := by simpa [g, σ] using hf01.trans hs11.symm
  have h12 : g 1 1 = g 2 0 := by simpa [g, σ] using hs10.trans hf10.symm
  have h23 : g 2 1 = g 3 0 := by simpa [g, σ] using hf11.trans hs01.symm
  have h30 : g 3 1 = g 0 0 := by simpa [g, σ] using hs00.trans hf00.symm
  obtain ⟨c, hc, hraw, h0, h1, h2, h3⟩ :=
    apm_t97A03_quarterPaste_exists g hg h01 h12 h23 h30
  refine ⟨c, hc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [g, σ, Function.comp_def] using hraw
  · simpa [g] using h0.trans hf00
  · calc
      c apm_t97A03_circleI = g 1 0 := h1
      _ = d.sphere 0 apm_t97A03_south := by simpa [g, σ] using hs11
  · simpa [g] using h2.trans hf10
  · calc
      c apm_t97A03_circleNegI = g 3 0 := h3
      _ = d.sphere 1 apm_t97A03_south := by simpa [g, σ] using hs01

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_injective_aux_raw
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Circle → Y)
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw
        ![d.first 0, fun s ↦ d.second 1 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩,
          d.first 1, fun s ↦ d.second 0 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩] t) :
    Set.InjOn (fun t ↦ c (Circle.exp t)) (Set.Ico 0 (2 * Real.pi)) := by
  sorry

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_injective
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Circle → Y)
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw
        ![d.first 0, fun s ↦ d.second 1 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩,
          d.first 1, fun s ↦ d.second 0 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩] t) :
    Function.Injective c := by
  apply apm_t97A03_circleLiftIcc_injective (fun t ↦ c (Circle.exp t)) c
  · intro t ht
    rfl
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_injective_aux_raw
        A B hAB Y p hp d c hraw

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_range
    (A B : Circle)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Circle → Y)
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw
        ![d.first 0, fun s ↦ d.second 1 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩,
          d.first 1, fun s ↦ d.second 0 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩] t) :
    ∀ w, ∃ z, p (c w) = apm_t97A03_baseCircle A B z := by
  have hrep : ∀ z : Circle, ∃ t ∈ Set.Icc 0 (2 * Real.pi), Circle.exp t = z := by
    intro z
    refine ⟨toIcoMod Real.two_pi_pos 0 (Complex.arg (z : ℂ)), ?_, ?_⟩
    · have hm := toIcoMod_mem_Ico Real.two_pi_pos 0 (Complex.arg (z : ℂ))
      simpa using Set.mem_Icc.mpr ⟨hm.1, hm.2.le⟩
    · have hperiod : Function.Periodic Circle.exp (2 * Real.pi) := Circle.periodic_exp
      rw [toIcoMod, hperiod.sub_zsmul_eq, Circle.exp_arg]
  intro w
  obtain ⟨t, ht, rfl⟩ := hrep w
  rw [hraw t ht]
  unfold apm_t97A03_quarterPasteRaw
  split_ifs with h0 h1 h2
  · refine ⟨apm_t97A03_circleArc A B
        (Set.projIcc 0 1 zero_le_one (t / (Real.pi / 2))), ?_⟩
    change p (d.first 0 _) = _
    rw [d.first_lifts]
    rfl
  · refine ⟨apm_t97A03_complementaryCircleArc A B
        ⟨1 - Set.projIcc 0 1 zero_le_one ((t - Real.pi / 2) / (Real.pi / 2)),
          by
            have hs := (Set.projIcc 0 1 zero_le_one
              ((t - Real.pi / 2) / (Real.pi / 2))).property
            exact ⟨by linarith [hs.2], by linarith [hs.1]⟩⟩, ?_⟩
    change p (d.second 1 _) = _
    rw [d.second_lifts]
    rfl
  · refine ⟨apm_t97A03_circleArc A B
        (Set.projIcc 0 1 zero_le_one ((t - Real.pi) / (Real.pi / 2))), ?_⟩
    change p (d.first 1 _) = _
    rw [d.first_lifts]
    rfl
  · refine ⟨apm_t97A03_complementaryCircleArc A B
        ⟨1 - Set.projIcc 0 1 zero_le_one ((t - 3 * Real.pi / 2) / (Real.pi / 2)),
          by
            have hs := (Set.projIcc 0 1 zero_le_one
              ((t - 3 * Real.pi / 2) / (Real.pi / 2))).property
            exact ⟨by linarith [hs.2], by linarith [hs.1]⟩⟩, ?_⟩
    change p (d.second 0 _) = _
    rw [d.second_lifts]
    rfl

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_cover_aux_two
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Circle → Y)
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw
        ![d.first 0, fun s ↦ d.second 1 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩,
          d.first 1, fun s ↦ d.second 0 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩] t) :
    ∀ z, ∃ w₀ w₁, w₀ ≠ w₁ ∧
      p (c w₀) = apm_t97A03_baseCircle A B z ∧
      p (c w₁) = apm_t97A03_baseCircle A B z := by
  sorry

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_cover_aux_card
    (A B : Circle) (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (c : Circle → Y) (hinj : Function.Injective c)
    (htwo : ∀ z, ∃ w₀ w₁, w₀ ≠ w₁ ∧
      p (c w₀) = apm_t97A03_baseCircle A B z ∧
      p (c w₁) = apm_t97A03_baseCircle A B z) :
    ∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y := by
  intro y z hy
  obtain ⟨w₀, w₁, hne, h0, h1⟩ := htwo z
  have hc : c w₀ ≠ c w₁ := fun h => hne (hinj h)
  have hcard := hdegree (apm_t97A03_baseCircle A B z)
  rw [Nat.card_coe_set_eq, Set.ncard_eq_two] at hcard
  obtain ⟨a, b, hab, hS⟩ := hcard
  have m0 : c w₀ ∈ ({a, b} : Set Y) := hS ▸ (show c w₀ ∈ p ⁻¹' {apm_t97A03_baseCircle A B z} from h0)
  have m1 : c w₁ ∈ ({a, b} : Set Y) := hS ▸ (show c w₁ ∈ p ⁻¹' {apm_t97A03_baseCircle A B z} from h1)
  have my : y ∈ ({a, b} : Set Y) := hS ▸ (show y ∈ p ⁻¹' {apm_t97A03_baseCircle A B z} from hy)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m0 m1 my
  rcases my with rfl | rfl <;> rcases m0 with h0' | h0' <;> rcases m1 with h1' | h1'
  all_goals first
    | exact ⟨w₀, h0'⟩ | exact ⟨w₁, h1'⟩
    | exact absurd (h0'.trans h1'.symm) hc

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_cover
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B) (hp : IsCoveringMap p)
    (hdegree : ∀ x, Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (d : apm_t97A03_ClassifySheetData A B Y p)
    (c : Circle → Y)
    (hraw : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
      c (Circle.exp t) = apm_t97A03_quarterPasteRaw
        ![d.first 0, fun s ↦ d.second 1 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩,
          d.first 1, fun s ↦ d.second 0 ⟨1 - s, by constructor <;> linarith [s.property.1, s.property.2]⟩] t) :
    ∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y := by
  apply
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_cover_aux_card
      A B Y p hdegree c
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_injective
        A B hAB Y p hp d c hraw
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_cover_aux_two
        A B hAB Y p hp d c hraw

theorem apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste
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
    ∃ c : Circle → Y, Continuous c ∧ Function.Injective c ∧
      c apm_t97A03_circleOne = d.sphere 0 apm_t97A03_north ∧
      c apm_t97A03_circleI = d.sphere 0 apm_t97A03_south ∧
      c apm_t97A03_circleNegOne = d.sphere 1 apm_t97A03_north ∧
      c apm_t97A03_circleNegI = d.sphere 1 apm_t97A03_south ∧
      (∀ w, ∃ z, p (c w) = apm_t97A03_baseCircle A B z) ∧
      (∀ y z, p y = apm_t97A03_baseCircle A B z → ∃ w, c w = y) := by
  obtain ⟨c, hc, hraw, hn0, hs0, hn1, hs1⟩ :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_paste
      A B Y p d hendpoints
  refine ⟨c, hc, ?_, hn0, hs0, hn1, hs1, ?_, ?_⟩
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_injective
        A B hAB Y p hp d c hraw
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_range
        A B Y p d c hraw
  · exact
      apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste_aux_cover
        A B hAB Y p hp hdegree d c hraw

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
  obtain ⟨c, hc, hcinj, hn0, hs0, hn1, hs1, hcrange, hcover⟩ :=
    apm_t97A03_classify_aux_oneCircle_homeomorph_aux_descend_aux_secondSwap_aux_geometric_aux_decoder_aux_circlePaste
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

/-- Equality in a point wedge: two representatives have the same image exactly
when they are equal or both are wedge basepoints.  The shared tool for the
normal-form kernel, generator and surjectivity arguments. -/
theorem apm_t97A03_wedge_quotientMap_eq_iff {X Y : Type*} (x₀ : X) (y₀ : Y)
    (p q : Sum X Y) :
    quotientMap x₀ y₀ p = quotientMap x₀ y₀ q ↔
      p = q ∨ ((p = .inl x₀ ∨ p = .inr y₀) ∧ (q = .inl x₀ ∨ q = .inr y₀)) := by
  constructor
  · intro h
    have hr : Relation.EqvGen (Rel x₀ y₀) p q := Quotient.exact h
    clear h
    induction hr with
    | rel a b hab => cases hab; exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    | refl => exact Or.inl rfl
    | symm a b _ ih =>
        rcases ih with h | ⟨ha, hb⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨hb, ha⟩
    | trans a b c _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | ⟨ha, hb⟩
        · exact ih₂
        · rcases ih₂ with rfl | ⟨_, hc⟩
          · exact Or.inr ⟨ha, hb⟩
          · exact Or.inr ⟨ha, hc⟩
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · have hbase : quotientMap x₀ y₀ (.inl x₀) = quotientMap x₀ y₀ (.inr y₀) :=
        Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · rfl
      · exact hbase
      · exact hbase.symm
      · rfl

theorem apm_t97A03_wedge_ll {X Y : Type*} {x₀ : X} {y₀ : Y} {a b : X}
    (h : quotientMap x₀ y₀ (.inl a) = quotientMap x₀ y₀ (.inl b)) : a = b ∨ a = x₀ := by
  rcases (apm_t97A03_wedge_quotientMap_eq_iff x₀ y₀ _ _).mp h with h' | ⟨ha, -⟩
  · exact Or.inl (Sum.inl_injective h')
  · rcases ha with ha | ha
    · exact Or.inr (Sum.inl_injective ha)
    · cases ha

theorem apm_t97A03_wedge_rr {X Y : Type*} {x₀ : X} {y₀ : Y} {a b : Y}
    (h : quotientMap x₀ y₀ (.inr a) = quotientMap x₀ y₀ (.inr b)) : a = b ∨ a = y₀ := by
  rcases (apm_t97A03_wedge_quotientMap_eq_iff x₀ y₀ _ _).mp h with h' | ⟨ha, -⟩
  · exact Or.inl (Sum.inr_injective h')
  · rcases ha with ha | ha
    · cases ha
    · exact Or.inr (Sum.inr_injective ha)

theorem apm_t97A03_wedge_lr {X Y : Type*} {x₀ : X} {y₀ : Y} {a : X} {b : Y}
    (h : quotientMap x₀ y₀ (.inl a) = quotientMap x₀ y₀ (.inr b)) : a = x₀ ∧ b = y₀ := by
  rcases (apm_t97A03_wedge_quotientMap_eq_iff x₀ y₀ _ _).mp h with h' | ⟨ha, hb⟩
  · cases h'
  · refine ⟨?_, ?_⟩
    · rcases ha with ha | ha
      · exact Sum.inl_injective ha
      · cases ha
    · rcases hb with hb | hb
      · cases hb
      · exact Sum.inr_injective hb


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
  let f : ℝ → ι × Circle := fun t ↦ (w₀.1, w₀.2 * Circle.exp t)
  have hf : Continuous f := by
    exact continuous_const.prodMk (continuous_const.mul Circle.exp.continuous)
  have hf0 : f 0 = w₀ := by
    ext <;> simp [f]
  have hpre : f ⁻¹' U ∈ nhds (0 : ℝ) := by
    exact hf.continuousAt.preimage_mem_nhds (hUopen.mem_nhds (hf0 ▸ hwU))
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hpre
  let ε := min (r / 2) (Real.pi / 4)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_, ?_⟩
  · dsimp [ε]
    have : Real.pi / 4 < Real.pi / 2 := by linarith
    exact lt_of_le_of_lt (min_le_right _ _) this
  · intro w hw1 hwangle
    let t := apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2
    have htr : |t| < r := by
      have hle : |t| ≤ r / 2 := hwangle.trans (min_le_left _ _)
      linarith
    have hft : f t ∈ U := hrU (by simpa [Real.dist_eq] using htr)
    have hcircle : w₀.2 * Circle.exp t = w.2 := by
      change w₀.2 * Circle.exp (Complex.arg (((w₀.2⁻¹ * w.2 : Circle) : ℂ))) = w.2
      rw [Circle.exp_arg]
      simp
    rw [← Prod.eta w, hw1]
    simpa [f, t, hcircle] using hft

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
  intro x y hxy
  cases hxy with
  | att w y haw =>
      by_cases hw : w = w₀
      · subst w
        have hzero : apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w₀.2 = 0 := by
          simp [apm_t97A03_invariants_aux_slide_aux_angle]
        have hyz : y = z := Option.some.inj (haw.symm.trans hz)
        subst y
        have hhalf : 0 ≤ ε / 2 := by positivity
        simp [apm_t97A03_invariants_aux_slide_aux_detourRaw, hzero, hε.le, hhalf]
      · have ha'w : a' w = some y := by
          rw [← hsame w hw]
          exact haw
        have hoff : ¬ (w.1 = w₀.1 ∧
            |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε) := by
          rintro ⟨hw1, hwangle⟩
          exact hw (harc w hw1 hwangle (by simp [haw]))
        simp only [apm_t97A03_invariants_aux_slide_aux_detourRaw, hoff, if_false]
        exact Quotient.sound (Relation.EqvGen.rel _ _
          (apm_t97A03_invariants_aux_slide_GenRel.att w y ha'w))

/-- Continuity of the detour: the pieces agree at `|θ| = ε/2` (because `w₀` is
glued to `z'` in the target) and at `|θ| = ε`; the arc avoids the cut of `arg`. -/
theorem apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_angle
    (c₀ : Circle) :
    ContinuousOn (apm_t97A03_invariants_aux_slide_aux_angle c₀)
      {c : Circle | |apm_t97A03_invariants_aux_slide_aux_angle c₀ c| ≤ Real.pi / 2} := by
  intro c hc
  apply (Complex.continuousAt_arg ?_).comp_continuousWithinAt
    ((continuous_subtype_val.comp (continuous_const.mul continuous_id)).continuousWithinAt)
  rw [Complex.mem_slitPlane_iff]
  have hre : 0 ≤ (((c₀⁻¹ * c : Circle) : ℂ)).re :=
    Complex.abs_arg_le_pi_div_two_iff.mp hc
  have hne : ((c₀⁻¹ * c : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rcases lt_or_eq_of_le hre with hre | hre
  · exact Or.inl hre
  · exact Or.inr (by
    intro him
    apply hne
    exact Complex.ext hre.symm him)

theorem apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_inactive
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a' : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z} (i : ι) (hi : i ≠ w₀.1)
    ( γ : Path z z') ( ε : ℝ) :
    Continuous (fun c ↦ apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε (.inr (i, c))) := by
  simpa only [apm_t97A03_invariants_aux_slide_aux_detourRaw, hi, false_and, if_false] using
    (continuous_coinduced_rng.comp (continuous_inr.comp (continuous_const.prodMk continuous_id)))

theorem apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_active_aux_pinched (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun θ : ℝ => Real.sign θ * max 0 (2 * |θ| - ε)) := by
  classical
  have h : Continuous (fun θ : ℝ => if θ ≤ 0 then
      -max 0 (-2 * θ - ε) else max 0 (2 * θ - ε)) := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    intro θ hθ
    change θ = 0 at hθ
    subst θ
    simp [max_eq_left (by linarith : -ε ≤ 0)]
  convert h using 1
  funext θ
  rcases lt_trichotomy θ 0 with ht | ht | ht
  · simp [Real.sign_of_neg ht, abs_of_neg ht, le_of_lt ht]
  · subst θ; simp [max_eq_left (by linarith : -ε ≤ 0)]
  · simp [Real.sign_of_pos ht, abs_of_pos ht, not_le.mpr ht]

theorem apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_active
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a' : ι × Circle → Option Z) (w₀ : ι × Circle) (z z' : Z) (hz' : a' w₀ = some z')
    (γ : Path z z') (ε : ℝ) (hε : 0 < ε) (hεπ : ε < Real.pi / 2)
    (hangle : ContinuousOn (apm_t97A03_invariants_aux_slide_aux_angle w₀.2)
      {c : Circle | |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 c| ≤ Real.pi / 2}) :
    Continuous (fun c ↦ apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε (.inr (w₀.1, c))) := by
  classical
  let F := fun c ↦ apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε (.inr (w₀.1, c))
  have hr : ContinuousOn F {c : Circle | 0 ≤ ((w₀.2⁻¹ * c : Circle) : ℂ).re} := by
    rw [continuousOn_iff_continuous_restrict]
    let R := {c : Circle | 0 ≤ ((w₀.2⁻¹ * c : Circle) : ℂ).re}
    let θ : R → ℝ := fun p => apm_t97A03_invariants_aux_slide_aux_angle w₀.2 p.1
    have hθ : Continuous θ := by
      exact hangle.comp_continuous continuous_subtype_val
        (fun p => Complex.abs_arg_le_pi_div_two_iff.mpr p.2)
    let B : R → ℝ := fun p => Real.sign (θ p) * max 0 (2 * |θ p| - ε)
    have hb : Continuous B := (apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_active_aux_pinched ε hε).comp hθ
    let f : R → Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a')) :=
      fun p => Quotient.mk _ (.inl (γ.extend (2 * |θ p| / ε)))
    let g : R → Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a')) :=
      fun p => Quotient.mk _ (.inr (w₀.1, w₀.2 * Circle.exp (B p)))
    let d : R → Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a')) :=
      fun p => Quotient.mk _ (.inr (w₀.1, p.1))
    have hf : Continuous f := continuous_quot_mk.comp (continuous_inl.comp
      (γ.continuous_extend.comp ((continuous_const.mul hθ.abs).div_const ε)))
    have hg : Continuous g := continuous_quot_mk.comp (continuous_inr.comp
      (continuous_const.prodMk (continuous_const.mul (Circle.exp.continuous.comp hb))))
    have hd : Continuous d := continuous_quot_mk.comp (continuous_inr.comp
      (continuous_const.prodMk continuous_subtype_val))
    have hfg := hf.if_le hg hθ.abs (continuous_const : Continuous (fun _ : R => ε / 2)) (fun p hp => by
      have ht : 2 * |θ p| / ε = 1 := by rw [hp]; field_simp
      have hB : B p = 0 := by
        dsimp [B]
        rw [hp]
        have he : 2 * (ε / 2) - ε = 0 := by ring
        rw [he]
        simp
      dsimp [f, g]
      rw [ht, Path.extend_one, hB, Circle.exp_zero, mul_one]
      exact (Quotient.sound (Relation.EqvGen.rel _ _ (.att w₀ z' hz'))).symm)
    have hfull := hfg.if_le hd hθ.abs (continuous_const : Continuous (fun _ : R => ε)) (fun p hp => by
      have hnot : ¬ |θ p| ≤ ε / 2 := by rw [hp]; linarith
      simp only [hnot, if_false]
      have hm : max 0 (2 * |θ p| - ε) = ε := by
        rw [hp]
        have he : 2 * ε - ε = ε := by ring
        rw [he, max_eq_right (le_of_lt hε)]
      have hs : Real.sign (θ p) * ε = θ p := by
        rw [← hp]
        rcases lt_trichotomy (θ p) 0 with h | h | h
        · simp [Real.sign_of_neg h, abs_of_neg h]
        · simp [h]
        · simp [Real.sign_of_pos h, abs_of_pos h]
      dsimp [g, d, B]
      rw [hm, hs]
      have hcirc : w₀.2 * Circle.exp (θ p) = p.1 := by
        change w₀.2 * Circle.exp (Complex.arg ((w₀.2⁻¹ * p.1 : Circle) : ℂ)) = p.1
        rw [Circle.exp_arg]
        simp
      rw [hcirc])
    convert hfull using 1
    funext p
    dsimp [F, apm_t97A03_invariants_aux_slide_aux_detourRaw, f, g, d, B]
    simp only [true_and]
    split_ifs with h hinner
    · rfl
    · rw [max_eq_right (by dsimp [θ] at hinner ⊢; linarith)]
    · rfl
  have hl : ContinuousOn F {c : Circle | ((w₀.2⁻¹ * c : Circle) : ℂ).re ≤ 0} := by
    have hc : Continuous (fun c : Circle =>
        (Quotient.mk _ (.inr (w₀.1, c)) : Quotient
          (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a')))) :=
      continuous_quot_mk.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))
    apply hc.continuousOn.congr
    intro c hc
    have hout : ¬ |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 c| ≤ ε := by
      intro h
      have hr := Complex.abs_arg_lt_pi_div_two_iff.mp (lt_of_le_of_lt h hεπ)
      rcases hr with hr | hr
      · exact (not_lt_of_ge hc) hr
      · exact (w₀.2⁻¹ * c).coe_ne_zero hr
    simp [F, apm_t97A03_invariants_aux_slide_aux_detourRaw, hout]
  have hc : Continuous (fun c : Circle => ((w₀.2⁻¹ * c : Circle) : ℂ).re) := by fun_prop
  have h := hr.union_of_isClosed hl
    (isClosed_le continuous_const hc) (isClosed_le hc continuous_const)
  have hu : {c : Circle | 0 ≤ ((w₀.2⁻¹ * c : Circle) : ℂ).re} ∪
      {c | ((w₀.2⁻¹ * c : Circle) : ℂ).re ≤ 0} = Set.univ := by
    ext c
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total _ _
  rw [hu] at h
  exact continuousOn_univ.mp h

theorem apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a' : ι × Circle → Option Z) (w₀ : ι × Circle) (z z' : Z) (hz' : a' w₀ = some z')
    (γ : Path z z') (ε : ℝ) (hε : 0 < ε) (hεπ : ε < Real.pi / 2) :
    Continuous (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε) := by
  apply continuous_sum_dom.mpr
  constructor
  · show Continuous (fun y : Z ↦
      (_root_.Quotient.mk _ (.inl y) : _root_.Quotient
        (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a'))))
    exact continuous_coinduced_rng.comp continuous_inl
  · rw [continuous_prod_of_discrete_left]
    intro i
    by_cases hi : i = w₀.1
    · subst i
      exact apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_active
        a' w₀ z z' hz' γ ε hε hεπ
        (apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_angle w₀.2)
    · exact apm_t97A03_invariants_aux_slide_aux_detourRaw_continuous_aux_inactive
        a' w₀ i hi γ ε

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

/-- The first deformation shrinks the triangular path parameter to zero.
The unequal slopes record the two successive half-arc detours. -/
noncomputable def apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z}
    (γ : Path z z') (ε : ℝ) (p : unitInterval × Sum Z (ι × Circle)) :
    Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)) := by
  classical
  exact match p.2 with
  | .inl y => Quotient.mk _ (.inl y)
  | .inr w =>
    let θ := apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2
    if w.1 = w₀.1 ∧ |θ| ≤ ε then
      if |θ| ≤ 3 * ε / 4 then
        Quotient.mk _ (.inl (γ.extend ((1 - (p.1 : ℝ)) *
          min (2 * |θ| / ε) (3 - 4 * |θ| / ε))))
      else Quotient.mk _ (.inr (w.1, w₀.2 * Circle.exp
        (Real.sign θ * (4 * |θ| - 3 * ε))))
    else Quotient.mk _ (.inr w)

/-- The second deformation linearly removes the pinched circle interval. -/
noncomputable def apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) (ε : ℝ)
    (p : unitInterval × Sum Z (ι × Circle)) :
    Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)) := by
  classical
  exact match p.2 with
  | .inl y => Quotient.mk _ (.inl y)
  | .inr w =>
    let θ := apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2
    if w.1 = w₀.1 ∧ |θ| ≤ ε then
      Quotient.mk _ (.inr (w.1, w₀.2 * Circle.exp
        ((1 - (p.1 : ℝ)) * (Real.sign θ * max 0 (4 * |θ| - 3 * ε)) +
          (p.1 : ℝ) * θ)))
    else Quotient.mk _ (.inr w)

/-- Glue along radii `3ε/4` and `ε`; the first seam is attached to `z`.
The angular chart is used only on a closed arc avoiding its branch cut.
For a closed-cover proof, split the relative circle into the right and left
semicircles. On the right semicircle `arg` is continuous, and closed pasting
at the two radii applies. On the left semicircle the map is the original
quotient map, since `ε < π/2`. The loop parameter has value zero at `3ε/4`;
at `ε` the stretched angle is the original angle. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_paste
    {ι Z Q : Type} [TopologicalSpace ι] [DiscreteTopology ι]
    [TopologicalSpace Z] [TopologicalSpace Q]
    (F : unitInterval × Sum Z (ι × Circle) → Q) (c₀ : Circle)
    (hZ : Continuous (fun p : unitInterval × Z => F (p.1, .inl p.2)))
    (hr : ∀ i, ContinuousOn (fun p : unitInterval × Circle => F (p.1, .inr (i, p.2)))
      {p | 0 ≤ ((c₀⁻¹ * p.2 : Circle) : ℂ).re})
    (hl : ∀ i, ContinuousOn (fun p : unitInterval × Circle => F (p.1, .inr (i, p.2)))
      {p | ((c₀⁻¹ * p.2 : Circle) : ℂ).re ≤ 0}) : Continuous F := by
  have hc : Continuous (fun p : unitInterval × Circle =>
      ((c₀⁻¹ * p.2 : Circle) : ℂ).re) := by fun_prop
  have hi (i : ι) : Continuous (fun p : unitInterval × Circle =>
      F (p.1, .inr (i, p.2))) := by
    have h := (hr i).union_of_isClosed (hl i)
      (isClosed_le continuous_const hc) (isClosed_le hc continuous_const)
    have hu : {p : unitInterval × Circle | 0 ≤ ((c₀⁻¹ * p.2 : Circle) : ℂ).re} ∪
        {p | ((c₀⁻¹ * p.2 : Circle) : ℂ).re ≤ 0} = Set.univ := by
      ext p
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_total _ _
    rw [hu] at h
    exact continuousOn_univ.mp h
  have hC : Continuous (fun p : unitInterval × (ι × Circle) => F (p.1, .inr p.2)) := by
    have h : Continuous (fun p : (unitInterval × Circle) × ι =>
        F (p.1.1, .inr (p.2, p.1.2))) := continuous_prod_of_discrete_right.mpr hi
    exact h.comp ((continuous_fst.prodMk (continuous_snd.snd)).prodMk continuous_snd.fst)
  have hh := (hZ.sumElim hC).comp (Homeomorph.prodSumDistrib.continuous)
  convert hh using 1
  funext p
  rcases p with ⟨t, y | w⟩ <;> rfl

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_pinched (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun θ : ℝ => Real.sign θ * max 0 (4 * |θ| - 3 * ε)) := by
  classical
  have h : Continuous (fun θ : ℝ => if θ ≤ 0 then
      -max 0 (-4 * θ - 3 * ε) else max 0 (4 * θ - 3 * ε)) := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    intro θ hθ
    change θ = 0 at hθ
    subst θ
    simp [max_eq_left (by linarith : -(3 * ε) ≤ 0)]
  convert h using 1
  funext θ
  rcases lt_trichotomy θ 0 with ht | ht | ht
  · simp [Real.sign_of_neg ht, abs_of_neg ht, le_of_lt ht]
  · subst θ; simp [max_eq_left (by linarith : -(3 * ε) ≤ 0)]
  · simp [Real.sign_of_pos ht, abs_of_pos ht, not_le.mpr ht]

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_angle (c₀ : Circle) :
    Continuous (fun p : {p : unitInterval × Circle |
      0 ≤ ((c₀⁻¹ * p.2 : Circle) : ℂ).re} =>
      apm_t97A03_invariants_aux_slide_aux_angle c₀ p.1.2) := by
  have hc : Continuous (fun p : {p : unitInterval × Circle |
      0 ≤ ((c₀⁻¹ * p.2 : Circle) : ℂ).re} => ((c₀⁻¹ * p.1.2 : Circle) : ℂ)) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro p
  have hs : ((c₀⁻¹ * p.1.2 : Circle) : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff_arg.mpr
    refine ⟨?_, (c₀⁻¹ * p.1.2).coe_ne_zero⟩
    have h := Complex.abs_arg_le_pi_div_two_iff.mpr p.2
    intro he
    rw [he, abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_pos]
  exact (Complex.continuousAt_arg hs).comp
    (f := fun q : {p : unitInterval × Circle |
      0 ≤ ((c₀⁻¹ * p.2 : Circle) : ℂ).re} => ((c₀⁻¹ * q.1.2 : Circle) : ℂ))
    (x := p) hc.continuousAt

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_right
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z}
    (hz : a w₀ = some z) (γ : Path z z') (ε : ℝ)
    (hε : 0 < ε) (hεπ : ε < Real.pi / 2) (i : ι) :
    ContinuousOn (fun p : unitInterval × Circle =>
      apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (p.1, .inr (i, p.2)))
      {p | 0 ≤ ((w₀.2⁻¹ * p.2 : Circle) : ℂ).re} := by
  classical
  by_cases hi : i = w₀.1
  · rw [continuousOn_iff_continuous_restrict]
    let R := {p : unitInterval × Circle | 0 ≤ ((w₀.2⁻¹ * p.2 : Circle) : ℂ).re}
    let θ : R → ℝ := fun p => apm_t97A03_invariants_aux_slide_aux_angle w₀.2 p.1.2
    let B : R → ℝ := fun p => Real.sign (θ p) * max 0 (4 * |θ p| - 3 * ε)
    have hθ : Continuous θ := apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_angle w₀.2
    have ht : Continuous (fun p : R => (p.1.1 : ℝ)) := by fun_prop
    have hb : Continuous B := (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_pinched ε hε).comp hθ
    let f : R → Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)) :=
      fun p => Quotient.mk _ (.inl (γ.extend ((1 - (p.1.1 : ℝ)) *
        min (2 * |θ p| / ε) (3 - 4 * |θ p| / ε))))
    let g : R → Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)) :=
      fun p => Quotient.mk _ (.inr (i, w₀.2 * Circle.exp (B p)))
    let d : R → Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)) :=
      fun p => Quotient.mk _ (.inr (i, p.1.2))
    have hf : Continuous f := by
      apply continuous_quot_mk.comp
      apply continuous_inl.comp
      apply γ.continuous_extend.comp
      exact (continuous_const.sub ht).mul
        (((continuous_const.mul hθ.abs).div_const ε).min
          (continuous_const.sub ((continuous_const.mul hθ.abs).div_const ε)))
    have hg : Continuous g := continuous_quot_mk.comp (continuous_inr.comp
      (continuous_const.prodMk (continuous_const.mul (Circle.exp.continuous.comp hb))))
    have hd : Continuous d := continuous_quot_mk.comp (continuous_inr.comp
      (continuous_const.prodMk (continuous_snd.comp continuous_subtype_val)))
    have hfg := hf.if_le hg hθ.abs (continuous_const : Continuous (fun _ : R => 3 * ε / 4)) (fun p hp => by
      have hz0 : 3 - 4 * |θ p| / ε = 0 := by rw [hp]; field_simp; ring
      have hm : min (2 * |θ p| / ε) (3 - 4 * |θ p| / ε) = 0 := by
        rw [hz0, min_eq_right]; positivity
      have hB : B p = 0 := by
        dsimp [B]
        rw [hp]
        have he : 4 * (3 * ε / 4) - 3 * ε = 0 := by ring
        rw [he]
        simp
      dsimp [f, g]
      rw [hm, mul_zero, Path.extend_zero, hB, Circle.exp_zero, mul_one, hi]
      exact (Quotient.sound (Relation.EqvGen.rel _ _ (.att w₀ z hz))).symm)
    have hfull := hfg.if_le hd hθ.abs (continuous_const : Continuous (fun _ : R => ε)) (fun p hp => by
      have hnot : ¬ |θ p| ≤ 3 * ε / 4 := by rw [hp]; linarith
      simp only [hnot, if_false]
      have hm : max 0 (4 * |θ p| - 3 * ε) = ε := by
        rw [hp]
        have he : 4 * ε - 3 * ε = ε := by ring
        rw [he, max_eq_right (le_of_lt hε)]
      have hs : Real.sign (θ p) * ε = θ p := by
        rw [← hp]
        rcases lt_trichotomy (θ p) 0 with h | h | h
        · simp [Real.sign_of_neg h, abs_of_neg h]
        · simp [h]
        · simp [Real.sign_of_pos h, abs_of_pos h]
      dsimp [g, d, B]
      rw [hm, hs]
      have hcirc : w₀.2 * Circle.exp (θ p) = p.1.2 := by
        change w₀.2 * Circle.exp (Complex.arg ((w₀.2⁻¹ * p.1.2 : Circle) : ℂ)) = p.1.2
        rw [Circle.exp_arg]
        simp
      rw [hcirc])
    convert hfull using 1
    funext p
    dsimp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne, f, g, d, B]
    simp only [hi, true_and]
    split_ifs with h hinner
    · rfl
    · rw [max_eq_right (by dsimp [θ] at hinner ⊢; linarith)]
    · rfl
  · have hc : Continuous (fun p : unitInterval × Circle =>
        (Quotient.mk _ (.inr (i, p.2)) : Quotient
          (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)))) :=
      continuous_quot_mk.comp (continuous_inr.comp (continuous_const.prodMk continuous_snd))
    simpa [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne, hi] using hc.continuousOn

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_left
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z}
    (hz : a w₀ = some z) (γ : Path z z') (ε : ℝ)
    (hε : 0 < ε) (hεπ : ε < Real.pi / 2) (i : ι) :
    ContinuousOn (fun p : unitInterval × Circle =>
      apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (p.1, .inr (i, p.2)))
      {p | ((w₀.2⁻¹ * p.2 : Circle) : ℂ).re ≤ 0} := by
  have hc : Continuous (fun p : unitInterval × Circle =>
      (Quotient.mk _ (.inr (i, p.2)) : Quotient
        (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)))) :=
    continuous_quot_mk.comp (continuous_inr.comp (continuous_const.prodMk continuous_snd))
  apply hc.continuousOn.congr
  intro p hp
  have hout : ¬ |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 p.2| ≤ ε := by
    intro h
    have hr := Complex.abs_arg_lt_pi_div_two_iff.mp (lt_of_le_of_lt h hεπ)
    rcases hr with hr | hr
    · exact (not_lt_of_ge hp) hr
    · exact (w₀.2⁻¹ * p.2).coe_ne_zero hr
  simp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne, hout]

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z}
    (hz : a w₀ = some z) (γ : Path z z') (ε : ℝ)
    (hε : 0 < ε) (hεπ : ε < Real.pi / 2) :
    Continuous (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε) := by
  apply apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_paste _ w₀.2
  · change Continuous (fun p : unitInterval × Z =>
      (Quotient.mk _ (.inl p.2) : Quotient
        (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a))))
    exact continuous_quot_mk.comp (continuous_inl.comp continuous_snd)
  · exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_right a w₀ hz γ ε hε hεπ
  · exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_left a w₀ hz γ ε hε hεπ

/-- The pinched angular coordinate is continuous, including at angle zero,
and equals the original angle at the boundary of the supporting arc.
The signed maximum vanishes on a neighbourhood of zero, so the apparent
jump of `Real.sign` causes no discontinuity. As in stage one, use the right
semicircle for the angular chart and the unchanged left semicircle to avoid
the branch cut. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo_continuous_aux_right
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) (ε : ℝ)
    (hε : 0 < ε) (hεπ : ε < Real.pi / 2) (i : ι) :
    ContinuousOn (fun p : unitInterval × Circle =>
      apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo a w₀ ε (p.1, .inr (i, p.2)))
      {p | 0 ≤ ((w₀.2⁻¹ * p.2 : Circle) : ℂ).re} := by
  classical
  by_cases hi : i = w₀.1
  · rw [continuousOn_iff_continuous_restrict]
    let R := {p : unitInterval × Circle | 0 ≤ ((w₀.2⁻¹ * p.2 : Circle) : ℂ).re}
    let θ : R → ℝ := fun p => apm_t97A03_invariants_aux_slide_aux_angle w₀.2 p.1.2
    have hθ : Continuous θ := apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_angle w₀.2
    have ht : Continuous (fun p : R => (p.1.1 : ℝ)) := by fun_prop
    have hb := (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_pinched ε hε).comp hθ
    have hc : Continuous (fun p : R =>
        (Quotient.mk _ (.inr (i, w₀.2 * Circle.exp
          ((1 - (p.1.1 : ℝ)) * (Real.sign (θ p) * max 0 (4 * |θ p| - 3 * ε)) +
            (p.1.1 : ℝ) * θ p))) : Quotient
          (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)))) := by
      apply continuous_quot_mk.comp
      apply continuous_inr.comp
      apply continuous_const.prodMk
      exact continuous_const.mul (Circle.exp.continuous.comp
        (((continuous_const.sub ht).mul hb).add (ht.mul hθ)))
    have hd : Continuous (fun p : R =>
        (Quotient.mk _ (.inr (i, p.1.2)) : Quotient
          (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)))) := by
      exact continuous_quot_mk.comp (continuous_inr.comp
        (continuous_const.prodMk (continuous_snd.comp continuous_subtype_val)))
    have hh := hc.if_le hd hθ.abs (continuous_const : Continuous (fun _ : R => ε)) (fun p hp => by
      have hm : max 0 (4 * |θ p| - 3 * ε) = ε := by
        rw [hp]
        have he : 4 * ε - 3 * ε = ε := by ring
        rw [he, max_eq_right (le_of_lt hε)]
      have hs : Real.sign (θ p) * ε = θ p := by
        rw [← hp]
        rcases lt_trichotomy (θ p) 0 with h | h | h
        · simp [Real.sign_of_neg h, abs_of_neg h]
        · simp [h]
        · simp [Real.sign_of_pos h, abs_of_pos h]
      rw [hm, hs]
      have he : (1 - (p.1.1 : ℝ)) * θ p + (p.1.1 : ℝ) * θ p = θ p := by ring
      rw [he]
      have hcirc : w₀.2 * Circle.exp (θ p) = p.1.2 := by
        change w₀.2 * Circle.exp (Complex.arg ((w₀.2⁻¹ * p.1.2 : Circle) : ℂ)) = p.1.2
        rw [Circle.exp_arg]
        simp
      rw [hcirc])
    simpa [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo, hi, θ] using hh
  · have hc : Continuous (fun p : unitInterval × Circle =>
        (Quotient.mk _ (.inr (i, p.2)) : Quotient
          (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)))) :=
      continuous_quot_mk.comp (continuous_inr.comp (continuous_const.prodMk continuous_snd))
    simpa [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo, hi] using hc.continuousOn

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo_continuous_aux_left
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) (ε : ℝ)
    (hε : 0 < ε) (hεπ : ε < Real.pi / 2) (i : ι) :
    ContinuousOn (fun p : unitInterval × Circle =>
      apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo a w₀ ε (p.1, .inr (i, p.2)))
      {p | ((w₀.2⁻¹ * p.2 : Circle) : ℂ).re ≤ 0} := by
  have hc : Continuous (fun p : unitInterval × Circle =>
      (Quotient.mk _ (.inr (i, p.2)) : Quotient
        (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a)))) :=
    continuous_quot_mk.comp (continuous_inr.comp (continuous_const.prodMk continuous_snd))
  apply hc.continuousOn.congr
  intro p hp
  have hout : ¬ |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 p.2| ≤ ε := by
    intro h
    have hr := Complex.abs_arg_lt_pi_div_two_iff.mp (lt_of_le_of_lt h hεπ)
    rcases hr with hr | hr
    · exact (not_lt_of_ge hp) hr
    · exact (w₀.2⁻¹ * p.2).coe_ne_zero hr
  simp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo, hout]

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo_continuous
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) (ε : ℝ)
    (hε : 0 < ε) (hεπ : ε < Real.pi / 2) :
    Continuous (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo a w₀ ε) := by
  apply apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous_aux_paste _ w₀.2
  · change Continuous (fun p : unitInterval × Z =>
      (Quotient.mk _ (.inl p.2) : Quotient
        (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a))))
    exact continuous_quot_mk.comp (continuous_inl.comp continuous_snd)
  · exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo_continuous_aux_right a w₀ ε hε hεπ
  · exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo_continuous_aux_left a w₀ ε hε hεπ

/-- Both deformations fix every attached representative in the quotient. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_respects
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z}
    (hz : a w₀ = some z) (γ : Path z z') (ε : ℝ) (hε : 0 < ε)
    (harc : ∀ w : ι × Circle, w.1 = w₀.1 →
      |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε →
      (a w).isSome → w = w₀) :
    ∀ t x y, apm_t97A03_invariants_aux_slide_GenRel a x y →
      apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (t, x) = apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (t, y) ∧
      apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo a w₀ ε (t, x) = apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo a w₀ ε (t, y) := by
  classical
  intro t x y h
  cases h with
  | att w y hy =>
    by_cases hw : w = w₀
    · subst w
      have hyz : y = z := Option.some.inj (hy.symm.trans hz)
      subst y
      have he : (0 : ℝ) ≤ ε := le_of_lt hε
      have he' : (0 : ℝ) ≤ 3 * ε / 4 := by positivity
      have hq : (Quotient.mk _ (.inr w₀) :
          Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a))) =
          Quotient.mk _ (.inl z) :=
        Quotient.sound (Relation.EqvGen.rel _ _ (.att w₀ z hz))
      constructor
      · simp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne, apm_t97A03_invariants_aux_slide_aux_angle,
          he, he', Path.extend_zero]
      · simpa [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo, apm_t97A03_invariants_aux_slide_aux_angle] using hq
    · have hout : ¬ (w.1 = w₀.1 ∧
          |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε) := by
        intro h
        exact hw (harc w h.1 h.2 (by simp [hy]))
      have hq : (Quotient.mk _ (.inr w) :
          Quotient (Relation.EqvGen.setoid (apm_t97A03_invariants_aux_slide_GenRel a))) =
          Quotient.mk _ (.inl y) :=
        Quotient.sound (Relation.EqvGen.rel _ _ (.att w y hy))
      constructor <;> simpa [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne, apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo, hout] using hq


/-- The two explicit stages meet at the pinched-circle map. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_seam
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) {z z' : Z}
    (hz : a w₀ = some z) (γ : Path z z') (ε : ℝ) (hε : 0 < ε)
    (x : Sum Z (ι × Circle)) :
    apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (1, x) = apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo a w₀ ε (0, x) := by
  classical
  cases x with
  | inl y => rfl
  | inr w =>
    unfold apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo
    dsimp only
    split_ifs with h hinner
    · have hm : max 0 (4 * |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| -
          3 * ε) = 0 := max_eq_left (by linarith)
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero, sub_self, zero_mul,
        Path.extend_zero, hm, mul_zero, sub_zero, one_mul, add_zero, Circle.exp_zero, mul_one]
      have hw : (w.1, w₀.2) = w₀ := Prod.ext h.1 rfl
      rw [hw]
      exact (Quotient.sound (Relation.EqvGen.rel _ _ (.att w₀ z hz))).symm
    · have hm : max 0 (4 * |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| -
          3 * ε) = 4 * |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| -
          3 * ε := max_eq_right (by linarith)
      simp [hm]
    · rfl


/-- The second stage ends at the literal quotient map. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_finish
    {ι Z : Type} [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace Z]
    (a : ι × Circle → Option Z) (w₀ : ι × Circle) (ε : ℝ)
    (x : Sum Z (ι × Circle)) :
    apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo a w₀ ε (1, x) = Quotient.mk _ x := by
  classical
  cases x with
  | inl y => rfl
  | inr w =>
    simp only [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    split_ifs
    · rw [apm_t97A03_invariants_aux_slide_aux_angle, Circle.exp_arg]
      simp
    · rfl

/-- Quotient descent into the space of paths avoids any product-quotient assumption. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_descend
    {X Q : Type} [TopologicalSpace X] [TopologicalSpace Q]
    (r : X → X → Prop) (H : unitInterval × X → Q) (hc : Continuous H)
    (hr : ∀ t x y, r x y → H (t, x) = H (t, y)) :
    ∃ F : C(Quotient (Relation.EqvGen.setoid r), C(unitInterval, Q)),
      ∀ x t, F (Quotient.mk _ x) t = H (t, x) := by
  let K : C(X, C(unitInterval, Q)) :=
    ContinuousMap.curry ⟨fun p : X × unitInterval => H (p.2, p.1),
      hc.comp continuous_swap⟩
  refine ⟨⟨Quotient.lift K ?_, K.continuous.quotient_lift _⟩, ?_⟩
  · intro x y h
    induction h with
    | rel x y h => ext t; exact hr t x y h
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  · intro x t
    rfl

/-- Evaluate the composite in the three radial ranges. In the middle range,
the second detour's path parameter is `2 * (2 * |θ| - ε) / ε` on `γ.symm`,
which is `3 - 4 * |θ| / ε` on `γ`. In the outer range the twice-stretched
angle is `sign θ * (4 * |θ| - 3 * ε)`. All angles are smaller than `π`, so
`Circle.arg_exp` applies without a winding correction. -/
theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start_aux_stretched_angle (c₀ c : Circle) (ε : ℝ)
    (hε : 0 < ε) (hεπ : ε < Real.pi / 2)
    (hlo : ε / 2 < |apm_t97A03_invariants_aux_slide_aux_angle c₀ c|)
    (hhi : |apm_t97A03_invariants_aux_slide_aux_angle c₀ c| ≤ ε) :
    let θ := apm_t97A03_invariants_aux_slide_aux_angle c₀ c
    let θ' := apm_t97A03_invariants_aux_slide_aux_angle c₀
      (c₀ * Circle.exp (Real.sign θ * (2 * |θ| - ε)))
    θ' = Real.sign θ * (2 * |θ| - ε) ∧
      |θ'| = 2 * |θ| - ε ∧ Real.sign θ' = Real.sign θ := by
  dsimp only
  set θ := apm_t97A03_invariants_aux_slide_aux_angle c₀ c
  have hpos : 0 < 2 * |θ| - ε := by linarith
  have hbound : 2 * |θ| - ε ≤ ε := by linarith
  have hπ : ε < Real.pi := by linarith [Real.pi_pos]
  have hn : θ ≠ 0 := by intro he; simp [he] at hlo; linarith
  have heq : apm_t97A03_invariants_aux_slide_aux_angle c₀
      (c₀ * Circle.exp (Real.sign θ * (2 * |θ| - ε))) =
      Real.sign θ * (2 * |θ| - ε) := by
    unfold apm_t97A03_invariants_aux_slide_aux_angle
    rw [inv_mul_cancel_left]
    apply Circle.arg_exp
    · rcases lt_or_gt_of_ne hn with ht | ht
      · rw [Real.sign_of_neg ht]; nlinarith
      · rw [Real.sign_of_pos ht]; nlinarith
    · rcases lt_or_gt_of_ne hn with ht | ht
      · rw [Real.sign_of_neg ht]; nlinarith
      · rw [Real.sign_of_pos ht]; nlinarith
  rw [heq]
  refine ⟨rfl, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hn with ht | ht
    · rw [Real.sign_of_neg ht, neg_one_mul, abs_neg, abs_of_pos hpos]
    · simp [Real.sign_of_pos ht, abs_of_pos hpos]
  · rcases lt_or_gt_of_ne hn with ht | ht
    · rw [Real.sign_of_neg ht, neg_one_mul, Real.sign_of_neg (neg_neg_of_pos hpos)]
    · simp [Real.sign_of_pos ht, Real.sign_of_pos hpos]

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start_aux_middle
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
    (hcont' : Continuous (apm_t97A03_invariants_aux_slide_aux_detourRaw a w₀ δ ε)) (w : ι × Circle)
    (hw : w.1 = w₀.1)
    (hr : |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε)
    (hlo : ε / 2 < |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2|)
    (hhi : |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ 3 * ε / 4) :
    apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (0, .inr w) =
      apm_t97A03_invariants_aux_slide_aux_detour a' a w₀ δ ε hresp' hcont'
        (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε (.inr w)) := by
  classical
  subst δ
  let θ := apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2
  have hhalf : ε / 2 < |θ| := by dsimp [θ]; linarith
  obtain ⟨heq, habs, hsign⟩ := apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start_aux_stretched_angle w₀.2 w.2 ε hε hεπ hhalf hr
  have hout : w.1 = w₀.1 ∧ |θ| ≤ ε := ⟨hw, hr⟩
  have hsmall : 2 * |θ| - ε ≤ ε := by dsimp [θ]; linarith
  have hsmallhalf : 2 * |θ| - ε ≤ ε / 2 := by dsimp [θ]; linarith
  have hm : 3 - 4 * |θ| / ε ≤ 2 * |θ| / ε := by
    rw [le_div_iff₀ hε]
    field_simp
    nlinarith
  have ht : 1 - 2 * (2 * |θ| - ε) / ε = 3 - 4 * |θ| / ε := by
    field_simp
    ring
  dsimp [θ] at hm ht hsmall hsmallhalf
  simp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne,
    apm_t97A03_invariants_aux_slide_aux_detourRaw,
    apm_t97A03_invariants_aux_slide_aux_detour, hw, hr, not_le.mpr hlo,
    hhi, habs, hsmall, hsmallhalf, min_eq_right hm, Path.extend_symm_apply, ht]

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start_aux_outer
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
    (hcont' : Continuous (apm_t97A03_invariants_aux_slide_aux_detourRaw a w₀ δ ε)) (w : ι × Circle)
    (hw : w.1 = w₀.1)
    (hr : |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε)
    (hlo : 3 * ε / 4 < |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2|) :
    apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (0, .inr w) =
      apm_t97A03_invariants_aux_slide_aux_detour a' a w₀ δ ε hresp' hcont'
        (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε (.inr w)) := by
  classical
  subst δ
  let θ := apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2
  have hhalf : ε / 2 < |θ| := by dsimp [θ]; linarith
  obtain ⟨heq, habs, hsign⟩ := apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start_aux_stretched_angle w₀.2 w.2 ε hε hεπ hhalf hr
  have hout : w.1 = w₀.1 ∧ |θ| ≤ ε := ⟨hw, hr⟩
  have hsmall : 2 * |θ| - ε ≤ ε := by dsimp [θ]; linarith
  have hlarge : ¬ 2 * |θ| - ε ≤ ε / 2 := by dsimp [θ]; linarith
  have hnot : ¬ |θ| ≤ 3 * ε / 4 := by dsimp [θ]; linarith
  dsimp [θ] at hhalf hnot hsmall hlarge
  simp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne,
    apm_t97A03_invariants_aux_slide_aux_detourRaw,
    apm_t97A03_invariants_aux_slide_aux_detour, hw, hr, not_le.mpr hhalf,
    hnot, habs, hsmall, hlarge, hsign]
  congr 4 <;> ring

theorem apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start
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
    ∀ x, apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne a w₀ γ ε (0, x) =
      apm_t97A03_invariants_aux_slide_aux_detour a' a w₀ δ ε hresp' hcont'
        (apm_t97A03_invariants_aux_slide_aux_detourRaw a' w₀ γ ε x) := by
  classical
  subst δ
  intro x
  cases x with
  | inl y => rfl
  | inr w =>
    by_cases h : w.1 = w₀.1 ∧ |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε
    · by_cases hin : |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ ε / 2
      · have hthree : |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ 3 * ε / 4 := by linarith
        have hm : 2 * |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| / ε ≤
            3 - 4 * |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| / ε := by
          rw [div_le_iff₀ hε]
          have he : ε ≠ 0 := ne_of_gt hε
          field_simp
          nlinarith
        simp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne,
          apm_t97A03_invariants_aux_slide_aux_detourRaw,
          apm_t97A03_invariants_aux_slide_aux_detour, h, hin, hthree, min_eq_left hm]
      · by_cases hthree : |apm_t97A03_invariants_aux_slide_aux_angle w₀.2 w.2| ≤ 3 * ε / 4
        · exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start_aux_middle a a' w₀ hsame z z' hz hz' γ γ.symm rfl ε hε hεπ harc
            hresp hcont hresp' hcont' w h.1 h.2 (lt_of_not_ge hin) hthree
        · exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start_aux_outer a a' w₀ hsame z z' hz hz' γ γ.symm rfl ε hε hεπ harc
            hresp hcont hresp' hcont' w h.1 h.2 (lt_of_not_ge hthree)
    · simp [apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne,
        apm_t97A03_invariants_aux_slide_aux_detourRaw,
        apm_t97A03_invariants_aux_slide_aux_detour, h]

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
  obtain ⟨F, hF⟩ := apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_descend _ _
    (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageOne_continuous a w₀ hz γ ε hε hεπ)
    (fun t x y h => (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_respects a w₀ hz γ ε hε harc t x y h).1)
  obtain ⟨G, hG⟩ := apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_descend _ _
    (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_stageTwo_continuous a w₀ ε hε hεπ)
    (fun t x y h => (apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_respects a w₀ hz γ ε hε harc t x y h).2)
  let mid : C(Quotient (Relation.EqvGen.setoid
      (apm_t97A03_invariants_aux_slide_GenRel a)), _) :=
    ⟨fun x => G x 0, G.continuous.eval continuous_const⟩
  have h₁ : ((apm_t97A03_invariants_aux_slide_aux_detour a' a w₀ δ ε hresp' hcont').comp
      (apm_t97A03_invariants_aux_slide_aux_detour a a' w₀ γ ε hresp hcont)).Homotopic mid := by
    refine ⟨{ toFun := fun p => F p.2 p.1
              continuous_toFun := (F.continuous.comp continuous_snd).eval continuous_fst
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro x
      refine Quotient.inductionOn x ?_
      intro x
      rw [hF]
      exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_start a a' w₀ hsame z z' hz hz' γ δ hδ ε hε hεπ harc
        hresp hcont hresp' hcont' x
    · intro x
      refine Quotient.inductionOn x ?_
      intro x
      change F (Quotient.mk _ x) 1 = G (Quotient.mk _ x) 0
      rw [hF, hG]
      exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_seam a w₀ hz γ ε hε x
  apply h₁.trans
  refine ⟨{ toFun := fun p => G p.2 p.1
            continuous_toFun := (G.continuous.comp continuous_snd).eval continuous_fst
            map_zero_left := fun _ => rfl
            map_one_left := ?_ }⟩
  intro x
  refine Quotient.inductionOn x ?_
  intro x
  rw [hG]
  exact apm_t97A03_invariants_aux_slide_aux_detour_comp_aux_finish a w₀ ε x


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

private lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source_aux_points :
    apm_t97A03_circleI ≠ apm_t97A03_circleOne ∧
    apm_t97A03_circleNegOne ≠ apm_t97A03_circleOne ∧
    apm_t97A03_circleNegOne ≠ apm_t97A03_circleI ∧
    apm_t97A03_circleNegI ≠ apm_t97A03_circleOne ∧
    apm_t97A03_circleNegI ≠ apm_t97A03_circleI ∧
    apm_t97A03_circleNegI ≠ apm_t97A03_circleNegOne := by
  constructor
  · intro e; have := congrArg (fun z : Circle => z.1.im) e
    norm_num [apm_t97A03_circleI, apm_t97A03_circleOne] at this
  constructor
  · intro e; have := congrArg (fun z : Circle => z.1.re) e
    norm_num [apm_t97A03_circleNegOne, apm_t97A03_circleOne] at this
  constructor
  · intro e; have := congrArg (fun z : Circle => z.1.im) e
    norm_num [apm_t97A03_circleNegOne, apm_t97A03_circleI] at this
  constructor
  · intro e; have := congrArg (fun z : Circle => z.1.im) e
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleOne] at this
  constructor
  · intro e; have := congrArg (fun z : Circle => z.1.im) e
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleI] at this
  · intro e; have := congrArg (fun z : Circle => z.1.re) e
    norm_num [apm_t97A03_circleNegI, apm_t97A03_circleNegOne] at this

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t97A03_OneCircleCover
      (Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0)))) := by
  let h : Sum apm_t97A03_TwoSpheres (Unit × Circle) ≃ₜ
      Sum apm_t97A03_TwoSpheres Circle :=
    Homeomorph.sumCongr (Homeomorph.refl _) (Homeomorph.punitProd Circle)
  rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source_aux_points with
    ⟨hI1, hn11, hn1I, hnI1, hnII, hnIn1⟩
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
            · rcases w with ⟨u, w⟩; change w = _ at h1; subst w; cases hz
              simpa [h] using Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.n0
            · rcases w with ⟨u, w⟩; change w = _ at hI; subst w; cases hz
              simpa [h] using Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.s0
            · rcases w with ⟨u, w⟩; change w = _ at hn1; subst w; cases hz
              simpa [h] using Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.n1
            · rcases w with ⟨u, w⟩; change w = _ at hnI; subst w; cases hz
              simpa [h] using Relation.EqvGen.rel _ _ apm_t97A03_OneCircleRel.s1)
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
          | n0 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleOne) _ (by simp
              [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0]))
          | s0 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleI) _ (by
              simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0, hI1]))
          | n1 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleNegOne) _ (by
              simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0, hn11, hn1I]))
          | s1 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleNegI) _ (by
              simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a0,
                hnI1, hnII, hnIn1])))
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
/-
  let h : Sum apm_t97A03_TwoSpheres (Unit × Circle) ≃ₜ
      Sum apm_t97A03_TwoSpheres Circle :=
    Homeomorph.sumCongr (Homeomorph.refl _) (Homeomorph.punitProd Circle)
  rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source_aux_points with
    ⟨hI1, hn11, hn1I, hnI1, hnII, hnIn1⟩
  rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source_aux_points with
    ⟨hI1, hn11, hn1I, hnI1, hnII, hnIn1⟩
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
  let h : Sum apm_t97A03_TwoSpheres (Unit × Circle) ≃ₜ
      Sum apm_t97A03_TwoSpheres Circle :=
    Homeomorph.sumCongr (Homeomorph.refl _) (Homeomorph.punitProd Circle)
  rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_aux_source_aux_points with
    ⟨hI1, hn11, hn1I, hnI1, hnII, hnIn1⟩
  let f : (Quotient (Relation.EqvGen.setoid
      (apm_t97A03_invariants_aux_slide_GenRel
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2))) →
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover :=
    Quotient.lift (fun x => Quotient.mk _ (h x)) (by
    intro x y hxy
    apply Quotient.sound
    exact Relation.EqvGen.rec
      (fun _ _ hr => by
        cases hr with
        | att w z hz =>
          simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2] at hz
          split_ifs at hz with h1 hI hn1 hnI
          · rcases w with ⟨u, w⟩; change w = _ at h1; subst w; cases hz
            simpa [h] using Relation.EqvGen.rel _ _
              apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p0
          · rcases w with ⟨u, w⟩; change w = _ at hI; subst w; cases hz
            simpa [h] using Relation.EqvGen.rel _ _
              apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p1
          · rcases w with ⟨u, w⟩; change w = _ at hn1; subst w; cases hz
            simpa [h] using Relation.EqvGen.rel _ _
              apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p2
          · rcases w with ⟨u, w⟩; change w = _ at hnI; subst w; cases hz
            simpa [h] using Relation.EqvGen.rel _ _
              apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p3)
      (fun x => Relation.EqvGen.refl (h x))
      (fun _ _ _ ih => Relation.EqvGen.symm _ _ ih)
      (fun _ _ _ _ _ ih₁ ih₂ => Relation.EqvGen.trans _ _ _ ih₁ ih₂) hxy)
  let g : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover →
      Quotient (Relation.EqvGen.setoid
        (apm_t97A03_invariants_aux_slide_GenRel
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2)) :=
    Quotient.lift (fun x => Quotient.mk _ (h.symm x)) (by
    intro x y hxy
    apply Quotient.sound
    exact Relation.EqvGen.rec
      (fun _ _ hr => by
        cases hr with
        | p0 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleOne) _ (by simp
            [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2]))
        | p1 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleI) _ (by
            simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2, hI1]))
        | p2 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleNegOne) _ (by
            simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2, hn11, hn1I]))
        | p3 => simpa [h] using Relation.EqvGen.rel _ _ (.att ((), apm_t97A03_circleNegI) _ (by
            simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2,
              hnI1, hnII, hnIn1])))
      (fun x => Relation.EqvGen.refl (h.symm x))
      (fun _ _ _ ih => Relation.EqvGen.symm _ _ ih)
      (fun _ _ _ _ _ ih₁ ih₂ => Relation.EqvGen.trans _ _ _ ih₁ ih₂) hxy)
  have hf : Continuous f := by
    apply continuous_coinduced_dom.mpr
    exact continuous_coinduced_rng.comp h.continuous
  have hg : Continuous g := by
    apply continuous_coinduced_dom.mpr
    exact continuous_coinduced_rng.comp h.symm.continuous
  let e : (Quotient (Relation.EqvGen.setoid
      (apm_t97A03_invariants_aux_slide_GenRel
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_slide_a2))) ≃ₜ
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover :=
    { toFun := f
      invFun := g
      left_inv := by
        intro x; refine Quotient.inductionOn x ?_; intro x
        exact congrArg (Quotient.mk _) (h.symm_apply_apply x)
      right_inv := by
        intro x; refine Quotient.inductionOn x ?_; intro x
        exact congrArg (Quotient.mk _) (h.apply_symm_apply x)
      continuous_toFun := hf
      continuous_invFun := hg }
  exact ⟨e.toHomotopyEquiv⟩
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

section
local notation "OSC" => apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidCover
local notation "OCC" => apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_space
local notation "ON₀" => (Quotient.mk _ (Sum.inl (0, apm_t97A03_north)) : OSC)
local notation "ON₁" => (Quotient.mk _ (Sum.inl (1, apm_t97A03_north)) : OSC)

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge : Path ON₀ ON₁ :=
  ((apm_t97A03_circleArc apm_t97A03_circleI apm_t97A03_circleNegOne).map
    (show Continuous (fun z : Circle => (Quotient.mk _ (.inr z) : OSC)) from
      continuous_coinduced_rng.comp continuous_inr)).cast
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p1)).symm
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p2)).symm

/-- Polynomial double-angle map; its restriction to the lower hemisphere
stretches that hemisphere over the whole sphere. -/
noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold : ContinuousMap apm_t97A03_S2 apm_t97A03_S2 where
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

lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold_equator (x : apm_t97A03_S2) (hx : x.1 2 = 0) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold x = apm_t97A03_north := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold, apm_t97A03_north, hx]

/-- Pinch the upper hemisphere onto the tree edge, with the pole at ON₀. -/
noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap : ContinuousMap apm_t97A03_S2 OSC where
  toFun x := if 0 ≤ x.1 2 then
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge (Set.projIcc 0 1 (by norm_num) (1 - x.1 2))
    else Quotient.mk _ (.inl (1, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold x))
  continuous_toFun := by
    apply Continuous.if_le
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.continuous.comp (continuous_projIcc.comp (by fun_prop)))
      (continuous_coinduced_rng.comp (continuous_inl.comp
        (continuous_const.prodMk apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold.continuous)))
      continuous_const (by fun_prop)
    intro x hx
    simp only [Function.comp_apply]
    rw [show 1 - x.1 2 = 1 by linarith]
    simp only [Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)]
    rw [show (⟨(1 : ℝ), by norm_num⟩ : unitInterval) = 1 from rfl,
      Path.target, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold_equator x hx.symm]

lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap_north : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap apm_t97A03_north = ON₀ := by
  simpa [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap, apm_t97A03_north, Set.projIcc] using apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.source

/-- The unchanged first quadrant, a loop at sheet zero. -/
noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first : Path ON₀ ON₀ :=
  ((apm_t97A03_circleArc apm_t97A03_circleOne apm_t97A03_circleI).map
    (show Continuous (fun z : Circle => (Quotient.mk _ (.inr z) : OSC)) from
      continuous_coinduced_rng.comp continuous_inr)).cast
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p0)).symm
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p1)).symm

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_thirdCircle : Path apm_t97A03_circleNegOne apm_t97A03_circleNegI :=
  (((apm_t97A03_circleArc apm_t97A03_circleI apm_t97A03_circleNegOne).map
    (show Continuous (fun z : Circle => z⁻¹) from continuous_inv)).symm).cast
    (by apply Circle.ext; simp [apm_t97A03_circleNegOne])
    (by apply Circle.ext; simp [apm_t97A03_circleI, apm_t97A03_circleNegI])

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_third : Path ON₁ ON₁ :=
  (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_thirdCircle.map
    (show Continuous (fun z : Circle => (Quotient.mk _ (.inr z) : OSC)) from
      continuous_coinduced_rng.comp continuous_inr)).cast
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p2)).symm
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p3)).symm

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fourthCircle : Path apm_t97A03_circleNegI apm_t97A03_circleOne :=
  (((apm_t97A03_circleArc apm_t97A03_circleOne apm_t97A03_circleI).map
    (show Continuous (fun z : Circle => z⁻¹) from continuous_inv)).symm).cast
    (by apply Circle.ext; simp [apm_t97A03_circleI, apm_t97A03_circleNegI])
    (by apply Circle.ext; simp [apm_t97A03_circleOne])

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fourth : Path ON₁ ON₀ :=
  (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fourthCircle.map
    (show Continuous (fun z : Circle => (Quotient.mk _ (.inr z) : OSC)) from
      continuous_coinduced_rng.comp continuous_inr)).cast
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p3)).symm
    (Quotient.sound (Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel.p0)).symm

lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half : (Real.pi / 2) / Real.pi = (1 : ℝ) / 2 := by
  field_simp

/-- Quarter-circle parameter, clamped outside its intended quadrant. -/
noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle (a b : ℝ) : C(Circle, unitInterval) where
  toFun z := Set.projIcc 0 1 (by norm_num) (a + b * (Real.arccos z.1.re / Real.pi))
  continuous_toFun := (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := by norm_num)).comp (by fun_prop)

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_upper : C(Circle, OSC) where
  toFun z := if 0 ≤ z.1.re then apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 0 2 z) else ON₀
  continuous_toFun := by
    apply Continuous.if_le (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first.continuous.comp (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 0 2).continuous)
      continuous_const continuous_const (by fun_prop)
    intro z hz
    have ha : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 0 2 z = 1 := by
      apply Subtype.ext
      norm_num [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, hz.symm, Real.arccos_zero, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half, Set.projIcc, Real.pi_ne_zero]
    dsimp only [Function.comp_apply]
    rw [ha]
    exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first.target

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_lower : C(Circle, OSC) where
  toFun z := if z.1.re ≤ 0 then
      ((apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.trans apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_third).trans apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.symm) (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 2 (-2) z)
    else (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.trans apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fourth) (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 1 (-2) z)
  continuous_toFun := by
    apply Continuous.if_le
      (((apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.trans apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_third).trans apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.symm).continuous.comp (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 2 (-2)).continuous)
      ((apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge.trans apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fourth).continuous.comp (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 1 (-2)).continuous)
      (by fun_prop) continuous_const
    intro z hz
    have h1 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 2 (-2) z = 1 := by
      apply Subtype.ext
      norm_num [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, hz, Real.arccos_zero, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half, Set.projIcc, Real.pi_ne_zero]
    have h0 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 1 (-2) z = 0 := by
      apply Subtype.ext
      norm_num [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, hz, Real.arccos_zero, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half, Set.projIcc, Real.pi_ne_zero]
    dsimp only [Function.comp_apply]
    rw [h1, h0]
    simp

lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_real (z : Circle) (h : z.1.im = 0) :
    z = apm_t97A03_circleOne ∨ z = apm_t97A03_circleNegOne := by
  have hn := Circle.normSq_coe z
  rw [Complex.normSq_apply] at hn
  have hre : z.1.re = 1 ∨ z.1.re = -1 := by
    have : (z.1.re - 1) * (z.1.re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hre with hr | hr
  · left; apply Circle.ext; apply Complex.ext <;> simp [apm_t97A03_circleOne, hr, h]
  · right; apply Circle.ext; apply Complex.ext <;> simp [apm_t97A03_circleNegOne, hr, h]

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle : C(Circle, OSC) where
  toFun z := if 0 ≤ z.1.im then apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_upper z else apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_lower z
  continuous_toFun := by
    apply Continuous.if_le apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_upper.continuous apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_lower.continuous
      continuous_const (by fun_prop)
    intro z hz
    rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_real z hz.symm with rfl | rfl <;>
      simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_upper, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_lower, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_circleOne,
        apm_t97A03_circleNegOne, Set.projIcc, Real.pi_ne_zero]

lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_points :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle apm_t97A03_circleOne = ON₀ ∧
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle apm_t97A03_circleI = ON₀ ∧
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle apm_t97A03_circleNegOne = ON₀ ∧
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle apm_t97A03_circleNegI = ON₀ := by
  norm_num [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_upper, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_lower, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half,
    apm_t97A03_circleOne, apm_t97A03_circleI, apm_t97A03_circleNegOne,
    apm_t97A03_circleNegI, Set.projIcc, Real.pi_ne_zero]

lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_arc (z : Circle)
    (hz : z ∈ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle z = ON₀ := by
  change (if 0 ≤ z.1.im then apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_upper z else apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_lower z) = ON₀
  rw [if_pos hz.2]
  change (if 0 ≤ z.1.re then apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 0 2 z) else ON₀) = ON₀
  split_ifs with hr
  · have he : z.1.re = 0 := le_antisymm hz.1 hr
    have ha : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle 0 2 z = 1 := by
      apply Subtype.ext
      norm_num [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, he, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half, Set.projIcc]
    rw [ha]
    exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first.target
  · rfl

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw : C(Sum apm_t97A03_TwoSpheres Circle, OSC) where
  toFun := Sum.elim
    (fun w => if w.1 = 0 then Quotient.mk _ (.inl (0, w.2)) else apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap w.2)
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle
  continuous_toFun := by
    rw [continuous_sum_dom]
    constructor
    · rw [continuous_prod_of_discrete_left]
      intro i
      fin_cases i
      · change Continuous (fun x : apm_t97A03_S2 => (Quotient.mk _ (.inl (0, x)) : OSC))
        exact continuous_coinduced_rng.comp
          (continuous_inl.comp (continuous_const.prodMk continuous_id))
      · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap.continuous
    · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle.continuous

lemma apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_respects (x y : Sum apm_t97A03_TwoSpheres Circle)
    (h : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw x = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw y := by
  have h0 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw (.inl (0, apm_t97A03_north)) = ON₀ := rfl
  have h1 : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw (.inl (1, apm_t97A03_north)) = ON₀ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap_north
  cases h with
  | p0 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_points.1
  | p1 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_points.2.1
  | p2 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_points.2.2.1.trans h1.symm
  | p3 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_points.2.2.2.trans h1.symm
  | arc z hz => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_arc z hz

noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_s : C(OCC, OSC) where
  toFun := Quotient.lift apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw (by
    intro x y h
    induction h with
    | rel x y h => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_respects x y h
    | refl x => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂)
  continuous_toFun := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw.continuous.quotient_lift _

local notation "OQ" => apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q
local notation "OQC" => (ContinuousMap.mk OQ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q_continuous)
local notation "OV" => (Quotient.mk _ (Sum.inl (0, apm_t97A03_north)) : OCC)

private noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) : ℝ :=
  ((p.1.2 : ℝ) - p.1.1.1 2) / (1 + (p.1.2 : ℝ))

private noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) : ℝ :=
  1 - 2 * Real.rpow
    (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u p)
    (2 - (p.1.2 : ℝ))

private noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) : ℝ :=
  Real.sqrt (1 -
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2) /
    Real.sqrt (1 - (p.1.1.1 2) ^ 2)

private noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) :
    apm_t97A03_R3 :=
  WithLp.toLp 2 ![
    p.1.1.1 0 * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k p,
    p.1.1.1 1 * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k p,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p]

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_coords (x : apm_t97A03_S2) :
    (x.1 0)^2 + (x.1 1)^2 + (x.1 2)^2 = 1 := by
  have hn : ‖x.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.2
  have hs := EuclideanSpace.real_norm_sq_eq x.1
  simp [Fin.sum_univ_succ, hn] at hs
  linarith

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u_bounds
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) :
    0 ≤ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u p ∧ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u p ≤ 1 := by
  have ht0 := p.1.2.2.1
  have hzt : p.1.1.1 2 ≤ (p.1.2 : ℝ) := p.2
  have hc := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_coords p.1.1
  have hz : -1 ≤ p.1.1.1 2 := by nlinarith [sq_nonneg (p.1.1.1 0), sq_nonneg (p.1.1.1 1)]
  have hd : 0 < 1 + (p.1.2 : ℝ) := by linarith
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u
  exact ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith)⟩

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_bounds
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) :
    0 ≤ 1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2 := by
  obtain ⟨h0, h1⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u_bounds p
  have ht1 := p.1.2.2.2
  have hw0 : 0 ≤ Real.rpow (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u p) (2 - (p.1.2 : ℝ)) := Real.rpow_nonneg h0 _
  have hw1 : Real.rpow (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u p) (2 - (p.1.2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one h0 h1 (by linarith)
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H
  nlinarith

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_pole
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)})
    (hp : 1 - (p.1.1.1 2) ^ 2 = 0) : (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2 = 1 := by
  have ht0 := p.1.2.2.1
  have ht1 := p.1.2.2.2
  have hzt : p.1.1.1 2 ≤ (p.1.2 : ℝ) := p.2
  have hd : (1 + (p.1.2 : ℝ)) ≠ 0 := by linarith
  have hz : p.1.1.1 2 = 1 ∨ p.1.1.1 2 = -1 := by
    have : (p.1.1.1 2 - 1) * (p.1.1.1 2 + 1) = 0 := by linear_combination -hp
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u
  rcases hz with hz | hz
  · have ht : (p.1.2 : ℝ) = 1 := by linarith
    rw [hz, ht]; norm_num
  · rw [hz, show ((p.1.2 : ℝ) - -1) / (1 + (p.1.2 : ℝ)) = 1 by
      rw [div_eq_one_iff_eq hd]; ring]
    norm_num

/-- `x_i * (A / sqrt (1 - z²)) = x_i * c` once `A = c * sqrt (1 - z²)`, poles included. -/
private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk (x : apm_t97A03_S2) (i : Fin 3) (hi : i ≠ 2) (A c : ℝ)
    (h : A = c * Real.sqrt (1 - (x.1 2) ^ 2)) :
    x.1 i * (A / Real.sqrt (1 - (x.1 2) ^ 2)) = x.1 i * c := by
  by_cases hs : Real.sqrt (1 - (x.1 2) ^ 2) = 0
  · have hc := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_coords x
    have hle : 1 - (x.1 2) ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 hs
    have h0 : x.1 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)])
    have h1 : x.1 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      (by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)])
    fin_cases i
    · simp [h0]
    · simp [h1]
    · exact absurd rfl hi
  · rw [h, mul_div_cancel_right₀ _ hs]

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw_mem
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p ∈
      Metric.sphere (0 : apm_t97A03_R3) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hc := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_coords p.1.1
  have hH := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_bounds p
  have hsq : (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p 0) ^ 2 + (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p 1) ^ 2 + (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p 2) ^ 2 = 1 := by
    simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k
    set z := p.1.1.1 2
    set H := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p
    rcases (sub_nonneg.2 (show z ^ 2 ≤ 1 by nlinarith [sq_nonneg (p.1.1.1 0), sq_nonneg (p.1.1.1 1)])).eq_or_lt with hz | hz
    · have hp := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_pole p hz.symm
      rw [← hz, Real.sqrt_zero, div_zero, mul_zero, mul_zero]
      show (0:ℝ) ^ 2 + 0 ^ 2 + apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p ^ 2 = 1
      rw [hp]; norm_num
    · rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hH, Real.sq_sqrt hz.le]
      field_simp
      linear_combination (1 - H ^ 2) * hc
  have hs := EuclideanSpace.real_norm_sq_eq (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hs
  have hn := norm_nonneg (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p)
  have : ‖apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p‖ ^ 2 = 1 := by rw [hs]; simpa [add_assoc] using hsq
  nlinarith

private noncomputable def apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_fun
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) :
    apm_t97A03_S2 :=
  ⟨apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw p,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_raw_mem p⟩

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_bound
    (p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)}) (i : Fin 3) (hi : i ≠ 2) :
    ‖p.1.1.1 i * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k p‖ ≤ Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2) := by
  have hc := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_coords p.1.1
  have hxi : (p.1.1.1 i) ^ 2 ≤ 1 - (p.1.1.1 2) ^ 2 := by
    fin_cases i
    · show (p.1.1.1 0) ^ 2 ≤ _; nlinarith [sq_nonneg (p.1.1.1 1)]
    · show (p.1.1.1 1) ^ 2 ≤ _; nlinarith [sq_nonneg (p.1.1.1 0)]
    · exact absurd rfl hi
  have habs : |p.1.1.1 i| ≤ Real.sqrt (1 - (p.1.1.1 2) ^ 2) := Real.abs_le_sqrt hxi
  have hA := Real.sqrt_nonneg (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2)
  have hB := Real.sqrt_nonneg (1 - (p.1.1.1 2) ^ 2)
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg hA hB)]
  by_cases hB0 : Real.sqrt (1 - (p.1.1.1 2) ^ 2) = 0
  · rw [hB0, div_zero, mul_zero]; exact hA
  · calc |p.1.1.1 i| * (Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2) / Real.sqrt (1 - (p.1.1.1 2) ^ 2))
        ≤ Real.sqrt (1 - (p.1.1.1 2) ^ 2) *
            (Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2) / Real.sqrt (1 - (p.1.1.1 2) ^ 2)) :=
          mul_le_mul_of_nonneg_right habs (div_nonneg hA hB)
      _ = Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H p) ^ 2) := mul_div_cancel₀ _ hB0

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_z_continuous (i : Fin 3) :
    Continuous fun p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)} => p.1.1.1 i :=
  ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_t_continuous :
    Continuous fun p : {p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)} => (p.1.2 : ℝ) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_continuous : Continuous apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H := by
  have hu : Continuous apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u := by
    unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_u
    refine (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_t_continuous.sub (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_z_continuous 2)).div
      (continuous_const.add apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_t_continuous) (fun p => ?_)
    have := p.1.2.2.1
    exact ne_of_gt (by linarith)
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H
  refine continuous_const.sub (continuous_const.mul ?_)
  exact hu.rpow (continuous_const.sub apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_t_continuous) (fun p => Or.inr (by
    have := p.1.2.2.2
    linarith))

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk_continuous (i : Fin 3) (hi : i ≠ 2) :
    Continuous fun p => p.1.1.1 i * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k p := by
  rw [continuous_iff_continuousAt]
  intro p
  have hHs : Continuous fun q => Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H q) ^ 2) :=
    (continuous_const.sub (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_continuous.pow 2)).sqrt
  by_cases hp : 1 - (p.1.1.1 2) ^ 2 = 0
  · have hval : p.1.1.1 i * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k p = 0 := by
      unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k; rw [hp, Real.sqrt_zero, div_zero, mul_zero]
    have hlim : Filter.Tendsto (fun q => Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H q) ^ 2)) (nhds p) (nhds 0) := by
      have := hHs.tendsto p
      rwa [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_pole p hp, sub_self, Real.sqrt_zero] at this
    show Filter.Tendsto _ (nhds p) (nhds (p.1.1.1 i * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k p))
    rw [hval]
    exact squeeze_zero_norm (fun q => apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_bound q i hi) hlim
  · have hc := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_coords p.1.1
    have hpos : Real.sqrt (1 - (p.1.1.1 2) ^ 2) ≠ 0 := by
      have : 0 < 1 - (p.1.1.1 2) ^ 2 :=
        lt_of_le_of_ne (by nlinarith [sq_nonneg (p.1.1.1 0), sq_nonneg (p.1.1.1 1)]) (Ne.symm hp)
      exact (Real.sqrt_pos.2 this).ne'
    unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k
    exact (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_z_continuous i).continuousAt.mul
      (hHs.continuousAt.div
        ((continuous_const.sub ((apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_z_continuous 2).pow 2)).sqrt.continuousAt) hpos)

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_continuous :
    Continuous apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_fun := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk_continuous 0 (by decide)
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk_continuous 1 (by decide)
  · exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H_continuous

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_zero
    (x : apm_t97A03_S2) (hx : x.1 2 ≤ 0) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_fun ⟨(x, 0), hx⟩ =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold x := by
  have hH : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 0), hx⟩ = 1 - 2 * (x.1 2) ^ 2 := by
    show 1 - 2 * ((0 - x.1 2) / (1 + 0)) ^ (2 - (0 : ℝ)) = _
    rw [show (2 : ℝ) - 0 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    ring
  have hA : Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 0), hx⟩) ^ 2) =
      (-2 * x.1 2) * Real.sqrt (1 - (x.1 2) ^ 2) := by
    rw [hH, show 1 - (1 - 2 * (x.1 2) ^ 2) ^ 2 = (-2 * x.1 2) ^ 2 * (1 - (x.1 2) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  apply Subtype.ext
  ext i
  fin_cases i
  · show x.1 0 * (Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 0), hx⟩) ^ 2) / Real.sqrt (1 - (x.1 2) ^ 2)) =
      -2 * x.1 2 * x.1 0
    rw [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk x 0 (by decide) _ _ hA]; ring
  · show x.1 1 * (Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 0), hx⟩) ^ 2) / Real.sqrt (1 - (x.1 2) ^ 2)) =
      -2 * x.1 2 * x.1 1
    rw [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk x 1 (by decide) _ _ hA]; ring
  · exact hH

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_one
    (x : apm_t97A03_S2) (hx : x.1 2 ≤ 1) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_fun ⟨(x, 1), hx⟩ = x := by
  have hH : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 1), hx⟩ = x.1 2 := by
    show 1 - 2 * ((1 - x.1 2) / (1 + 1)) ^ (2 - (1 : ℝ)) = _
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  have hA : Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 1), hx⟩) ^ 2) =
      1 * Real.sqrt (1 - (x.1 2) ^ 2) := by
    rw [hH, one_mul]
  apply Subtype.ext
  ext i
  fin_cases i
  · show x.1 0 * (Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 1), hx⟩) ^ 2) / Real.sqrt (1 - (x.1 2) ^ 2)) = x.1 0
    rw [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk x 0 (by decide) _ _ hA]; ring
  · show x.1 1 * (Real.sqrt (1 - (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, 1), hx⟩) ^ 2) / Real.sqrt (1 - (x.1 2) ^ 2)) = x.1 1
    rw [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_xk x 1 (by decide) _ _ hA]; ring
  · exact hH

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_boundary
    (x : apm_t97A03_S2) (t : unitInterval) (hx : x.1 2 = (t : ℝ)) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_fun ⟨(x, t), hx.le⟩ =
      apm_t97A03_north := by
  have ht1 := t.2.2
  have hH : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, t), hx.le⟩ = 1 := by
    show 1 - 2 * (((t : ℝ) - x.1 2) / (1 + (t : ℝ))) ^ (2 - (t : ℝ)) = _
    rw [hx, sub_self, zero_div, Real.zero_rpow (by linarith)]
    ring
  have hk : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k ⟨(x, t), hx.le⟩ = 0 := by
    unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k; rw [hH]; norm_num
  apply Subtype.ext
  ext i
  fin_cases i
  · show x.1 0 * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k ⟨(x, t), hx.le⟩ = _
    rw [hk]; simp [apm_t97A03_north]
  · show x.1 1 * apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_k ⟨(x, t), hx.le⟩ = _
    rw [hk]; simp [apm_t97A03_north]
  · show apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_H ⟨(x, t), hx.le⟩ = _
    rw [hH]; simp [apm_t97A03_north]

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower :
    ∃ L : C({p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)},
        apm_t97A03_S2),
      (∀ x (hx : x.1 2 ≤ 0), L ⟨(x, 0), hx⟩ =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold x) ∧
      (∀ x (hx : x.1 2 ≤ 1), L ⟨(x, 1), hx⟩ = x) ∧
      (∀ x (t : unitInterval) (hx : x.1 2 = (t : ℝ)),
        L ⟨(x, t), hx.le⟩ = apm_t97A03_north) := by
  exact ⟨⟨_, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_continuous⟩,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_zero,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_one,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower_aux_boundary⟩

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_upper :
    ∃ U : C({p : apm_t97A03_S2 × unitInterval | (p.2 : ℝ) ≤ p.1.1 2},
        apm_t97A03_S2),
      ∀ x (t : unitInterval) (hx : x.1 2 = (t : ℝ)),
        U ⟨(x, t), hx.ge⟩ = apm_t97A03_north := by
  exact ⟨⟨fun _ => apm_t97A03_north, continuous_const⟩, fun _ _ _ => rfl⟩

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_paste
    (L : C({p : apm_t97A03_S2 × unitInterval | p.1.1 2 ≤ (p.2 : ℝ)},
      apm_t97A03_S2))
    (U : C({p : apm_t97A03_S2 × unitInterval | (p.2 : ℝ) ≤ p.1.1 2},
      apm_t97A03_S2))
    (hLU : ∀ x (t : unitInterval) (hx : x.1 2 = (t : ℝ)),
      L ⟨(x, t), hx.le⟩ = U ⟨(x, t), hx.ge⟩) :
    ∃ F : C(apm_t97A03_S2 × unitInterval, apm_t97A03_S2),
      (∀ x (t : unitInterval) (hx : x.1 2 ≤ (t : ℝ)),
        F (x, t) = L ⟨(x, t), hx⟩) ∧
      (∀ x (t : unitInterval) (hx : (t : ℝ) ≤ x.1 2),
        F (x, t) = U ⟨(x, t), hx⟩) := by
  classical
  let f : apm_t97A03_S2 × unitInterval → apm_t97A03_S2 := fun p =>
    if h : p.1.1 2 ≤ (p.2 : ℝ) then L ⟨p, h⟩
    else U ⟨p, le_of_not_ge h⟩
  have hc₁ : Continuous (fun p : apm_t97A03_S2 × unitInterval => p.1.1 2) := by
    fun_prop
  have hc₂ : Continuous (fun p : apm_t97A03_S2 × unitInterval => (p.2 : ℝ)) := by
    fun_prop
  let A : Set (apm_t97A03_S2 × unitInterval) :=
    {p | p.1.1 2 ≤ (p.2 : ℝ)}
  let B : Set (apm_t97A03_S2 × unitInterval) :=
    {p | (p.2 : ℝ) ≤ p.1.1 2}
  have hAc : IsClosed A := by
    dsimp [A]
    exact isClosed_le hc₁ hc₂
  have hBc : IsClosed B := by
    dsimp [B]
    exact isClosed_le hc₂ hc₁
  have hfA : ContinuousOn f A := by
    have hcont : Continuous (fun p : A => L ⟨p.1, p.2⟩) :=
      L.continuous.comp (continuous_subtype_val.subtype_mk fun p => p.2)
    have heq : A.restrict f = (fun q : A => L ⟨q.1, q.2⟩) := by
      funext q
      exact dif_pos q.2
    rw [continuousOn_iff_continuous_restrict, heq]
    exact hcont
  have hfB : ContinuousOn f B := by
    have hcont : Continuous (fun p : B => U ⟨p.1, p.2⟩) :=
      U.continuous.comp (continuous_subtype_val.subtype_mk fun p => p.2)
    have heq : B.restrict f = (fun q : B => U ⟨q.1, q.2⟩) := by
      funext q
      change f q.1 = U ⟨q.1, q.2⟩
      by_cases h : q.1.1.1 2 ≤ (q.1.2 : ℝ)
      · simpa only [f, dif_pos h] using
          hLU q.1.1 q.1.2 (le_antisymm h q.2)
      · simp [f, h]
    rw [continuousOn_iff_continuous_restrict, heq]
    exact hcont
  have hAB : A ∪ B = Set.univ := by
    ext p
    simp only [A, B, mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total _ _
  have hf : Continuous f := by
    rw [← continuousOn_univ, ← hAB]
    exact hfA.union_of_isClosed hfB hAc hBc
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro x t hx
    simp [f, hx]
  · intro x t hx
    change f (x, t) = U ⟨(x, t), hx⟩
    by_cases h : x.1 2 ≤ (t : ℝ)
    · simpa only [f, dif_pos h] using hLU x t (le_antisymm h hx)
    · simp [f, h]

/-- Polar cap interpolation, with its north pole following the connecting edge.
Use the same polar formula as for two circles: cap angle `(1-t)π/2`,
complementary polar angle `π(θ-(1-t)π/2)/(π-(1-t)π/2)`, and on the cap
edge parameter `t+(1-t)(1-cos θ)/(1-cos((1-t)π/2))`. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family :
    ∃ F : C(apm_t97A03_S2 × unitInterval, apm_t97A03_S2),
      (∀ x, x.1 2 ≤ 0 → F (x, 0) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold x) ∧
      (∀ x, F (x, 1) = x) ∧
      (∀ x (t : unitInterval), x.1 2 = (t : ℝ) → F (x, t) = apm_t97A03_north) := by
  obtain ⟨L, hL0, hL1, hLb⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_lower
  obtain ⟨U, hUb⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_upper
  obtain ⟨F, hFlo, hFhi⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family_aux_paste
      L U (fun x t hx => (hLb x t hx).trans (hUb x t hx).symm)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x hx
    rw [hFlo x 0 hx]
    exact hL0 x hx
  · intro x
    have hxnorm : ‖x.1‖ = 1 := by
      simpa using x.2
    have hsumsq : (x.1 0) ^ 2 + (x.1 1) ^ 2 + (x.1 2) ^ 2 = 1 := by
      have h := congrArg (fun r : ℝ => r ^ 2) hxnorm
      change ‖x.1‖ ^ 2 = 1 ^ 2 at h
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simp [Fin.sum_univ_succ] at h
      nlinarith
    have hx : x.1 2 ≤ (1 : ℝ) := by
      nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1), sq_nonneg (x.1 2)]
    rw [hFlo x 1 hx]
    exact hL1 x hx
  · intro x t hx
    rw [hFlo x t hx.le]
    exact hLb x t hx

theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_glue
    (F : C(apm_t97A03_S2 × unitInterval, apm_t97A03_S2))
    (hF0 : ∀ x, x.1 2 ≤ 0 → F (x, 0) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fold x)
    (hF1 : ∀ x, F (x, 1) = x)
    (hFb : ∀ x (t : unitInterval), x.1 2 = (t : ℝ) → F (x, t) = apm_t97A03_north) :
    ∃ H : C(apm_t97A03_S2, C(unitInterval, OSC)),
      (∀ x, H x 0 = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap x) ∧
      (∀ x, H x 1 = Quotient.mk _ (.inl (1, x))) ∧
      (∀ t, H apm_t97A03_north t = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge t) := by
  let E := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge
  let G : C(apm_t97A03_S2 × unitInterval, OSC) :=
    ⟨fun p => if (p.2 : ℝ) ≤ p.1.1 2 then
        E (Set.projIcc 0 1 (by norm_num) ((p.2 : ℝ) + 1 - p.1.1 2))
      else Quotient.mk _ (.inl (1, F p)), by
      apply Continuous.if_le
        (E.continuous.comp (continuous_projIcc.comp (by fun_prop)))
        (continuous_coinduced_rng.comp (continuous_inl.comp
          (continuous_const.prodMk F.continuous)))
        (by fun_prop) (by fun_prop)
      intro p hp
      have hb : F p = apm_t97A03_north := hFb p.1 p.2 hp.symm
      change E (Set.projIcc 0 1 (by norm_num)
        ((p.2 : ℝ) + 1 - p.1.1 2)) = Quotient.mk _ (.inl (1, F p))
      rw [show (p.2 : ℝ) + 1 - p.1.1 2 = 1 by linarith, hb]
      simpa [Set.projIcc] using E.target⟩
  refine ⟨ContinuousMap.curry G, ?_, ?_, ?_⟩
  · intro x
    dsimp [G, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap]
    split_ifs with hx
    · apply congrArg E
      apply Subtype.ext
      norm_num
    · rw [hF0 x (le_of_not_ge hx)]
  · intro x
    dsimp only [G]
    by_cases h : (1 : ℝ) ≤ x.1 2
    · have hx : x = apm_t97A03_north := by
        have hn : ‖x.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.2
        have hc_le : x.1 2 ≤ 1 := by
          calc x.1 2 ≤ |x.1 2| := le_abs_self _
            _ = ‖x.1 2‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖x.1‖ := PiLp.norm_apply_le x.1 2
            _ = 1 := hn
        have hc : x.1 2 = 1 := le_antisymm hc_le h
        have hs := EuclideanSpace.real_norm_sq_eq x.1
        simp [Fin.sum_univ_succ, hn, hc] at hs
        have h0 : x.1 0 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
        have h1 : x.1 1 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
        apply Subtype.ext
        ext i
        fin_cases i
        · simp [apm_t97A03_north, h0]
        · simp [apm_t97A03_north, h1]
        · simp [apm_t97A03_north, hc]
      subst x
      simpa [apm_t97A03_north, Set.projIcc] using E.target
    · simp [h, hF1]
  · intro t
    dsimp only [G]
    change (if (t : ℝ) ≤ 1 then E (Set.projIcc 0 1 (by norm_num) ((t : ℝ) + 1 - 1)) else _) = E t
    rw [if_pos t.2.2]
    congr 1
    apply Subtype.ext
    simp [Set.projIcc, apm_t97A03_north, t.2.1, t.2.2]

theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion :
    ∃ H : C(apm_t97A03_S2, C(unitInterval, OSC)),
      (∀ x, H x 0 = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_cap x) ∧
      (∀ x, H x 1 = Quotient.mk _ (.inl (1, x))) ∧
      (∀ t, H apm_t97A03_north t = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge t) := by
  obtain ⟨F, h0, h1, hb⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family
  exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_glue F h0 h1 hb

set_option maxHeartbeats 800000 in
/-- Keep quadrant one fixed, grow the collapsed edge in quadrant two,
and shorten the inserted edge detours in quadrants three and four.
Both sheet-one attachments follow `edge t`; every point in the contracted
quarter arc stays in that arc, so its projection is constant. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_motion :
    ∃ H : C(Circle, C(unitInterval, OSC)),
      (∀ z, H z 0 = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle z) ∧
      (∀ z, H z 1 = Quotient.mk _ (.inr z)) ∧
      (∀ t, H apm_t97A03_circleOne t = ON₀) ∧
      (∀ t, H apm_t97A03_circleI t = ON₀) ∧
      (∀ t, H apm_t97A03_circleNegOne t = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge t) ∧
      (∀ t, H apm_t97A03_circleNegI t = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge t) ∧
      (∀ z, z ∈ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc →
        ∀ t, OQ (H z t) = OV) := by
  let E := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_edge
  let A := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first
  let B := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_third
  let D := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_fourth
  let P := (E.trans B).trans E.symm
  let R := E.trans D
  let f₂ (t : unitInterval) (u : ℝ) := E.extend ((t : ℝ) * u)
  let f₃ (t : unitInterval) (u : ℝ) := P.extend ((t : ℝ) / 4 + (1 - 3 * (t : ℝ) / 4) * u)
  let f₄ (t : unitInterval) (u : ℝ) := R.extend ((t : ℝ) / 2 + (1 - (t : ℝ) / 2) * u)
  have h₂0 (t : unitInterval) : f₂ t 0 = ON₀ := by simp [f₂]
  have h₂1 (t : unitInterval) : f₂ t 1 = E t := by simp [f₂]
  have h₃0 (t : unitInterval) : f₃ t 0 = E t := by
    dsimp [f₃, P]
    rw [Path.extend_trans_of_le_half _ _ (by linarith [t.2.2]),
      Path.extend_trans_of_le_half _ _ (by linarith [t.2.2])]
    convert E.extend_extends' t using 1 <;> congr 1 <;> ring
  have h₃1 (t : unitInterval) : f₃ t 1 = E t := by
    dsimp [f₃, P]
    rw [Path.extend_trans_of_half_le _ _ (by linarith [t.2.2]), Path.extend_symm_apply]
    convert E.extend_extends' t using 1 <;> congr 1 <;> ring
  have h₄0 (t : unitInterval) : f₄ t 0 = E t := by
    dsimp [f₄, R]
    rw [Path.extend_trans_of_le_half _ _ (by linarith [t.2.2])]
    convert E.extend_extends' t using 1 <;> congr 1 <;> ring
  have h₄1 (t : unitInterval) : f₄ t 1 = ON₀ := by
    dsimp [f₄]
    rw [show (t : ℝ) / 2 + (1 - (t : ℝ) / 2) * 1 = 1 by ring]
    exact R.extend_one
  have h₃end (u : unitInterval) : f₃ 1 u = B u := by
    dsimp [f₃, P]
    rw [Path.extend_trans_of_le_half _ _ (by linarith [u.2.2]),
      Path.extend_trans_of_half_le _ _ (by linarith [u.2.1])]
    convert B.extend_extends' u using 1 <;> congr 1 <;> ring
  have h₄end (u : unitInterval) : f₄ 1 u = D u := by
    dsimp [f₄, R]
    rw [Path.extend_trans_of_half_le _ _ (by linarith [u.2.1])]
    convert D.extend_extends' u using 1 <;> congr 1 <;> ring
  let α := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle
  have hα (z : Circle) (hz : z.1.re = 0) :
      α 0 2 z = 1 ∧ α (-1) 2 z = 0 ∧ α 2 (-2) z = 1 ∧ α 1 (-2) z = 0 := by
    dsimp [α]
    norm_num [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, hz, Real.arccos_zero, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half, Set.projIcc, Real.pi_ne_zero]
  let U : C(Circle × unitInterval, OSC) :=
    ⟨fun p => if 0 ≤ p.1.1.re then A (α 0 2 p.1) else f₂ p.2 (α (-1) 2 p.1), by
      apply Continuous.if_le
        (A.continuous.comp ((α 0 2).continuous.comp continuous_fst))
        (E.continuous_extend.comp (by dsimp [α]; fun_prop))
        continuous_const (by fun_prop)
      intro p hp
      change A (α 0 2 p.1) = f₂ p.2 (α (-1) 2 p.1)
      rw [(hα p.1 hp.symm).1, (hα p.1 hp.symm).2.1]
      simp only [Set.Icc.coe_zero, h₂0]
      exact A.target⟩
  let L : C(Circle × unitInterval, OSC) :=
    ⟨fun p => if p.1.1.re ≤ 0 then f₃ p.2 (α 2 (-2) p.1) else f₄ p.2 (α 1 (-2) p.1), by
      apply Continuous.if_le
        (P.continuous_extend.comp (by dsimp [α]; fun_prop))
        (R.continuous_extend.comp (by dsimp [α]; fun_prop))
        (by fun_prop) continuous_const
      intro p hp
      change f₃ p.2 (α 2 (-2) p.1) = f₄ p.2 (α 1 (-2) p.1)
      rw [(hα p.1 hp).2.2.1, (hα p.1 hp).2.2.2]
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero, h₃1, h₄0]⟩
  have hUL (z : Circle) (t : unitInterval) (hz : z.1.im = 0) : U (z,t) = L (z,t) := by
    rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_real z hz with rfl | rfl
    · change (if _ then _ else _) = (if _ then _ else _)
      norm_num [α, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_circleOne, Set.projIcc] 
    · change (if _ then _ else _) = (if _ then _ else _)
      norm_num [α, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_circleNegOne, Set.projIcc, Real.pi_ne_zero]
      simpa [f₂, f₃] using (h₂1 t).trans (h₃0 t).symm
  let H : C(Circle, C(unitInterval, OSC)) := ContinuousMap.curry
    ⟨fun p => if 0 ≤ p.1.1.im then U p else L p, by
      apply Continuous.if_le U.continuous L.continuous continuous_const (by fun_prop)
      intro p hp
      exact hUL p.1 p.2 hp.symm⟩
  have hE (u : unitInterval) : E u = Quotient.mk _ (.inr
      (Circle.exp ((1 - (u : ℝ)) * (Real.pi / 2) + (u : ℝ) * Real.pi))) := by
    change (Quotient.mk _ (Sum.inr (Circle.exp
      ((1 - (u : ℝ)) * Complex.arg (apm_t97A03_circleI : ℂ) +
        (u : ℝ) * Complex.arg (apm_t97A03_circleNegOne : ℂ)))) : OSC) = _
    simp only [apm_t97A03_circleI, apm_t97A03_circleNegOne,
      Complex.arg_I, Complex.arg_neg_one]
  have hA (u : unitInterval) : A u = Quotient.mk _ (.inr
      (Circle.exp ((u : ℝ) * (Real.pi / 2)))) := by
    simp [A, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_first, apm_t97A03_circleArc, Path.ofLine,
      apm_t97A03_circleOne, apm_t97A03_circleI]
  have hB (u : unitInterval) : B u = Quotient.mk _ (.inr
      (Circle.exp (-(Real.pi) + (u : ℝ) * (Real.pi / 2)))) := by
    change (Quotient.mk _ (Sum.inr (Circle.exp
      ((1 - (1 - (u : ℝ))) * Complex.arg (apm_t97A03_circleI : ℂ) +
        (1 - (u : ℝ)) * Complex.arg (apm_t97A03_circleNegOne : ℂ)))⁻¹) : OSC) = _
    rw [← Circle.exp_neg]
    congr 3
    simp only [apm_t97A03_circleI, apm_t97A03_circleNegOne,
      Complex.arg_I, Complex.arg_neg_one]
    ring
  have hD (u : unitInterval) : D u = Quotient.mk _ (.inr
      (Circle.exp (-((1 - (u : ℝ)) * (Real.pi / 2))))) := by
    change (Quotient.mk _ (Sum.inr (Circle.exp
      ((1 - (1 - (u : ℝ))) * Complex.arg (apm_t97A03_circleOne : ℂ) +
        (1 - (u : ℝ)) * Complex.arg (apm_t97A03_circleI : ℂ)))⁻¹) : OSC) = _
    simp only [apm_t97A03_circleOne, apm_t97A03_circleI, Complex.arg_one,
      Complex.arg_I, mul_zero, zero_add, Circle.exp_neg]
  have hαval (a b : ℝ) (z : Circle)
      (hz : 0 ≤ a + b * (Real.arccos z.1.re / Real.pi) ∧
        a + b * (Real.arccos z.1.re / Real.pi) ≤ 1) :
      (α a b z : ℝ) = a + b * (Real.arccos z.1.re / Real.pi) := by
    change (Set.projIcc (0 : ℝ) 1 (by norm_num)
      (a + b * (Real.arccos z.1.re / Real.pi)) : ℝ) = _
    rw [Set.projIcc_of_mem _ hz]
  have hbounds (z : Circle) : 0 ≤ Real.arccos z.1.re / Real.pi ∧
      Real.arccos z.1.re / Real.pi ≤ 1 :=
    ⟨div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le,
      (div_le_one Real.pi_pos).2 (Real.arccos_le_pi _)⟩
  have hsmall (z : Circle) (hz : 0 ≤ z.1.re) :
      Real.arccos z.1.re / Real.pi ≤ 1 / 2 := by
    apply (div_le_iff₀ Real.pi_pos).2
    linarith [Real.arccos_le_pi_div_two.mpr hz]
  have hlarge (z : Circle) (hz : z.1.re ≤ 0) :
      1 / 2 ≤ Real.arccos z.1.re / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    have h := Real.arccos_le_arccos hz
    rw [Real.arccos_zero] at h
    linarith
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    change (if 0 ≤ z.1.im then U (z, 0) else L (z, 0)) = _
    simp [U, L, f₂, f₃, f₄, P, R, E, A, B, D, α, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle,
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_upper, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_lower]
  · intro z
    change (if 0 ≤ z.1.im then U (z, 1) else L (z, 1)) = _
    have hb := hbounds z
    by_cases hi : 0 ≤ z.1.im
    · rw [if_pos hi]
      have hexp : Circle.exp (Real.arccos z.1.re) = z := by
        have h := Complex.arg_of_im_nonneg_of_ne_zero hi (Circle.coe_ne_zero z)
        simp only [Circle.norm_coe, div_one] at h
        rw [← h, Circle.exp_arg]
      change (if 0 ≤ z.1.re then _ else _) = _
      split_ifs with hr
      · rw [hA, hαval 0 2 z (by have := hsmall z hr; constructor <;> linarith)]
        rw [show (0 + 2 * (Real.arccos z.1.re / Real.pi)) * (Real.pi / 2) =
          Real.arccos z.1.re by field_simp; ring, hexp]
      · change f₂ 1 (α (-1) 2 z) = _
        simp only [f₂, Set.Icc.coe_one, one_mul, Path.extend_extends']
        rw [hE, hαval (-1) 2 z (by have := hlarge z (le_of_not_ge hr); constructor <;> linarith)]
        rw [show (1 - (-1 + 2 * (Real.arccos z.1.re / Real.pi))) * (Real.pi / 2) +
          (-1 + 2 * (Real.arccos z.1.re / Real.pi)) * Real.pi =
          Real.arccos z.1.re by field_simp; ring, hexp]
    · rw [if_neg hi]
      have hexp : Circle.exp (-Real.arccos z.1.re) = z := by
        have h := Complex.arg_of_im_neg (lt_of_not_ge hi)
        simp only [Circle.norm_coe, div_one] at h
        rw [← h, Circle.exp_arg]
      change (if z.1.re ≤ 0 then _ else _) = _
      split_ifs with hr
      · change f₃ 1 (α 2 (-2) z) = _
        rw [h₃end, hB, hαval 2 (-2) z (by have := hlarge z hr; constructor <;> linarith)]
        rw [show -Real.pi + (2 + -2 * (Real.arccos z.1.re / Real.pi)) * (Real.pi / 2) =
          -Real.arccos z.1.re by field_simp; ring, hexp]
      · change f₄ 1 (α 1 (-2) z) = _
        rw [h₄end, hD, hαval 1 (-2) z (by have := hsmall z (le_of_not_ge hr); constructor <;> linarith)]
        rw [show -((1 - (1 + -2 * (Real.arccos z.1.re / Real.pi))) * (Real.pi / 2)) =
          -Real.arccos z.1.re by field_simp; ring, hexp]
  · intro t
    change (if _ then U _ else L _) = _
    norm_num [U, α, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_circleOne, Set.projIcc]
  · intro t
    change (if _ then U _ else L _) = _
    norm_num [U, α, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_circleI, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half, Set.projIcc]
  · intro t
    change (if _ then U _ else L _) = _
    norm_num [U, α, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_circleNegOne, Set.projIcc, Real.pi_ne_zero]
    exact h₂1 t
  · intro t
    change (if _ then U _ else L _) = _
    norm_num [L, α, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_angle, apm_t97A03_circleNegI, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_half, Set.projIcc]
    exact h₃1 t
  · intro z hz t
    have hedge (u : unitInterval) : OQ (E u) = OV := by
      rw [hE]
      apply Quotient.sound
      apply Relation.EqvGen.rel
      apply apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
      change (Circle.exp _ : ℂ).re ≤ 0 ∧ 0 ≤ (Circle.exp _ : ℂ).im
      have hl : Real.pi / 2 ≤ (1 - (u : ℝ)) * (Real.pi / 2) + (u : ℝ) * Real.pi := by
        nlinarith [u.2.1, Real.pi_pos]
      have hu : (1 - (u : ℝ)) * (Real.pi / 2) + (u : ℝ) * Real.pi ≤ Real.pi := by
        nlinarith [u.2.2, Real.pi_pos]
      have hre (r : ℝ) : (Circle.exp r : ℂ).re = Real.cos r := by
        simp [Circle.coe_exp, Complex.exp_re]
      have him (r : ℝ) : (Circle.exp r : ℂ).im = Real.sin r := by
        simp [Circle.coe_exp, Complex.exp_im]
      constructor
      · rw [hre]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hl (hu.trans (by linarith [Real.pi_pos]))
      · rw [him]
        exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) hu
    change OQ (if 0 ≤ z.1.im then U (z,t) else L (z,t)) = _
    rw [if_pos hz.2]
    change OQ (if 0 ≤ z.1.re then _ else _) = _
    split_ifs with hr
    · have he := (hα z (le_antisymm hz.1 hr)).1
      rw [he, A.target]
      rfl
    · change OQ (E.extend ((t : ℝ) * (α (-1) 2 z : ℝ))) = _
      exact hedge (Set.projIcc 0 1 (by norm_num) _)


/-- A single family on the disjoint union respects the slid relation, and
its projection also respects the stronger collapse relation. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw_motion :
    ∃ H : C(Sum apm_t97A03_TwoSpheres Circle, C(unitInterval, OSC)),
      (∀ x, H x 0 = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw x) ∧
      (∀ x, H x 1 = Quotient.mk _ x) ∧
      (∀ x y, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel x y → H x = H y) ∧
      (∀ x y, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel x y →
        (OQC).comp (H x) = (OQC).comp (H y)) := by
  obtain ⟨HS, hs0, hs1, hsN⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion
  obtain ⟨HC, hc0, hc1, h0, h1, h2, h3, ha⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_circle_motion
  let H : C(Sum apm_t97A03_TwoSpheres Circle, C(unitInterval, OSC)) :=
    ⟨Sum.elim
      (fun w => if w.1 = 0 then ContinuousMap.const _ (Quotient.mk _ (.inl (0, w.2)))
        else HS w.2) HC, by
      rw [continuous_sum_dom]
      constructor
      · rw [continuous_prod_of_discrete_left]
        intro i
        fin_cases i
        · exact ContinuousMap.continuous_const'.comp
            (continuous_coinduced_rng.comp (continuous_inl.comp (continuous_const.prodMk continuous_id)))
        · exact HS.continuous
      · exact HC.continuous⟩
  have hrel : ∀ x y, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_SlidRel x y → H x = H y := by
    intro x y h
    ext t
    cases h with
    | p0 => exact h0 t
    | p1 => exact h1 t
    | p2 => exact (h2 t).trans (hsN t).symm
    | p3 => exact (h3 t).trans (hsN t).symm
  refine ⟨H, ?_, ?_, hrel, ?_⟩
  · rintro (⟨i, x⟩ | z)
    · fin_cases i
      · rfl
      · exact hs0 x
    · exact hc0 z
  · rintro (⟨i, x⟩ | z)
    · fin_cases i
      · rfl
      · exact hs1 x
    · exact hc1 z
  · intro x y h
    cases h with
    | p0 => exact congrArg (ContinuousMap.comp (OQC)) (hrel _ _ .p0)
    | p1 => exact congrArg (ContinuousMap.comp (OQC)) (hrel _ _ .p1)
    | p2 => exact congrArg (ContinuousMap.comp (OQC)) (hrel _ _ .p2)
    | p3 => exact congrArg (ContinuousMap.comp (OQC)) (hrel _ _ .p3)
    | arc z hz => ext t; exact ha z hz t

/-- Shrink the sphere cap and all inserted copies of the connecting quarter
arc. The north pole of sheet one and both circle attachment points on that
sheet move along the same edge, so the families descend through SlidRel. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_left :
    (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_s.comp (ContinuousMap.mk
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q_continuous)).Homotopic
      (ContinuousMap.id OSC) := by
  obtain ⟨H, h0, h1, hs, hc⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw_motion
  let F : C(OSC, C(unitInterval, OSC)) :=
    ⟨Quotient.lift H (by
      intro x y h
      induction h with
      | rel x y h => exact hs x y h
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
    intro z
    exact h0 z
  · intro x
    refine Quotient.inductionOn x ?_
    intro z
    exact h1 z

/-- Project the same shrinking families: every point of the quarter arc
stays in that arc, whose image in the collapse quotient is constant. -/
theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_right :
    ((ContinuousMap.mk
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_q_continuous).comp apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_s).Homotopic
      (ContinuousMap.id OCC) := by
  obtain ⟨H, h0, h1, hs, hc⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_raw_motion
  let G : C(Sum apm_t97A03_TwoSpheres Circle, C(unitInterval, OCC)) :=
    ⟨fun x => (OQC).comp (H x), (ContinuousMap.continuous_postcomp (OQC)).comp H.continuous⟩
  let F : C(OCC, C(unitInterval, OCC)) :=
    ⟨Quotient.lift G (by
      intro x y h
      induction h with
      | rel x y h => exact hc x y h
      | refl x => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz),
      G.continuous.quotient_lift _⟩
  refine ⟨{ toFun := fun p => F p.2 p.1
            continuous_toFun := (F.continuous.comp continuous_snd).eval continuous_fst
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    refine Quotient.inductionOn x ?_
    intro z
    exact congrArg OQ (h0 z)
  · intro x
    refine Quotient.inductionOn x ?_
    intro z
    exact congrArg OQ (h1 z)

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
  exact ⟨apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_s, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_left, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_right⟩

end

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
  simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw]
  apply (continuous_quotientMap _ _).comp
  apply continuous_inl.comp
  apply (continuous_quotientMap _ _).comp
  apply continuous_prod_of_discrete_left.mpr
  intro i
  fin_cases i
  · simpa using (continuous_inl.comp continuous_id :
      Continuous (fun z : apm_t97A03_S2 => (Sum.inl z : Sum apm_t97A03_S2 apm_t97A03_S2)))
  · simpa using (continuous_inr.comp continuous_id :
      Continuous (fun z : apm_t97A03_S2 => (Sum.inr z : Sum apm_t97A03_S2 apm_t97A03_S2)))

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

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_outer_base :
    (quotientMap apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inr ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase) :
      apm_t97A03_modelWedge) = apm_t97A03_modelWedgeBase :=
  (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

/-- Every leg sends a fourth root of unity to the wedge basepoint. -/
private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base (j : Fin 3) (z : Circle) (hz : z ^ 4 = 1) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j z = apm_t97A03_modelWedgeBase := by
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_circlePow4
  simp only [hz]
  fin_cases j
  · show quotientMap _ _ (.inr (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft 1))) = _
    rw [ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft_base]; exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_outer_base
  · show quotientMap _ _ (.inr (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight 1))) = _
    rw [ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight_base]; exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_outer_base
  · show quotientMap _ _ (.inr (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew 1)) = _
    rw [ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew_base]; exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_outer_base

/-- Both sphere north poles map to the wedge basepoint. -/
private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_sphere_north (k : Fin 2) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere (k, apm_t97A03_north) = apm_t97A03_modelWedgeBase := by
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere
  fin_cases k
  · rfl
  · show quotientMap _ _ (.inl (quotientMap apm_t97A03_north apm_t97A03_north (.inr apm_t97A03_north))) = _
    rw [show (quotientMap apm_t97A03_north apm_t97A03_north (.inr apm_t97A03_north) :
        apm_t97A03_twoSphereWedge) = apm_t97A03_twoSphereBase from
      (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm]
    rfl

/-- Equal leg values are either the wedge basepoint or come from the same leg with
equal fourth powers (claude-14). -/
private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_cases (j k : Fin 3) (a b : Circle)
    (h : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j a = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg k b) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j a = apm_t97A03_modelWedgeBase ∨ (j = k ∧ a ^ 4 = b ^ 4) := by
  have hbase3 : ∀ X, X = ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase →
      (quotientMap apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inr X) : apm_t97A03_modelWedge) =
        apm_t97A03_modelWedgeBase := by
    rintro X rfl; exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm
  have hbaseA : a ^ 4 = 1 → apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j a = apm_t97A03_modelWedgeBase := fun ha => apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base j a ha
  unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_circlePow4 at h ⊢
  fin_cases j <;> fin_cases k <;>
    simp only [ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld, ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew, ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft, ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight] at h ⊢ <;>
    rcases apm_t97A03_wedge_rr h with h1 | h1 <;>
    first
    | exact Or.inl (hbase3 _ h1)
    | (rcases apm_t97A03_wedge_ll h1 with h2 | h2
       · first
         | (rcases apm_t97A03_wedge_ll h2 with h3 | h3
            · right; first | exact ⟨rfl, h3⟩ | exact h3 | exact ⟨trivial, h3⟩
            · exact Or.inl (hbaseA h3))
         | (rcases apm_t97A03_wedge_rr h2 with h3 | h3
            · right; first | exact ⟨rfl, h3⟩ | exact h3 | exact ⟨trivial, h3⟩
            · exact Or.inl (hbaseA h3))
         | exact Or.inl (hbaseA (apm_t97A03_wedge_lr h2).1)
         | exact Or.inl (hbaseA (apm_t97A03_wedge_lr h2.symm).2)
       · exact Or.inl (hbase3 _ (by rw [h2]; rfl)))
    | (rcases apm_t97A03_wedge_rr h1 with h2 | h2
       · right; first | exact ⟨rfl, h2⟩ | exact h2 | exact ⟨trivial, h2⟩
       · exact Or.inl (hbaseA h2))
    | exact Or.inl (hbase3 _ (by rw [(apm_t97A03_wedge_lr h1).1]; rfl))
    | exact Or.inl (hbaseA (apm_t97A03_wedge_lr h1.symm).2)

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p0 :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr apm_t97A03_circleOne) =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl (0, apm_t97A03_north)) := by
  have hr : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr apm_t97A03_circleOne) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 0 apm_t97A03_circleOne := by
    unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw; simp [apm_t97A03_circleOne]
  rw [hr, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base 0 _ (by apply Subtype.ext; simp [apm_t97A03_circleOne])]
  exact (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_sphere_north 0).symm

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p1 :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr apm_t97A03_circleI) =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl (0, apm_t97A03_north)) := by
  simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw,
    apm_t97A03_circleI, apm_t97A03_modelWedgeBase, apm_t97A03_twoSphereBase,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere]

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p2 :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr apm_t97A03_circleNegOne) =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl (1, apm_t97A03_north)) := by
  have hr : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr apm_t97A03_circleNegOne) = apm_t97A03_modelWedgeBase := by
    unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw; simp [apm_t97A03_circleNegOne]
  rw [hr]
  exact (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_sphere_north 1).symm

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p3 :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr apm_t97A03_circleNegI) =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl (1, apm_t97A03_north)) := by
  have hr : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr apm_t97A03_circleNegI) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 1 apm_t97A03_circleNegI := by
    unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw; simp [apm_t97A03_circleNegI]; norm_num
  rw [hr, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base 1 _ (by
    apply Subtype.ext; simp [apm_t97A03_circleNegI]; rw [neg_pow, Complex.I_pow_four]; norm_num)]
  exact (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_sphere_north 1).symm

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_arc
    (z : Circle) (hz : z ∈ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr z) =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl (0, apm_t97A03_north)) := by
  change z.1.re ≤ 0 ∧ 0 ≤ z.1.im at hz
  simp [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw,
    hz, apm_t97A03_modelWedgeBase, apm_t97A03_twoSphereBase,
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere]

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator
    {x y : Sum apm_t97A03_TwoSpheres Circle}
    (h : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw x =
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw y := by
  cases h with
  | p0 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p0
  | p1 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p1
  | p2 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p2
  | p3 => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_p3
  | arc z hz => exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_respects_aux_generator_aux_arc z hz

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

/-- Every circle point has a fourth root in the closed first quadrant (claude-14). -/
private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_root4 (ζ : Circle) :
    ∃ w : Circle, 0 ≤ w.1.re ∧ 0 ≤ w.1.im ∧ w ^ 4 = ζ := by
  set θ := toIcoMod Real.two_pi_pos 0 (Complex.arg (ζ : ℂ)) with hθ
  have hmem : θ ∈ Set.Ico 0 (2 * Real.pi) := by
    simpa using toIcoMod_mem_Ico Real.two_pi_pos 0 (Complex.arg (ζ : ℂ))
  have hpi := Real.pi_pos
  refine ⟨Circle.exp (θ / 4), ?_, ?_, ?_⟩
  · show 0 ≤ (Circle.exp (θ / 4) : ℂ).re
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  · show 0 ≤ (Circle.exp (θ / 4) : ℂ).im
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmem.1]) (by linarith [hmem.2])
  · rw [← Circle.exp_nsmul, nsmul_eq_mul, show ((4 : ℕ) : ℝ) * (θ / 4) = θ by push_cast; ring,
      hθ, toIcoMod, Circle.periodic_exp.sub_zsmul_eq, Circle.exp_arg]

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_map_surjective_aux_raw :
    Function.Surjective
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw := by
  have hI4 : apm_t97A03_circleI ^ 4 = 1 := by
    apply Subtype.ext; simp [apm_t97A03_circleI, Complex.I_pow_four]
  have hn4 : apm_t97A03_circleNegOne ^ 4 = 1 := by
    apply Subtype.ext; simp [apm_t97A03_circleNegOne]; norm_num
  have hnI4 : apm_t97A03_circleNegI ^ 4 = 1 := by
    apply Subtype.ext; simp [apm_t97A03_circleNegI]; rw [neg_pow, Complex.I_pow_four]; norm_num
  -- any z whose raw branch is a different leg or the arc maps to the basepoint there
  have hbase : ∀ (j : Fin 3) (z : Circle), z ^ 4 = 1 →
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr z) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j z := by
    intro j z hz
    rw [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base j z hz]
    dsimp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw]
    split_ifs <;> first | rfl | exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base _ z hz
  intro w
  induction w using Quotient.inductionOn with
  | h p =>
  rcases p with s | t
  · induction s using Quotient.inductionOn with
    | h q =>
    rcases q with x | x
    · exact ⟨.inl (0, x), rfl⟩
    · exact ⟨.inl (1, x), rfl⟩
  · -- the three legs: fourth roots in the first, third and fourth quadrants
    have hleg : ∀ (j : Fin 3) (ζ : Circle), ∃ z : Circle, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr z) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j z ∧ z ^ 4 = ζ := by
      intro j ζ
      obtain ⟨w, hre, him, hw⟩ := apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_root4 ζ
      fin_cases j
      · refine ⟨w, ?_, hw⟩
        dsimp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw]
        by_cases harc : w.1.re ≤ 0 ∧ 0 ≤ w.1.im
        · have hre0 : w.1.re = 0 := le_antisymm harc.1 hre
          -- then w = i
          have hwI : w = apm_t97A03_circleI := by
            apply Subtype.ext; apply Complex.ext
            · simp [apm_t97A03_circleI, hre0]
            · have hn : w.1.re ^ 2 + w.1.im ^ 2 = 1 := by
                have := Circle.normSq_coe w; rw [Complex.normSq_apply] at this; nlinarith
              rw [hre0] at hn
              have : w.1.im = 1 := by nlinarith
              simp [apm_t97A03_circleI, this]
          rw [if_pos harc, hwI]; exact (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base _ _ hI4).symm
        · rw [if_neg harc, if_pos ⟨hre, him⟩]; rfl
      · refine ⟨apm_t97A03_circleNegOne * w, ?_, by rw [mul_pow, hn4, one_mul, hw]⟩
        by_cases h1 : (apm_t97A03_circleNegOne * w) ^ 4 = 1
        · exact hbase 1 _ h1
        · dsimp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw]
          have hre' : (apm_t97A03_circleNegOne * w : Circle).1.re = -w.1.re := by
            simp [apm_t97A03_circleNegOne]
          have him' : (apm_t97A03_circleNegOne * w : Circle).1.im = -w.1.im := by
            simp [apm_t97A03_circleNegOne]
          rw [hre', him']
          by_cases h0 : w.1.im = 0
          · exfalso; apply h1
            have hn : w.1.re ^ 2 + w.1.im ^ 2 = 1 := by
              have := Circle.normSq_coe w; rw [Complex.normSq_apply] at this; nlinarith
            rw [h0] at hn
            have hr1 : w.1.re = 1 := by nlinarith
            have : w = 1 := by apply Subtype.ext; apply Complex.ext <;> simp [hr1, h0]
            rw [this, mul_one, hn4]
          · have himpos : 0 < w.1.im := lt_of_le_of_ne him (Ne.symm h0)
            rw [if_neg (by intro h; linarith [h.2]), if_neg (by intro h; linarith [h.2]),
              if_pos ⟨by linarith, by linarith⟩]; rfl
      · set iN := apm_t97A03_circleNegI
        refine ⟨iN * w, ?_, by rw [mul_pow, hnI4, one_mul, hw]⟩
        by_cases h1 : (iN * w) ^ 4 = 1
        · exact hbase 2 _ h1
        · dsimp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw]
          have hre' : (iN * w : Circle).1.re = w.1.im := by simp [iN, apm_t97A03_circleNegI]
          have him' : (iN * w : Circle).1.im = -w.1.re := by simp [iN, apm_t97A03_circleNegI]
          rw [hre', him']
          have hn : w.1.re ^ 2 + w.1.im ^ 2 = 1 := by
            have := Circle.normSq_coe w; rw [Complex.normSq_apply] at this; nlinarith
          by_cases h0 : w.1.re = 0
          · exfalso; apply h1
            rw [h0] at hn
            have hi1 : w.1.im = 1 := by nlinarith
            have : w = apm_t97A03_circleI := by
              apply Subtype.ext; apply Complex.ext <;> simp [apm_t97A03_circleI, hi1, h0]
            rw [this, mul_pow, hnI4, hI4, one_mul]
          · by_cases h0' : w.1.im = 0
            · exfalso; apply h1
              rw [h0'] at hn
              have hr1 : w.1.re = 1 := by nlinarith
              have : w = 1 := by apply Subtype.ext; apply Complex.ext <;> simp [hr1, h0']
              rw [this, mul_one, hnI4]
            · have hrp : 0 < w.1.re := lt_of_le_of_ne hre (Ne.symm h0)
              have hip : 0 < w.1.im := lt_of_le_of_ne him (Ne.symm h0')
              rw [if_neg (by intro h; linarith [h.1]), if_neg (by intro h; linarith [h.2]),
                if_neg (by intro h; linarith [h.1])]; rfl
    induction t using Quotient.inductionOn with
    | h r =>
    rcases r with u | c
    · induction u using Quotient.inductionOn with
      | h v =>
      rcases v with c | c
      · obtain ⟨z, hz, hz4⟩ := hleg 0 c
        exact ⟨.inr z, by rw [hz]; unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_circlePow4; rw [hz4]; rfl⟩
      · obtain ⟨z, hz, hz4⟩ := hleg 1 c
        exact ⟨.inr z, by rw [hz]; unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_circlePow4; rw [hz4]; rfl⟩
    · obtain ⟨z, hz, hz4⟩ := hleg 2 c
      exact ⟨.inr z, by rw [hz]; unfold apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_circlePow4; rw [hz4]; rfl⟩

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
  classical
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  change
    quotientMap apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
        (.inl (quotientMap apm_t97A03_north apm_t97A03_north
          (if i = 0 then .inl x else .inr x))) =
      quotientMap apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
        (.inl (quotientMap apm_t97A03_north apm_t97A03_north
          (if j = 0 then .inl y else .inr y))) at h
  apply ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective at h
  fin_cases i <;> fin_cases j
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte] at h
    have hxy :=
      ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective
        apm_t97A03_north apm_t97A03_north h
    simp only [Fin.zero_eta] at hxy ⊢
    subst hxy
    exact Relation.EqvGen.refl _
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, OfNat.ofNat_ne_zero] at h
    have hp :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        apm_t97A03_north apm_t97A03_north x y).mp h
    rcases hp with ⟨hx, hy⟩
    simp only [Fin.zero_eta] at hx hy ⊢
    subst hx
    subst hy
    have harc : apm_t97A03_circleNegOne ∈
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc := by
      simp [apm_t97A03_circleNegOne,
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc]
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _
          (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
            apm_t97A03_circleNegOne harc)))
      (Relation.EqvGen.rel _ _
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p2)
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, OfNat.ofNat_ne_zero] at h
    have hp :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        apm_t97A03_north apm_t97A03_north y x).mp h.symm
    rcases hp with ⟨hy, hx⟩
    simp only [Fin.zero_eta] at hx hy ⊢
    subst hx
    subst hy
    have harc : apm_t97A03_circleNegOne ∈
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc := by
      simp [apm_t97A03_circleNegOne,
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc]
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p2))
      (Relation.EqvGen.rel _ _
        (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
          apm_t97A03_circleNegOne harc))
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, OfNat.ofNat_ne_zero] at h
    have hxy :=
      ConstructionTargets.PointWedgeExactEquality.quotientMap_inr_injective
        apm_t97A03_north apm_t97A03_north h
    simp only [Fin.zero_eta] at hxy ⊢
    subst hxy
    exact Relation.EqvGen.refl _

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_fourthRoots
    (z : Circle) (h : (z : ℂ) ^ 4 = 1) :
    z = apm_t97A03_circleOne ∨ z = apm_t97A03_circleNegOne ∨
      z = apm_t97A03_circleI ∨ z = apm_t97A03_circleNegI := by
  have hf : ((z : ℂ) ^ 2 - 1) * ((z : ℂ) ^ 2 + 1) = 0 := by
    calc
      ((z : ℂ) ^ 2 - 1) * ((z : ℂ) ^ 2 + 1) = (z : ℂ) ^ 4 - 1 := by ring
      _ = 0 := by rw [h]; ring
  rcases mul_eq_zero.mp hf with hm | hm
  · have hz : (z : ℂ) ^ 2 = 1 := sub_eq_zero.mp hm
    rcases sq_eq_one_iff.mp hz with hz | hz
    · left
      apply Subtype.ext
      simpa [apm_t97A03_circleOne] using hz
    · right; left
      apply Subtype.ext
      simpa [apm_t97A03_circleNegOne] using hz
  · have hz : (z : ℂ) ^ 2 = -1 := by
      exact eq_neg_of_add_eq_zero_left hm
    have hfI : ((z : ℂ) - Complex.I) * ((z : ℂ) + Complex.I) = 0 := by
      calc
        ((z : ℂ) - Complex.I) * ((z : ℂ) + Complex.I) =
            (z : ℂ) ^ 2 - Complex.I ^ 2 := by ring
        _ = (z : ℂ) ^ 2 + 1 := by rw [Complex.I_sq]; ring
        _ = 0 := by rw [hz]; ring
    rcases mul_eq_zero.mp hfI with hz | hz
    · right; right; left
      apply Subtype.ext
      simpa [apm_t97A03_circleI] using sub_eq_zero.mp hz
    · right; right; right
      apply Subtype.ext
      simpa [apm_t97A03_circleNegI] using eq_neg_of_add_eq_zero_left hz

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex_aux_classify_aux_leg_base
    (j : Fin 3) (y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j y =
        apm_t97A03_modelWedgeBase) :
    (y : ℂ) ^ 4 = 1 := by
  have ho := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
    apm_t97A03_twoSphereBase
    ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
    apm_t97A03_twoSphereBase _).mp h.symm
  have ht := ho.2
  fin_cases j
  · have ht' := ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint 1 ht
    have hz := ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective 1 1 ht'
    exact congrArg Subtype.val hz
  · have ht' := ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint 1 ht
    have hz := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
      1 1 1 _).mp ht'.symm
    exact congrArg Subtype.val hz.2
  · have hz := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint 1
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint _).mp ht.symm
    exact congrArg Subtype.val hz.2

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex_aux_classify
    (y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y) =
        apm_t97A03_modelWedgeBase) :
    y ∈ apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc ∨
    y = apm_t97A03_circleOne ∨ y = apm_t97A03_circleNegOne ∨
      y = apm_t97A03_circleI ∨ y = apm_t97A03_circleNegI := by
  classical
  simp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw] at h
  split_ifs at h with h0 h1 h2
  · exact Or.inl h0
  · right
    exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_fourthRoots y
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex_aux_classify_aux_leg_base 0 y h)
  · right
    exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_fourthRoots y
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex_aux_classify_aux_leg_base 1 y h)
  · right
    exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_fourthRoots y
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex_aux_classify_aux_leg_base 2 y h)

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex
    (y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y) =
        apm_t97A03_modelWedgeBase) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
        (.inr y) (.inl (0, apm_t97A03_north)) := by
  rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex_aux_classify y h with
    hy | rfl | rfl | rfl | rfl
  · exact Relation.EqvGen.rel _ _
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.arc y hy)
  · exact Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p0
  · have ha : apm_t97A03_circleNegOne ∈
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc := by
      simp [apm_t97A03_circleNegOne,
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc]
    exact Relation.EqvGen.rel _ _
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.arc _ ha)
  · exact Relation.EqvGen.rel _ _
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p1
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p3)
      (Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p2))
        (Relation.EqvGen.rel _ _
          (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
            apm_t97A03_circleNegOne (by
              simp [apm_t97A03_circleNegOne,
                apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc]))))

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_sphere_vertex_aux_split
    (x : apm_t97A03_TwoSpheres) (y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
        apm_t97A03_modelWedgeBase ∧
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y) =
        apm_t97A03_modelWedgeBase := by
  have hs : ∃ q, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
      quotientMap apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inl q) := ⟨_, rfl⟩
  have hy : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y) = apm_t97A03_modelWedgeBase ∨
      ∃ r, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y) = quotientMap apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inr r) := by
    dsimp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw]
    split_ifs
    · exact Or.inl rfl
    all_goals exact Or.inr ⟨_, rfl⟩
  rcases hy with hb | ⟨r, hr⟩
  · exact ⟨h.trans hb, hb⟩
  · obtain ⟨q, hq⟩ := hs
    have heq := hq.symm.trans (h.trans hr)
    rw [apm_t97A03_wedge_quotientMap_eq_iff] at heq
    rcases heq with h' | ⟨hq', hr'⟩
    · cases h'
    · have hq0 : q = apm_t97A03_twoSphereBase := by
        rcases hq' with h'' | h''
        · exact Sum.inl_injective h''
        · cases h''
      have hr0 : r = ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase := by
        rcases hr' with h'' | h''
        · cases h''
        · exact Sum.inr_injective h''
      refine ⟨by rw [hq, hq0]; rfl, ?_⟩
      rw [hr, hr0]; exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_sphere_vertex_aux_sphere
    (x : apm_t97A03_TwoSpheres)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
        apm_t97A03_modelWedgeBase) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
        (.inl x) (.inl (0, apm_t97A03_north)) := by
  rcases x with ⟨i, x⟩
  change
    quotientMap apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
        (.inl (quotientMap apm_t97A03_north apm_t97A03_north
          (if i = 0 then .inl x else .inr x))) =
      quotientMap apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
        (.inl apm_t97A03_twoSphereBase) at h
  have hi :=
    ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective
      apm_t97A03_twoSphereBase
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase h
  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte] at hi ⊢
    have hx :=
      ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective
        apm_t97A03_north apm_t97A03_north hi
    subst x
    exact Relation.EqvGen.refl _
  · simp only [Fin.isValue, OfNat.ofNat_ne_zero, ↓reduceIte] at hi ⊢
    have hx :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        apm_t97A03_north apm_t97A03_north apm_t97A03_north x).mp hi.symm
    rcases hx with ⟨-, hx⟩
    subst x
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.p2))
      (Relation.EqvGen.rel _ _
        (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
          apm_t97A03_circleNegOne (by
            simp [apm_t97A03_circleNegOne,
              apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_arc])))

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_sphere_vertex
    (x : apm_t97A03_TwoSpheres) (y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    Relation.EqvGen
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel
          (.inl x) (.inl (0, apm_t97A03_north)) ∧
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y) =
        apm_t97A03_modelWedgeBase := by
  obtain ⟨hx, hy⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_sphere_vertex_aux_split x y h
  exact ⟨apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_sphere_vertex_aux_sphere x hx, hy⟩

/-- Fourth powers separate points of one closed quarter, away from the axes (claude-14). -/
private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_quarter_inj (x y : Circle) (hxy : x ^ 4 = y ^ 4) (hne : x ^ 4 ≠ 1)
    (hq : (0 ≤ x.1.re ∧ 0 ≤ x.1.im ∧ 0 ≤ y.1.re ∧ 0 ≤ y.1.im) ∨
      (x.1.re ≤ 0 ∧ x.1.im ≤ 0 ∧ y.1.re ≤ 0 ∧ y.1.im ≤ 0) ∨
      (0 < x.1.re ∧ x.1.im < 0 ∧ 0 < y.1.re ∧ y.1.im < 0)) : x = y := by
  have hn : y.1.re ^ 2 + y.1.im ^ 2 = 1 := by
    have := Circle.normSq_coe y; rw [Complex.normSq_apply] at this; nlinarith
  set ζ := x * y⁻¹ with hζ
  have hx : x = ζ * y := by rw [hζ, inv_mul_cancel_right]
  have hζ4 : ((ζ : Circle) : ℂ) ^ 4 = 1 := by
    have : ζ ^ 4 = 1 := by rw [hζ, mul_pow, inv_pow, hxy, mul_inv_cancel]
    have h' : ((ζ ^ 4 : Circle) : ℂ) = 1 := by rw [this]; rfl
    simpa using h'
  -- a point on an axis has fourth power 1
  have hax : ∀ w : Circle, (w.1.re = 0 ∨ w.1.im = 0) → w ^ 4 = 1 := by
    intro w hw
    have hnw : w.1.re ^ 2 + w.1.im ^ 2 = 1 := by
      have := Circle.normSq_coe w; rw [Complex.normSq_apply] at this; nlinarith
    apply Subtype.ext
    show (w : ℂ) ^ 4 = 1
    have hw2 : (w : ℂ) ^ 2 = (w.1.re ^ 2 - w.1.im ^ 2 : ℝ) := by
      apply Complex.ext
      · simp [sq, Complex.mul_re]
      · rcases hw with h | h <;> simp [sq, Complex.mul_im, h]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hw2]
    rcases hw with h | h
    · rw [h] at hnw ⊢; rw [show (0 : ℝ) ^ 2 - w.1.im ^ 2 = -1 by nlinarith]; push_cast; ring
    · rw [h] at hnw ⊢; rw [show w.1.re ^ 2 - (0 : ℝ) ^ 2 = 1 by nlinarith]; push_cast; ring
  have hcontra : ∀ w : Circle, (w.1.re = 0 ∨ w.1.im = 0) → y = w → False := by
    intro w hw hyw; apply hne; rw [hxy, hyw]; exact hax w hw
  rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_fourthRoots ζ hζ4 with h | h | h | h
  · rw [hx, h]; apply Subtype.ext; simp [apm_t97A03_circleOne]
  · exfalso
    have hre : x.1.re = -y.1.re := by rw [hx, h]; simp [apm_t97A03_circleNegOne]
    have him : x.1.im = -y.1.im := by rw [hx, h]; simp [apm_t97A03_circleNegOne]
    rcases hq with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ <;> nlinarith
  · exfalso
    have hre : x.1.re = -y.1.im := by rw [hx, h]; simp [apm_t97A03_circleI]
    have him : x.1.im = y.1.re := by rw [hx, h]; simp [apm_t97A03_circleI]
    rcases hq with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · exact hcontra y (Or.inr (by linarith)) rfl
    · exact hcontra y (Or.inr (by linarith)) rfl
    · linarith
  · exfalso
    have hre : x.1.re = y.1.im := by rw [hx, h]; simp [apm_t97A03_circleNegI]
    have him : x.1.im = -y.1.re := by rw [hx, h]; simp [apm_t97A03_circleNegI]
    rcases hq with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · exact hcontra y (Or.inl (by linarith)) rfl
    · exact hcontra y (Or.inl (by linarith)) rfl
    · linarith

private theorem apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_raw_cases (z : Circle) :
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr z) = apm_t97A03_modelWedgeBase ∨
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr z) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 0 z ∧ 0 ≤ z.1.re ∧ 0 ≤ z.1.im) ∨
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr z) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 1 z ∧ z.1.re ≤ 0 ∧ z.1.im ≤ 0) ∨
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr z) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg 2 z ∧ 0 < z.1.re ∧ z.1.im < 0) := by
  dsimp only [apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw]
  by_cases h0 : z.1.re ≤ 0 ∧ 0 ≤ z.1.im
  · rw [if_pos h0]; exact Or.inl rfl
  · rw [if_neg h0]
    by_cases h1 : 0 ≤ z.1.re ∧ 0 ≤ z.1.im
    · rw [if_pos h1]; exact Or.inr (Or.inl ⟨rfl, h1⟩)
    · rw [if_neg h1]
      by_cases h2 : z.1.re ≤ 0 ∧ z.1.im ≤ 0
      · rw [if_pos h2]; exact Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩))
      · rw [if_neg h2]
        push_neg at h0 h1 h2
        have him : z.1.im < 0 := by
          rcases le_total z.1.re 0 with h | h
          · exact h0 h
          · exact h1 h
        have hre : 0 < z.1.re := by
          by_contra hc; push_neg at hc; linarith [h2 hc]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, hre, him⟩))

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_circle_aux_normal_aux_injective
    (x y : Circle)
    (hx : apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) ≠
      apm_t97A03_modelWedgeBase)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    x = y := by
  have hne : ∀ j : Fin 3, apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) = apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_leg j x → x ^ 4 ≠ 1 := by
    intro j hj h4; exact hx (hj.trans (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_base j x h4))
  rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_raw_cases x with hb | ⟨hxr, hq⟩ | ⟨hxr, hq⟩ | ⟨hxr, hq⟩
  · exact absurd hb hx
  all_goals
    rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_raw_cases y with hyb | ⟨hyr, hq'⟩ | ⟨hyr, hq'⟩ | ⟨hyr, hq'⟩
    · exact absurd (h.trans hyb) hx
    all_goals
      have hlegs := hxr.symm.trans (h.trans hyr)
      rcases apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_leg_cases _ _ x y hlegs with hb | ⟨hjk, h4⟩
      · exact absurd (hxr.trans hb) hx
      · first
        | (exfalso; revert hjk; decide)
        | exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_quarter_inj x y h4 (hne _ hxr)
            (by first
              | exact Or.inl ⟨hq.1, hq.2, hq'.1, hq'.2⟩
              | exact Or.inr (Or.inl ⟨hq.1, hq.2, hq'.1, hq'.2⟩)
              | exact Or.inr (Or.inr ⟨hq.1, hq.2, hq'.1, hq'.2⟩))

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle
    (x : apm_t97A03_TwoSpheres) (y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel (.inl x) (.inr y) := by
  obtain ⟨hx, hy⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_sphere_vertex
      x y h
  exact Relation.EqvGen.trans _ _ _ hx
    (Relation.EqvGen.symm _ _
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex
        y hy))

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_sphere
    (x : Circle) (y : apm_t97A03_TwoSpheres)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inl y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) (.inl y) := by
  exact
    (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle
      y x h.symm).symm

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_circle_aux_normal
    (x y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    x = y ∨
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
          apm_t97A03_modelWedgeBase ∧
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y) =
          apm_t97A03_modelWedgeBase) := by
  by_cases hx :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
        apm_t97A03_modelWedgeBase
  · right
    exact ⟨hx, h ▸ hx⟩
  · left
    exact apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_circle_aux_normal_aux_injective x y hx h

private theorem
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_circle
    (x y : Circle)
    (h :
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw (.inr y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) (.inr y) := by
  rcases
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_circle_circle_aux_normal
        x y h with hxy | ⟨hx, hy⟩
  · subst y
    exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.trans _ _ _
      (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex
        x hx)
      (Relation.EqvGen.symm _ _
        (apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_raw_kernel_aux_sphere_circle_aux_circle_vertex
          y hy))

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
theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere_aux_fold_family :
    ∃ F : C(apm_t97A03_S2 × unitInterval, apm_t97A03_S2),
      (∀ x, x.1 2 ≤ 0 → F (x, 0) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold x) ∧
      (∀ x, F (x, 1) = x) ∧
      (∀ x (t : unitInterval), x.1 2 = (t : ℝ) →
        F (x, t) = apm_t97A03_north) := by
  obtain ⟨F, h0, h1, hb⟩ :=
    apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_contract_aux_s_homotopies_aux_sphere_motion_aux_fold_family
  refine ⟨F, ?_, h1, hb⟩
  intro x hx
  rw [h0 x hx]
  rfl

theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere_aux_glue
    (F : C(apm_t97A03_S2 × unitInterval, apm_t97A03_S2))
    (hF0 : ∀ x, x.1 2 ≤ 0 → F (x, 0) =
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_fold x)
    (hF1 : ∀ x, F (x, 1) = x)
    (hFb : ∀ x (t : unitInterval), x.1 2 = (t : ℝ) →
      F (x, t) = apm_t97A03_north) :
    ∃ H : C(apm_t97A03_S2, C(unitInterval, SC)),
      (∀ x, H x 0 = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap x) ∧
      (∀ x, H x 1 = Quotient.mk _ (.inl (1, x))) ∧
      (∀ t, H apm_t97A03_north t =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge t) := by
  let E := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge
  let G : C(apm_t97A03_S2 × unitInterval, SC) :=
    ⟨fun p => if (p.2 : ℝ) ≤ p.1.1 2 then
        E (Set.projIcc 0 1 (by norm_num) ((p.2 : ℝ) + 1 - p.1.1 2))
      else Quotient.mk _ (.inl (1, F p)), by
      apply Continuous.if_le
        (E.continuous.comp (continuous_projIcc.comp (by fun_prop)))
        (continuous_coinduced_rng.comp (continuous_inl.comp
          (continuous_const.prodMk F.continuous)))
        (by fun_prop) (by fun_prop)
      intro p hp
      have hb : F p = apm_t97A03_north := hFb p.1 p.2 hp.symm
      change E (Set.projIcc 0 1 (by norm_num)
        ((p.2 : ℝ) + 1 - p.1.1 2)) = Quotient.mk _ (.inl (1, F p))
      rw [show (p.2 : ℝ) + 1 - p.1.1 2 = 1 by linarith, hb]
      simpa [Set.projIcc] using E.target⟩
  refine ⟨ContinuousMap.curry G, ?_, ?_, ?_⟩
  · intro x
    dsimp [G, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap]
    split_ifs with hx
    · apply congrArg E
      apply Subtype.ext
      norm_num
    · rw [hF0 x (le_of_not_ge hx)]
  · intro x
    dsimp only [G]
    by_cases h : (1 : ℝ) ≤ x.1 2
    · have hx : x = apm_t97A03_north := by
        have hn : ‖x.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.2
        have hc_le : x.1 2 ≤ 1 := by
          calc x.1 2 ≤ |x.1 2| := le_abs_self _
            _ = ‖x.1 2‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖x.1‖ := PiLp.norm_apply_le x.1 2
            _ = 1 := hn
        have hc : x.1 2 = 1 := le_antisymm hc_le h
        have hs := EuclideanSpace.real_norm_sq_eq x.1
        simp [Fin.sum_univ_succ, hn, hc] at hs
        have h0 : x.1 0 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
        have h1 : x.1 1 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
        apply Subtype.ext
        ext i
        fin_cases i
        · simp [apm_t97A03_north, h0]
        · simp [apm_t97A03_north, h1]
        · simp [apm_t97A03_north, hc]
      subst x
      simpa [apm_t97A03_north, Set.projIcc] using E.target
    · simp [h, hF1]
  · intro t
    dsimp only [G]
    change (if (t : ℝ) ≤ 1 then E (Set.projIcc 0 1 (by norm_num) ((t : ℝ) + 1 - 1)) else _) = E t
    rw [if_pos t.2.2]
    congr 1
    apply Subtype.ext
    simp [Set.projIcc, apm_t97A03_north, t.2.1, t.2.2]

theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere :
    ∃ H : C(apm_t97A03_S2, C(unitInterval, SC)),
      (∀ x, H x 0 = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_cap x) ∧
      (∀ x, H x 1 = Quotient.mk _ (.inl (1, x))) ∧
      (∀ t, H apm_t97A03_north t = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge t) := by
  obtain ⟨F, h0, h1, hb⟩ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere_aux_fold_family
  exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_left_homotopy_aux_sphere_aux_glue
    F h0 h1 hb

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
  let E := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_edge
  let A := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_upperOne
  let B := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_lowerOne
  let P := E.trans A
  let R := B.trans E.symm
  let α := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle
  let f (t : unitInterval) (u : ℝ) := P.extend ((t : ℝ) / 2 + (1 - (t : ℝ) / 2) * u)
  let g (t : unitInterval) (u : ℝ) := R.extend ((1 - (t : ℝ) / 2) * u)
  have hf0 (t : unitInterval) : f t 0 = E t := by
    dsimp [f, P]
    rw [Path.extend_trans_of_le_half _ _ (by linarith [t.2.2])]
    convert E.extend_extends' t using 1 <;> congr 1 <;> ring
  have hf1 (t : unitInterval) : f t 1 = N₀ := by
    dsimp [f]
    rw [show (t : ℝ) / 2 + (1 - (t : ℝ) / 2) * 1 = 1 by ring]
    exact P.extend_one
  have hg0 (t : unitInterval) : g t 0 = N₀ := by simp [g]
  have hg1 (t : unitInterval) : g t 1 = E t := by
    dsimp [g, R]
    rw [Path.extend_trans_of_half_le _ _ (by linarith [t.2.2]), Path.extend_symm_apply]
    convert E.extend_extends' t using 1 <;> congr 1 <;> ring
  have hfend (u : unitInterval) : f 1 u = A u := by
    dsimp [f, P]
    rw [Path.extend_trans_of_half_le _ _ (by linarith [u.2.1])]
    convert A.extend_extends' u using 1 <;> congr 1 <;> ring
  have hgend (u : unitInterval) : g 1 u = B u := by
    dsimp [g, R]
    rw [Path.extend_trans_of_le_half _ _ (by linarith [u.2.2])]
    convert B.extend_extends' u using 1 <;> congr 1 <;> ring
  have ha0 : α apm_t97A03_circleOne = 0 := by
    apply Subtype.ext
    simp [α, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle, apm_t97A03_circleOne, Set.projIcc]
  have ha1 : α apm_t97A03_circleNegOne = 1 := by
    apply Subtype.ext
    simp [α, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_angle, apm_t97A03_circleNegOne, Set.projIcc, Real.pi_ne_zero]
  let H : C(Circle, C(unitInterval, SC)) := ContinuousMap.curry
    ⟨fun p => if 0 ≤ p.1.1.im then f p.2 (α p.1) else
      g p.2 (unitInterval.symm (α p.1)), by
      apply Continuous.if_le
        (P.continuous_extend.comp (by dsimp [α]; fun_prop))
        (R.continuous_extend.comp (by dsimp [α]; fun_prop))
        continuous_const (by fun_prop)
      intro p hp
      change f p.2 (α p.1) = g p.2 (unitInterval.symm (α p.1))
      rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_real p.1 hp.symm with h | h
      · simp only [h, ha0, unitInterval.symm_zero, Set.Icc.coe_zero,
          Set.Icc.coe_one, hf0, hg1]
      · simp only [h, ha1, unitInterval.symm_one, Set.Icc.coe_zero,
          Set.Icc.coe_one, hf1, hg0]⟩
  have haval (z : Circle) : (α z : ℝ) = Real.arccos z.1.re / Real.pi := by
    change (Set.projIcc (0 : ℝ) 1 (by norm_num) _ : ℝ) = _
    rw [Set.projIcc_of_mem _ (show Real.arccos z.1.re / Real.pi ∈ Set.Icc 0 1 from
      ⟨div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le,
      (div_le_one Real.pi_pos).2 (Real.arccos_le_pi _)⟩)]
  have hA (u : unitInterval) : A u = Quotient.mk _ (.inr
      (1, Circle.exp ((u : ℝ) * Real.pi))) := by
    simp [A, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_upperOne, apm_t97A03_circleArc, Path.ofLine,
      apm_t97A03_circleOne, apm_t97A03_circleNegOne]
  have hB (u : unitInterval) : B u = Quotient.mk _ (.inr
      (1, Circle.exp (-((1 - (u : ℝ)) * Real.pi)))) := by
    change (Quotient.mk _ (Sum.inr (1, (Circle.exp
      ((1 - (1 - (u : ℝ))) * Complex.arg (apm_t97A03_circleOne : ℂ) +
        (1 - (u : ℝ)) * Complex.arg (apm_t97A03_circleNegOne : ℂ)))⁻¹)) : SC) = _
    simp only [apm_t97A03_circleOne, apm_t97A03_circleNegOne, Complex.arg_one,
      Complex.arg_neg_one, mul_zero, zero_add, Circle.exp_neg]
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro z
    change (if 0 ≤ z.1.im then f 0 (α z) else g 0 (unitInterval.symm (α z))) = _
    simp only [f, g, Set.Icc.coe_zero, zero_div, sub_zero, one_mul, zero_add,
      Path.extend_extends', P, R, E, A, B, α,
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_contract_aux_circleOne, ContinuousMap.coe_mk]
    rfl
  · intro z
    change (if 0 ≤ z.1.im then f 1 (α z) else g 1 (unitInterval.symm (α z))) = _
    by_cases hi : 0 ≤ z.1.im
    · rw [if_pos hi, hfend, hA, haval]
      have hexp : Circle.exp (Real.arccos z.1.re) = z := by
        have h := Complex.arg_of_im_nonneg_of_ne_zero hi (Circle.coe_ne_zero z)
        simp only [Circle.norm_coe, div_one] at h
        rw [← h, Circle.exp_arg]
      rw [div_mul_cancel₀ _ Real.pi_ne_zero, hexp]
    · rw [if_neg hi, hgend, hB]
      have hexp : Circle.exp (-Real.arccos z.1.re) = z := by
        have h := Complex.arg_of_im_neg (lt_of_not_ge hi)
        simp only [Circle.norm_coe, div_one] at h
        rw [← h, Circle.exp_arg]
      simp only [unitInterval.coe_symm_eq, sub_sub_cancel, haval,
        div_mul_cancel₀ _ Real.pi_ne_zero, hexp]
  · intro t
    change (if _ then f t (α _) else g t _) = _
    rw [if_pos (by simp [apm_t97A03_circleOne]), ha0]
    exact hf0 t
  · intro t
    change (if _ then f t (α _) else g t _) = _
    rw [if_pos (by simp [apm_t97A03_circleNegOne]), ha1]
    exact hf1 t

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

/-- The two-circle legs: each closed semicircle goes once round its circle of
`threeBase` by `z ↦ z ^ 2` (the one-circle `_leg` uses `z ^ 4` for quarter arcs and
must not be composed with a further power). -/
private def
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2
    (j : Fin 3) (z : Circle) : apm_t97A03_modelWedge :=
  quotientMap apm_t97A03_twoSphereBase
    ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
    (.inr (match j with
      | ⟨0, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld
          (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft (z ^ 2))
      | ⟨1, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld
          (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight (z ^ 2))
      | ⟨2, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew (z ^ 2)))

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
          apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2
            0 z
      else if 0 ≤ z.1.im then
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2
          1 z
      else
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2
          2 z

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_sphere :
    Continuous (fun w : apm_t97A03_TwoSpheres ↦
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw
        (.inl w)) := by
  simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw]
  apply (continuous_quotientMap _ _).comp
  apply continuous_inl.comp
  apply (continuous_quotientMap _ _).comp
  apply continuous_prod_of_discrete_left.mpr
  intro i
  fin_cases i
  · simpa using (continuous_inl.comp continuous_id :
      Continuous (fun z : apm_t97A03_S2 => (Sum.inl z : Sum apm_t97A03_S2 apm_t97A03_S2)))
  · simpa using (continuous_inr.comp continuous_id :
      Continuous (fun z : apm_t97A03_S2 => (Sum.inr z : Sum apm_t97A03_S2 apm_t97A03_S2)))

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_leg
    (j : Fin 3) : Continuous (fun z : Circle ↦
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 j z) := by
  simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2]
  apply (continuous_quotientMap _ _).comp
  apply continuous_inr.comp
  fin_cases j
  · exact (continuous_quotientMap _ _).comp (continuous_inl.comp
      ((continuous_quotientMap _ _).comp
        (continuous_inl.comp (continuous_pow 2))))
  · exact (continuous_quotientMap _ _).comp (continuous_inl.comp
      ((continuous_quotientMap _ _).comp
        (continuous_inr.comp (continuous_pow 2))))
  · exact (continuous_quotientMap _ _).comp
      (continuous_inr.comp (continuous_pow 2))

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary_aux_sq
    (z : Circle) (hz : z.1.im = 0) : z ^ 2 = 1 := by
  apply Subtype.ext
  apply Complex.ext
  · have hn : ‖z.1‖ ^ 2 = 1 := by
      have hnorm : ‖z.1‖ = 1 := by simpa [Submonoid.unitSphere] using z.2
      rw [hnorm]
      norm_num
    change (z.1 ^ 2).re = 1
    simp only [pow_two, Complex.mul_re]
    rw [Complex.sq_norm] at hn
    simp only [Complex.normSq_apply] at hn
    nlinarith
  · change (z.1 ^ 2).im = 0
    simp [pow_two, Complex.mul_im, hz]

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary_aux_three
    (j : Fin 3) :
      (match j with
        | ⟨0, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld
            (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft 1)
        | ⟨1, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld
            (ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight 1)
        | ⟨2, _⟩ => ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew 1) =
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase := by
  fin_cases j <;>
    simp only [ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld,
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew,
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft,
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight,
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase,
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint]
  · exact congrArg (fun q => quotientMap _ _ (.inl q))
      ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight_base
  · exact ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew_base

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary
    (j : Fin 3) (z : Circle) (hz : z.1.im = 0) :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 j z =
        apm_t97A03_modelWedgeBase := by
  unfold apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2
  rw [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary_aux_sq z hz,
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary_aux_three j]
  exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle
    (i : Fin 2) :
    Continuous (fun z : Circle ↦
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw
        (.inr (i, z))) := by
  fin_cases i
  · simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
      ↓reduceIte]
    apply Continuous.if_le continuous_const
      (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_leg 0)
      continuous_const (Complex.continuous_im.comp continuous_subtype_val)
    intro z hz
    exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 0 z hz.symm).symm
  · simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
      OfNat.ofNat_ne_zero, ↓reduceIte]
    apply Continuous.if_le
      (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_leg 1)
      (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_leg 2)
      continuous_const (Complex.continuous_im.comp continuous_subtype_val)
    intro z hz
    exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 1 z hz.symm).trans
      (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 2 z hz.symm).symm

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous :
    Continuous
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw := by
  rw [continuous_sum_dom]
  constructor
  · exact
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_sphere
  · rw [continuous_prod_of_discrete_left]
    exact
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator_aux_sphere
    (i : Fin 2) :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw
          (.inl (i, apm_t97A03_north)) = apm_t97A03_modelWedgeBase := by
  fin_cases i <;>
    simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
      apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
      apm_t97A03_modelWedgeBase, apm_t97A03_twoSphereBase, Fin.isValue,
      Fin.zero_eta, ↓reduceIte, OfNat.ofNat_ne_zero]
  · exact congrArg (fun q => quotientMap _ _ (.inl q))
      (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator
    {x y : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)}
    (h : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw x =
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw y := by
  cases h with
  | c0a =>
      simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
        apm_t97A03_circleOne, Fin.isValue, ↓reduceIte, Complex.one_im, le_refl]
      exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator_aux_sphere 0).symm
  | c0b =>
      simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
        apm_t97A03_circleNegOne, Fin.isValue, ↓reduceIte, Complex.neg_im, Complex.one_im,
        neg_zero, le_refl]
      exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator_aux_sphere 1).symm
  | c1a =>
      simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
        OfNat.ofNat_ne_zero, ↓reduceIte, apm_t97A03_circleOne, Complex.one_im, le_refl]
      exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 1 apm_t97A03_circleOne (by norm_num [apm_t97A03_circleOne])).trans
        (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator_aux_sphere 1).symm
  | c1b =>
      simp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
        OfNat.ofNat_ne_zero, ↓reduceIte, apm_t97A03_circleNegOne, Complex.neg_im,
        Complex.one_im, neg_zero, le_refl]
      exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 1 apm_t97A03_circleNegOne (by norm_num [apm_t97A03_circleNegOne])).trans
        (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator_aux_sphere 0).symm
  | arc z hz =>
      have hb := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator_aux_sphere 0
      change (if 0 ≤ z.1.im then apm_t97A03_modelWedgeBase else _) = _
      change 0 ≤ z.1.im at hz
      rw [if_pos hz]
      exact hb.symm

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects
    {x y : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)}
    (h : Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel x y) :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw x =
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw y := by
  exact Relation.EqvGen.rec
    (fun _ _ h ↦
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects_aux_generator h)
    (fun _ ↦ rfl)
    (fun _ _ _ ih ↦ ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ ↦ ih₁.trans ih₂)
    h

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

/-- Every circle point has a square root in the closed upper half (claude-14). -/
private theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_sqrt_upper (ζ : Circle) :
    ∃ z : Circle, 0 ≤ z.1.im ∧ z ^ 2 = ζ := by
  set θ := toIcoMod Real.two_pi_pos 0 (Complex.arg (ζ : ℂ)) with hθ
  have hmem : θ ∈ Set.Ico 0 (2 * Real.pi) := by
    simpa using toIcoMod_mem_Ico Real.two_pi_pos 0 (Complex.arg (ζ : ℂ))
  refine ⟨Circle.exp (θ / 2), ?_, ?_⟩
  · show 0 ≤ (Circle.exp (θ / 2) : ℂ).im
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hmem.1]) (by linarith [hmem.2])
  · rw [sq, ← Circle.exp_add, add_halves, hθ, toIcoMod,
      Circle.periodic_exp.sub_zsmul_eq, Circle.exp_arg]

/-- ... and one in the closed lower half: multiply by `-1`. -/
private theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_sqrt_lower (ζ : Circle) :
    ∃ z : Circle, z.1.im ≤ 0 ∧ z ^ 2 = ζ := by
  obtain ⟨z, hz, hz2⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_sqrt_upper ζ
  refine ⟨apm_t97A03_circleNegOne * z, ?_, ?_⟩
  · show ((apm_t97A03_circleNegOne * z : Circle) : ℂ).im ≤ 0
    simp [apm_t97A03_circleNegOne]; linarith
  · rw [mul_pow, ← hz2]
    have : apm_t97A03_circleNegOne ^ 2 = 1 := by
      apply Subtype.ext; simp [apm_t97A03_circleNegOne]
    rw [this, one_mul]

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_surjective_aux_raw :
    Function.Surjective
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw := by
  intro w
  induction w using Quotient.inductionOn with
  | h p =>
  rcases p with s | t
  · induction s using Quotient.inductionOn with
    | h q =>
    rcases q with x | x
    · exact ⟨.inl (0, x), rfl⟩
    · exact ⟨.inl (1, x), rfl⟩
  · induction t using Quotient.inductionOn with
    | h r =>
    rcases r with u | c
    · induction u using Quotient.inductionOn with
      | h v =>
      rcases v with c | c
      · obtain ⟨z, hz, hz2⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_sqrt_lower c
        refine ⟨.inr (0, z), ?_⟩
        have htarget : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 0 z =
            quotientMap apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
              (.inr (quotientMap _ _ (.inl (quotientMap 1 1 (.inl c))))) := by
          unfold apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2; rw [hz2]; rfl
        rcases lt_or_eq_of_le hz with hlt | heq
        · show apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr (0, z)) = _
          dsimp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw]; simp only [if_true]; rw [if_neg (by linarith)]; exact htarget
        · show apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr (0, z)) = _
          dsimp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw]; simp only [if_true]; rw [if_pos heq.symm.le]
          exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 0 z heq).symm.trans htarget
      · obtain ⟨z, hz, hz2⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_sqrt_upper c
        refine ⟨.inr (1, z), ?_⟩
        show apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr (1, z)) = _
        dsimp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw]
        rw [if_neg (show (1 : Fin 2) ≠ 0 by decide), if_pos hz]
        unfold apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2; rw [hz2]; rfl
    · obtain ⟨z, hz, hz2⟩ := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_sqrt_lower c
      refine ⟨.inr (1, z), ?_⟩
      have htarget : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 2 z =
          quotientMap apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inr (quotientMap _ _ (.inr c))) := by
        unfold apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2; rw [hz2]; rfl
      show apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr (1, z)) = _
      dsimp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw]
      rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      rcases lt_or_eq_of_le hz with hlt | heq
      · rw [if_neg (by linarith)]; exact htarget
      · rw [if_pos heq.symm.le, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 1 z heq]
        exact (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary 2 z heq).symm.trans htarget

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_surjective :
    Function.Surjective
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map := by
  intro z
  obtain ⟨x, hx⟩ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_map_surjective_aux_raw z
  exact ⟨Quotient.mk _ x, hx⟩

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_sphere
    (x y : apm_t97A03_TwoSpheres)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inl x) (.inl y) := by
  classical
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  change
    quotientMap apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
        (.inl (quotientMap apm_t97A03_north apm_t97A03_north
          (if i = 0 then .inl x else .inr x))) =
      quotientMap apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase
        (.inl (quotientMap apm_t97A03_north apm_t97A03_north
          (if j = 0 then .inl y else .inr y))) at h
  apply ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective at h
  fin_cases i <;> fin_cases j
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte] at h
    have hxy := ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective
      apm_t97A03_north apm_t97A03_north h
    simp only [Fin.zero_eta] at hxy ⊢
    subst hxy
    exact Relation.EqvGen.refl _
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, OfNat.ofNat_ne_zero] at h
    obtain ⟨hx, hy⟩ :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        apm_t97A03_north apm_t97A03_north x y).mp h
    simp only [Fin.zero_eta] at hx hy ⊢
    subst hx
    subst hy
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
          apm_t97A03_circleNegOne (by simp
            [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc,
              apm_t97A03_circleNegOne]))))
      (Relation.EqvGen.rel _ _
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c0b)
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, OfNat.ofNat_ne_zero] at h
    obtain ⟨hy, hx⟩ :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        apm_t97A03_north apm_t97A03_north y x).mp h.symm
    simp only [Fin.zero_eta] at hx hy ⊢
    subst hx
    subst hy
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c0b))
      (Relation.EqvGen.rel _ _
        (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.arc
          apm_t97A03_circleNegOne (by simp
            [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc,
              apm_t97A03_circleNegOne])))
  · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, OfNat.ofNat_ne_zero] at h
    have hxy := ConstructionTargets.PointWedgeExactEquality.quotientMap_inr_injective
      apm_t97A03_north apm_t97A03_north h
    simp only [Fin.zero_eta] at hxy ⊢
    subst hxy
    exact Relation.EqvGen.refl _

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_sphere
    (x : apm_t97A03_TwoSpheres) (y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inl x) (.inl (0, apm_t97A03_north)) := by
  classical
  apply
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_sphere
  rcases y with ⟨i, y⟩
  fin_cases i
  · by_cases hy : 0 ≤ y.1.im
    · simpa [
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
        apm_t97A03_modelWedgeBase, hy] using h
    · have hx :=
        (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
          apm_t97A03_twoSphereBase
          ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase _ _).mp (by
            simpa [
              apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
              apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
              apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2,
              hy] using h)
      simpa [
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
        apm_t97A03_modelWedgeBase] using congrArg
          (fun z => quotientMap apm_t97A03_twoSphereBase
            ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inl z)) hx.1
  · by_cases hy : 0 ≤ y.1.im
    all_goals
      have hx :=
      (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
        apm_t97A03_twoSphereBase
        ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase _ _).mp (by
          simpa [
            apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
            apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
            apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2,
            hy] using h)
      simpa [
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw,
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
        apm_t97A03_modelWedgeBase] using congrArg
          (fun z => quotientMap apm_t97A03_twoSphereBase
            ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inl z)) hx.1

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_circle_aux_leg_base
    (j : Fin 3) (z : Circle)
    (h : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 j z =
      apm_t97A03_modelWedgeBase) : z ^ 2 = 1 := by
  unfold apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 at h
  fin_cases j
  all_goals
    simp only [apm_t97A03_modelWedgeBase] at h
    obtain ⟨_, h⟩ := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
      apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase _ _).mp h.symm
  · apply ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective at h
    apply ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective at h
    exact h
  · apply ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_injective at h
    obtain ⟨_, h⟩ := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
      (1 : Circle) (1 : Circle) _ _).mp h.symm
    exact h
  · obtain ⟨_, h⟩ := (ConstructionTargets.PointWedgeExactEquality.quotientMap_inl_eq_inr_iff
      ConstructionTargets.StatementSurfaceModels.twoCirclesPoint (1 : Circle) _ _).mp h.symm
    exact h

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_circle
    (x : apm_t97A03_TwoSpheres) (y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
      (.inr y) (.inl (0, apm_t97A03_north)) := by
  classical
  rcases y with ⟨i, z⟩
  fin_cases i
  · by_cases hz : 0 ≤ z.1.im
    · exact Relation.EqvGen.rel _ _
        (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.arc z hz)
    · have hb : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 0 z = apm_t97A03_modelWedgeBase := by
        have hs := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_sphere x (0, z) h
        simpa [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw, hz,
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
          apm_t97A03_modelWedgeBase] using h.symm.trans
            (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects hs)
      have hz2 := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_circle_aux_leg_base 0 z hb
      have hz2c : (z : ℂ) ^ 2 = 1 := congrArg Subtype.val hz2
      rcases (sq_eq_one_iff).mp hz2c with hz | hz
      · have hz' : z = apm_t97A03_circleOne := by apply Subtype.ext; simpa [apm_t97A03_circleOne] using hz
        subst z; exact Relation.EqvGen.rel _ _ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c0a
      · have hz' : z = apm_t97A03_circleNegOne := by apply Subtype.ext; simpa [apm_t97A03_circleNegOne] using hz
        subst z
        exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c0b)
          (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c0b))
            (Relation.EqvGen.rel _ _ (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.arc apm_t97A03_circleNegOne (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc, apm_t97A03_circleNegOne]))))
  · by_cases hz : 0 ≤ z.1.im
    all_goals
      have hs := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_sphere x (1, z) h
      have hb : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 (if 0 ≤ z.1.im then 1 else 2) z = apm_t97A03_modelWedgeBase := by
        simpa [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw, hz,
          apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_sphere,
          apm_t97A03_modelWedgeBase] using h.symm.trans
            (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_respects hs)
      have hz2 := apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_circle_aux_leg_base (if 0 ≤ z.1.im then 1 else 2) z hb
      have hz2c : (z : ℂ) ^ 2 = 1 := congrArg Subtype.val hz2
      rcases (sq_eq_one_iff).mp hz2c with hzp | hzp
      · have hz' : z = apm_t97A03_circleOne := by apply Subtype.ext; simpa [apm_t97A03_circleOne] using hzp
        subst z
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c1a)
          (Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c0b))
            (Relation.EqvGen.rel _ _ (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.arc apm_t97A03_circleNegOne (by simp [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_arc, apm_t97A03_circleNegOne]))))
      · have hz' : z = apm_t97A03_circleNegOne := by apply Subtype.ext; simpa [apm_t97A03_circleNegOne] using hzp
        subst z
        exact Relation.EqvGen.rel _ _ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel.c1b

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex
    (x : apm_t97A03_TwoSpheres) (y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    Relation.EqvGen
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
          (.inl x) (.inl (0, apm_t97A03_north)) ∧
      Relation.EqvGen
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
          (.inr y) (.inl (0, apm_t97A03_north)) := by
  exact ⟨
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_sphere x y h,
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_circle x y h⟩

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle
    (x : apm_t97A03_TwoSpheres) (y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inl x) (.inr y) := by
  obtain ⟨hx, hy⟩ :=
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex
      x y h
  exact Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.symm _ _ hy)

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_sphere
    (x : Fin 2 × Circle) (y : apm_t97A03_TwoSpheres)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) (.inl y) := by
  exact Relation.EqvGen.symm _ _
    (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle
      y x h.symm)

/-- `leg2 j a` is the basepoint when `a ^ 2 = 1` (claude-14). -/
private theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_leg2_base (j : Fin 3) (a : Circle) (ha : a ^ 2 = 1) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 j a = apm_t97A03_modelWedgeBase := by
  unfold apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2
  rw [ha, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary_aux_three j]
  exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

/-- Equal `leg2` values: basepoint, or same leg with equal squares (claude-14). -/
private theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_leg2_cases (j k : Fin 3) (a b : Circle)
    (h : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 j a = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 k b) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 j a = apm_t97A03_modelWedgeBase ∨ (j = k ∧ a ^ 2 = b ^ 2) := by
  have hbase3 : ∀ X, X = ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase →
      (quotientMap apm_t97A03_twoSphereBase ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeBase (.inr X) : apm_t97A03_modelWedge) =
        apm_t97A03_modelWedgeBase := by
    rintro X rfl; exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm
  have hbaseA : a ^ 2 = 1 → apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 j a = apm_t97A03_modelWedgeBase :=
    fun ha => apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_leg2_base j a ha
  unfold apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 at h ⊢
  fin_cases j <;> fin_cases k <;>
    simp only [ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeOld, ConstructionTargets.FiniteCircleWedgeFundamentalGroup.threeNew, ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoLeft, ConstructionTargets.FiniteCircleWedgeFundamentalGroup.twoRight] at h ⊢ <;>
    rcases apm_t97A03_wedge_rr h with h1 | h1 <;>
    first
    | exact Or.inl (hbase3 _ h1)
    | (rcases apm_t97A03_wedge_ll h1 with h2 | h2
       · first
         | (rcases apm_t97A03_wedge_ll h2 with h3 | h3
            · right; first | exact ⟨rfl, h3⟩ | exact h3 | exact ⟨trivial, h3⟩
            · exact Or.inl (hbaseA h3))
         | (rcases apm_t97A03_wedge_rr h2 with h3 | h3
            · right; first | exact ⟨rfl, h3⟩ | exact h3 | exact ⟨trivial, h3⟩
            · exact Or.inl (hbaseA h3))
         | exact Or.inl (hbaseA (apm_t97A03_wedge_lr h2).1)
         | exact Or.inl (hbaseA (apm_t97A03_wedge_lr h2.symm).2)
       · exact Or.inl (hbase3 _ (by rw [h2]; rfl)))
    | (rcases apm_t97A03_wedge_rr h1 with h2 | h2
       · right; first | exact ⟨rfl, h2⟩ | exact h2 | exact ⟨trivial, h2⟩
       · exact Or.inl (hbaseA h2))
    | exact Or.inl (hbase3 _ (by rw [(apm_t97A03_wedge_lr h1).1]; rfl))
    | exact Or.inl (hbaseA (apm_t97A03_wedge_lr h1.symm).2)

/-- Branches of the two-circle raw map on the circles (claude-14). -/
private theorem apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_raw_cases (x : Fin 2 × Circle) :
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) = apm_t97A03_modelWedgeBase ∨
      (x.1 = 0 ∧ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 0 x.2 ∧ x.2.1.im < 0) ∨
      (x.1 = 1 ∧ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 1 x.2 ∧ 0 ≤ x.2.1.im) ∨
      (x.1 = 1 ∧ apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) = apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_leg2 2 x.2 ∧ x.2.1.im < 0) := by
  obtain ⟨i, z⟩ := x
  fin_cases i
  · dsimp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw]
    by_cases hz : 0 ≤ z.1.im
    · left; simp [hz]
    · right; left; refine ⟨rfl, by simp [hz], by linarith⟩
  · dsimp only [apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw]
    by_cases hz : 0 ≤ z.1.im
    · right; right; left; refine ⟨rfl, by simp [hz], hz⟩
    · right; right; right; refine ⟨rfl, by simp [hz], by linarith⟩

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_square_aux_extract
    (x y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    x = y ∨
      ((x.2 : ℂ) = -(y.2 : ℂ) ∧ x.1 = y.1) ∨
      ∃ v : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle),
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) v ∧
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr y) v := by
  have hv : ∀ z : Fin 2 × Circle, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr z) = apm_t97A03_modelWedgeBase →
      Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
        (.inr z) (.inl (0, apm_t97A03_north)) := fun z hz =>
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_circle (0, apm_t97A03_north) z
      ((show apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl (0, apm_t97A03_north)) = apm_t97A03_modelWedgeBase from
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_sphere_north 0).trans hz.symm)
  have hbothbase : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) = apm_t97A03_modelWedgeBase →
      ∃ v : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle),
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) v ∧
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr y) v :=
    fun hb => ⟨_, hv x hb, hv y (h.symm.trans hb)⟩
  by_cases hb : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) = apm_t97A03_modelWedgeBase
  · exact Or.inr (Or.inr (hbothbase hb))
  have hsq_cases : ∀ a b : Circle, a ^ 2 = b ^ 2 → a = b ∨ (a : ℂ) = -(b : ℂ) := by
    intro a b hab
    have hc : ((a : ℂ) - b) * ((a : ℂ) + b) = 0 := by
      have : (a : ℂ) ^ 2 = (b : ℂ) ^ 2 := by exact_mod_cast congrArg Subtype.val hab
      linear_combination this
    rcases mul_eq_zero.mp hc with h1 | h1
    · left; apply Subtype.ext; exact sub_eq_zero.mp h1
    · right; linear_combination h1
  rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_raw_cases x with hx0 | ⟨hi, hr, hq⟩ | ⟨hi, hr, hq⟩ | ⟨hi, hr, hq⟩
  · exact absurd hx0 hb
  all_goals
    rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_raw_cases y with hy0 | ⟨hi', hr', hq'⟩ | ⟨hi', hr', hq'⟩ | ⟨hi', hr', hq'⟩
    · exact absurd (h.trans hy0) hb
    all_goals
      rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_leg2_cases _ _ _ _ (hr.symm.trans (h.trans hr')) with hb' | ⟨hjk, hsq⟩
      · exact absurd (hr.trans hb') hb
      · first
        | (exfalso; revert hjk; decide)
        | (have hii : x.1 = y.1 := by rw [hi, hi']
           rcases hsq_cases _ _ hsq with he | he
           · exact Or.inl (Prod.ext hii he)
           · exact Or.inr (Or.inl ⟨he, hii⟩))

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_square
    (x y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    x = y ∨
      ((x.2 : ℂ) = -(y.2 : ℂ) ∧ x.1 = y.1) ∨
      ∃ v : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle),
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) v ∧
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr y) v := by
  exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_square_aux_extract x y h

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_antipodal_aux_halves
    (x y : Fin 2 × Circle) (hneg : (x.2 : ℂ) = -(y.2 : ℂ)) (hi : x.1 = y.1)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    ∃ v : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle),
      Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) v ∧
      Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr y) v := by
  have hv : ∀ z : Fin 2 × Circle, apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr z) = apm_t97A03_modelWedgeBase →
      Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
        (.inr z) (.inl (0, apm_t97A03_north)) := fun z hz =>
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle_aux_vertex_aux_circle (0, apm_t97A03_north) z
      ((show apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inl (0, apm_t97A03_north)) = apm_t97A03_modelWedgeBase from
        apm_t97A03_invariants_aux_oneCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_aux_sphere_north 0).trans hz.symm)
  have hbothbase : apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) = apm_t97A03_modelWedgeBase →
      ∃ v : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle),
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) v ∧
        Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr y) v :=
    fun hb => ⟨_, hv x hb, hv y (h.symm.trans hb)⟩
  apply hbothbase
  by_contra hb
  have him : (y.2 : ℂ).im = -(x.2 : ℂ).im := by rw [hneg]; simp
  rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_raw_cases x with hx0 | ⟨hi, hr, hq⟩ | ⟨hi, hr, hq⟩ | ⟨hi, hr, hq⟩
  · exact hb hx0
  all_goals
    rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_raw_cases y with hy0 | ⟨hi', hr', hq'⟩ | ⟨hi', hr', hq'⟩ | ⟨hi', hr', hq'⟩
    · exact hb (h.trans hy0)
    all_goals
      rcases apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_leg2_cases _ _ _ _ (hr.symm.trans (h.trans hr')) with hb' | ⟨hjk, hsq⟩
      · exact hb (hr.trans hb')
      · first
        | (revert hjk; decide)
        | (change (y.2 : ℂ).im = _ at him; linarith)
        | (have h0 : (x.2 : ℂ).im = 0 := by
             change (y.2 : ℂ).im = _ at him; linarith
           exact hb (hr.trans (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_aux_leg2_base _ _
             (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_continuous_aux_circle_aux_boundary_aux_sq _ h0))))

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_antipodal
    (x y : Fin 2 × Circle) (hneg : (x.2 : ℂ) = -(y.2 : ℂ)) (hi : x.1 = y.1)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    ∃ v : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle),
      Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) v ∧
      Relation.EqvGen apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr y) v := by
  exact apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_antipodal_aux_halves x y hneg hi h

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal
    (x y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    x = y ∨
      ∃ v : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle),
        Relation.EqvGen
            apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
            (.inr x) v ∧
          Relation.EqvGen
            apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel
            (.inr y) v := by
  rcases
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_square
        x y h with hxy | ⟨hneg, hi⟩ | hv
  · exact Or.inl hxy
  · exact Or.inr
      (apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal_aux_antipodal
        x y hneg hi h)
  · exact Or.inr hv

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle
    (x y : Fin 2 × Circle)
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr x) =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw (.inr y)) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel (.inr x) (.inr y) := by
  rcases
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle_aux_normal
        x y h with rfl | ⟨v, hx, hy⟩
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.symm _ _ hy)

private theorem
    apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel
    {x y : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle)}
    (h :
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw x =
        apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw y) :
    Relation.EqvGen
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_Rel x y := by
  rcases x with x | x <;> rcases y with y | y
  · exact
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_sphere
        x y h
  · exact
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_sphere_circle
        x y h
  · exact
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_sphere
        x y h
  · exact
      apm_t97A03_invariants_aux_twoCircle_homotopyEquiv_aux_collapse_aux_normalForm_aux_continuousEquiv_aux_raw_kernel_aux_circle_circle
        x y h

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
