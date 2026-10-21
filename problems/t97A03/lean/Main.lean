import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.t97A03Closure
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.PolygonCellPiOne

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

/-- The opposite lifted interval from `A` to `B`.  Its endpoint differs in
the real lift by one full turn, so this is the complementary circle arc and
not a second choice of an arbitrary path. -/
noncomputable def apm_t97A03_complementaryCircleArc (A B : Circle) : Path A B :=
  Path.ofLine (f := fun t : ℝ ↦
      Circle.exp ((1 - t) * Complex.arg A +
        t * (Complex.arg B + 2 * Real.pi)))
    (by fun_prop) (by simp) (by simp)

lemma apm_t97A03_circleArcs_ne (A B : Circle) :
    apm_t97A03_circleArc A B ≠ apm_t97A03_complementaryCircleArc A B := by
  intro h
  have hm := congrArg (fun p : Path A B ↦ p ⟨(1 / 2 : ℝ), by norm_num⟩) h
  simp [apm_t97A03_circleArc, apm_t97A03_complementaryCircleArc,
    Path.ofLine] at hm
  rw [show (2 : ℝ)⁻¹ * (Complex.arg B + 2 * Real.pi) =
      2⁻¹ * Complex.arg B + Real.pi by ring, Circle.exp_add] at hm
  have hpi : (1 : Circle) = Circle.exp Real.pi := by
    apply mul_left_cancel (a := Circle.exp (2⁻¹ * Complex.arg B))
    simpa using hm
  exact Circle.exp_pi_ne_one hpi.symm

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
  sorry

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
  sorry

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
  /-
  PARTIAL boundary (closer hop 1).

  New progress: `apm_t97A03_surjective_of_fiber_card_two` proves that the
  frozen cardinality condition makes `p` surjective, by showing an omitted
  base point would have an empty fiber of cardinality zero.  Hence subsequent
  work may treat `p` as a genuine connected two-sheeted covering without
  separately recovering surjectivity from `IsCoveringMap`.

  The remaining theorem requires three major bridges.  First, the concrete
  EqvGen quotient for the base must be identified up to homotopy with
  `S² ∨ S¹ ∨ S¹`, and connected degree-two coverings must be classified by
  the three index-two subgroups of its `F₂` fundamental group, then matched to
  the two frozen quotient models.  Second, the cellular chain complex of each
  quotient must be connected to Mathlib singular homology to obtain ranks
  `1,3,2`.  Third, the covering injection on fundamental groups must be
  combined with a quantitative Nielsen--Schreier rank formula to obtain
  `FreeGroup (Fin 3)`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, all closed artifacts,
  Mathlib's covering/lifting/fundamental-groupoid, singular-homology,
  free-group, Schreier, and Nielsen--Schreier sources, and git history found no
  classification of connected coverings by subgroups, no CW/cellular homology
  comparison for these adjunction quotients, and no finite-index free-rank
  equality.  Mathlib proves only that subgroups of free groups are free and
  provides Schreier rank bounds; sibling `t00J08` independently records the
  missing quantitative equality, while `t94J04`, `t01A04`, and `t93A03`
  record the unavailable subgroup-cover and wedge fundamental-group bridges.
  Thus none of the six frozen conjuncts can yet be obtained merely by
  transporting through an existing classification theorem.

  Closer hop 2 exposes the base adjunction's two generating equalities as
  `apm_t97A03_base_north_eq` and `apm_t97A03_base_south_eq`. These are the
  exact point-set attachments needed by a future van Kampen or cellular model,
  but they do not supply either comparison theorem or the covering/subgroup
  classification, so the six-conjunct bridge remains open.

  CLOSER HOP 3: `apm_t97A03_fiber_equiv_fin_two` upgrades the frozen numeric
  fiber equation to an actual equivalence of every fiber subtype with `Fin 2`.
  It derives finiteness using `Nat.finite_of_card_ne_zero` and then applies
  `Fintype.equivOfCardEq`; thus explicit two-sheet fiber structure, including
  finiteness, is no longer hidden behind `Nat.card`. Together with hop 1's
  surjectivity lemma, the hypotheses now provide a surjective covering with
  genuinely two-element fibers. Renewed inspection of `IsCoveringMap` fiber
  trivializations, monodromy, fundamental-groupoid actions, `FreeGroupBasis`,
  singular homology, and the cover siblings found no theorem classifying such
  a connected two-sheet cover or computing its frozen invariants. Equal
  two-element fibers alone do not choose the global monodromy. The remaining
  bridge is still global covering classification plus van Kampen/cellular-to-
  singular comparison and quantitative Nielsen--Schreier. The frozen
  statement is unchanged.
  -/
  sorry
