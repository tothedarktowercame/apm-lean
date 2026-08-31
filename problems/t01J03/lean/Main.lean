import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.T01J03FrozenQuotientRepresentation
import ConstructionTargets.BoundaryTorusH0Cokernel
import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.TwiceSpiralBasedCoordinateInterface
import ConstructionTargets.TwiceSpiralFundamentalGroupExtraction
import ConstructionTargets.TwiceSpiralGluingHomologyTable

/-!
# APM t01J03: A twice-wound gluing of solid tori

## Statement repairs

None.

## Encoding questions

The informal "spirals twice" curve is encoded algebraically in genuine
fundamental groups. Boundary coordinates are required to be compatible with
the inclusions into the solid tori: the meridian is killed and the longitude
maps to the core generator. The glued space is the actual topological quotient.
-/

open CategoryTheory
open ConstructionTargets.T01J03FrozenQuotientRepresentation

noncomputable section

abbrev apm_t01J03_Torus := Circle × Circle
abbrev apm_t01J03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01J03_Disk2 := Metric.closedBall (0 : apm_t01J03_E2) 1
abbrev apm_t01J03_BoundaryCircle := Metric.sphere (0 : apm_t01J03_E2) 1
abbrev apm_t01J03_SolidTorus := Circle × apm_t01J03_Disk2
abbrev apm_t01J03_BoundaryTorus := Circle × apm_t01J03_BoundaryCircle

def apm_t01J03_boundaryInclusion :
    apm_t01J03_BoundaryTorus → apm_t01J03_SolidTorus :=
  fun z ↦ (z.1, ⟨z.2.1, le_of_eq z.2.2⟩)

/-- The boundary torus embeds continuously into the solid torus. This is the
map used in both fundamental-group homomorphisms below. -/
lemma apm_t01J03_continuous_boundaryInclusion :
    Continuous apm_t01J03_boundaryInclusion := by
  exact continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

inductive apm_t01J03_glueRel (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :
    Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus →
      Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus → Prop
  | glue (z : apm_t01J03_BoundaryTorus) :
      apm_t01J03_glueRel h
        (Sum.inl (apm_t01J03_boundaryInclusion z))
        (Sum.inr (apm_t01J03_boundaryInclusion (h z)))

def apm_t01J03_gluedSpace (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :=
  Quotient (Relation.EqvGen.setoid (apm_t01J03_glueRel h))

noncomputable instance (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) : TopologicalSpace (apm_t01J03_gluedSpace h) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t01J03_glueRel h)) z)
    inferInstance

theorem apm_t01J03_glueRel_iff_coordinateGlueRel
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) (x y) :
    apm_t01J03_glueRel h x y ↔ CoordinateGlueRel h x y := by
  constructor <;> rintro ⟨z⟩
  · exact CoordinateGlueRel.glue z
  · exact apm_t01J03_glueRel.glue z

theorem apm_t01J03_eqvGen_iff_coordinateEqvGen
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) (x y) :
    Relation.EqvGen (apm_t01J03_glueRel h) x y ↔
      Relation.EqvGen (CoordinateGlueRel h) x y := by
  constructor
  · intro hxy
    induction hxy with
    | rel a b hab =>
        exact Relation.EqvGen.rel _ _
          ((apm_t01J03_glueRel_iff_coordinateGlueRel h a b).mp hab)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    induction hxy with
    | rel a b hab =>
        exact Relation.EqvGen.rel _ _
          ((apm_t01J03_glueRel_iff_coordinateGlueRel h a b).mpr hab)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def apm_t01J03_homeomorph_coordinateGluing
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) :
    apm_t01J03_gluedSpace h ≃ₜ CoordinateGluing h where
  toFun := Quotient.lift (fun x ↦ Quotient.mk _ x) fun _ _ hxy ↦
    Quotient.sound ((apm_t01J03_eqvGen_iff_coordinateEqvGen h _ _).mp hxy)
  invFun := Quotient.lift (fun x ↦ Quotient.mk _ x) fun _ _ hxy ↦
    Quotient.sound ((apm_t01J03_eqvGen_iff_coordinateEqvGen h _ _).mpr hxy)
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by rintro ⟨x⟩; rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

def apm_t01J03_homeomorph_gluing
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) :
    apm_t01J03_gluedSpace h ≃ₜ
      ConstructionTargets.SolidTorusGluingOpenCover.Gluing
        (conjugateBoundaryHomeomorph h) :=
  (apm_t01J03_homeomorph_coordinateGluing h).trans
    (coordinateGluingHomeomorph h)

@[simp] theorem apm_t01J03_homeomorph_coordinateGluing_mk
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (x : Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus) :
    apm_t01J03_homeomorph_coordinateGluing h (Quotient.mk _ x) =
      Quotient.mk _ x := rfl

@[simp] theorem apm_t01J03_homeomorph_gluing_mk
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (x : Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus) :
    apm_t01J03_homeomorph_gluing h (Quotient.mk _ x) = Quotient.mk _ x := rfl

def apm_t01J03_gluedInl (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :
    apm_t01J03_SolidTorus → apm_t01J03_gluedSpace h :=
  fun x ↦ Quotient.mk _ (Sum.inl x)

def apm_t01J03_gluedInr (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) :
    apm_t01J03_SolidTorus → apm_t01J03_gluedSpace h :=
  fun x ↦ Quotient.mk _ (Sum.inr x)

lemma apm_t01J03_continuous_gluedInl
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) :
    Continuous (apm_t01J03_gluedInl h) := by
  exact continuous_coinduced_rng.comp continuous_inl

lemma apm_t01J03_continuous_gluedInr
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) :
    Continuous (apm_t01J03_gluedInr h) := by
  exact continuous_coinduced_rng.comp continuous_inr

/-- The two canonical maps into the quotient agree on precisely the boundary
points prescribed by the gluing homeomorphism. -/
lemma apm_t01J03_gluedInl_boundary_eq_gluedInr
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z : apm_t01J03_BoundaryTorus) :
    apm_t01J03_gluedInl h (apm_t01J03_boundaryInclusion z) =
      apm_t01J03_gluedInr h (apm_t01J03_boundaryInclusion (h z)) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t01J03_glueRel.glue z))

/-- Compatible maps out of the two solid tori respect the equivalence relation
used to form the glued space. -/
lemma apm_t01J03_gluedDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) {x y}
    (hxy : Relation.EqvGen (apm_t01J03_glueRel h) x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
    cases hab with
    | glue z => exact hfg z
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The actual continuous pushout eliminator for the generated-relation
quotient: compatible continuous maps from the two pieces descend to the glued
space. -/
def apm_t01J03_gluedDesc
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) :
    C(apm_t01J03_gluedSpace h, Y) := by
  let raw : Sum apm_t01J03_SolidTorus apm_t01J03_SolidTorus → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy =>
      apm_t01J03_gluedDesc_respects h f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy =>
      apm_t01J03_gluedDesc_respects h f g hfg hxy)⟩

@[simp] lemma apm_t01J03_gluedDesc_gluedInl
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) (x : apm_t01J03_SolidTorus) :
    apm_t01J03_gluedDesc h f g hfg (apm_t01J03_gluedInl h x) = f x := rfl

@[simp] lemma apm_t01J03_gluedDesc_gluedInr
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z))) (x : apm_t01J03_SolidTorus) :
    apm_t01J03_gluedDesc h f g hfg (apm_t01J03_gluedInr h x) = g x := rfl

/-- The descended map is uniquely determined by its restrictions to the two
solid-torus pieces. -/
lemma apm_t01J03_gluedDesc_unique
    {Y : Type*} [TopologicalSpace Y]
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (f g : C(apm_t01J03_SolidTorus, Y))
    (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) =
      g (apm_t01J03_boundaryInclusion (h z)))
    (u : C(apm_t01J03_gluedSpace h, Y))
    (hul : ∀ x, u (apm_t01J03_gluedInl h x) = f x)
    (hur : ∀ x, u (apm_t01J03_gluedInr h x) = g x) :
    u = apm_t01J03_gluedDesc h f g hfg := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (x | x)
  · exact hul x
  · exact hur x

def apm_t01J03_gluedBasepoint (h : apm_t01J03_BoundaryTorus ≃ₜ
    apm_t01J03_BoundaryTorus) (z₀ : apm_t01J03_BoundaryTorus) :
    apm_t01J03_gluedSpace h :=
  Quotient.mk _ (Sum.inl (apm_t01J03_boundaryInclusion z₀))

abbrev apm_t01J03_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- The frozen product-of-complex-circles presentation is homeomorphic to the
Euclidean boundary-torus presentation used by the Mayer--Vietoris calculation. -/
noncomputable def apm_t01J03_torusHomeomorphBoundaryTorus :
    apm_t01J03_Torus ≃ₜ apm_t01J03_BoundaryTorus :=
  (Homeomorph.refl Circle).prodCongr
    ConstructionTargets.CircleHomology.circleHomeomorphSphereOne

/-- The four integral homology clauses of `apm_t01J03_bridge_1`, separated
from its still-independent fundamental-group clause. -/
theorem apm_t01J03_torus_module_homology :
    Nonempty (apm_t01J03_H 0 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 apm_t01J03_Torus ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (apm_t01J03_H 2 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t01J03_H k apm_t01J03_Torus) := by
  let e (k : ℕ) :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      apm_t01J03_torusHomeomorphBoundaryTorus.toHomotopyEquiv k
  obtain ⟨h0, h1, h2, hhigh⟩ :=
    ConstructionTargets.BoundaryTorusH0Cokernel.boundaryTorus_complete_module_homology
  refine ⟨⟨e 0 ≪≫ Classical.choice h0⟩,
    ⟨e 1 ≪≫ Classical.choice h1⟩,
    ⟨e 2 ≪≫ Classical.choice h2⟩, ?_⟩
  intro k hk
  exact (hhigh k hk).of_iso (e k)

#print axioms apm_t01J03_torus_module_homology

def apm_t01J03_hasTwiceSpiral
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z₀ : apm_t01J03_BoundaryTorus)
    (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ) : Prop :=
  (∀ g, c₁ ((FundamentalGroup.map
      ⟨apm_t01J03_boundaryInclusion, continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩ z₀) g) =
      Multiplicative.ofAdd (e₁ g).toAdd.2) ∧
  (∀ g, c₂ ((FundamentalGroup.map
      ⟨apm_t01J03_boundaryInclusion, continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩ (h z₀)) g) =
      Multiplicative.ofAdd (e₂ g).toAdd.2) ∧
  e₂ ((FundamentalGroup.map ⟨h, h.continuous⟩ z₀)
    (e₁.symm (Multiplicative.ofAdd (1, 0)))) =
      Multiplicative.ofAdd (1, 2)

/-- Why this unblocks the first five conjuncts of `apm_t01j03`: this is the
missing fundamental-group and integral singular-homology computation for the
actual product `Circle × Circle`, including vanishing above its dimension. -/
theorem apm_t01J03_bridge_1 :
    Nonempty
      (FundamentalGroup apm_t01J03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty (apm_t01J03_H 0 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 apm_t01J03_Torus ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (apm_t01J03_H 2 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t01J03_H k apm_t01J03_Torus) := by
  let e : FundamentalGroup apm_t01J03_Torus (1, 1) ≃*
      Multiplicative (ℤ × ℤ) :=
    (ConstructionTargets.FundamentalGroupProduct.fundamentalGroupProdMulEquiv
        (1 : Circle) (1 : Circle)).trans
      (ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.prodCongr
        ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt) |>.trans
      (MulEquiv.prodMultiplicative ℤ ℤ).symm
  obtain ⟨h0, h1, h2, hhigh⟩ := apm_t01J03_torus_module_homology
  exact ⟨⟨e⟩, h0, h1, h2, hhigh⟩

#print axioms apm_t01J03_bridge_1

/-- The five homology clauses needed by `apm_t01J03_bridge_2`, separated from
its still-independent fundamental-group clause. -/
theorem apm_t01J03_twiceSpiral_module_homology
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z₀ : apm_t01J03_BoundaryTorus)
    (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ)
    (hspiral : apm_t01J03_hasTwiceSpiral h z₀ e₁ e₂ c₁ c₂) :
    let M := apm_t01J03_gluedSpace h
    Nonempty (apm_t01J03_H 0 M ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 M ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Limits.IsZero (apm_t01J03_H 2 M) ∧
    Nonempty (apm_t01J03_H 3 M ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 4 ≤ k → Limits.IsZero (apm_t01J03_H k M) := by
  dsimp only
  rcases hspiral with ⟨hinc₁, hinc₂, h10⟩
  let h' := conjugateBoundaryHomeomorph h
  let z₀' := coordinateBoundaryTorusHomeomorph z₀
  have hinc₁' : ∀ p, c₁ (FundamentalGroup.map
      ⟨ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
        ConstructionTargets.SolidTorusGluingOpenCover.continuous_boundaryInclusion⟩
      z₀' p) =
        ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom (e₁ p) := by
    simpa [z₀', coordinateBoundaryTorusHomeomorph,
      apm_t01J03_boundaryInclusion,
      ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
      ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom] using hinc₁
  have hinc₂' : ∀ p, c₂ (FundamentalGroup.map
      ⟨ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
        ConstructionTargets.SolidTorusGluingOpenCover.continuous_boundaryInclusion⟩
      (h' z₀') p) =
        ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom (e₂ p) := by
    simpa [h', z₀', conjugateBoundaryHomeomorph,
      coordinateBoundaryTorusHomeomorph, apm_t01J03_boundaryInclusion,
      ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
      ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom] using hinc₂
  have h10' : ConstructionTargets.TwiceSpiralH1Coordinates.boundaryCoordinateMap
      h' z₀' e₁ e₂ (Multiplicative.ofAdd (1, 0)) =
        Multiplicative.ofAdd (1, 2) := by
    simpa [h', z₀', conjugateBoundaryHomeomorph,
      coordinateBoundaryTorusHomeomorph,
      ConstructionTargets.TwiceSpiralH1Coordinates.boundaryCoordinateMap] using h10
  obtain ⟨g0, g1, g2, g3, ghi⟩ :=
    ConstructionTargets.TwiceSpiralGluingHomologyTable.gluing_complete_module_homology
      h' z₀' e₁ e₂ c₁ c₂ hinc₁' hinc₂' h10'
  let transfer (k : ℕ) :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      (apm_t01J03_homeomorph_gluing h).toHomotopyEquiv k
  exact ⟨⟨transfer 0 ≪≫ Classical.choice g0⟩,
    ⟨transfer 1 ≪≫ Classical.choice g1⟩,
    g2.of_iso (transfer 2),
    ⟨transfer 3 ≪≫ Classical.choice g3⟩,
    fun k hk => (ghi k hk).of_iso (transfer k)⟩

#print axioms apm_t01J03_twiceSpiral_module_homology

/-- Why this unblocks the final conjunct of `apm_t01j03`: this is the missing
Seifert--van Kampen and singular Mayer--Vietoris computation for the concrete
pushout quotient under precisely the encoded twice-spiral boundary relation. -/
theorem apm_t01J03_bridge_2
    (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
    (z₀ : apm_t01J03_BoundaryTorus)
    (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
      Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
      Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
    (c₂ : FundamentalGroup apm_t01J03_SolidTorus
      (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ)
    (hspiral : apm_t01J03_hasTwiceSpiral h z₀ e₁ e₂ c₁ c₂) :
    let M := apm_t01J03_gluedSpace h
    let m₀ := apm_t01J03_gluedBasepoint h z₀
    Nonempty (FundamentalGroup M m₀ ≃* Multiplicative (ZMod 2)) ∧
    Nonempty (apm_t01J03_H 0 M ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 M ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Limits.IsZero (apm_t01J03_H 2 M) ∧
    Nonempty (apm_t01J03_H 3 M ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 4 ≤ k → Limits.IsZero (apm_t01J03_H k M) := by
  dsimp only
  rcases hspiral with ⟨hinc₁, hinc₂, h10⟩
  let h' := conjugateBoundaryHomeomorph h
  let z₀' := coordinateBoundaryTorusHomeomorph z₀
  have hinc₁' : ∀ p, c₁ (FundamentalGroup.map
      ⟨ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
        ConstructionTargets.SolidTorusGluingOpenCover.continuous_boundaryInclusion⟩
      z₀' p) =
        ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom (e₁ p) := by
    simpa [z₀', coordinateBoundaryTorusHomeomorph,
      apm_t01J03_boundaryInclusion,
      ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
      ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom] using hinc₁
  have hinc₂' : ∀ p, c₂ (FundamentalGroup.map
      ⟨ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
        ConstructionTargets.SolidTorusGluingOpenCover.continuous_boundaryInclusion⟩
      (h' z₀') p) =
        ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom (e₂ p) := by
    simpa [h', z₀', conjugateBoundaryHomeomorph,
      coordinateBoundaryTorusHomeomorph, apm_t01J03_boundaryInclusion,
      ConstructionTargets.SolidTorusGluingOpenCover.boundaryInclusion,
      ConstructionTargets.TwiceSpiralH1Coordinates.secondCoordinateHom] using hinc₂
  have h10' : ConstructionTargets.TwiceSpiralH1Coordinates.boundaryCoordinateMap
      h' z₀' e₁ e₂ (Multiplicative.ofAdd (1, 0)) =
        Multiplicative.ofAdd (1, 2) := by
    simpa [h', z₀', conjugateBoundaryHomeomorph,
      coordinateBoundaryTorusHomeomorph,
      ConstructionTargets.TwiceSpiralH1Coordinates.boundaryCoordinateMap] using h10
  let B :
      ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction.PointedCoordinateBases
        h' (ConstructionTargets.TwiceSpiralH1Coordinates.twiceSpiralSecondCoefficient
          h' z₀' e₁ e₂) :=
    { coordinates :=
        ConstructionTargets.TwiceSpiralBasedCoordinateInterface.ofCoordinateHypotheses
          h' z₀' e₁ e₂ c₁ c₂ hinc₁' hinc₂' h10' }
  have hfg :
      Nonempty (FundamentalGroup (apm_t01J03_gluedSpace h)
        (apm_t01J03_gluedBasepoint h z₀) ≃* Multiplicative (ZMod 2)) := by
    refine ⟨(ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
      (apm_t01J03_homeomorph_gluing h)
        (apm_t01J03_gluedBasepoint h z₀)).trans ?_⟩
    exact ConstructionTargets.TwiceSpiralFundamentalGroupExtraction.gluingFundamentalGroupMulEquivZModTwo B
        ((apm_t01J03_homeomorph_gluing h) (apm_t01J03_gluedBasepoint h z₀))
  obtain ⟨g0, g1, g2, g3, ghi⟩ :=
    apm_t01J03_twiceSpiral_module_homology h z₀ e₁ e₂ c₁ c₂
      ⟨hinc₁, hinc₂, h10⟩
  exact ⟨hfg, g0, g1, g2, g3, ghi⟩

theorem apm_t01j03 :
    Nonempty
      (FundamentalGroup apm_t01J03_Torus (1, 1) ≃*
        Multiplicative (ℤ × ℤ)) ∧
    Nonempty (apm_t01J03_H 0 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t01J03_H 1 apm_t01J03_Torus ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (apm_t01J03_H 2 apm_t01J03_Torus ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t01J03_H k apm_t01J03_Torus)) ∧
    (∀ (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus)
        (z₀ : apm_t01J03_BoundaryTorus)
        (e₁ : FundamentalGroup apm_t01J03_BoundaryTorus z₀ ≃*
          Multiplicative (ℤ × ℤ))
        (e₂ : FundamentalGroup apm_t01J03_BoundaryTorus (h z₀) ≃*
          Multiplicative (ℤ × ℤ))
        (c₁ : FundamentalGroup apm_t01J03_SolidTorus
          (apm_t01J03_boundaryInclusion z₀) ≃* Multiplicative ℤ)
        (c₂ : FundamentalGroup apm_t01J03_SolidTorus
          (apm_t01J03_boundaryInclusion (h z₀)) ≃* Multiplicative ℤ),
      apm_t01J03_hasTwiceSpiral h z₀ e₁ e₂ c₁ c₂ →
      let M := apm_t01J03_gluedSpace h
      let m₀ := apm_t01J03_gluedBasepoint h z₀
      Nonempty (FundamentalGroup M m₀ ≃* Multiplicative (ZMod 2)) ∧
      Nonempty (apm_t01J03_H 0 M ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t01J03_H 1 M ≅ ModuleCat.of ℤ (ZMod 2)) ∧
      Limits.IsZero (apm_t01J03_H 2 M) ∧
      Nonempty (apm_t01J03_H 3 M ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k : ℕ, 4 ≤ k → Limits.IsZero (apm_t01J03_H k M)) := by
  obtain ⟨gπ, g0, g1, g2, ghigh⟩ := apm_t01J03_bridge_1
  refine ⟨gπ, g0, g1, g2, ghigh, ?_⟩
  intro h z₀ e₁ e₂ c₁ c₂ hspiral
  exact apm_t01J03_bridge_2 h z₀ e₁ e₂ c₁ c₂ hspiral
