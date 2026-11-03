import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.TwoOpenFreeProductMapping
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.IntegralOpenCoverMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.SurfaceSchoenflies
import ConstructionTargets.T97A04FrozenH1Coordinate
import ConstructionTargets.BoundaryTorusIntegralHomologyComplete
import ConstructionTargets.CircleSingularHomology
import ConstructionTargets.ProjectiveQuotientExactSplitting
import ConstructionTargets.SingularHomologyHomotopy

/-! # Blueprint for APM t03J02 -/

open CategoryTheory

noncomputable section

abbrev apm_t03J02_Torus := Circle × Circle

inductive apm_t03J02_glueRel
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Sum apm_t03J02_Torus apm_t03J02_Torus →
      Sum apm_t03J02_Torus apm_t03J02_Torus → Prop
  | glue (z : Circle) :
      apm_t03J02_glueRel j₁ j₂ (Sum.inl (j₁ z)) (Sum.inr (j₂ z))

def apm_t03J02_space (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :=
  Quotient (Relation.EqvGen.setoid (apm_t03J02_glueRel j₁ j₂))

noncomputable instance (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    TopologicalSpace (apm_t03J02_space j₁ j₂) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t03J02_Torus apm_t03J02_Torus ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t03J02_glueRel j₁ j₂)) z)
    inferInstance

def apm_t03J02_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Sum apm_t03J02_Torus apm_t03J02_Torus → apm_t03J02_space j₁ j₂ :=
  fun z => Quotient.mk _ z

lemma apm_t03J02_continuous_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Continuous (apm_t03J02_quotientMap j₁ j₂) := by
  exact continuous_coinduced_rng

lemma apm_t03J02_surjective_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Function.Surjective (apm_t03J02_quotientMap j₁ j₂) := by
  exact Quotient.mk_surjective

lemma apm_t03J02_glue_eq
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (z : Circle) :
    apm_t03J02_quotientMap j₁ j₂ (Sum.inl (j₁ z)) =
      apm_t03J02_quotientMap j₁ j₂ (Sum.inr (j₂ z)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (apm_t03J02_glueRel.glue z)

lemma apm_t03J02_gluedDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) {x y}
    (hxy : Relation.EqvGen (apm_t03J02_glueRel j₁ j₂) x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
    cases hab with
    | glue z => exact hfg z
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t03J02_gluedDesc
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) :
    C(apm_t03J02_space j₁ j₂, Y) := by
  let raw : Sum apm_t03J02_Torus apm_t03J02_Torus → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy =>
      apm_t03J02_gluedDesc_respects j₁ j₂ f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy =>
      apm_t03J02_gluedDesc_respects j₁ j₂ f g hfg hxy)⟩

@[simp] lemma apm_t03J02_gluedDesc_inl
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) (x : apm_t03J02_Torus) :
    apm_t03J02_gluedDesc j₁ j₂ f g hfg
      (apm_t03J02_quotientMap j₁ j₂ (.inl x)) = f x := rfl

@[simp] lemma apm_t03J02_gluedDesc_inr
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) (x : apm_t03J02_Torus) :
    apm_t03J02_gluedDesc j₁ j₂ f g hfg
      (apm_t03J02_quotientMap j₁ j₂ (.inr x)) = g x := rfl

lemma apm_t03J02_gluedDesc_unique
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z))
    (u : C(apm_t03J02_space j₁ j₂, Y))
    (hul : ∀ x, u (apm_t03J02_quotientMap j₁ j₂ (.inl x)) = f x)
    (hur : ∀ x, u (apm_t03J02_quotientMap j₁ j₂ (.inr x)) = g x) :
    u = apm_t03J02_gluedDesc j₁ j₂ f g hfg := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (x | x)
  · exact hul x
  · exact hur x

def apm_t03J02_gluedInl
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    C(apm_t03J02_Torus, apm_t03J02_space j₁ j₂) :=
  ⟨fun x ↦ apm_t03J02_quotientMap j₁ j₂ (.inl x),
    (apm_t03J02_continuous_quotientMap j₁ j₂).comp continuous_inl⟩

def apm_t03J02_gluedInr
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    C(apm_t03J02_Torus, apm_t03J02_space j₁ j₂) :=
  ⟨fun x ↦ apm_t03J02_quotientMap j₁ j₂ (.inr x),
    (apm_t03J02_continuous_quotientMap j₁ j₂).comp continuous_inr⟩

def apm_t03J02_CompatibleMaps
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (Y : Type*) [TopologicalSpace Y] :=
  {fg : C(apm_t03J02_Torus, Y) × C(apm_t03J02_Torus, Y) //
    ∀ z, fg.1 (j₁ z) = fg.2 (j₂ z)}

def apm_t03J02_gluedDescEquiv
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    apm_t03J02_CompatibleMaps j₁ j₂ Y ≃
      C(apm_t03J02_space j₁ j₂, Y) where
  toFun fg := apm_t03J02_gluedDesc j₁ j₂ fg.1.1 fg.1.2 fg.2
  invFun u := ⟨(u.comp (apm_t03J02_gluedInl j₁ j₂),
      u.comp (apm_t03J02_gluedInr j₁ j₂)), fun z ↦ by
        exact congrArg u (apm_t03J02_glue_eq j₁ j₂ z)⟩
  left_inv fg := by
    apply Subtype.ext
    apply Prod.ext <;> ext x <;> rfl
  right_inv u := by
    symm
    apply apm_t03J02_gluedDesc_unique j₁ j₂
        (u.comp (apm_t03J02_gluedInl j₁ j₂))
        (u.comp (apm_t03J02_gluedInr j₁ j₂))
        (fun z ↦ congrArg u (apm_t03J02_glue_eq j₁ j₂ z))
    · intro x
      rfl
    · intro x
      rfl

def apm_t03J02_basepoint
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (z₀ : Circle) :
    apm_t03J02_space j₁ j₂ :=
  Quotient.mk _ (Sum.inl (j₁ z₀))

abbrev apm_t03J02_generator := Fin 2 × Fin 2

def apm_t03J02_commutatorRelation (i : Fin 2) :
    FreeGroup apm_t03J02_generator :=
  FreeGroup.of (i, 0) * FreeGroup.of (i, 1) *
    (FreeGroup.of (i, 0))⁻¹ * (FreeGroup.of (i, 1))⁻¹

abbrev apm_t03J02_freeProductZ2Z2 :=
  PresentedGroup (Set.range apm_t03J02_commutatorRelation)

abbrev apm_t03J02_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

theorem apm_t03J02_isPushout (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    CategoryTheory.IsPushout (TopCat.ofHom j₁) (TopCat.ofHom j₂)
      (TopCat.ofHom (apm_t03J02_gluedInl j₁ j₂))
      (TopCat.ofHom (apm_t03J02_gluedInr j₁ j₂)) := by
  sorry

def apm_t03J02_overlapToLeft
    {X : Type*} [TopologicalSpace X] (U V : Set X) : C((U ∩ V : Set X), U) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def apm_t03J02_overlapToRight
    {X : Type*} [TopologicalSpace X] (U V : Set X) : C((U ∩ V : Set X), V) :=
  ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

structure apm_t03J02_CompatibleOpenCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (Y : Type) [TopologicalSpace Y] where
  leftSet : Set (Y)
  rightSet : Set (Y)
  open_left : IsOpen leftSet
  open_right : IsOpen rightSet
  cover : leftSet ∪ rightSet = Set.univ
  leftEquiv : ContinuousMap.HomotopyEquiv leftSet apm_t03J02_Torus
  rightEquiv : ContinuousMap.HomotopyEquiv rightSet apm_t03J02_Torus
  overlapEquiv : ContinuousMap.HomotopyEquiv
    (leftSet ∩ rightSet : Set (Y)) Circle
  left_compat :
    (leftEquiv.toFun.comp (apm_t03J02_overlapToLeft leftSet rightSet)).Homotopic
      (j₁.comp overlapEquiv.toFun)
  right_compat :
    (rightEquiv.toFun.comp (apm_t03J02_overlapToRight leftSet rightSet)).Homotopic
      (j₂.comp overlapEquiv.toFun)

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) [PathConnectedSpace Y] :
    PathConnectedSpace X := by
  refine ⟨⟨e.symm (Classical.choice (inferInstance : Nonempty Y))⟩, ?_⟩
  intro x y
  let middle : Path (e.symm (e x)) (e.symm (e y)) :=
    (PathConnectedSpace.somePath (e x) (e y)).map e.symm.continuous
  exact ⟨(e.left_inv.some.evalAt x).symm.trans
    (middle.trans (e.left_inv.some.evalAt y))⟩

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_torus
    (t : apm_t03J02_Torus) :
    Nonempty (FundamentalGroup apm_t03J02_Torus t ≃* Multiplicative (ℤ × ℤ)) := by
  letI : PathConnectedSpace apm_t03J02_Torus := { 
    nonempty := ⟨((1 : Circle), (1 : Circle))⟩
    joined x y := ⟨(PathConnectedSpace.somePath x.1 y.1).prod
      (PathConnectedSpace.somePath x.2 y.2)⟩ }
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected t
      ((1 : Circle), (1 : Circle))).trans
    ((ConstructionTargets.FundamentalGroupProduct.fundamentalGroupProdMulEquiv
        (1 : Circle) (1 : Circle)).trans
      ((MulEquiv.prodCongr
          ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt
          ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt).trans
        (MulEquiv.prodMultiplicative ℤ ℤ).symm))⟩

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_groupoid
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) (hf : f.Nullhomotopic) :
    ∃ b : B, Nonempty
      (FundamentalGroupoid.map f ≅
        FundamentalGroupoid.map (ContinuousMap.const A b)) := by
  obtain ⟨b, ⟨H⟩⟩ := hf
  exact ⟨b, ⟨asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso H)⟩⟩

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_map_eq_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) (hf : f.Nullhomotopic) (a : A)
    (g : FundamentalGroup A a) :
    FundamentalGroup.map f a g = 1 := by
  obtain ⟨b, H⟩ := hf
  obtain ⟨K⟩ := H
  have hn := (FundamentalGroupoidFunctor.homotopicMapsNatIso K).naturality g
  change (FundamentalGroupoid.map f).map g ≫ ⟦K.evalAt a⟧ =
    ⟦K.evalAt a⟧ ≫
      (FundamentalGroupoid.map (ContinuousMap.const A b)).map g at hn
  have hc :
      (FundamentalGroupoid.map (ContinuousMap.const A b)).map g =
        𝟙 (FundamentalGroupoid.mk b) := by
    induction g using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Path.Homotopy.refl _⟩
  rw [hc] at hn
  let q : FundamentalGroupoid.mk (f a) ⟶ FundamentalGroupoid.mk b :=
    ⟦K.evalAt a⟧
  change (FundamentalGroupoid.map f).map g ≫ q = q ≫ 𝟙 _ at hn
  have hn' : (FundamentalGroupoid.map f).map g ≫ ⟦K.evalAt a⟧ =
      ⟦K.evalAt a⟧ := by
    simpa only [Category.comp_id] using hn
  change (FundamentalGroupoid.map f).map g = 𝟙 _
  apply (cancel_mono ⟦K.evalAt a⟧).1
  simpa only [Category.id_comp] using hn'

/-- A connected fundamental groupoid: a path-connected space has a connected
fundamental groupoid. -/
lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_isConnected
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] :
    CategoryTheory.IsConnected (FundamentalGroupoid Y) := by
  haveI : Nonempty (FundamentalGroupoid Y) :=
    ⟨FundamentalGroupoid.mk (Classical.choice (inferInstance : Nonempty Y))⟩
  refine isConnected_of_zigzag (fun j₁ j₂ => ⟨[j₂], ?_, by simp⟩)
  simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
  let f : j₁ ⟶ j₂ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath j₁.as j₂.as)
  exact Zag.of_hom f

/-- Over a connected overlap category `W`, pseudo-cocones on a span whose two
legs factor through the point are the same as pseudo-cocones on the point
span, naturally in the target category.  (Whiskering by `W ⥤ pt` is fully
faithful on functor categories when `W` is connected:
`Functor.const` is full for `IsConnected W`.) -/
def apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux_isoMk {K L R C : Type} [Category.{0} K] [Category.{0} L]
    [Category.{0} R] [Category.{0} C] {l : K ⥤ L} {r : K ⥤ R}
    {P Q : ConstructionTargets.GenericSpanPseudoCoconeTransport.SpanPseudoCocone l r C}
    (eL : P.left ≅ Q.left) (eR : P.right ≅ Q.right)
    (h : ∀ k, P.glue.hom.app k ≫ eR.hom.app (r.obj k) =
      eL.hom.app (l.obj k) ≫ Q.glue.hom.app k) :
    P ≅ Q where
  hom :=
    { left := eL.hom
      right := eR.hom
      glue_naturality := by
        ext k
        simpa using h k }
  inv :=
    { left := eL.inv
      right := eR.inv
      glue_naturality := by
        ext k
        have := congrArg (fun f => eL.inv.app (l.obj k) ≫ f ≫ eR.inv.app (r.obj k)) (h k)
        simpa using this.symm }
  hom_inv_id := by
    apply ConstructionTargets.GenericSpanPseudoCoconeTransport.SpanPseudoCoconeHom.ext <;>
      exact Iso.hom_inv_id _
  inv_hom_id := by
    apply ConstructionTargets.GenericSpanPseudoCoconeTransport.SpanPseudoCoconeHom.ext <;>
      exact Iso.inv_hom_id _

namespace apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux

open ConstructionTargets.GenericSpanPseudoCoconeTransport

@[simp] lemma comp_left_app {K L R C : Type} [Category.{0} K] [Category.{0} L]
    [Category.{0} R] [Category.{0} C] {l : K ⥤ L} {r : K ⥤ R}
    {P Q S : SpanPseudoCocone l r C} (f : P ⟶ Q) (g : Q ⟶ S) (x : L) :
    (f ≫ g).left.app x = f.left.app x ≫ g.left.app x := rfl

@[simp] lemma comp_right_app {K L R C : Type} [Category.{0} K] [Category.{0} L]
    [Category.{0} R] [Category.{0} C] {l : K ⥤ L} {r : K ⥤ R}
    {P Q S : SpanPseudoCocone l r C} (f : P ⟶ Q) (g : Q ⟶ S) (x : R) :
    (f ≫ g).right.app x = f.right.app x ≫ g.right.app x := rfl

variable {W L R C : Type} [Category.{0} W] [Category.{0} L] [Category.{0} R]
  [Category.{0} C] [CategoryTheory.IsConnected W]
  (a : SingleObj PUnit.{1} ⥤ L) (b : SingleObj PUnit.{1} ⥤ R)

abbrev wide (C : Type) [Category.{0} C] := SpanPseudoCocone
  ((Functor.const W).obj (SingleObj.star PUnit.{1}) ⋙ a)
  ((Functor.const W).obj (SingleObj.star PUnit.{1}) ⋙ b) C
abbrev point (C : Type) [Category.{0} C] := SpanPseudoCocone a b C

/-- The glue components over a connected index category are all equal. -/
lemma glue_const (P : wide (W := W) a b C) (w w' : W) :
    (P.glue.hom.app w : P.left.obj (a.obj (SingleObj.star _)) ⟶
      P.right.obj (b.obj (SingleObj.star _))) = P.glue.hom.app w' := by
  refine constant_of_preserves_morphisms
    (α := P.left.obj (a.obj (SingleObj.star _)) ⟶ P.right.obj (b.obj (SingleObj.star _)))
    (fun w => P.glue.hom.app w) (fun j₁ j₂ f => ?_) w w'
  have := P.glue.hom.naturality f
  simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
    Functor.const_obj_map] at this
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp] at this
  exact this.symm

def collapseObj (P : wide (W := W) a b C) : point a b C where
  left := P.left
  right := P.right
  glue := NatIso.ofComponents (fun _ => P.glue.app (Classical.arbitrary W)) (fun f => by
    change PUnit at f
    cases f
    change P.left.map (a.map (𝟙 _)) ≫ _ = _ ≫ P.right.map (b.map (𝟙 _))
    simp)

def expandObj (Q : point a b C) : wide (W := W) a b C where
  left := Q.left
  right := Q.right
  glue := NatIso.ofComponents (fun _ => Q.glue.app (SingleObj.star _)) (fun f => by
    change Q.left.map (a.map (𝟙 _)) ≫ _ = _ ≫ Q.right.map (b.map (𝟙 _))
    simp)

def collapse : wide (W := W) a b C ⥤ point a b C where
  obj := collapseObj a b
  map {P Q} φ :=
    { left := φ.left
      right := φ.right
      glue_naturality := by
        ext x
        cases x
        have := NatTrans.congr_app φ.glue_naturality (Classical.arbitrary W)
        simpa [collapseObj] using this }

def expand : point a b C ⥤ wide (W := W) a b C where
  obj := expandObj a b
  map {P Q} φ :=
    { left := φ.left
      right := φ.right
      glue_naturality := by
        ext w
        have := NatTrans.congr_app φ.glue_naturality (SingleObj.star _)
        simpa [expandObj] using this }

def unitIso : 𝟭 (wide (W := W) a b C) ≅ collapse a b ⋙ expand a b :=
  NatIso.ofComponents
    (fun P => apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux_isoMk (Iso.refl _) (Iso.refl _) (fun w => by
      simp [collapse, expand, collapseObj, expandObj, glue_const a b P w (Classical.arbitrary W)]))
    (fun φ => by
      apply SpanPseudoCoconeHom.ext <;> ext <;> simp [apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux_isoMk, collapse, expand]
      all_goals exact (Category.comp_id _).trans (Category.id_comp _).symm)

def counitIso : expand a b ⋙ collapse (W := W) a b ≅ 𝟭 (point a b C) :=
  NatIso.ofComponents
    (fun Q => apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux_isoMk (Iso.refl _) (Iso.refl _) (fun x => by
      cases x
      simp [collapse, expand, collapseObj, expandObj]
      all_goals rfl))
    (fun φ => by
      apply SpanPseudoCoconeHom.ext <;> ext <;> simp [apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux_isoMk, collapse, expand]
      all_goals exact (Category.comp_id _).trans (Category.id_comp _).symm)

def equiv (C : Type) [Category.{0} C] : wide (W := W) a b C ≌ point a b C :=
  CategoryTheory.Equivalence.mk (collapse a b) (expand a b) (unitIso a b) (counitIso a b)

@[simp] lemma equiv_functor (C : Type) [Category.{0} C] :
    (equiv (W := W) a b C).functor = collapse a b := rfl

def naturality (C D : Type) [Category.{0} C] [Category.{0} D] (H : C ⥤ D) :
    postcomposeFunctor H ⋙ (equiv (W := W) a b D).functor ≅
      (equiv a b C).functor ⋙ postcomposeFunctor H :=
  NatIso.ofComponents
    (fun P => apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux_isoMk (Iso.refl _) (Iso.refl _) (fun x => by
      cases x
      simp [collapse, collapseObj, postcomposeFunctor, postcomposeObj]
      all_goals rfl))
    (fun φ => by
      apply SpanPseudoCoconeHom.ext <;> ext <;>
        simp [apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux_isoMk, collapse, postcomposeFunctor] <;>
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

end apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse
    {W L R : Type} [Category.{0} W] [Category.{0} L] [Category.{0} R]
    [CategoryTheory.IsConnected W]
    (a : SingleObj PUnit.{1} ⥤ L) (b : SingleObj PUnit.{1} ⥤ R) :
    Nonempty (Σ E : ∀ (C : Type) [Category.{0} C],
        ConstructionTargets.GenericSpanPseudoCoconeTransport.SpanPseudoCocone
            ((Functor.const W).obj (SingleObj.star PUnit.{1}) ⋙ a)
            ((Functor.const W).obj (SingleObj.star PUnit.{1}) ⋙ b) C ≌
          ConstructionTargets.GenericSpanPseudoCoconeTransport.SpanPseudoCocone a b C,
      ∀ (C D : Type) [Category.{0} C] [Category.{0} D] (H : C ⥤ D),
        ConstructionTargets.GenericSpanPseudoCoconeTransport.postcomposeFunctor H ⋙
            (E D).functor ≅
          (E C).functor ⋙
            ConstructionTargets.GenericSpanPseudoCoconeTransport.postcomposeFunctor H) := by
  exact ⟨⟨fun C _ => apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux.equiv a b C, fun C D _ _ H => apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux.naturality a b C D H⟩⟩

/-- The target-natural family of mapping-category equivalences for a two-open
cover with nullhomotopic overlap legs: as in
`TwoOpenFreeProductMapping.mapping`, but the overlap span is first replaced
(legs naturally isomorphic to constant functors, `_aux_groupoid`) by one whose
legs factor through the point, then collapsed by `_aux_collapse`; the pieces
use the path connectors at `w` (`TwoOpenLegCompatibleConnectorSystems.pathConnector`)
in place of `leftConnectors`/`rightConnectors`, which need a simply connected
overlap. -/
lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_mapping
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hl : (apm_t03J02_overlapToLeft U V).Nullhomotopic)
    (hr : (apm_t03J02_overlapToRight U V).Nullhomotopic)
    (w : (U ∩ V : Set X)) :
    Nonempty (Σ E : ∀ (C : Type) [Category.{0} C],
        (FundamentalGroupoid X ⥤ C) ≌
          (SingleObj (Monoid.Coprod
              (End (FundamentalGroupoid.mk (⟨w.1, w.2.1⟩ : U)))
              (End (FundamentalGroupoid.mk (⟨w.1, w.2.2⟩ : V)))) ⥤ C),
      ∀ (C D : Type) [Category.{0} C] [Category.{0} D] (K : C ⥤ D),
        (Functor.whiskeringRight (FundamentalGroupoid X) C D).obj K ⋙ (E D).functor ≅
          (E C).functor ⋙ (Functor.whiskeringRight _ C D).obj K) := by
  open ConstructionTargets.TwoOpenFundamentalGroupoidSpan in
    open ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout in
    open ConstructionTargets.GenericSpanPseudoCoconeTransport in
    open ConstructionTargets.FreeProductPointSpanRepresentations in
    open ConstructionTargets.FreeProductRepresentationSingleObjEquivalence in
    open ConstructionTargets.ConnectedGroupoidSingleObjEquivalence in
    open ConstructionTargets.TwoOpenLegCompatibleConnectorSystems in
    open ConstructionTargets.TwoOpenFreeProductMapping in
    classical
    obtain ⟨u, ⟨iu⟩⟩ :=
      apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_groupoid
        (apm_t03J02_overlapToLeft U V) hl
    obtain ⟨v, ⟨iv⟩⟩ :=
      apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_groupoid
        (apm_t03J02_overlapToRight U V) hr
    let W := FundamentalGroupoid (U ∩ V : Set X)
    letI : CategoryTheory.IsConnected W :=
      apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_isConnected
        (Y := (U ∩ V : Set X))
    let L := FundamentalGroupoid U
    let R := FundamentalGroupoid V
    let P := SingleObj PUnit.{1}
    let c : W ⥤ P := (Functor.const W).obj (SingleObj.star PUnit.{1})
    let a : P ⥤ L := (Functor.const P).obj (FundamentalGroupoid.mk u)
    let b : P ⥤ R := (Functor.const P).obj (FundamentalGroupoid.mk v)
    let SL : ConstructionTargets.ConnectedGroupoidVertexReconstruction.ConnectorSystem L :=
      { base := FundamentalGroupoid.mk (⟨w.1, w.2.1⟩ : U)
        connector := pathConnector (⟨w.1, w.2.1⟩ : U) }
    let SR : ConstructionTargets.ConnectedGroupoidVertexReconstruction.ConnectorSystem R :=
      { base := FundamentalGroupoid.mk (⟨w.1, w.2.2⟩ : V)
        connector := pathConnector (⟨w.1, w.2.2⟩ : V) }
    let eL : L ≌ SingleObj (End SL.base) := connectorSingleObjEquivalence SL
    let eR : R ≌ SingleObj (End SR.base) := connectorSingleObjEquivalence SR
    let pcL : a ⋙ eL.functor ≅ pointLeg (End SL.base) :=
      ConstructionTargets.TwoOpenPointSpanComparison.pointComparison (a ⋙ eL.functor)
    let pcR : b ⋙ eR.functor ≅ pointLeg (End SR.base) :=
      ConstructionTargets.TwoOpenPointSpanComparison.pointComparison (b ⋙ eR.functor)
    let iu' : (CategoryTheory.Equivalence.refl (C := W)).inverse ⋙
        overlapFundamentalGroupoidMap (U := U) (V := V) true ⋙
        (CategoryTheory.Equivalence.refl (C := L)).functor ≅ c ⋙ a := by
      refine (eqToIso ?_).trans (iu.trans (eqToIso ?_))
      · aesop_cat
      · refine CategoryTheory.Functor.ext (fun x => rfl) ?_
        intro x y f
        induction f using Quotient.inductionOn with
        | h p =>
          apply Quotient.sound
          refine ⟨?_⟩
          convert Path.Homotopy.refl (Path.refl u) using 1 <;>
            ext t <;> simp [c, a]
    let iv' : (CategoryTheory.Equivalence.refl (C := W)).inverse ⋙
        overlapFundamentalGroupoidMap (U := U) (V := V) false ⋙
        (CategoryTheory.Equivalence.refl (C := R)).functor ≅ c ⋙ b := by
      refine (eqToIso ?_).trans (iv.trans (eqToIso ?_))
      · aesop_cat
      · refine CategoryTheory.Functor.ext (fun x => rfl) ?_
        intro x y f
        induction f using Quotient.inductionOn with
        | h p =>
          apply Quotient.sound
          refine ⟨?_⟩
          convert Path.Homotopy.refl (Path.refl v) using 1 <;>
            ext t <;> simp [c, b]
    let pcL' : (CategoryTheory.Equivalence.refl (C := P)).inverse ⋙ a ⋙ eL.functor ≅
        pointLeg (End SL.base) := by simpa using pcL
    let pcR' : (CategoryTheory.Equivalence.refl (C := P)).inverse ⋙ b ⋙ eR.functor ≅
        pointLeg (End SR.base) := by simpa using pcR
    let spanConst (C : Type) [Category.{0} C] :=
      pseudoCoconeEquivalenceOfSpanEquivalences
        (overlapFundamentalGroupoidMap (U := U) (V := V) true)
        (overlapFundamentalGroupoidMap (U := U) (V := V) false)
        (c ⋙ a) (c ⋙ b)
        (CategoryTheory.Equivalence.refl (C := W))
        (CategoryTheory.Equivalence.refl (C := L))
        (CategoryTheory.Equivalence.refl (C := R))
        iu' iv' (C := C)
    let collapsed (C : Type) [Category.{0} C] :=
      apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux.equiv
        (W := W) a b C
    let pointCoords (C : Type) [Category.{0} C] :=
      pseudoCoconeEquivalenceOfSpanEquivalences a b
        (pointLeg (End SL.base)) (pointLeg (End SR.base))
        (CategoryTheory.Equivalence.refl (C := P)) eL eR pcL' pcR' (C := C)
    let E (C : Type) [Category.{0} C] :=
      let e0 := twoOpenFundamentalGroupoidPseudopushoutEquivalence (C := C) hU hV hcov
      let e1 := e0.trans (pseudoSpanEquivalence (U := U) (V := V) C)
      let e2 := e1.trans (spanConst C)
      let e3 := e2.trans (collapsed C)
      let e4 := e3.trans (pointCoords C)
      let e5 := e4.trans (freeProductPointSpanEquivalence (End SL.base) (End SR.base) C)
      e5.trans (representationSingleObjEquivalence (C := C) (End SL.base) (End SR.base))
    refine ⟨⟨fun C _ => E C, ?_⟩⟩
    intro C D _ _ K
    let s0 : CatCommSq _
        (twoOpenFundamentalGroupoidPseudopushoutEquivalence (C := C) hU hV hcov).functor
        (twoOpenFundamentalGroupoidPseudopushoutEquivalence (C := D) hU hV hcov).functor
        (postcomposePseudoFunctorCoconeFunctor K) :=
      ⟨pseudopushoutPostcomposeNatIso hU hV hcov K⟩
    let s1 : CatCommSq (postcomposePseudoFunctorCoconeFunctor K)
        (pseudoSpanEquivalence (U := U) (V := V) C).functor
        (pseudoSpanEquivalence (U := U) (V := V) D).functor (postcomposeFunctor K) :=
      ⟨eqToIso (by rfl)⟩
    let s2 : CatCommSq (postcomposeFunctor K) (spanConst C).functor
        (spanConst D).functor (postcomposeFunctor K) :=
      ⟨equivalenceFunctorPostcomposeIso _ _ _ _ _ _ _ iu' iv' K⟩
    let s3 : CatCommSq (postcomposeFunctor K) (collapsed C).functor
        (collapsed D).functor (postcomposeFunctor K) :=
      ⟨apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_collapse_aux.naturality
        (W := W) a b C D K⟩
    let s4 : CatCommSq (postcomposeFunctor K) (pointCoords C).functor
        (pointCoords D).functor (postcomposeFunctor K) :=
      ⟨equivalenceFunctorPostcomposeIso _ _ _ _ _ eL eR pcL' pcR' K⟩
    let s5 : CatCommSq (postcomposeFunctor K)
        (freeProductPointSpanEquivalence (End SL.base) (End SR.base) C).functor
        (freeProductPointSpanEquivalence (End SL.base) (End SR.base) D).functor
        (ConstructionTargets.FreeProductPointSpanRepresentations.postcomposeRepresentationFunctor
          (End SL.base) (End SR.base) K) :=
      ⟨ConstructionTargets.FreeProductPointSpanRepresentations.equivalenceFunctorPostcomposeIso
        (End SL.base) (End SR.base) K⟩
    let s6 : CatCommSq
        (ConstructionTargets.FreeProductPointSpanRepresentations.postcomposeRepresentationFunctor
          (End SL.base) (End SR.base) K)
        (representationSingleObjEquivalence (C := C) (End SL.base) (End SR.base)).functor
        (representationSingleObjEquivalence (C := D) (End SL.base) (End SR.base)).functor _ :=
      ⟨representationToFunctorPostcomposeIso (End SL.base) (End SR.base) K⟩
    exact (CatCommSq.vComp'
      (CatCommSq.vComp' (CatCommSq.vComp' (CatCommSq.vComp' s0 s1) s2) s3)
      (CatCommSq.vComp' s4 (CatCommSq.vComp' s5 s6))).iso

/-- Two-open van Kampen when both overlap inclusions are nullhomotopic: the
fundamental group is the free product of the two pieces' groups.  The overlap
need not be simply connected; on fundamental groupoids each leg functor is
naturally isomorphic to one through a point, so the overlap cocone condition
collapses as in `TwoOpenFreeProductMapping`. -/
lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hl : (apm_t03J02_overlapToLeft U V).Nullhomotopic)
    (hr : (apm_t03J02_overlapToRight U V).Nullhomotopic)
    (w : (U ∩ V : Set X)) :
    Nonempty
      (FundamentalGroup X w.1 ≃*
        Monoid.Coprod (FundamentalGroup U ⟨w.1, w.2.1⟩)
          (FundamentalGroup V ⟨w.1, w.2.2⟩)) := by
  obtain ⟨⟨E, post⟩⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general_aux_mapping U V hU hV hcov hl hr w
  let S := ConstructionTargets.GenericTargetNaturalSourceReconstruction.sourceEquivalence
    (fun C _ => E C) (fun {C D} _ _ K => post C D K)
  exact ⟨(S.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk w.val)).trans
    ((Iso.conj (eqToIso (show S.functor.obj (FundamentalGroupoid.mk w.val) =
      SingleObj.star _ from Subsingleton.elim _ _))).trans (SingleObj.toEnd _).symm)⟩

/-- Both overlap inclusions of a compatible cover are nullhomotopic:
`leftEquiv ∘ leg ≃ j₁ ∘ overlapEquiv` is null, and composing with
`leftEquiv.invFun` recovers `leg` up to homotopy. -/
lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_nullLegs
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    (apm_t03J02_overlapToLeft hcover.leftSet hcover.rightSet).Nullhomotopic ∧
      (apm_t03J02_overlapToRight hcover.leftSet hcover.rightSet).Nullhomotopic := by
  constructor
  · let leg := apm_t03J02_overlapToLeft hcover.leftSet hcover.rightSet
    have hforward : (hcover.leftEquiv.toFun.comp leg).Nullhomotopic := by
      obtain ⟨y, hy⟩ := hnull₁.comp_left hcover.overlapEquiv.toFun
      exact ⟨y, hcover.left_compat.trans hy⟩
    obtain ⟨x, hx⟩ := hforward.comp_right hcover.leftEquiv.invFun
    refine ⟨x, ?_⟩
    have hrecover := hcover.leftEquiv.left_inv.comp
      (ContinuousMap.Homotopic.refl leg)
    exact hrecover.symm.trans hx
  · let leg := apm_t03J02_overlapToRight hcover.leftSet hcover.rightSet
    have hforward : (hcover.rightEquiv.toFun.comp leg).Nullhomotopic := by
      obtain ⟨y, hy⟩ := hnull₂.comp_left hcover.overlapEquiv.toFun
      exact ⟨y, hcover.right_compat.trans hy⟩
    obtain ⟨x, hx⟩ := hforward.comp_right hcover.rightEquiv.invFun
    refine ⟨x, ?_⟩
    have hrecover := hcover.rightEquiv.left_inv.comp
      (ContinuousMap.Homotopic.refl leg)
    exact hrecover.symm.trans hx

/-- A homotopy equivalence between path-connected spaces identifies their
fundamental groups at any two base points. -/
lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_hequiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) [PathConnectedSpace Y]
    (x : X) (y : Y) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y y) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  let eπ := E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk x)
  exact ⟨eπ.trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e x) y)⟩

/-- Two path-connected sets covering a space with nonempty intersection make
the space path-connected. -/
lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_pathConnectedSpace
    {X : Type} [TopologicalSpace X] (U V : Set X) (hcov : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    (w : (U ∩ V : Set X)) :
    PathConnectedSpace X := by
  rw [pathConnectedSpace_iff_univ, ← hcov]
  exact
    (isPathConnected_iff_pathConnectedSpace.mpr (inferInstance : PathConnectedSpace U)).union
      (isPathConnected_iff_pathConnectedSpace.mpr (inferInstance : PathConnectedSpace V))
      ⟨w.1, w.2.1, w.2.2⟩

/-- The van Kampen equivalence for the concrete gluing, with the two vertex
groups read off the torus through the cover's homotopy equivalences. -/
lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (y₀ : Y)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    Nonempty
      (FundamentalGroup (Y)
          (y₀) ≃*
        Monoid.Coprod
          (FundamentalGroup apm_t03J02_Torus (j₁ 1))
          (FundamentalGroup apm_t03J02_Torus (j₂ 1))) := by
  letI : PathConnectedSpace apm_t03J02_Torus := {
    nonempty := ⟨((1 : Circle), (1 : Circle))⟩
    joined x y := ⟨(PathConnectedSpace.somePath x.1 y.1).prod
      (PathConnectedSpace.somePath x.2 y.2)⟩ }
  haveI : PathConnectedSpace hcover.leftSet :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected
      hcover.leftEquiv
  haveI : PathConnectedSpace hcover.rightSet :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected
      hcover.rightEquiv
  haveI : PathConnectedSpace (hcover.leftSet ∩ hcover.rightSet :
      Set (Y)) :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected
      hcover.overlapEquiv
  let w : (hcover.leftSet ∩ hcover.rightSet : Set (Y)) :=
    hcover.overlapEquiv.invFun 1
  haveI : PathConnectedSpace (Y) :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_pathConnectedSpace
      hcover.leftSet hcover.rightSet hcover.cover w
  obtain ⟨hl, hr⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_nullLegs
      j₁ j₂ hnull₁ hnull₂ hcover
  obtain ⟨g⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_general
      hcover.leftSet hcover.rightSet hcover.open_left hcover.open_right
      hcover.cover hl hr w
  obtain ⟨e₁⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_hequiv
      hcover.leftEquiv ⟨w.1, w.2.1⟩ (j₁ 1)
  obtain ⟨e₂⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_hequiv
      hcover.rightEquiv ⟨w.1, w.2.2⟩ (j₂ 1)
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath
      (PathConnectedSpace.somePath _ w.1)).trans
    (g.trans (MulEquiv.coprodCongr e₁ e₂))⟩

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (y₀ : Y)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    Nonempty
      (FundamentalGroup (Y)
          (y₀) ≃*
        Monoid.Coprod (Multiplicative (ℤ × ℤ))
          (Multiplicative (ℤ × ℤ))) := by
  obtain ⟨evk⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs
      j₁ j₂ hnull₁ hnull₂ y₀ hcover
  obtain ⟨e₁⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_torus
      (j₁ 1)
  obtain ⟨e₂⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_torus
      (j₂ 1)
  exact ⟨evk.trans (MulEquiv.coprodCongr e₁ e₂)⟩

def apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_pairHom
    {G : Type*} [Group G] (x y : G) (hxy : Commute x y) :
    Multiplicative (ℤ × ℤ) →* G where
  toFun p := x ^ p.toAdd.1 * y ^ p.toAdd.2
  map_one' := by simp
  map_mul' p q := by
    change x ^ (p.toAdd.1 + q.toAdd.1) * y ^ (p.toAdd.2 + q.toAdd.2) = _
    rw [zpow_add, zpow_add]
    calc
      _ = x ^ p.toAdd.1 * (x ^ q.toAdd.1 * y ^ p.toAdd.2) * y ^ q.toAdd.2 := by
        simp [mul_assoc]
      _ = x ^ p.toAdd.1 * (y ^ p.toAdd.2 * x ^ q.toAdd.1) * y ^ q.toAdd.2 := by
        rw [hxy.zpow_zpow q.toAdd.1 p.toAdd.2]
      _ = _ := by simp [mul_assoc]

def apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis
    (j : Fin 2) : ℤ × ℤ :=
  if j = 0 then (1, 0) else (0, 1)

def apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side
    (i : Fin 2) : Multiplicative (ℤ × ℤ) →*
      Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative (ℤ × ℤ)) :=
  if i = 0 then Monoid.Coprod.inl else Monoid.Coprod.inr

def apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen
    (ij : apm_t03J02_generator) :
      Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative (ℤ × ℤ)) :=
  apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side ij.1
    (.ofAdd (apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis ij.2))

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_rel
    (r : FreeGroup apm_t03J02_generator)
    (hr : r ∈ Set.range apm_t03J02_commutatorRelation) :
    FreeGroup.lift
      apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen r = 1 := by
  obtain ⟨i, rfl⟩ := hr
  simp [apm_t03J02_commutatorRelation,
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen,
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis]
  exact commutatorElement_eq_one_iff_commute.mpr <|
    (Commute.all (Multiplicative.ofAdd (1, 0))
    (Multiplicative.ofAdd (0, 1))).map
      (apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side i)

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_commute
    (i : Fin 2) :
    Commute
      (PresentedGroup.of (rels := Set.range apm_t03J02_commutatorRelation) (i, 0))
      (PresentedGroup.of (rels := Set.range apm_t03J02_commutatorRelation) (i, 1)) := by
  rw [← commutatorElement_eq_one_iff_commute]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_toGroup_of
    (ij : apm_t03J02_generator) :
    PresentedGroup.toGroup
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_rel
        (PresentedGroup.of ij) =
      apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen ij :=
  PresentedGroup.toGroup.of _

lemma apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation :
    Nonempty
      (Monoid.Coprod (Multiplicative (ℤ × ℤ))
          (Multiplicative (ℤ × ℤ)) ≃*
        apm_t03J02_freeProductZ2Z2) := by
  let forward : Monoid.Coprod (Multiplicative (ℤ × ℤ))
      (Multiplicative (ℤ × ℤ)) →* apm_t03J02_freeProductZ2Z2 :=
    Monoid.Coprod.lift
      (apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_pairHom
        (PresentedGroup.of (0, 0)) (PresentedGroup.of (0, 1))
        (apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_commute 0))
      (apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_pairHom
        (PresentedGroup.of (1, 0)) (PresentedGroup.of (1, 1))
        (apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_commute 1))
  let backward : apm_t03J02_freeProductZ2Z2 →*
      Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative (ℤ × ℤ)) :=
    PresentedGroup.toGroup
      apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_rel
  refine ⟨MonoidHom.toMulEquiv forward backward ?_ ?_⟩
  · apply Monoid.Coprod.hom_ext
    · apply MonoidHom.ext
      intro p
      rcases p with ⟨a, b⟩
      dsimp [forward, backward,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_pairHom,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis]
      rw [map_mul, map_zpow, map_zpow]
      erw [
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_toGroup_of,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_toGroup_of]
      simp [apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis,
        ← map_zpow, ← map_mul]
      congr 1
      change (a • (1, 0) + b • (0, 1) : ℤ × ℤ) = (a, b)
      simp
    · apply MonoidHom.ext
      intro p
      rcases p with ⟨a, b⟩
      dsimp [forward, backward,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_pairHom,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis]
      rw [map_mul, map_zpow, map_zpow]
      erw [
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_toGroup_of,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_toGroup_of]
      simp [apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis,
        ← map_zpow, ← map_mul]
      congr 1
      change (a • (1, 0) + b • (0, 1) : ℤ × ℤ) = (a, b)
      simp
  · apply PresentedGroup.ext
    rintro ⟨i, j⟩
    change forward (backward (PresentedGroup.of (i, j))) = PresentedGroup.of (i, j)
    dsimp [backward]
    erw [apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_toGroup_of]
    fin_cases i <;> fin_cases j <;>
      norm_num [forward,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_pairHom,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_gen,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_side,
        apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation_aux_basis]

/-- LIBRARY: van Kampen plus the algebraic identification of the two trivial
attaching legs.  The open-cover conclusion is supplied as a hypothesis so this
program can run in parallel with the homology program after the geometry lands. -/
theorem apm_t03J02_fundamentalGroup_of_compatibleOpenCover
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (y₀ : Y)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    Nonempty
      (FundamentalGroup (Y)
        (y₀) ≃*
          apm_t03J02_freeProductZ2Z2) := by
  obtain ⟨e₁⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen
      j₁ j₂ hnull₁ hnull₂ y₀ hcover
  obtain ⟨e₂⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_presentation
  exact ⟨e₁.trans e₂⟩

theorem apm_t03J02_H0_of_compatibleOpenCover
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    Nonempty (apm_t03J02_H 0 Y ≅ ModuleCat.of ℤ ℤ) := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have hc : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
          |>.isPathConnected_preimage.mpr isPathConnected_univ
      simpa using hc)
  letI : PathConnectedSpace apm_t03J02_Torus :=
    ⟨⟨(1, 1)⟩, fun x y =>
      ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
        (PathConnectedSpace.somePath x.2 y.2)⟩⟩
  haveI : PathConnectedSpace hcover.leftSet :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected hcover.leftEquiv
  haveI : PathConnectedSpace hcover.rightSet :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected hcover.rightEquiv
  let w : (hcover.leftSet ∩ hcover.rightSet : Set Y) := hcover.overlapEquiv.invFun 1
  letI : PathConnectedSpace Y :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_pathConnectedSpace
      hcover.leftSet hcover.rightSet hcover.cover w
  exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℤ w.1⟩

/-- A null-homotopic map is zero on degree-one integral homology. -/
lemma apm_t03J02_H1_of_compatibleOpenCover_aux_null_map
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (hf : f.Nullhomotopic) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f) = 0 :=
  ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_zero_of_nullhomotopic
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero f hf

/-- Each torus piece has `H₁ ≅ ℤ²`. -/
lemma apm_t03J02_H1_of_compatibleOpenCover_aux_piece_iso :
    Nonempty (apm_t03J02_H 1 apm_t03J02_Torus ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  exact ⟨ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      (ConstructionTargets.T97A04FrozenH1Coordinate.frozenTorusHomeomorphBoundaryTorus.trans
        (Homeomorph.prodCongr (Homeomorph.refl Circle)
          ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.symm)).symm.toHomotopyEquiv 1 ≪≫
    ConstructionTargets.T97A04FrozenH1Coordinate.frozenTorusH1ModuleIsoFinTwo⟩

/-- Degree-one Mayer--Vietoris calculation; null-homotopy kills both legs. -/
lemma apm_t03J02_H1_of_compatibleOpenCover_aux_pathConnected
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) [PathConnectedSpace Y] :
    PathConnectedSpace X := by
  refine ⟨⟨e.symm (Classical.choice (inferInstance : Nonempty Y))⟩, ?_⟩
  intro x y
  let p : Path (e.symm (e x)) (e.symm (e y)) :=
    (PathConnectedSpace.somePath (e x) (e y)).map e.symm.continuous
  exact ⟨(e.left_inv.some.evalAt x).symm.trans
    (p.trans (e.left_inv.some.evalAt y))⟩

lemma apm_t03J02_H1_of_compatibleOpenCover_aux_equiv_map_isIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.toFun)) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  refine ⟨⟨F.map (TopCat.ofHom e.invFun), ?_, ?_⟩⟩
  · rw [← F.map_comp]
    change F.map (TopCat.ofHom (e.invFun.comp e.toFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) e.left_inv 1]
    exact F.map_id _
  · rw [← F.map_comp]
    change F.map (TopCat.ofHom (e.toFun.comp e.invFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) e.right_inv 1]
    exact F.map_id _

theorem apm_t03J02_H1_of_compatibleOpenCover
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic) (hnull₂ : j₂.Nullhomotopic)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    Nonempty (apm_t03J02_H 1 (Y) ≅
      ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  let U := hcover.leftSet
  let V := hcover.rightSet
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hleft : IntegralMV.mvIncl (A := U ∩ V) (B := U) Set.inter_subset_left 1 = 0 := by
    letI : IsIso (F.map (TopCat.ofHom hcover.leftEquiv.toFun)) :=
      apm_t03J02_H1_of_compatibleOpenCover_aux_equiv_map_isIso hcover.leftEquiv
    apply (cancel_mono (F.map (TopCat.ofHom hcover.leftEquiv.toFun))).1
    simp only [Limits.zero_comp]
    unfold IntegralMV.mvIncl
    change F.map (TopCat.ofHom (apm_t03J02_overlapToLeft U V)) ≫
      F.map (TopCat.ofHom hcover.leftEquiv.toFun) = 0
    rw [← F.map_comp]
    change F.map (TopCat.ofHom
      (hcover.leftEquiv.toFun.comp (apm_t03J02_overlapToLeft U V))) = 0
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hcover.left_compat 1]
    rw [show TopCat.ofHom (j₁.comp hcover.overlapEquiv.toFun) =
      TopCat.ofHom hcover.overlapEquiv.toFun ≫ TopCat.ofHom j₁ from rfl,
      F.map_comp, apm_t03J02_H1_of_compatibleOpenCover_aux_null_map j₁ hnull₁,
      Limits.comp_zero]
  have hright : IntegralMV.mvIncl (A := U ∩ V) (B := V) Set.inter_subset_right 1 = 0 := by
    letI : IsIso (F.map (TopCat.ofHom hcover.rightEquiv.toFun)) :=
      apm_t03J02_H1_of_compatibleOpenCover_aux_equiv_map_isIso hcover.rightEquiv
    apply (cancel_mono (F.map (TopCat.ofHom hcover.rightEquiv.toFun))).1
    simp only [Limits.zero_comp]
    unfold IntegralMV.mvIncl
    change F.map (TopCat.ofHom (apm_t03J02_overlapToRight U V)) ≫
      F.map (TopCat.ofHom hcover.rightEquiv.toFun) = 0
    rw [← F.map_comp]
    change F.map (TopCat.ofHom
      (hcover.rightEquiv.toFun.comp (apm_t03J02_overlapToRight U V))) = 0
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hcover.right_compat 1]
    rw [show TopCat.ofHom (j₂.comp hcover.overlapEquiv.toFun) =
      TopCat.ofHom hcover.overlapEquiv.toFun ≫ TopCat.ofHom j₂ from rfl,
      F.map_comp, apm_t03J02_H1_of_compatibleOpenCover_aux_null_map j₂ hnull₂,
      Limits.comp_zero]
  have hI1 : IntegralMV.mvI U V 1 = 0 := by
    apply Limits.biprod.hom_ext
    · simpa [IntegralMV.mvI] using hleft
    · simpa [IntegralMV.mvI] using hright
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have hc : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
          |>.isPathConnected_preimage.mpr isPathConnected_univ
      simpa using hc)
  letI : PathConnectedSpace (U ∩ V : Set _) :=
    apm_t03J02_H1_of_compatibleOpenCover_aux_pathConnected hcover.overlapEquiv
  let incl := apm_t03J02_overlapToLeft U V
  have hmono0 : Function.Injective
      (IntegralMV.mvIncl (A := U ∩ V) (B := U) Set.inter_subset_left 0).hom := by
    intro x y hxy
    have hn := congrArg (fun z =>
      (ConstructionTargets.CoefficientH0.h0Augmentation ℤ (X := U)).hom z) hxy
    have hnat := ConstructionTargets.CoefficientH0.h0Augmentation_naturality
      (R := ℤ) incl
    have hc : IntegralMV.mvIncl (A := U ∩ V) (B := U) Set.inter_subset_left 0 ≫
        ConstructionTargets.CoefficientH0.h0Augmentation ℤ (X := U) =
        ConstructionTargets.CoefficientH0.h0Augmentation ℤ (X := (U ∩ V : Set _)) := by
      exact hnat
    change ((IntegralMV.mvIncl (A := U ∩ V) (B := U) Set.inter_subset_left 0 ≫
      ConstructionTargets.CoefficientH0.h0Augmentation ℤ (X := U)).hom x) =
      ((IntegralMV.mvIncl (A := U ∩ V) (B := U) Set.inter_subset_left 0 ≫
        ConstructionTargets.CoefficientH0.h0Augmentation ℤ (X := U)).hom y) at hn
    rw [hc] at hn
    let e0 := ConstructionTargets.CoefficientH0.h0Iso ℤ
      (Classical.choice (inferInstance : Nonempty (U ∩ V : Set _)))
    exact (ModuleCat.mono_iff_injective e0.hom).mp (by infer_instance) hn
  have hI0 : Function.Injective (IntegralMV.mvI U V 0).hom := by
    intro x y hxy
    apply hmono0
    have := congrArg (fun z => (Limits.biprod.fst : IntegralMV.HZ 0 U ⊞
      IntegralMV.HZ 0 V ⟶ IntegralMV.HZ 0 U).hom z) hxy
    simpa [IntegralMV.mvI, ← ModuleCat.comp_apply] using this
  obtain ⟨δ, hexI, hexJ, hexD⟩ := IntegralMV.integralMayerVietoris U V
    hcover.open_left hcover.open_right hcover.cover
  have hJmono : Function.Injective (IntegralMV.mvJ U V 1).hom := by
    rw [← LinearMap.ker_eq_bot, ← hexI 1]
    rw [hI1]
    exact LinearMap.range_zero
  have hd0 : δ 0 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.range_eq_bot.mp
    rw [hexD 0, LinearMap.ker_eq_bot.mpr hI0]
  have hJepi : Function.Surjective (IntegralMV.mvJ U V 1).hom := by
    rw [← LinearMap.range_eq_top, hexJ 0, hd0]
    exact LinearMap.ker_zero
  letI : Mono (IntegralMV.mvJ U V 1) :=
    (ModuleCat.mono_iff_injective _).mpr hJmono
  letI : Epi (IntegralMV.mvJ U V 1) :=
    (ModuleCat.epi_iff_surjective _).mpr hJepi
  letI : IsIso (IntegralMV.mvJ U V 1) := isIso_of_mono_of_epi _
  let eL := ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
    hcover.leftEquiv 1 ≪≫
      Classical.choice apm_t03J02_H1_of_compatibleOpenCover_aux_piece_iso
  let eR := ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
    hcover.rightEquiv 1 ≪≫
      Classical.choice apm_t03J02_H1_of_compatibleOpenCover_aux_piece_iso
  let ePieces := Limits.biprod.mapIso eL eR
  let e4 : ((Fin 2 → ℤ) × (Fin 2 → ℤ)) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) ℤ ℤ).symm ≪≫ₗ
      LinearEquiv.funCongrLeft ℤ ℤ (finSumFinEquiv (m := 2) (n := 2)).symm
  exact ⟨(asIso (IntegralMV.mvJ U V 1)).symm ≪≫ ePieces ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of ℤ (Fin 2 → ℤ))
      (ModuleCat.of ℤ (Fin 2 → ℤ)) ≪≫ e4.toModuleIso⟩

/-- Degree-two Mayer--Vietoris calculation, including the kernel `ℤ`. -/
lemma apm_t03J02_H2_of_compatibleOpenCover_aux_circle_H2_zero :
    Limits.IsZero (apm_t03J02_H 2 Circle) := by
  exact (ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
    1 2 (by omega) (by omega)).of_iso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).mapIso
          (TopCat.isoOfHomeo
            ConstructionTargets.CircleHomology.circleHomeomorphSphereOne))

noncomputable def apm_t03J02_H2_of_compatibleOpenCover_aux_torus_H2_iso :
    apm_t03J02_H 2 apm_t03J02_Torus ≅ ModuleCat.of ℤ ℤ :=
  let e : apm_t03J02_Torus ≃ₜ
      ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus :=
    (Homeomorph.refl Circle).prodCongr
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e)) ≪≫
    ConstructionTargets.BoundaryTorusIntegralHomologyComplete.boundaryTorusH2ModuleIsoInt

lemma apm_t03J02_H2_of_compatibleOpenCover_aux_inclusion_H1_zero
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic) (hnull₂ : j₂.Nullhomotopic)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    IntegralMV.mvI hcover.leftSet hcover.rightSet 1 = 0 := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hz₁ : F.map (TopCat.ofHom j₁) = 0 :=
    ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_zero_of_nullhomotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero j₁ hnull₁
  have hz₂ : F.map (TopCat.ofHom j₂) = 0 :=
    ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_zero_of_nullhomotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero j₂ hnull₂
  have hl : IntegralMV.mvIncl
      (X := Y)
      (A := hcover.leftSet ∩ hcover.rightSet) (B := hcover.leftSet)
      Set.inter_subset_left 1 = 0 := by
    let q := F.map (TopCat.ofHom hcover.leftEquiv.toFun)
    let r := F.map (TopCat.ofHom hcover.leftEquiv.invFun)
    have hqr : q ≫ r = 𝟙 _ := by
      rw [← F.map_comp]
      have hc := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hcover.leftEquiv.left_inv 1
      rw [show TopCat.ofHom hcover.leftEquiv.toFun ≫
          TopCat.ofHom hcover.leftEquiv.invFun =
        TopCat.ofHom (hcover.leftEquiv.invFun.comp hcover.leftEquiv.toFun) by rfl,
        hc]
      rw [show TopCat.ofHom (ContinuousMap.id hcover.leftSet) =
        𝟙 (TopCat.of hcover.leftSet) by rfl, F.map_id]
    have hqinj : Function.Injective q.hom := by
      intro x y h
      have hh := congrArg r.hom h
      have hqrhom := congrArg ModuleCat.Hom.hom hqr
      calc
        x = r.hom (q.hom x) := by
          have hx := congrArg (fun f => f x) hqrhom
          simpa using hx.symm
        _ = r.hom (q.hom y) := hh
        _ = y := by
          have hy := congrArg (fun f => f y) hqrhom
          simpa using hy
    letI : Mono q := (ModuleCat.mono_iff_injective q).mpr hqinj
    apply (cancel_mono q).1
    have hm : IntegralMV.mvIncl Set.inter_subset_left 1 =
        F.map (TopCat.ofHom (apm_t03J02_overlapToLeft
          hcover.leftSet hcover.rightSet)) := by rfl
    rw [hm]
    simp only [Limits.zero_comp]
    change F.map (TopCat.ofHom (apm_t03J02_overlapToLeft
      hcover.leftSet hcover.rightSet)) ≫ q = 0
    rw [← F.map_comp]
    have hc := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hcover.left_compat 1
    rw [← show TopCat.ofHom (hcover.leftEquiv.toFun.comp
        (apm_t03J02_overlapToLeft hcover.leftSet hcover.rightSet)) =
      TopCat.ofHom (apm_t03J02_overlapToLeft hcover.leftSet hcover.rightSet) ≫
        TopCat.ofHom hcover.leftEquiv.toFun by rfl]
    rw [hc]
    rw [show TopCat.ofHom (j₁.comp hcover.overlapEquiv.toFun) =
      TopCat.ofHom hcover.overlapEquiv.toFun ≫ TopCat.ofHom j₁ by rfl,
      F.map_comp]
    rw [hz₁]
    simp
  have hr : IntegralMV.mvIncl
      (X := Y)
      (A := hcover.leftSet ∩ hcover.rightSet) (B := hcover.rightSet)
      Set.inter_subset_right 1 = 0 := by
    let q := F.map (TopCat.ofHom hcover.rightEquiv.toFun)
    let r := F.map (TopCat.ofHom hcover.rightEquiv.invFun)
    have hqr : q ≫ r = 𝟙 _ := by
      rw [← F.map_comp]
      have hc := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hcover.rightEquiv.left_inv 1
      rw [show TopCat.ofHom hcover.rightEquiv.toFun ≫
          TopCat.ofHom hcover.rightEquiv.invFun =
        TopCat.ofHom (hcover.rightEquiv.invFun.comp hcover.rightEquiv.toFun) by rfl,
        hc]
      rw [show TopCat.ofHom (ContinuousMap.id hcover.rightSet) =
        𝟙 (TopCat.of hcover.rightSet) by rfl, F.map_id]
    have hqinj : Function.Injective q.hom := by
      intro x y h
      have hh := congrArg r.hom h
      have hqrhom := congrArg ModuleCat.Hom.hom hqr
      calc
        x = r.hom (q.hom x) := by
          have hx := congrArg (fun f => f x) hqrhom
          simpa using hx.symm
        _ = r.hom (q.hom y) := hh
        _ = y := by
          have hy := congrArg (fun f => f y) hqrhom
          simpa using hy
    letI : Mono q := (ModuleCat.mono_iff_injective q).mpr hqinj
    apply (cancel_mono q).1
    have hm : IntegralMV.mvIncl Set.inter_subset_right 1 =
        F.map (TopCat.ofHom (apm_t03J02_overlapToRight
          hcover.leftSet hcover.rightSet)) := by rfl
    rw [hm]
    simp only [Limits.zero_comp]
    change F.map (TopCat.ofHom (apm_t03J02_overlapToRight
      hcover.leftSet hcover.rightSet)) ≫ q = 0
    rw [← F.map_comp]
    have hc := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hcover.right_compat 1
    rw [← show TopCat.ofHom (hcover.rightEquiv.toFun.comp
        (apm_t03J02_overlapToRight hcover.leftSet hcover.rightSet)) =
      TopCat.ofHom (apm_t03J02_overlapToRight hcover.leftSet hcover.rightSet) ≫
        TopCat.ofHom hcover.rightEquiv.toFun by rfl]
    rw [hc]
    rw [show TopCat.ofHom (j₂.comp hcover.overlapEquiv.toFun) =
      TopCat.ofHom hcover.overlapEquiv.toFun ≫ TopCat.ofHom j₂ by rfl,
      F.map_comp]
    rw [hz₂]
    simp
  apply Limits.biprod.hom_ext
  · simp [IntegralMV.mvI, hl]
  · simp [IntegralMV.mvI, hr]

noncomputable def apm_t03J02_H2_of_compatibleOpenCover_aux_finThreeIso :
    (ModuleCat.of ℤ ℤ ⊞ ModuleCat.of ℤ ℤ) ⊞ ModuleCat.of ℤ ℤ ≅
      ModuleCat.of ℤ (Fin 3 → ℤ) :=
  Limits.biprod.mapIso (ModuleCat.biprodIsoProd _ _) (Iso.refl _) ≪≫
    ModuleCat.biprodIsoProd _ _ ≪≫
    (LinearEquiv.ofBijective
      { toFun := fun (p : (ℤ × ℤ) × ℤ) i => Fin.cases p.2 (fun k => Fin.cases p.1.1 (fun _ => p.1.2) k) i
        map_add' := by intros; ext i; fin_cases i <;> rfl
        map_smul' := by intros; ext i; fin_cases i <;> rfl }
      ⟨by
        intro x y h
        apply Prod.ext
        · apply Prod.ext
          · exact congrFun h 1
          · exact congrFun h 2
        · exact congrFun h 0,
       by
        intro z
        exact ⟨((z 1, z 2), z 0), by
          ext i
          fin_cases i <;> rfl⟩⟩).toModuleIso

theorem apm_t03J02_H2_of_compatibleOpenCover
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic) (hnull₂ : j₂.Nullhomotopic)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    Nonempty (apm_t03J02_H 2 (Y) ≅
      ModuleCat.of ℤ (Fin 3 → ℤ)) := by
  let U := hcover.leftSet
  let V := hcover.rightSet
  obtain ⟨δ, hexI, hexJ, hexD⟩ := IntegralMV.integralMayerVietoris U V
    hcover.open_left hcover.open_right hcover.cover
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (IntegralMV.mvJ U V 2) (δ 1) (by
      apply ModuleCat.hom_ext
      ext x
      change (δ 1).hom ((IntegralMV.mvJ U V 2).hom x) = 0
      rw [← LinearMap.mem_ker, ← hexJ 1]
      exact ⟨x, rfl⟩)
  have hSexact : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hexJ 1
  have hI2zero : Limits.IsZero (IntegralMV.HZ 2 (U ∩ V : Set _)) :=
    apm_t03J02_H2_of_compatibleOpenCover_aux_circle_H2_zero.of_iso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        hcover.overlapEquiv 2)
  have hmono : Function.Injective (IntegralMV.mvJ U V 2).hom := by
    rw [← LinearMap.ker_eq_bot, ← hexI 2]
    apply LinearMap.range_eq_bot.mpr
    have hm : IntegralMV.mvI U V 2 = 0 := hI2zero.eq_of_src _ 0
    exact congrArg ModuleCat.Hom.hom hm
  letI : Mono S.f := (ModuleCat.mono_iff_injective _).mpr hmono
  have hI1zero : IntegralMV.mvI U V 1 = 0 :=
    apm_t03J02_H2_of_compatibleOpenCover_aux_inclusion_H1_zero
      j₁ j₂ hnull₁ hnull₂ hcover
  have hepi : Function.Surjective (δ 1).hom := by
    rw [← LinearMap.range_eq_top, hexD 1, hI1zero]
    exact LinearMap.ker_zero
  letI : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr hepi
  letI : Projective (IntegralMV.HZ 1 (U ∩ V : Set _)) := by
    let e := ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      hcover.overlapEquiv 1 ≪≫
      ConstructionTargets.SingularHomologyConcrete.circleSingularH1IsoInt
    exact Projective.of_iso e.symm inferInstance
  let split := ProjectiveQuotientExactSplitting.exactIsoBiprod S hSexact
  let pieceIso : (IntegralMV.HZ 2 U ⊞ IntegralMV.HZ 2 V) ≅
      (ModuleCat.of ℤ ℤ ⊞ ModuleCat.of ℤ ℤ) :=
    Limits.biprod.mapIso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        hcover.leftEquiv 2 ≪≫
        apm_t03J02_H2_of_compatibleOpenCover_aux_torus_H2_iso)
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        hcover.rightEquiv 2 ≪≫
        apm_t03J02_H2_of_compatibleOpenCover_aux_torus_H2_iso)
  let overlapIso :=
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
      hcover.overlapEquiv 1 ≪≫
      ConstructionTargets.SingularHomologyConcrete.circleSingularH1IsoInt
  exact ⟨split ≪≫ Limits.biprod.mapIso pieceIso overlapIso ≪≫
    apm_t03J02_H2_of_compatibleOpenCover_aux_finThreeIso⟩

/-- Mayer--Vietoris above the dimensions of the circle and torus. -/
lemma apm_t03J02_Hhigh_of_compatibleOpenCover_aux_circle_zero
    (n : ℕ) (hn : 2 ≤ n) : Limits.IsZero (apm_t03J02_H n Circle) := by
  exact (ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
    1 n (by omega) (by omega)).of_iso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).mapIso
          (TopCat.isoOfHomeo
            ConstructionTargets.CircleHomology.circleHomeomorphSphereOne))

lemma apm_t03J02_Hhigh_of_compatibleOpenCover_aux_torus_zero
    (n : ℕ) (hn : 3 ≤ n) : Limits.IsZero (apm_t03J02_H n apm_t03J02_Torus) := by
  let e : apm_t03J02_Torus ≃ₜ ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus :=
    (Homeomorph.refl Circle).prodCongr
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
  exact (ConstructionTargets.BoundaryTorusIntegralHomologyComplete.boundaryTorusModuleHomology_isZero_of_two_lt
    n (by omega)).of_iso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e))

theorem apm_t03J02_Hhigh_of_compatibleOpenCover
    {Y : Type} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂ Y) :
    ∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (apm_t03J02_H k (Y)) := by
  intro k hk
  let U := hcover.leftSet
  let V := hcover.rightSet
  have hUk : Limits.IsZero (IntegralMV.HZ k U) :=
    (apm_t03J02_Hhigh_of_compatibleOpenCover_aux_torus_zero k hk).of_iso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        hcover.leftEquiv k)
  have hVk : Limits.IsZero (IntegralMV.HZ k V) :=
    (apm_t03J02_Hhigh_of_compatibleOpenCover_aux_torus_zero k hk).of_iso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        hcover.rightEquiv k)
  have hIp : Limits.IsZero (IntegralMV.HZ (k - 1) (U ∩ V : Set _)) :=
    (apm_t03J02_Hhigh_of_compatibleOpenCover_aux_circle_zero (k - 1) (by omega)).of_iso
      (ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
        hcover.overlapEquiv (k - 1))
  obtain ⟨δ, -, hexJ, -⟩ := IntegralMV.integralMayerVietoris U V
    hcover.open_left hcover.open_right hcover.cover
  have hk' : k - 1 + 1 = k := by omega
  have hUk' : Limits.IsZero (IntegralMV.HZ (k - 1 + 1) U) := by
    simpa only [hk'] using hUk
  have hVk' : Limits.IsZero (IntegralMV.HZ (k - 1 + 1) V) := by
    simpa only [hk'] using hVk
  let d := δ (k - 1)
  have hdmono : Function.Injective d.hom := by
    rw [← LinearMap.ker_eq_bot, ← hexJ (k - 1)]
    apply LinearMap.range_eq_bot.mpr
    have hpieces :=
      (CategoryTheory.Limits.biprod_isZero_iff _ _).mpr ⟨hUk', hVk'⟩
    have hm : IntegralMV.mvJ U V (k - 1 + 1) = 0 := hpieces.eq_of_src _ 0
    exact congrArg ModuleCat.Hom.hom hm
  letI : Mono d := (ModuleCat.mono_iff_injective d).mpr hdmono
  have hz := @Limits.IsZero.of_mono (ModuleCat ℤ) _ _ _ _ d inferInstance hIp
  simpa only [hk'] using hz

/-! ### Replacing the collar (2026-11-03)

An arbitrary embedded circle has no cheap collar, so the open cover is not built on the quotient
`X`.  It is built on `Cyl ⊆ X × ℝ`: the left torus at height `-1`, the right torus at height `1`,
and the glued circle at all heights between.  There the cover is `s < 1/2`, `s > -1/2` and every
homotopy is linear in `s`.  `X` is homotopy equivalent to `Cyl` because each pair (torus, circle)
has the following neighbourhood deformation, from Tietze and straight lines in the flat torus. -/

open unitInterval

/-- `H` deforms the torus to a map carrying `{β < 1}` into the circle, fixing the circle. -/
structure apm_t03J02_Retractile (j : C(Circle, apm_t03J02_Torus)) where
  H : C(apm_t03J02_Torus × I, apm_t03J02_Torus)
  β : C(apm_t03J02_Torus, ℝ)
  H_zero : ∀ x, H (x, 0) = x
  H_fix : ∀ z t, H (j z, t) = j z
  β_nonneg : ∀ x, 0 ≤ β x
  β_le_one : ∀ x, β x ≤ 1
  β_fix : ∀ z, β (j z) = 0
  H_one : ∀ x, β x < 1 → H (x, 1) ∈ Set.range j

section Retractile
open Set Topology

theorem apm_t03J02_exists_retractile_aux_construct (j : C(Circle, apm_t03J02_Torus))
    (hj : IsEmbedding j) :
    ∃ (H : C(apm_t03J02_Torus × I, apm_t03J02_Torus)) (β : C(apm_t03J02_Torus, ℝ)),
      (∀ x, H (x, 0) = x) ∧ (∀ z t, H (j z, t) = j z) ∧ (∀ x, 0 ≤ β x) ∧ (∀ x, β x ≤ 1) ∧
      (∀ z, β (j z) = 0) ∧ (∀ x, β x < 1 → H (x, 1) ∈ Set.range j) := by
  classical
  have hJc : IsCompact (range j) := isCompact_range j.continuous
  have hJ : IsClosed (range j) := hJc.isClosed
  have hJne : (range j).Nonempty := ⟨j 1, 1, rfl⟩
  -- Tietze
  let e := hj.toHomeomorph
  let f : C(range j, ℂ) := ⟨fun y => ((e.symm y : Circle) : ℂ),
    (continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp e.symm.continuous⟩
  obtain ⟨G, hG⟩ := f.exists_restrict_eq hJ
  have hGj : ∀ z, G (j z) = z := by
    intro z
    have h := DFunLike.congr_fun hG ⟨j z, z, rfl⟩
    have h2 : e.symm ⟨j z, z, rfl⟩ = z := e.symm_apply_apply z
    simpa [f, h2] using h
  -- the retraction
  let ρ : apm_t03J02_Torus → Circle := fun x =>
    if h : G x ≠ 0 then ⟨G x / ‖G x‖, by
      simp [Submonoid.unitSphere, norm_div, h]⟩ else 1
  have hρcoe : ∀ x, G x ≠ 0 → (ρ x : ℂ) = G x / ‖G x‖ := fun x h => by
    simp only [ρ, dif_pos h]
  let U₀ : Set apm_t03J02_Torus := {x | G x ≠ 0}
  have hU₀ : IsOpen U₀ := isOpen_ne_fun G.continuous continuous_const
  have hind : IsInducing (fun z : Circle => (z : ℂ)) := ⟨rfl⟩
  have hρ : ContinuousOn ρ U₀ := by
    refine hind.continuousOn_iff.2 ?_
    have : ContinuousOn (fun x => G x / (‖G x‖ : ℂ)) U₀ := by
      apply ContinuousOn.div G.continuous.continuousOn
      · exact (Complex.continuous_ofReal.comp G.continuous.norm).continuousOn
      · intro x hx
        simpa using hx
    exact this.congr fun x hx => hρcoe x hx
  have hρj : ∀ z, ρ (j z) = z := by
    intro z
    apply Circle.ext
    rw [hρcoe _ (by rw [hGj]; exact Circle.coe_ne_zero z), hGj]
    simp
  have hG0 : ∀ z, j z ∈ U₀ := fun z => by
    change G (j z) ≠ 0
    rw [hGj]; exact Circle.coe_ne_zero z
  let k : apm_t03J02_Torus → apm_t03J02_Torus := fun x => j (ρ x)
  have hk : ContinuousOn k U₀ := j.continuous.comp_continuousOn hρ
  let r₁ : apm_t03J02_Torus → Circle := fun x => (k x).1 / x.1
  let r₂ : apm_t03J02_Torus → Circle := fun x => (k x).2 / x.2
  have hr₁ : ContinuousOn r₁ U₀ :=
    (continuous_fst.comp_continuousOn hk).div' continuous_fst.continuousOn
  have hr₂ : ContinuousOn r₂ U₀ :=
    (continuous_snd.comp_continuousOn hk).div' continuous_snd.continuousOn
  have hkj : ∀ z, k (j z) = j z := fun z => by simp [k, hρj]
  have hr₁j : ∀ z, r₁ (j z) = 1 := fun z => by simp [r₁, hkj]
  have hr₂j : ∀ z, r₂ (j z) = 1 := fun z => by simp [r₂, hkj]
  let V : Set apm_t03J02_Torus := U₀ ∩ ((fun x => (r₁ x : ℂ)) ⁻¹' Complex.slitPlane ∩
    (fun x => (r₂ x : ℂ)) ⁻¹' Complex.slitPlane)
  have hc₁ : ContinuousOn (fun x => (r₁ x : ℂ)) U₀ :=
    (continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp_continuousOn hr₁
  have hc₂ : ContinuousOn (fun x => (r₂ x : ℂ)) U₀ :=
    (continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp_continuousOn hr₂
  have hV : IsOpen V := by
    have h1 := hc₁.isOpen_inter_preimage hU₀ Complex.isOpen_slitPlane
    have h2 := hc₂.isOpen_inter_preimage hU₀ Complex.isOpen_slitPlane
    have : V = (U₀ ∩ (fun x => (r₁ x : ℂ)) ⁻¹' Complex.slitPlane) ∩
        (U₀ ∩ (fun x => (r₂ x : ℂ)) ⁻¹' Complex.slitPlane) := by
      ext x; simp only [V, mem_inter_iff]; tauto
    rw [this]; exact h1.inter h2
  have hJV : range j ⊆ V := by
    rintro _ ⟨z, rfl⟩
    refine ⟨hG0 z, ?_, ?_⟩ <;> simp [hr₁j, hr₂j]
  obtain ⟨ε, hε, hth⟩ := hJc.exists_thickening_subset_open hV hJV
  let d : apm_t03J02_Torus → ℝ := fun x => Metric.infDist x (range j)
  have hd : Continuous d := Metric.continuous_infDist_pt _
  have hdj : ∀ z, d (j z) = 0 := fun z => Metric.infDist_zero_of_mem ⟨z, rfl⟩
  have hdV : ∀ x, d x < ε → x ∈ V := fun x hx =>
    hth ((Metric.mem_thickening_iff_infDist_lt hJne).2 hx)
  let lam : apm_t03J02_Torus → ℝ := fun x => max 0 (min 1 (2 - 3 * d x / ε))
  have hlam : Continuous lam := by fun_prop
  have hlam1 : ∀ x, d x < ε / 3 → lam x = 1 := by
    intro x hx
    have : 3 * d x / ε < 1 := by rw [div_lt_iff₀ hε]; linarith
    simp only [lam]
    rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  have hlam0 : ∀ x, 2 * ε / 3 < d x → lam x = 0 := by
    intro x hx
    have : 2 < 3 * d x / ε := by rw [lt_div_iff₀ hε]; linarith
    simp only [lam]
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have key : ∀ (r : apm_t03J02_Torus → Circle), ContinuousOn (fun x => (r x : ℂ)) U₀ →
      (∀ x ∈ V, (r x : ℂ) ∈ Complex.slitPlane) →
      Continuous fun x => lam x * Complex.arg (r x) := by
    intro r hr hrV
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : d x < ε
    · have hxV := hdV x hx
      have h1 : ContinuousAt (fun x => (r x : ℂ)) x :=
        hr.continuousAt (hU₀.mem_nhds hxV.1)
      exact hlam.continuousAt.mul
        (ContinuousAt.comp (f := fun x => (r x : ℂ)) (Complex.continuousAt_arg (hrV x hxV)) h1)
    · have h2 : 2 * ε / 3 < d x := by
        have := not_lt.1 hx
        linarith
      have h3 : ∀ᶠ y in 𝓝 x, lam y * Complex.arg (r y) = 0 := by
        filter_upwards [hd.continuousAt.eventually (lt_mem_nhds h2)] with y hy
        rw [hlam0 y hy, zero_mul]
      exact (continuousAt_const (y := (0 : ℝ))).congr (by
        filter_upwards [h3] with y hy using hy.symm)
  let φ₁ : apm_t03J02_Torus → ℝ := fun x => lam x * Complex.arg (r₁ x)
  let φ₂ : apm_t03J02_Torus → ℝ := fun x => lam x * Complex.arg (r₂ x)
  have hφ₁ : Continuous φ₁ := key r₁ hc₁ fun x hx => hx.2.1
  have hφ₂ : Continuous φ₂ := key r₂ hc₂ fun x hx => hx.2.2
  let H : C(apm_t03J02_Torus × I, apm_t03J02_Torus) := ⟨fun p =>
      (p.1.1 * Circle.exp ((p.2 : ℝ) * φ₁ p.1), p.1.2 * Circle.exp ((p.2 : ℝ) * φ₂ p.1)), by
    apply Continuous.prodMk
    · exact (continuous_fst.comp continuous_fst).mul
        (Circle.exp.continuous.comp
          ((continuous_subtype_val.comp continuous_snd).mul (hφ₁.comp continuous_fst)))
    · exact (continuous_snd.comp continuous_fst).mul
        (Circle.exp.continuous.comp
          ((continuous_subtype_val.comp continuous_snd).mul (hφ₂.comp continuous_fst)))⟩
  let β : C(apm_t03J02_Torus, ℝ) := ⟨fun x => min 1 (3 * d x / ε), by fun_prop⟩
  have hdnn : ∀ x, 0 ≤ d x := fun x => Metric.infDist_nonneg
  refine ⟨H, β, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [H]
  · intro z t
    have h1 : φ₁ (j z) = 0 := by simp [φ₁, hr₁j]
    have h2 : φ₂ (j z) = 0 := by simp [φ₂, hr₂j]
    simp [H, h1, h2]
  · intro x
    exact le_min zero_le_one (by have := hdnn x; positivity)
  · intro x
    exact min_le_left _ _
  · intro z
    simp [β, hdj]
  · intro x hx
    have h1 : 3 * d x / ε < 1 := by
      by_contra hc
      have : min (1 : ℝ) (3 * d x / ε) = 1 := min_eq_left (not_lt.1 hc)
      exact absurd hx (by simp only [β]; change ¬ min _ _ < _; rw [this]; norm_num)
    have h2 : d x < ε / 3 := by
      rw [div_lt_iff₀ hε] at h1; linarith
    have h3 := hlam1 x h2
    refine ⟨ρ x, ?_⟩
    apply Prod.ext
    · change (k x).1 = x.1 * Circle.exp (((1 : I) : ℝ) * (lam x * Complex.arg (r₁ x)))
      rw [h3]
      simp only [Icc.coe_one, one_mul]
      rw [Circle.exp_arg]
      simp [r₁]
    · change (k x).2 = x.2 * Circle.exp (((1 : I) : ℝ) * (lam x * Complex.arg (r₂ x)))
      rw [h3]
      simp only [Icc.coe_one, one_mul]
      rw [Circle.exp_arg]
      simp [r₂]

end Retractile

/-- Tietze extends the inverse of `j` to a map to `ℂ`; normalising gives a retraction `k` of an
open `N` onto the circle.  Straight lines in the flat torus join `x` to `k x` when they are close;
cut off with a function of the distance to the circle. -/
theorem apm_t03J02_exists_retractile (j : C(Circle, apm_t03J02_Torus))
    (hj : Topology.IsEmbedding j) : Nonempty (apm_t03J02_Retractile j) := by
  obtain ⟨H, β, h0, h1, h2, h3, h4, h5⟩ := apm_t03J02_exists_retractile_aux_construct j hj
  exact ⟨⟨H, β, h0, h1, h2, h3, h4, h5⟩⟩

section Glued
variable (j₁ j₂ : C(Circle, apm_t03J02_Torus))

/-- The glued circle in the quotient. -/
def apm_t03J02_gluedCircle : C(Circle, apm_t03J02_space j₁ j₂) :=
  (apm_t03J02_gluedInl j₁ j₂).comp j₁

variable {j₁ j₂}

theorem apm_t03J02_inl_eq_inl_iff_aux_eqvGen
    (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂)
    {a b : Sum apm_t03J02_Torus apm_t03J02_Torus}
    (h : Relation.EqvGen (apm_t03J02_glueRel j₁ j₂) a b) :
    match a, b with
    | .inl x, .inl y => x = y
    | .inr x, .inr y => x = y
    | .inl x, .inr y => ∃ z, x = j₁ z ∧ y = j₂ z
    | .inr x, .inl y => ∃ z, x = j₂ z ∧ y = j₁ z := by
  induction h with
  | rel a b hab =>
      cases hab with
      | glue z => exact ⟨z, rfl, rfl⟩
  | refl a => cases a <;> rfl
  | symm a b h ih =>
      cases a with
      | inl x =>
          cases b with
          | inl y => exact ih.symm
          | inr y => rcases ih with ⟨z, hy, hx⟩; exact ⟨z, hx, hy⟩
      | inr x =>
          cases b with
          | inl y => rcases ih with ⟨z, hy, hx⟩; exact ⟨z, hx, hy⟩
          | inr y => exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              cases c with
              | inl w =>
                  change x = y at ih₁
                  change y = w at ih₂
                  exact ih₁.trans ih₂
              | inr w =>
                  change x = y at ih₁
                  change ∃ z, y = j₁ z ∧ w = j₂ z at ih₂
                  rcases ih₂ with ⟨z, hy, hw⟩
                  exact ⟨z, ih₁.trans hy, hw⟩
          | inr y =>
              cases c with
              | inl w =>
                  rcases ih₁ with ⟨z, hx, hy⟩
                  rcases ih₂ with ⟨z', hy', hw⟩
                  have : z = z' := hj₂.injective (hy.symm.trans hy')
                  subst z'
                  exact hx.trans hw.symm
              | inr w =>
                  rcases ih₁ with ⟨z, hx, hy⟩
                  change y = w at ih₂
                  exact ⟨z, hx, (hy.symm.trans ih₂).symm⟩
      | inr x =>
          cases b with
          | inl y =>
              cases c with
              | inl w =>
                  rcases ih₁ with ⟨z, hx, hy⟩
                  change y = w at ih₂
                  exact ⟨z, hx, (hy.symm.trans ih₂).symm⟩
              | inr w =>
                  rcases ih₁ with ⟨z, hx, hy⟩
                  rcases ih₂ with ⟨z', hy', hw⟩
                  have : z = z' := hj₁.injective (hy.symm.trans hy')
                  subst z'
                  exact hx.trans hw.symm
          | inr y =>
              cases c with
              | inl w =>
                  change ∃ z, y = j₂ z ∧ w = j₁ z at ih₂
                  rcases ih₂ with ⟨z, hy, hw⟩
                  exact ⟨z, ih₁.trans hy, hw⟩
              | inr w =>
                  change x = y at ih₁
                  change y = w at ih₂
                  exact ih₁.trans ih₂

theorem apm_t03J02_inl_eq_inl_iff (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) {x y : apm_t03J02_Torus} :
    apm_t03J02_gluedInl j₁ j₂ x = apm_t03J02_gluedInl j₁ j₂ y ↔ x = y := by
  constructor
  · intro h
    exact apm_t03J02_inl_eq_inl_iff_aux_eqvGen hj₁ hj₂ (Quotient.exact h)
  · rintro rfl
    rfl

theorem apm_t03J02_inr_eq_inr_iff (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) {x y : apm_t03J02_Torus} :
    apm_t03J02_gluedInr j₁ j₂ x = apm_t03J02_gluedInr j₁ j₂ y ↔ x = y := by
  constructor
  · intro h
    exact apm_t03J02_inl_eq_inl_iff_aux_eqvGen hj₁ hj₂ (Quotient.exact h)
  · rintro rfl
    rfl

theorem apm_t03J02_inl_eq_inr_iff (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) {x y : apm_t03J02_Torus} :
    apm_t03J02_gluedInl j₁ j₂ x = apm_t03J02_gluedInr j₁ j₂ y ↔
      ∃ z, x = j₁ z ∧ y = j₂ z := by
  constructor
  · intro h
    exact apm_t03J02_inl_eq_inl_iff_aux_eqvGen hj₁ hj₂ (Quotient.exact h)
  · rintro ⟨z, rfl, rfl⟩
    exact apm_t03J02_glue_eq j₁ j₂ z

/-- Tietze: a map on the circle to `ℂ × ℂ` extends over the torus. -/
theorem apm_t03J02_t2Space_aux_extend {j : C(Circle, apm_t03J02_Torus)}
    (hj : Topology.IsEmbedding j) (u : C(Circle, ℂ × ℂ)) :
    ∃ G : C(apm_t03J02_Torus, ℂ × ℂ), ∀ z, G (j z) = u z := by
  have hJ : IsClosed (Set.range j) := (isCompact_range j.continuous).isClosed
  let e := hj.toHomeomorph
  let f : C(Set.range j, ℂ × ℂ) := ⟨fun y => u (e.symm y), u.continuous.comp e.symm.continuous⟩
  obtain ⟨G, hG⟩ := f.exists_restrict_eq hJ
  refine ⟨G, fun z => ?_⟩
  have h := DFunLike.congr_fun hG ⟨j z, z, rfl⟩
  have h2 : e.symm ⟨j z, z, rfl⟩ = z := e.symm_apply_apply z
  simpa [f, h2] using h

/-- The coordinates of the torus in `ℂ × ℂ`. -/
def apm_t03J02_t2Space_aux_coord : C(apm_t03J02_Torus, ℂ × ℂ) :=
  ⟨fun x => ((x.1 : ℂ), (x.2 : ℂ)),
    ((continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp continuous_fst).prodMk
      ((continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp continuous_snd)⟩

theorem apm_t03J02_t2Space_aux_coord_inj :
    Function.Injective apm_t03J02_t2Space_aux_coord := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (Circle.ext h1) (Circle.ext h2)

/-- `X` injects continuously into a Euclidean space: record the coordinates on each torus, a
Tietze extension of the other torus's coordinates, and the distances to the two circles. -/
theorem apm_t03J02_t2Space_aux_separation
    (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    T2Space (apm_t03J02_space j₁ j₂) := by
  let ι := apm_t03J02_t2Space_aux_coord
  obtain ⟨G₁, hG₁⟩ := apm_t03J02_t2Space_aux_extend hj₁ (ι.comp j₂)
  obtain ⟨G₂, hG₂⟩ := apm_t03J02_t2Space_aux_extend hj₂ (ι.comp j₁)
  let d₁ : C(apm_t03J02_Torus, ℝ) :=
    ⟨fun x => Metric.infDist x (Set.range j₁), Metric.continuous_infDist_pt _⟩
  let d₂ : C(apm_t03J02_Torus, ℝ) :=
    ⟨fun x => Metric.infDist x (Set.range j₂), Metric.continuous_infDist_pt _⟩
  let Y := (ℂ × ℂ) × (ℂ × ℂ) × ℝ × ℝ
  let f : C(apm_t03J02_Torus, Y) :=
    ⟨fun x => (ι x, G₁ x, d₁ x, 0), by fun_prop⟩
  let g : C(apm_t03J02_Torus, Y) :=
    ⟨fun x => (G₂ x, ι x, 0, d₂ x), by fun_prop⟩
  have hd₁ : ∀ z, d₁ (j₁ z) = 0 := fun z => Metric.infDist_zero_of_mem ⟨z, rfl⟩
  have hd₂ : ∀ z, d₂ (j₂ z) = 0 := fun z => Metric.infDist_zero_of_mem ⟨z, rfl⟩
  have hfg : ∀ z, f (j₁ z) = g (j₂ z) := by
    intro z
    change (ι (j₁ z), G₁ (j₁ z), d₁ (j₁ z), (0 : ℝ)) = (G₂ (j₂ z), ι (j₂ z), (0 : ℝ), d₂ (j₂ z))
    rw [hG₁, hG₂, hd₁, hd₂]
    rfl
  let Φ := apm_t03J02_gluedDesc j₁ j₂ f g hfg
  have hzero : ∀ {j : C(Circle, apm_t03J02_Torus)} (x : apm_t03J02_Torus),
      Metric.infDist x (Set.range j) = 0 → x ∈ Set.range j := by
    intro j x hx
    have hc : IsClosed (Set.range j) := (isCompact_range j.continuous).isClosed
    exact (hc.mem_iff_infDist_zero ⟨j 1, 1, rfl⟩).2 hx
  have hmixed : ∀ a b, f a = g b →
      apm_t03J02_quotientMap j₁ j₂ (.inl a) = apm_t03J02_quotientMap j₁ j₂ (.inr b) := by
    intro a b h
    have h1 : ι a = G₂ b := congrArg Prod.fst h
    have h3 : d₁ a = 0 := congrArg (fun t : Y => t.2.2.1) h
    have h4 : (0 : ℝ) = d₂ b := congrArg (fun t : Y => t.2.2.2) h
    obtain ⟨z, rfl⟩ := hzero a h3
    obtain ⟨w, rfl⟩ := hzero b h4.symm
    rw [hG₂] at h1
    have : j₁ z = j₁ w := apm_t03J02_t2Space_aux_coord_inj h1
    rw [this]
    exact apm_t03J02_glue_eq j₁ j₂ w
  have hinj : Function.Injective Φ := by
    intro p q
    obtain ⟨sp, rfl⟩ := apm_t03J02_surjective_quotientMap j₁ j₂ p
    obtain ⟨sq, rfl⟩ := apm_t03J02_surjective_quotientMap j₁ j₂ q
    intro h
    cases sp with
    | inl a =>
      cases sq with
      | inl b =>
        have : f a = f b := h
        rw [apm_t03J02_t2Space_aux_coord_inj (congrArg Prod.fst this : ι a = ι b)]
      | inr b => exact hmixed a b h
    | inr a =>
      cases sq with
      | inl b => exact (hmixed b a h.symm).symm
      | inr b =>
        have : g a = g b := h
        rw [apm_t03J02_t2Space_aux_coord_inj
          (congrArg (fun t : Y => t.2.1) this : ι a = ι b)]
  exact T2Space.of_injective_continuous hinj Φ.continuous

theorem apm_t03J02_t2Space (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    T2Space (apm_t03J02_space j₁ j₂) := by
  exact apm_t03J02_t2Space_aux_separation hj₁ hj₂

theorem apm_t03J02_compactSpace : CompactSpace (apm_t03J02_space j₁ j₂) := by
  rw [← isCompact_univ_iff]
  have hr : Set.range (apm_t03J02_quotientMap j₁ j₂) = Set.univ :=
    Set.range_eq_univ.mpr (apm_t03J02_surjective_quotientMap j₁ j₂)
  rw [← hr]
  simpa only [Set.image_univ] using
    isCompact_univ.image (apm_t03J02_continuous_quotientMap j₁ j₂)

variable (j₁ j₂)

/-- The left torus at height `-1`, the right at `1`, and the glued circle at every height between. -/
def apm_t03J02_cylSet : Set (apm_t03J02_space j₁ j₂ × ℝ) :=
  {p | (p.2 = -1 ∧ p.1 ∈ Set.range (apm_t03J02_gluedInl j₁ j₂)) ∨
    (p.2 = 1 ∧ p.1 ∈ Set.range (apm_t03J02_gluedInr j₁ j₂)) ∨
    (p.1 ∈ Set.range (apm_t03J02_gluedCircle j₁ j₂) ∧ p.2 ∈ Set.Icc (-1 : ℝ) 1)}

abbrev apm_t03J02_Cyl := ↥(apm_t03J02_cylSet j₁ j₂)

/-- The deformation of the quotient obtained by gluing two `Retractile`s, together with the height
function it is paired with. -/
structure apm_t03J02_Deform where
  E : C(apm_t03J02_space j₁ j₂ × I, apm_t03J02_space j₁ j₂)
  B : C(apm_t03J02_space j₁ j₂, ℝ)
  E_zero : ∀ x, E (x, 0) = x
  mem₁ : ∀ p ∈ apm_t03J02_cylSet j₁ j₂, ∀ t : I, (E (p.1, t), p.2) ∈ apm_t03J02_cylSet j₁ j₂
  mem₂ : ∀ p ∈ apm_t03J02_cylSet j₁ j₂, ∀ t : I,
    (E (p.1, 1), (1 - (t : ℝ)) * p.2 + t * B p.1) ∈ apm_t03J02_cylSet j₁ j₂
  fibre : ∀ x, ∃ s, (x, s) ∈ apm_t03J02_cylSet j₁ j₂

variable {j₁ j₂}

/-- `E = H₁` on the left and `H₂` on the right, `B = -β₁` on the left and `β₂` on the right.  Use
`apm_t03J02_gluedDesc` with target `C(I, X)` and uncurry for `E`. -/
theorem apm_t03J02_exists_deform (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂)
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) :
    Nonempty (apm_t03J02_Deform j₁ j₂) := by
  sorry

/-- `c = fst`, `b x = (E (x, 1), B x)`.  `c ∘ b` is homotopic to the identity through `E`.
`b ∘ c` goes to `id` in two stages: `(x, s) ↦ (E (x, t), s)`, then
`(x, s) ↦ (E (x, 1), (1 - t) s + t B x)`. -/
theorem apm_t03J02_homotopyEquiv_cyl (D : apm_t03J02_Deform j₁ j₂) :
    Nonempty (ContinuousMap.HomotopyEquiv (apm_t03J02_space j₁ j₂) (apm_t03J02_Cyl j₁ j₂)) := by
  sorry

variable (j₁ j₂)

def apm_t03J02_cylLeft : Set (apm_t03J02_Cyl j₁ j₂) := {p | p.1.2 < 1 / 2}
def apm_t03J02_cylRight : Set (apm_t03J02_Cyl j₁ j₂) := {p | -(1 / 2) < p.1.2}

variable {j₁ j₂}

/-- Inverse `x ↦ (inl x, -1)`; homotopy `(x, s) ↦ (x, (1 - t) s - t)`.  Below height `1/2` the first
coordinate lies in the range of `inl`, which is a closed embedding by compactness and `T2`. -/
theorem apm_t03J02_cylLeft_equiv (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    ∃ e : ContinuousMap.HomotopyEquiv (apm_t03J02_cylLeft j₁ j₂) apm_t03J02_Torus,
      ∀ p, apm_t03J02_gluedInl j₁ j₂ (e.toFun p) = p.1.1.1 := by
  sorry

theorem apm_t03J02_cylRight_equiv (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    ∃ e : ContinuousMap.HomotopyEquiv (apm_t03J02_cylRight j₁ j₂) apm_t03J02_Torus,
      ∀ p, apm_t03J02_gluedInr j₁ j₂ (e.toFun p) = p.1.1.1 := by
  sorry

/-- Inverse `z ↦ (gluedCircle z, 0)`; homotopy `(x, s) ↦ (x, (1 - t) s)`. -/
theorem apm_t03J02_cylOverlap_equiv (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) :
    ∃ e : ContinuousMap.HomotopyEquiv
        (apm_t03J02_cylLeft j₁ j₂ ∩ apm_t03J02_cylRight j₁ j₂ : Set (apm_t03J02_Cyl j₁ j₂)) Circle,
      ∀ p, apm_t03J02_gluedCircle j₁ j₂ (e.toFun p) = p.1.1.1 := by
  sorry

theorem apm_t03J02_cyl_cover (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    Nonempty (apm_t03J02_CompatibleOpenCover j₁ j₂ (apm_t03J02_Cyl j₁ j₂)) := by
  obtain ⟨eL, hL⟩ := apm_t03J02_cylLeft_equiv hj₁ hj₂
  obtain ⟨eR, hR⟩ := apm_t03J02_cylRight_equiv hj₁ hj₂
  obtain ⟨eO, hO⟩ := apm_t03J02_cylOverlap_equiv hj₁ hj₂
  refine ⟨{ leftSet := apm_t03J02_cylLeft j₁ j₂
            rightSet := apm_t03J02_cylRight j₁ j₂
            open_left := isOpen_lt (by fun_prop) continuous_const
            open_right := isOpen_lt continuous_const (by fun_prop)
            cover := ?_
            leftEquiv := eL
            rightEquiv := eR
            overlapEquiv := eO
            left_compat := ?_
            right_compat := ?_ }⟩
  · ext p
    simp only [Set.mem_union, Set.mem_univ, iff_true, apm_t03J02_cylLeft, apm_t03J02_cylRight,
      Set.mem_setOf_eq]
    by_cases h : p.1.2 < 1 / 2
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · have : eL.toFun.comp (apm_t03J02_overlapToLeft _ _) = j₁.comp eO.toFun := by
      ext1 p
      apply (apm_t03J02_inl_eq_inl_iff hj₁ hj₂).1
      exact (hL _).trans (hO p).symm
    rw [this]
  · have : eR.toFun.comp (apm_t03J02_overlapToRight _ _) = j₂.comp eO.toFun := by
      ext1 p
      apply (apm_t03J02_inr_eq_inr_iff hj₁ hj₂).1
      refine (hR _).trans ((hO p).symm.trans ?_)
      exact apm_t03J02_glue_eq j₁ j₂ _
    rw [this]

end Glued

theorem apm_t03j02
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂)
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (z₀ : Circle) :
    let X := apm_t03J02_space j₁ j₂
    let x₀ := apm_t03J02_basepoint j₁ j₂ z₀
    Nonempty (FundamentalGroup X x₀ ≃* apm_t03J02_freeProductZ2Z2) ∧
    Nonempty (apm_t03J02_H 0 X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t03J02_H 1 X ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
    Nonempty (apm_t03J02_H 2 X ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t03J02_H k X) := by
  obtain ⟨R₁⟩ := apm_t03J02_exists_retractile j₁ hj₁
  obtain ⟨R₂⟩ := apm_t03J02_exists_retractile j₂ hj₂
  obtain ⟨D⟩ := apm_t03J02_exists_deform hj₁ hj₂ R₁ R₂
  obtain ⟨e⟩ := apm_t03J02_homotopyEquiv_cyl D
  obtain ⟨hcover⟩ := apm_t03J02_cyl_cover hj₁ hj₂
  intro X x₀
  let y₀ : apm_t03J02_Cyl j₁ j₂ := e x₀
  obtain ⟨hπ⟩ := apm_t03J02_fundamentalGroup_of_compatibleOpenCover
    j₁ j₂ hnull₁ hnull₂ y₀ hcover
  obtain ⟨h0⟩ := apm_t03J02_H0_of_compatibleOpenCover j₁ j₂ hcover
  obtain ⟨h1⟩ := apm_t03J02_H1_of_compatibleOpenCover j₁ j₂ hnull₁ hnull₂ hcover
  obtain ⟨h2⟩ := apm_t03J02_H2_of_compatibleOpenCover j₁ j₂ hnull₁ hnull₂ hcover
  have hhi := apm_t03J02_Hhigh_of_compatibleOpenCover j₁ j₂ hcover
  have hH : ∀ k, apm_t03J02_H k X ≅ apm_t03J02_H k (apm_t03J02_Cyl j₁ j₂) := fun k =>
    ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv e k
  haveI : PathConnectedSpace Circle := pathConnectedSpace_iff_univ.mpr (by
    have hc : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
        |>.isPathConnected_preimage.mpr isPathConnected_univ
    simpa using hc)
  haveI : PathConnectedSpace apm_t03J02_Torus :=
    ⟨⟨(1, 1)⟩, fun x y =>
      ⟨Path.prod (PathConnectedSpace.somePath x.1 y.1)
        (PathConnectedSpace.somePath x.2 y.2)⟩⟩
  haveI : PathConnectedSpace hcover.leftSet :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected hcover.leftEquiv
  haveI : PathConnectedSpace hcover.rightSet :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_pathConnected hcover.rightEquiv
  haveI : PathConnectedSpace (apm_t03J02_Cyl j₁ j₂) :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_pathConnectedSpace
      hcover.leftSet hcover.rightSet hcover.cover (hcover.overlapEquiv.invFun 1)
  obtain ⟨eπ⟩ :=
    apm_t03J02_fundamentalGroup_of_compatibleOpenCover_aux_vanKampen_aux_trivialLegs_aux_hequiv
      e x₀ y₀
  exact ⟨⟨eπ.trans hπ⟩, ⟨(hH 0).trans h0⟩, ⟨(hH 1).trans h1⟩, ⟨(hH 2).trans h2⟩,
    fun k hk => (hhi k hk).of_iso (hH k)⟩

#print axioms apm_t03j02
