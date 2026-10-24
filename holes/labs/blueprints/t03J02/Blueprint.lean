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
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) where
  leftSet : Set (apm_t03J02_space j₁ j₂)
  rightSet : Set (apm_t03J02_space j₁ j₂)
  open_left : IsOpen leftSet
  open_right : IsOpen rightSet
  cover : leftSet ∪ rightSet = Set.univ
  leftEquiv : ContinuousMap.HomotopyEquiv leftSet apm_t03J02_Torus
  rightEquiv : ContinuousMap.HomotopyEquiv rightSet apm_t03J02_Torus
  overlapEquiv : ContinuousMap.HomotopyEquiv
    (leftSet ∩ rightSet : Set (apm_t03J02_space j₁ j₂)) Circle
  left_compat :
    (leftEquiv.toFun.comp (apm_t03J02_overlapToLeft leftSet rightSet)).Homotopic
      (j₁.comp overlapEquiv.toFun)
  right_compat :
    (rightEquiv.toFun.comp (apm_t03J02_overlapToRight leftSet rightSet)).Homotopic
      (j₂.comp overlapEquiv.toFun)

/-- LIBRARY: the common collar/open-cover comparison for the concrete quotient.
It packages exactly the shared geometric input needed by both invariant computations. -/
theorem apm_t03J02_compatibleOpenCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) :
    Nonempty (apm_t03J02_CompatibleOpenCover j₁ j₂) := by
  sorry

/-- LIBRARY: van Kampen plus the algebraic identification of the two trivial
attaching legs.  The open-cover conclusion is supplied as a hypothesis so this
program can run in parallel with the homology program after the geometry lands. -/
theorem apm_t03J02_fundamentalGroup_of_compatibleOpenCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic)
    (hnull₂ : j₂.Nullhomotopic)
    (z₀ : Circle)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂) :
    Nonempty
      (FundamentalGroup (apm_t03J02_space j₁ j₂)
        (apm_t03J02_basepoint j₁ j₂ z₀) ≃*
          apm_t03J02_freeProductZ2Z2) := by
  sorry

/-- Degree-zero Mayer--Vietoris calculation. -/
theorem apm_t03J02_H0_of_compatibleOpenCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂) :
    Nonempty (apm_t03J02_H 0 (apm_t03J02_space j₁ j₂) ≅ ModuleCat.of ℤ ℤ) := by
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
  let z₀ : Circle := Classical.choice inferInstance
  let ql := apm_t03J02_gluedInl j₁ j₂
  let qr := apm_t03J02_gluedInr j₁ j₂
  have joined_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) {x y : X} (h : Joined x y) : Joined (f x) (f y) := by
    exact ⟨h.somePath.map f.continuous⟩
  have hbridge : Joined (ql (j₁ z₀)) (qr (j₂ z₀)) := by
    rw [show ql (j₁ z₀) = qr (j₂ z₀) from apm_t03J02_glue_eq j₁ j₂ z₀]
  letI : PathConnectedSpace (apm_t03J02_space j₁ j₂) := {
    nonempty := ⟨ql (j₁ z₀)⟩
    joined := by
      intro x y
      refine Quotient.inductionOn x ?_
      intro sx
      refine Quotient.inductionOn y ?_
      intro sy
      cases sx with
      | inl x =>
          cases sy with
          | inl y =>
              exact joined_map ql (PathConnectedSpace.joined x y)
          | inr y =>
              exact (joined_map ql (PathConnectedSpace.joined x (j₁ z₀))).trans
                (hbridge.trans (joined_map qr (PathConnectedSpace.joined (j₂ z₀) y)))
      | inr x =>
          cases sy with
          | inl y =>
              exact (joined_map qr (PathConnectedSpace.joined x (j₂ z₀))).trans
                (hbridge.symm.trans
                  (joined_map ql (PathConnectedSpace.joined (j₁ z₀) y)))
          | inr y =>
              exact joined_map qr (PathConnectedSpace.joined x y)
    }
  exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℤ (ql (j₁ z₀))⟩

/-- Degree-one Mayer--Vietoris calculation; null-homotopy kills both legs. -/
theorem apm_t03J02_H1_of_compatibleOpenCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic) (hnull₂ : j₂.Nullhomotopic)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂) :
    Nonempty (apm_t03J02_H 1 (apm_t03J02_space j₁ j₂) ≅
      ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  sorry

/-- Degree-two Mayer--Vietoris calculation, including the kernel `ℤ`. -/
theorem apm_t03J02_H2_of_compatibleOpenCover
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hnull₁ : j₁.Nullhomotopic) (hnull₂ : j₂.Nullhomotopic)
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂) :
    Nonempty (apm_t03J02_H 2 (apm_t03J02_space j₁ j₂) ≅
      ModuleCat.of ℤ (Fin 3 → ℤ)) := by
  sorry

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
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (hcover : apm_t03J02_CompatibleOpenCover j₁ j₂) :
    ∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (apm_t03J02_H k (apm_t03J02_space j₁ j₂)) := by
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
  let hcover := Classical.choice (apm_t03J02_compatibleOpenCover j₁ j₂ hj₁ hj₂)
  have hπ := apm_t03J02_fundamentalGroup_of_compatibleOpenCover
    j₁ j₂ hnull₁ hnull₂ z₀ hcover
  have h0 := apm_t03J02_H0_of_compatibleOpenCover j₁ j₂ hcover
  have h1 := apm_t03J02_H1_of_compatibleOpenCover j₁ j₂ hnull₁ hnull₂ hcover
  have h2 := apm_t03J02_H2_of_compatibleOpenCover j₁ j₂ hnull₁ hnull₂ hcover
  have hhi := apm_t03J02_Hhigh_of_compatibleOpenCover j₁ j₂ hcover
  exact ⟨hπ, h0, h1, h2, hhi⟩

#print axioms apm_t03j02
