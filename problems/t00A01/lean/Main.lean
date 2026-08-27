import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.SphereHomology
import ConstructionTargets.MayerVietorisExactnessIsZero

/-!
# APM t00A01: Connected sums of integral homology 3-spheres

## Statement repairs

None.

## Encoding questions

Mathlib does not yet define triangulated manifolds or connected sums. We encode
the connected sum honestly as the quotient obtained by gluing two punctured
pieces along an actual topological `S²`. The presentation hypotheses expose
the standard geometric puncture facts used by van Kampen and Mayer--Vietoris:
each punctured piece is a homology ball and has the original fundamental group,
and the quotient has the standard two-piece cover with `S²` overlap.
The conclusion still concerns the genuine fundamental group and singular
homology of the quotient space, not scalar stand-ins.
-/

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

abbrev apm_t00A01_Sphere2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

inductive apm_t00A01_glueRel {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :
    Sum A B → Sum A B → Prop
  | glue (s : apm_t00A01_Sphere2) :
      apm_t00A01_glueRel iA iB (Sum.inl (iA s)) (Sum.inr (iB s))

def apm_t00A01_connectedSum {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :=
  Quotient (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB))

noncomputable instance {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :
    TopologicalSpace (apm_t00A01_connectedSum iA iB) :=
  TopologicalSpace.coinduced
    (fun z : Sum A B ↦ Quotient.mk
      (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) z) inferInstance

def apm_t00A01_basepoint {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (a : A) :
    apm_t00A01_connectedSum iA iB := Quotient.mk _ (Sum.inl a)

/-- The quotient construction really identifies the two boundary copies.
This records the geometric gluing fact independently of the unavailable
van Kampen and Mayer--Vietoris interfaces used by the main theorem. -/
lemma apm_t00A01_mk_inl_eq_mk_inr {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (s : apm_t00A01_Sphere2) :
    (Quotient.mk _ (Sum.inl (iA s)) : apm_t00A01_connectedSum iA iB) =
      Quotient.mk _ (Sum.inr (iB s)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (apm_t00A01_glueRel.glue s)

/-- The canonical map of the left punctured piece into the glued quotient. -/
def apm_t00A01_inl {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (a : A) :
    apm_t00A01_connectedSum iA iB :=
  Quotient.mk _ (Sum.inl a)

/-- The canonical map of the right punctured piece into the glued quotient. -/
def apm_t00A01_inr {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (b : B) :
    apm_t00A01_connectedSum iA iB :=
  Quotient.mk _ (Sum.inr b)

/-- The left canonical map is continuous for the coinduced quotient topology. -/
lemma apm_t00A01_continuous_inl {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :
    Continuous (apm_t00A01_inl iA iB) := by
  exact continuous_coinduced_rng.comp continuous_inl

/-- The right canonical map is continuous for the coinduced quotient topology. -/
lemma apm_t00A01_continuous_inr {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :
    Continuous (apm_t00A01_inr iA iB) := by
  exact continuous_coinduced_rng.comp continuous_inr

/-- The two continuous canonical maps agree after restriction to the glued
boundary sphere, i.e. they form the expected topological cocone. -/
lemma apm_t00A01_inl_comp_iA_eq_inr_comp_iB {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :
    apm_t00A01_inl iA iB ∘ iA = apm_t00A01_inr iA iB ∘ iB := by
  funext s
  exact apm_t00A01_mk_inl_eq_mk_inr iA iB s

/-- A compatible pair of maps from the two pieces descends to the glued
quotient. This is the set-level universal map underlying the pushout. -/
def apm_t00A01_glueLift {A B C : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (fA : A → C) (fB : B → C) (hcompat : fA ∘ iA = fB ∘ iB) :
    apm_t00A01_connectedSum iA iB → C :=
  Quotient.lift (Sum.elim fA fB) (by
    intro x y hxy
    induction hxy with
    | rel x y h =>
        cases h with
        | glue s => exact congrFun hcompat s
    | refl => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)

@[simp] lemma apm_t00A01_glueLift_inl {A B C : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (fA : A → C) (fB : B → C) (hcompat : fA ∘ iA = fB ∘ iB) (a : A) :
    apm_t00A01_glueLift iA iB fA fB hcompat (apm_t00A01_inl iA iB a) = fA a :=
  rfl

@[simp] lemma apm_t00A01_glueLift_inr {A B C : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (fA : A → C) (fB : B → C) (hcompat : fA ∘ iA = fB ∘ iB) (b : B) :
    apm_t00A01_glueLift iA iB fA fB hcompat (apm_t00A01_inr iA iB b) = fB b :=
  rfl

/-- The descended map is continuous whenever both piece maps are continuous. -/
lemma apm_t00A01_continuous_glueLift {A B C : Type}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (fA : A → C) (fB : B → C) (hcompat : fA ∘ iA = fB ∘ iB)
    (hfA : Continuous fA) (hfB : Continuous fB) :
    Continuous (apm_t00A01_glueLift iA iB fA fB hcompat) := by
  apply continuous_coinduced_dom.mpr
  simpa [apm_t00A01_glueLift] using hfA.sumElim hfB

/-- The descended map is the unique map having the prescribed restrictions to
the two canonical pieces. -/
lemma apm_t00A01_glueLift_unique {A B C : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (fA : A → C) (fB : B → C) (hcompat : fA ∘ iA = fB ∘ iB)
    (g : apm_t00A01_connectedSum iA iB → C)
    (hgA : g ∘ apm_t00A01_inl iA iB = fA)
    (hgB : g ∘ apm_t00A01_inr iA iB = fB) :
    g = apm_t00A01_glueLift iA iB fA fB hcompat := by
  funext q
  induction q using Quotient.inductionOn with
  | _ z =>
      cases z with
      | inl a => exact congrFun hgA a
      | inr b => exact congrFun hgB b

abbrev apm_t00A01_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t00A01_isHomologyBall (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (apm_t00A01_H 0 X ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, k ≠ 0 → Limits.IsZero (apm_t00A01_H k X)

def apm_t00A01_isHomology3Sphere (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (apm_t00A01_H 0 X ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t00A01_H 3 X ≅ ModuleCat.of ℤ ℤ) ∧
  (∀ k : ℕ, k ≠ 0 → k ≠ 3 → Limits.IsZero (apm_t00A01_H k X))

def apm_t00A01_hasStandardCover
    (X A B : Type) [TopologicalSpace X] [TopologicalSpace A]
    [TopologicalSpace B] : Prop :=
  ∃ U V : Set X,
    IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
    Nonempty (ContinuousMap.HomotopyEquiv ↥U A) ∧
    Nonempty (ContinuousMap.HomotopyEquiv ↥V B) ∧
    Nonempty (ContinuousMap.HomotopyEquiv ↥(U ∩ V) apm_t00A01_Sphere2)

/-- Why this unblocks `apm_t00a01`: this is the Seifert--van Kampen
comparison for the supplied standard cover, with the harmless
change-of-basepoint and the two given puncture-group identifications already
incorporated.  It supplies the first conjunct of the main theorem. -/
theorem apm_t00A01_bridge_fundamentalGroup_coprod
    (M₁ M₂ A B : Type)
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    [TopologicalSpace A] [TopologicalSpace B]
    (m₁ : M₁) (m₂ : M₂) (a : A) (b : B)
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (hπA : Nonempty (FundamentalGroup A a ≃* FundamentalGroup M₁ m₁))
    (hπB : Nonempty (FundamentalGroup B b ≃* FundamentalGroup M₂ m₂))
    (hconnA : PathConnectedSpace A) (hconnB : PathConnectedSpace B)
    (hiA : Continuous iA) (hiB : Continuous iB)
    (hcover : apm_t00A01_hasStandardCover
      (apm_t00A01_connectedSum iA iB) A B) :
    Nonempty
      (FundamentalGroup (apm_t00A01_connectedSum iA iB)
          (apm_t00A01_basepoint iA iB a) ≃*
        Monoid.Coprod (FundamentalGroup M₁ m₁) (FundamentalGroup M₂ m₂)) := by
  sorry

/-- Why this unblocks `apm_t00a01`: this is the singular-homology
Mayer--Vietoris calculation for two homology balls glued along the supplied
homotopy-sphere overlap.  It supplies the second conjunct of the main
theorem. -/
theorem apm_t00A01_bridge_connectedSum_isHomology3Sphere
    (A B : Type) [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (hA : apm_t00A01_isHomologyBall A)
    (hB : apm_t00A01_isHomologyBall B)
    (hcover : apm_t00A01_hasStandardCover
      (apm_t00A01_connectedSum iA iB) A B) :
    apm_t00A01_isHomology3Sphere (apm_t00A01_connectedSum iA iB) := by
  open ConstructionTargets.ProductionOpenCoverMayerVietoris in
   open ConstructionTargets.T00A01MayerVietorisAdapters in
   open ConstructionTargets.IntegralSingularHomologyComparison in
   open ConstructionTargets.SingularHomologyConcrete in
   open ConstructionTargets.SphereHomology in
   open ConstructionTargets.MayerVietorisExactnessIsZero in
   rcases hcover with ⟨U, V, hU, hV, hUV, ⟨eUA⟩, ⟨eVB⟩, ⟨eIS⟩⟩
   rcases hA with ⟨⟨eA0⟩, hAz⟩
   rcases hB with ⟨⟨eB0⟩, hBz⟩
   let X := apm_t00A01_connectedSum iA iB
   let groupIso (e : ContinuousMap.HomotopyEquiv U A) (k : ℕ) :=
     singularHomologyIsoOfHomotopyEquiv e k
   let eU0 : SingularHomology 0 (TopCat.of U) ≅ AddCommGrpCat.of ℤ :=
     groupIso eUA 0 ≪≫
       (singularHomologyComparison (TopCat.of A) 0).symm ≪≫
       forgetIntModules.mapIso eA0
   let eV0 : SingularHomology 0 (TopCat.of V) ≅ AddCommGrpCat.of ℤ :=
     singularHomologyIsoOfHomotopyEquiv eVB 0 ≪≫
       (singularHomologyComparison (TopCat.of B) 0).symm ≪≫
       forgetIntModules.mapIso eB0
   let eI0 : SingularHomology 0 (TopCat.of (U ∩ V : Set X)) ≅
       AddCommGrpCat.of ℤ :=
     singularHomologyIsoOfHomotopyEquiv eIS 0 ≪≫ sphereH0IsoInt 2 (by omega)
   let eI2 : SingularHomology 2 (TopCat.of (U ∩ V : Set X)) ≅
       AddCommGrpCat.of ℤ :=
     singularHomologyIsoOfHomotopyEquiv eIS 2 ≪≫
       sphereTopHomologyIsoInt 2 (by omega)
   let hUz (k : ℕ) (hk : k ≠ 0) : Limits.IsZero (SingularHomology k (TopCat.of U)) :=
     (groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of A) k (hAz k hk)).of_iso
       (singularHomologyIsoOfHomotopyEquiv eUA k)
   let hVz (k : ℕ) (hk : k ≠ 0) : Limits.IsZero (SingularHomology k (TopCat.of V)) :=
     (groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of B) k (hBz k hk)).of_iso
       (singularHomologyIsoOfHomotopyEquiv eVB k)
   let hIz (k : ℕ) (hk0 : k ≠ 0) (hk2 : k ≠ 2) :
       Limits.IsZero (SingularHomology k (TopCat.of (U ∩ V : Set X))) :=
     (sphereModuleHomology_isZero_of_ne_zero_top 2 k hk0 hk2 |> fun hm ↦
       groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of apm_t00A01_Sphere2) k hm).of_iso
       (singularHomologyIsoOfHomotopyEquiv eIS k)
   letI : Nonempty A :=
     ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eA0
   letI : Nonempty B :=
     ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eB0
   letI : Nonempty U := ⟨eUA.symm.toFun (Classical.choice inferInstance)⟩
   letI : Nonempty V := ⟨eVB.symm.toFun (Classical.choice inferInstance)⟩
   letI : Nonempty apm_t00A01_Sphere2 :=
     ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
   letI : Nonempty (U ∩ V : Set X) :=
     ⟨eIS.symm.toFun (Classical.choice inferInstance)⟩
   let eX0g := openCoverH0IsoOfCoordinates U V hU hV hUV eI0 eU0 eV0
   let eX0 := singularHomologyModuleIsoOfGroupIso (TopCat.of X) 0
     (ModuleCat.of ℤ ℤ) eX0g
   have hfg1 : productionReassemblyArrow U V 1 ≫
       productionConnecting U V hU hV hUV 0 = 0 := by
     rw [← booleanReassemblyArrow_eq_production U V hU hV hUV 1]
     simp only [productionConnecting]
     have hz := (ConstructionTargets.SingularExcision.subcomplexMayerVietorisShortComplex_shortExact
       (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
       (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V)).comp_δ 1 0 rfl
     have hcancel :
         HomologicalComplex.homologyMap
             (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).g 1 ≫
           (booleanUnionProductionHomologyIso U V hU hV hUV 1).hom ≫
           (booleanUnionProductionHomologyIso U V hU hV hUV 1).inv ≫
           ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
             (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
             (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0 =
         HomologicalComplex.homologyMap
             (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).g 1 ≫
           ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
             (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
             (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0 := by simp
     calc
       _ = (booleanPiecesProductionHomologyIso U V 1).inv ≫
           (HomologicalComplex.homologyMap
               (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).g 1 ≫
             (booleanUnionProductionHomologyIso U V hU hV hUV 1).hom ≫
             (booleanUnionProductionHomologyIso U V hU hV hUV 1).inv ≫
             ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
               (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
               (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0) ≫
           (booleanIntersectionProductionHomologyIso U V 0).hom := by
             simp only [Category.assoc]
       _ = (booleanPiecesProductionHomologyIso U V 1).inv ≫
           (HomologicalComplex.homologyMap
               (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).g 1 ≫
             ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
               (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
               (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0) ≫
           (booleanIntersectionProductionHomologyIso U V 0).hom :=
             congrArg (fun k ↦
               (booleanPiecesProductionHomologyIso U V 1).inv ≫ k ≫
                 (booleanIntersectionProductionHomologyIso U V 0).hom) hcancel
       _ = (booleanPiecesProductionHomologyIso U V 1).inv ≫ 0 ≫
           (booleanIntersectionProductionHomologyIso U V 0).hom :=
             congrArg (fun k ↦
               (booleanPiecesProductionHomologyIso U V 1).inv ≫ k ≫
                 (booleanIntersectionProductionHomologyIso U V 0).hom) hz
       _ = 0 := by simp
   have hgh0 : productionConnecting U V hU hV hUV 0 ≫
       productionIntersectionArrow U V 0 = 0 := by
     rw [← booleanIntersectionArrow_eq_production U V 0]
     simp only [productionConnecting]
     have hz := (ConstructionTargets.SingularExcision.subcomplexMayerVietorisShortComplex_shortExact
       (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
       (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V)).δ_comp 1 0 rfl
     have hcancel :
         ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
             (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
             (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0 ≫
           (booleanIntersectionProductionHomologyIso U V 0).hom ≫
           (booleanIntersectionProductionHomologyIso U V 0).inv ≫
           HomologicalComplex.homologyMap
             (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).f 0 =
         ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
             (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
             (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0 ≫
           HomologicalComplex.homologyMap
             (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).f 0 := by
       simpa only [Category.assoc] using congrArg
         (fun k ↦
           ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
               (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
               (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0 ≫ k)
         ((booleanIntersectionProductionHomologyIso U V 0).hom_inv_id_assoc
           (HomologicalComplex.homologyMap
             (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).f 0))
     calc
       _ = (booleanUnionProductionHomologyIso U V hU hV hUV 1).inv ≫
           (ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
               (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
               (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0 ≫
             (booleanIntersectionProductionHomologyIso U V 0).hom ≫
             (booleanIntersectionProductionHomologyIso U V 0).inv ≫
             HomologicalComplex.homologyMap
               (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).f 0) ≫
           (booleanPiecesProductionHomologyIso U V 0).hom := by
             simp only [Category.assoc]
       _ = (booleanUnionProductionHomologyIso U V hU hV hUV 1).inv ≫
           (ConstructionTargets.SingularExcision.subcomplexMayerVietorisConnecting
               (ConstructionTargets.BooleanTwoCoverScaffold.leftRange U)
               (ConstructionTargets.BooleanTwoCoverScaffold.rightRange V) 0 ≫
             HomologicalComplex.homologyMap
               (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex U V).f 0) ≫
           (booleanPiecesProductionHomologyIso U V 0).hom :=
             congrArg (fun k ↦
               (booleanUnionProductionHomologyIso U V hU hV hUV 1).inv ≫ k ≫
                 (booleanPiecesProductionHomologyIso U V 0).hom) hcancel
       _ = (booleanUnionProductionHomologyIso U V hU hV hUV 1).inv ≫ 0 ≫
           (booleanPiecesProductionHomologyIso U V 0).hom :=
             congrArg (fun k ↦
               (booleanUnionProductionHomologyIso U V hU hV hUV 1).inv ≫ k ≫
                 (booleanPiecesProductionHomologyIso U V 0).hom) hz
       _ = 0 := by simp
   have hX1g : Limits.IsZero (SingularHomology 1 (TopCat.of X)) := by
     letI : Mono (productionIntersectionArrow U V 0) :=
       productionIntersectionArrow_mono_zero_of_coordinates U V eI0 eU0
     exact isZero_middle_of_two_exact_of_isZero_left_of_mono_right
       (productionReassemblyArrow U V 1)
       (productionConnecting U V hU hV hUV 0)
       (productionIntersectionArrow U V 0) hfg1 hgh0
       (productionMayerVietoris_exact_union U V hU hV hUV 0)
       (productionMayerVietoris_exact_intersection U V hU hV hUV 0)
       ((Limits.biprod_isZero_iff _ _).mpr ⟨hUz 1 (by omega), hVz 1 (by omega)⟩)
   have hX2g : Limits.IsZero (SingularHomology 2 (TopCat.of X)) := by
     apply (productionMayerVietoris_exact_union U V hU hV hUV 1).isZero_X₂
     · exact (Limits.biprod_isZero_iff _ _).mpr
         ⟨hUz 2 (by omega), hVz 2 (by omega)⟩ |>.eq_of_src _ _
     · exact (hIz 1 (by omega) (by omega)).eq_of_tgt _ _
   let hconn : IsIso (productionConnecting U V hU hV hUV 2) :=
     productionConnecting_isIso_of_pieces_isZero U V hU hV hUV 2
       (hUz 3 (by omega)) (hVz 3 (by omega))
       (hUz 2 (by omega)) (hVz 2 (by omega))
   let eX3g : SingularHomology 3 (TopCat.of X) ≅ AddCommGrpCat.of ℤ :=
     @asIso _ _ _ _ (productionConnecting U V hU hV hUV 2) hconn ≪≫ eI2
   let eX3 := singularHomologyModuleIsoOfGroupIso (TopCat.of X) 3
     (ModuleCat.of ℤ ℤ) eX3g
   refine ⟨⟨eX0⟩, ⟨eX3⟩, ?_⟩
   intro k hk0 hk3
   apply singularHomologyModuleIsZeroOfGroupIsZero
   rcases k with _ | _ | _ | k
   · exact (hk0 rfl).elim
   · exact hX1g
   · exact hX2g
   · apply (productionMayerVietoris_exact_union U V hU hV hUV (k + 2)).isZero_X₂
     · exact (Limits.biprod_isZero_iff _ _).mpr
         ⟨hUz (k + 3) (by omega), hVz (k + 3) (by omega)⟩ |>.eq_of_src _ _
     · exact (hIz (k + 2) (by omega) (by omega)).eq_of_tgt _ _

theorem apm_t00a01
    (M₁ M₂ A B : Type)
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    [TopologicalSpace A] [TopologicalSpace B]
    (m₁ : M₁) (m₂ : M₂) (a : A) (b : B)
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (hM₁ : apm_t00A01_isHomology3Sphere M₁)
    (hM₂ : apm_t00A01_isHomology3Sphere M₂)
    (hA : apm_t00A01_isHomologyBall A)
    (hB : apm_t00A01_isHomologyBall B)
    (hπA : Nonempty (FundamentalGroup A a ≃* FundamentalGroup M₁ m₁))
    (hπB : Nonempty (FundamentalGroup B b ≃* FundamentalGroup M₂ m₂))
    (hconnA : PathConnectedSpace A) (hconnB : PathConnectedSpace B)
    (hiA : Continuous iA) (hiB : Continuous iB)
    (hcover : apm_t00A01_hasStandardCover
      (apm_t00A01_connectedSum iA iB) A B) :
    let X := apm_t00A01_connectedSum iA iB
    let x := apm_t00A01_basepoint iA iB a
    Nonempty
      (FundamentalGroup X x ≃*
        Monoid.Coprod (FundamentalGroup M₁ m₁) (FundamentalGroup M₂ m₂)) ∧
    apm_t00A01_isHomology3Sphere X := by
  /-
  Boundary (closer hop 2, still open): I searched Mathlib for a
  Seifert--van Kampen theorem
  computing `FundamentalGroup` of an open union and for the singular-homology
  Mayer--Vietoris long exact sequence. Neither API is present: the available
  `MayerVietoris` results concern sheaf cohomology, and the available
  `VanKampen` results concern categorical colimits rather than fundamental
  groups. Searches of all fully closed artifacts, `ConstructionTargets/`, and
  `YoungL2.lean` found no substitute; partial siblings `t01J03`, `t02A03`,
  `t97J04`, and `t97A01` record the same missing APIs. I additionally checked
  the categorical `VanKampen` files (they characterize colimit preservation),
  the sheaf-cohomology `MayerVietoris` files, `TopCat` colimit/extensivity
  results, the homotopy-invariance API for singular homology, repository git
  history, and the manual loop-subdivision work in `t94A04`. These do not
  provide the required pushout computation or exact sequence. The local lemma
  `apm_t00A01_mk_inl_eq_mk_inr` above verifies that the encoded quotient does
  identify the boundary copies. This hop packages the stronger reusable
  cocone data: `apm_t00A01_continuous_inl` and
  `apm_t00A01_continuous_inr` prove the two canonical piece maps continuous,
  while `apm_t00A01_inl_comp_iA_eq_inr_comp_iB` proves that their boundary
  restrictions agree as functions.  These point-set and continuity facts
  still cannot replace either theorem-level bridge. The hypotheses deliberately expose exactly the
  geometric inputs, but proving either requested conclusion would require
  developing those two missing algebraic-topology theorems.

  CLOSER HOP 3 goes beyond cocone compatibility and proves the full mapping
  universal property of the concrete quotient. `apm_t00A01_glueLift`
  descends every compatible pair of piece maps through `Relation.EqvGen`;
  its two simp lemmas compute both restrictions;
  `apm_t00A01_continuous_glueLift` proves the descended map continuous for
  continuous piece maps; and `apm_t00A01_glueLift_unique` proves uniqueness.
  Thus the quotient is now locally certified as the expected topological
  pushout at the level of continuous maps, not merely as a cocone.

  Renewed searches of Mathlib's `FundamentalGroupoid`, `TopCat` colimits, and
  singular-homology functor sources found no theorem carrying this pushout
  universal property to a fundamental-group coproduct or a homology long
  exact sequence. Consequently the remaining boundary is exclusively the
  invariant-preservation layer—Seifert--van Kampen and singular
  Mayer--Vietoris—and remains honestly open.
  -/
  sorry
