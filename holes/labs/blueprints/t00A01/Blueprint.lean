import ConstructionTargets.TwoOpenFreeProductMapping
import ConstructionTargets.SimplyConnectedSphereProducts
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

The summands are now closed second-countable Hausdorff smooth 3-manifolds, and the disk maps are topological embeddings.

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
open scoped ContDiff Manifold

noncomputable section

set_option maxHeartbeats 800000

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

@[reducible] noncomputable def apm_t00A01_connectedSumTopology
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :
    TopologicalSpace (apm_t00A01_connectedSum iA iB) :=
  TopologicalSpace.coinduced
    (fun z : Sum A B ↦ Quotient.mk
      (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) z) inferInstance

noncomputable instance {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) :
    TopologicalSpace (apm_t00A01_connectedSum iA iB) :=
  apm_t00A01_connectedSumTopology iA iB

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

abbrev apm_t00A01_Model3 := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

abbrev apm_t00A01_Disk3 :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- A larger ball furnishing the collar around the chosen unit ball. -/
abbrev apm_t00A01_LargeDisk3 :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2

/-- The canonical inclusion of the unit ball in the radius-two ball. -/
def apm_t00A01_unitToLarge : apm_t00A01_Disk3 → apm_t00A01_LargeDisk3 :=
  fun x ↦ ⟨x.1, le_trans x.2 (by norm_num : (1 : ℝ) ≤ 2)⟩

/-- A concrete tameness condition: the chosen ball extends across a collar,
and the interior of the larger ball is a genuine open neighbourhood. -/
def apm_t00A01_HasBallCollar {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) : Prop :=
  ∃ Φ : apm_t00A01_LargeDisk3 → M,
    Topology.IsEmbedding Φ ∧
    Φ ∘ apm_t00A01_unitToLarge = φ ∧
    IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})

/-- The complement of the open interior of an embedded closed three-disk. -/
abbrev apm_t00A01_punctured {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) : Type :=
  {x : M // x ∉ φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}}

/-- The boundary sphere maps canonically into the punctured manifold. -/
def apm_t00A01_boundaryMap {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Function.Injective φ) :
    apm_t00A01_Sphere2 → apm_t00A01_punctured φ := fun s ↦
  ⟨φ ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩, by
    rintro ⟨y, hy, heq⟩
    have hys : y.1 = s.1 := Subtype.ext_iff.mp (hφ heq)
    change dist y.1 0 < 1 at hy
    rw [hys] at hy
    have hs : dist s.1 0 = 1 := by simpa [Metric.mem_sphere, dist_comm] using s.2
    linarith⟩

def apm_t00A01_hasStandardCover
    (X A B : Type) [TopologicalSpace X] [TopologicalSpace A]
    [TopologicalSpace B] : Prop :=
  ∃ U V : Set X,
    IsOpen U ∧ IsOpen V ∧ U ∪ V = Set.univ ∧
    Nonempty (ContinuousMap.HomotopyEquiv ↥U A) ∧
    Nonempty (ContinuousMap.HomotopyEquiv ↥V B) ∧
    Nonempty (ContinuousMap.HomotopyEquiv ↥(U ∩ V) apm_t00A01_Sphere2)


private theorem apm_t00A01_pathConnected_of_hequiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : PathConnectedSpace X where
  nonempty := Nonempty.map e.invFun inferInstance
  joined x y := ⟨(e.left_inv.some.evalAt x).symm.trans
    (((PathConnectedSpace.somePath (e.toFun x) (e.toFun y)).map e.invFun.continuous).trans
      (e.left_inv.some.evalAt y))⟩

private def apm_t00A01_group_of_hequiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (y : Y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  ((FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath (e.toFun x) y))

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
  classical
  letI : PathConnectedSpace A := hconnA
  letI : PathConnectedSpace B := hconnB
  letI : SimplyConnectedSpace apm_t00A01_Sphere2 :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 2 (by omega)
  obtain ⟨U, V, hU, hV, hUV, ⟨eU⟩, ⟨eV⟩, ⟨eI⟩⟩ := hcover
  letI : PathConnectedSpace U := apm_t00A01_pathConnected_of_hequiv eU
  letI : PathConnectedSpace V := apm_t00A01_pathConnected_of_hequiv eV
  letI : SimplyConnectedSpace (U ∩ V : Set (apm_t00A01_connectedSum iA iB)) :=
    eI.simplyConnectedSpace
  let w : (U ∩ V : Set (apm_t00A01_connectedSum iA iB)) := Classical.choice inferInstance
  letI : PathConnectedSpace (apm_t00A01_connectedSum iA iB) := by
    rw [pathConnectedSpace_iff_univ, ← hUV]
    exact (isPathConnected_iff_pathConnectedSpace.mpr inferInstance).union
      (isPathConnected_iff_pathConnectedSpace.mpr inferInstance) ⟨w.val, w.property⟩
  obtain ⟨eA⟩ := hπA
  obtain ⟨eB⟩ := hπB
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath (apm_t00A01_basepoint iA iB a) w.val)).trans
    ((ConstructionTargets.TwoOpenFreeProductMapping.groupEquivalence hU hV hUV w).trans
      (MulEquiv.coprodCongr
        ((apm_t00A01_group_of_hequiv eU ⟨w.val,w.property.1⟩ a).trans eA)
        ((apm_t00A01_group_of_hequiv eV ⟨w.val,w.property.2⟩ b).trans eB)))⟩

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

/-- Superseded: the punctured-piece homology, fundamental groups, and
Mayer--Vietoris cover were hypotheses, so the homology-sphere premises did no work. -/
theorem apm_t00a01_previous_encoding
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
  exact ⟨apm_t00A01_bridge_fundamentalGroup_coprod M₁ M₂ A B m₁ m₂ a b
    iA iB hπA hπB hconnA hconnB hiA hiB hcover,
    apm_t00A01_bridge_connectedSum_isHomology3Sphere A B iA iB hA hB hcover⟩



set_option maxHeartbeats 800000

/-!
The blueprint is already closed because the original problem allows the embedded balls to be chosen as simplices of
the triangulations.  Since triangulated manifolds and simplex embeddings are
not represented in Mathlib, the repair exposes exactly the three standard
puncture consequences used by the informal proof for each piece, together
with the standard two-piece cover of the quotient.
-/

/-- LEAF: a closed homology three-sphere is path connected. `H₀ M ≅ ℤ`
leaves room for one path component only, and the path components of a
manifold are open because a manifold is locally path connected. -/
lemma apm_t00A01_punctured_pathConnected_aux_ambient
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) : PathConnectedSpace M := by
  classical
  letI : LocPathConnectedSpace M :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let eMmod := hM.1.some
  haveI : Nonempty M :=
    ConstructionTargets.SingularH0Augmentation.nonempty_of_module_singularH0_iso_int eMmod
  let eM : ConstructionTargets.SingularHomologyConcrete.SingularHomology 0
      (TopCat.of M) ≅ AddCommGrpCat.of ℤ :=
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of M) 0).symm ≪≫
        ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso eMmod
  letI : IsIso
      (ConstructionTargets.SingularH0Augmentation.h0Augmentation (X := M)) :=
    ConstructionTargets.SingularH0Augmentation.h0Augmentation_isIso_of_iso_int eM
  let p : M := Classical.choice inferInstance
  refine ⟨inferInstance, fun x y ↦ ?_⟩
  suffices h : ∀ z : M, Joined p z by exact (h x).symm.trans (h y)
  intro z
  by_contra hz
  let A : Set M := pathComponent p
  have hA : IsClopen A := IsClopen.pathComponent p
  let f : M → Bool := fun w ↦ decide (w ∈ A)
  have hf : Continuous f := by
    rw [continuous_bool_rng true]
    convert hA using 1
    ext w
    simp [f]
  let F : C(M, Bool) := ⟨f, hf⟩
  have hp : f p = true := by simp [f, A, mem_pathComponent_self]
  have hz' : f z = false := by
    simp only [f, decide_eq_false_iff_not]
    simpa [A, mem_pathComponent_iff] using hz
  let vp := ConstructionTargets.T02A06SphereH0.singularVertexH0Class p
  let vz := ConstructionTargets.T02A06SphereH0.singularVertexH0Class z
  have hv : vp = vz := by
    apply (cancel_mono
      (ConstructionTargets.SingularH0Augmentation.h0Augmentation (X := M))).1
    simpa [vp, vz] using
      (ConstructionTargets.SingularH0Augmentation.singularVertexH0Class_comp_h0Augmentation p).trans
        (ConstructionTargets.SingularH0Augmentation.singularVertexH0Class_comp_h0Augmentation z).symm
  have hbool :
      ConstructionTargets.T02A06SphereH0.singularVertexH0Class false =
        ConstructionTargets.T02A06SphereH0.singularVertexH0Class true := by
    have hnz := ConstructionTargets.T02A06SphereH0.singularVertexH0Class_naturality F z
    have hnp := ConstructionTargets.T02A06SphereH0.singularVertexH0Class_naturality F p
    rw [show F z = false by exact hz'] at hnz
    rw [show F p = true by exact hp] at hnp
    exact hnz.symm.trans ((congrArg (fun k ↦ k ≫ HomologicalComplex.homologyMap
      (ConstructionTargets.SingularSubdivision.singularPostcomposition F) 0) hv.symm).trans hnp)
  have hι :
      Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) false =
        Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) true := by
    let q := ConstructionTargets.T02A06SphereH0.singularVertexH0Class (X := Unit) ()
    haveI : Epi q := ConstructionTargets.T02A06SphereH0.singularVertexH0Class_epi ()
    let iFalse : C(Unit, Bool) := ⟨fun _ ↦ false, continuous_const⟩
    let iTrue : C(Unit, Bool) := ⟨fun _ ↦ true, continuous_const⟩
    have hm :
        HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              iFalse) 0 =
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              iTrue) 0 := by
      apply (cancel_epi q).1
      calc
        q ≫ _ = ConstructionTargets.T02A06SphereH0.singularVertexH0Class false := by
          simpa [q] using
            (ConstructionTargets.T02A06SphereH0.singularVertexH0Class_naturality
              iFalse ())
        _ = ConstructionTargets.T02A06SphereH0.singularVertexH0Class true := hbool
        _ = q ≫ _ := by
          simpa [q] using
            (ConstructionTargets.T02A06SphereH0.singularVertexH0Class_naturality
              iTrue ()).symm
    have hdFalse :=
      ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_pointInclusion
        AddCommGrpCat (AddCommGrpCat.of ℤ) false
    have hdTrue :=
      ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso_pointInclusion
        AddCommGrpCat (AddCommGrpCat.of ℤ) true
    apply (cancel_mono
      (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
        AddCommGrpCat (AddCommGrpCat.of ℤ) Bool).inv).1
    change Limits.Sigma.ι (fun _ : Bool ↦ AddCommGrpCat.of ℤ) false ≫ _ = _
    rw [← hdFalse, ← hdTrue]
    have hm' := congrArg (fun k ↦
      (Limits.Sigma.ι (fun _ : Unit ↦ AddCommGrpCat.of ℤ) () ≫
        (ConstructionTargets.SingularHomologyConcrete.directDiscreteH0Iso
          AddCommGrpCat (AddCommGrpCat.of ℤ) Unit).inv) ≫ k) hm
    simpa [iFalse, iTrue,
      ConstructionTargets.SingularHomologyConcrete.pointInclusion,
      ConstructionTargets.SingularSubdivision.singularPostcomposition,
      Category.assoc] using hm'
  let d : (∐ fun _ : Bool ↦ AddCommGrpCat.of ℤ) ⟶ AddCommGrpCat.of ℤ :=
    Limits.Sigma.desc (fun b ↦ if b then 0 else 𝟙 _)
  have hid : (𝟙 (AddCommGrpCat.of ℤ)) = 0 := by
    have hd := congrArg (fun g ↦ g ≫ d) hι
    simpa only [d, Limits.Sigma.ι_desc, Bool.false_eq_true, if_false, if_true] using hd
  have hone : (1 : ℤ) = 0 := by
    exact ConcreteCategory.congr_hom hid 1
  exact one_ne_zero hone

/-- LEAF: the collar makes the image of the open unit ball open in `M`. -/
lemma apm_t00A01_punctured_pathConnected_aux_inner_open
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (hcollar : apm_t00A01_HasBallCollar φ) :
    IsOpen (φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}) := by
  rcases hcollar with ⟨Φ, hΦ, hΦφ, hΦo⟩
  let S₁ : Set apm_t00A01_LargeDisk3 := {x | dist x.1 0 < 1}
  let S₂ : Set apm_t00A01_LargeDisk3 := {x | dist x.1 0 < 2}
  have hS₁ : IsOpen S₁ := by
    have hd : Continuous (fun x : apm_t00A01_LargeDisk3 ↦ dist x.1 0) :=
      continuous_subtype_val.dist
        (continuous_const : Continuous (fun _ : apm_t00A01_LargeDisk3 ↦
          (0 : EuclideanSpace ℝ (Fin 3))))
    exact isOpen_lt hd continuous_const
  obtain ⟨W, hW, hWpre⟩ := hΦ.isInducing.isOpen_iff.mp hS₁
  have himage : Φ '' S₁ = W ∩ Φ '' S₂ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxW : Φ x ∈ W := by
        have : x ∈ Φ ⁻¹' W := hWpre.symm ▸ hx
        exact this
      exact ⟨hxW, x, by dsimp [S₁, S₂] at hx ⊢; linarith, rfl⟩
    · rintro ⟨hzW, x, hx₂, rfl⟩
      refine ⟨x, ?_, rfl⟩
      have : x ∈ Φ ⁻¹' W := hzW
      exact hWpre ▸ this
  have hinner :
      φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1} = Φ '' S₁ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨apm_t00A01_unitToLarge y, ?_, ?_⟩
      · exact hy
      · exact congrFun hΦφ y
    · rintro ⟨x, hx, rfl⟩
      have hx' : dist x.1 0 < 1 := by exact hx
      let y : apm_t00A01_Disk3 :=
        ⟨x.1, by
          rw [Metric.mem_closedBall]
          exact le_of_lt hx'⟩
      refine ⟨y, hx', ?_⟩
      have heq : apm_t00A01_unitToLarge y = x := Subtype.ext rfl
      rw [← heq]
      exact (congrFun hΦφ y).symm
  rw [hinner, himage]
  exact hW.inter hΦo

/-- LEAF: first entrance into a closed set. In a path-connected space, a point
outside an open set `O` contained in a nonempty closed set `K` is joined,
without entering `O`, to a point of `K \ O`. -/
lemma apm_t00A01_punctured_pathConnected_aux_first_entry
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    {O K : Set X} (hO : IsOpen O) (hK : IsClosed K) (hOK : O ⊆ K)
    {x k : X} (hx : x ∉ O) (hk : k ∈ K) :
    ∃ z ∈ K \ O, JoinedIn Oᶜ x z := by
  classical
  by_cases hxK : x ∈ K
  · exact ⟨x, ⟨hxK, hx⟩, JoinedIn.refl hx⟩
  let γ : Path x k := PathConnectedSpace.somePath x k
  let S : Set ℝ := {t | t ∈ Set.Icc 0 1 ∧ γ.extend t ∈ K}
  have hS_closed : IsClosed S := by
    exact isClosed_Icc.inter (hK.preimage γ.continuous_extend)
  have hS_ne : S.Nonempty := by
    refine ⟨1, ⟨Set.right_mem_Icc.2 zero_le_one, ?_⟩⟩
    simpa [γ] using hk
  have hS_bdd : BddBelow S := ⟨0, fun _ ht ↦ ht.1.1⟩
  let t₀ : ℝ := sInf S
  have ht₀S : t₀ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht₀_nonneg : 0 ≤ t₀ := ht₀S.1.1
  have ht₀_le_one : t₀ ≤ 1 := ht₀S.1.2
  have ht₀_pos : 0 < t₀ := by
    refine lt_of_le_of_ne ht₀_nonneg (Ne.symm ?_)
    intro ht
    apply hxK
    have : γ.extend 0 ∈ K := by simpa [ht] using ht₀S.2
    simpa [γ] using this
  have hleast : ∀ s ∈ S, t₀ ≤ s := (isGLB_csInf hS_ne hS_bdd).1
  have ht₀_notO : γ.extend t₀ ∉ O := by
    intro htO
    have hopen : IsOpen (γ.extend ⁻¹' O) := hO.preimage γ.continuous_extend
    rcases Metric.isOpen_iff.1 hopen t₀ htO with ⟨ε, hε, hball⟩
    let s := t₀ - min (t₀ / 2) (ε / 2)
    have hmin_pos : 0 < min (t₀ / 2) (ε / 2) :=
      lt_min (half_pos ht₀_pos) (half_pos hε)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      have : min (t₀ / 2) (ε / 2) ≤ t₀ / 2 := min_le_left _ _
      linarith
    have hslt : s < t₀ := by simp [s, hmin_pos]
    have hs1 : s ≤ 1 := hslt.le.trans ht₀_le_one
    have hsO : γ.extend s ∈ O := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [s]
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (le_of_lt hmin_pos)]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
    exact (not_lt_of_ge (hleast s ⟨⟨hs0, hs1⟩, hOK hsO⟩)) hslt
  refine ⟨γ.extend t₀, ⟨ht₀S.2, ht₀_notO⟩, ?_⟩
  refine ⟨(γ.truncateOfLE ht₀_nonneg).cast (by simp [γ]) rfl, ?_⟩
  intro u
  change γ.extend (min (max (u : ℝ) 0) t₀) ∈ Oᶜ
  intro huO
  let s := min (max (u : ℝ) 0) t₀
  have hs0 : 0 ≤ s := by simp [s, ht₀_nonneg]
  have hst : s ≤ t₀ := min_le_right _ _
  have hs1 : s ≤ 1 := hst.trans ht₀_le_one
  by_cases hst' : s = t₀
  · exact ht₀_notO (by simpa [s, hst'] using huO)
  · have hslt : s < t₀ := lt_of_le_of_ne hst hst'
    exact (not_lt_of_ge (hleast s ⟨⟨hs0, hs1⟩, hOK (by simpa [s] using huO)⟩)) hslt

/-- LIBRARY: deleting the interior of a collared ball from a connected
homology three-manifold leaves a path-connected space. -/
theorem apm_t00A01_punctured_pathConnected
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    PathConnectedSpace (apm_t00A01_punctured φ) := by
  classical
  let O : Set M := φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}
  have hO : IsOpen O := apm_t00A01_punctured_pathConnected_aux_inner_open φ hcollar
  have hK : IsClosed (Set.range φ) := (isCompact_range hφ.continuous).isClosed
  have hOK : O ⊆ Set.range φ := Set.image_subset_range _ _
  haveI := apm_t00A01_punctured_pathConnected_aux_ambient M hM
  let b : apm_t00A01_Sphere2 → M := fun s ↦ (apm_t00A01_boundaryMap φ hφ.injective s).1
  have hb : Continuous b :=
    hφ.continuous.comp (Continuous.subtype_mk (continuous_subtype_val) _)
  haveI : PathConnectedSpace apm_t00A01_Sphere2 :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by
        rw [← Module.finrank_eq_rank']
        simp) 0 (by norm_num))
  have hS : IsPathConnected (Set.range b) := isPathConnected_range hb
  have hSO : Set.range b ⊆ Oᶜ := by
    rintro _ ⟨s, rfl⟩
    exact (apm_t00A01_boundaryMap φ hφ.injective s).2
  have hKO : Set.range φ \ O ⊆ Set.range b := by
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    have hy1 : ¬ dist y.1 0 < 1 := fun h ↦ hy ⟨y, h, rfl⟩
    have hy2 : dist y.1 0 ≤ 1 := y.2
    have hs : y.1 ∈ apm_t00A01_Sphere2 := by
      simpa [Metric.mem_sphere] using le_antisymm hy2 (not_lt.mp hy1)
    exact ⟨⟨y.1, hs⟩, rfl⟩
  have hP : IsPathConnected Oᶜ := by
    obtain ⟨s0, hs0⟩ := hS.nonempty
    refine ⟨s0, hSO hs0, fun {x} hx ↦ ?_⟩
    obtain ⟨z, hz, hxz⟩ :=
      apm_t00A01_punctured_pathConnected_aux_first_entry hO hK hOK hx
        (Set.mem_range_self (f := φ) ⟨0, by simp⟩)
    exact (hxz.trans ((hS.joinedIn _ (hKO hz) _ hs0).mono hSO)).symm
  exact isPathConnected_iff_pathConnectedSpace.mp hP

/-- LIBRARY: van Kampen for a manifold split into the punctured part and the
open radius-two collar ball. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_of_hequiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (e : ContinuousMap.HomotopyEquiv X Y)
    (p : Path (e.toFun x) y) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y y) := by
  exact ⟨((FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p)⟩

/-- The closed radius-one-half ball inside the collar. -/
def apm_t00A01_punctured_fundamentalGroup_aux_inner {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) : Set M :=
  Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ 1 / 2}

/-- The open radius-two collar ball. -/
def apm_t00A01_punctured_fundamentalGroup_aux_ball {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) : Set M :=
  Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2}

lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ) :
    φ '' {x : apm_t00A01_Disk3 | dist x.1 0 < 1} =
      Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 1} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨apm_t00A01_unitToLarge x, ?_, ?_⟩
    · exact hx
    · exact congrFun hΦφ x
  · rintro ⟨x, hx, rfl⟩
    have hxclosed : dist x.1 0 ≤ 1 := le_of_lt hx
    let y : apm_t00A01_Disk3 :=
      ⟨x.1, by simpa [Metric.mem_closedBall, dist_comm] using hxclosed⟩
    refine ⟨y, ?_, ?_⟩
    · exact hx
    · have hu : apm_t00A01_unitToLarge y = x := Subtype.ext rfl
      simpa [Function.comp_apply, hu] using (congrFun hΦφ y).symm

lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_inner_subset
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ) :
    apm_t00A01_punctured_fundamentalGroup_aux_inner Φ ⊆
      φ '' {x : apm_t00A01_Disk3 | dist x.1 0 < 1} := by
  rw [apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image
    φ Φ hΦφ]
  rintro z ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  change dist x.1 0 ≤ 1 / 2 at hx
  show dist x.1 0 < 1
  exact lt_of_le_of_lt hx (by norm_num)

def apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_inclusion
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ) :
    apm_t00A01_punctured φ →
      ↥(apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ :=
  fun x ↦ ⟨x.1, fun hx ↦ x.2
    (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_inner_subset
      φ Φ hΦφ hx)⟩

lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_inclusion_continuous
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ) :
    Continuous
      (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_inclusion
        φ Φ hΦφ) := by
  exact Continuous.subtype_mk continuous_subtype_val _

/-- The radial collar homotopy on `M`: a point `Φ x` with `‖x‖ < 1` moves along
the segment from `x` to `x / ‖x‖`; every other point stays put. At `t = 1` it is
the radial retraction of `M \ Φ(closedBall 0 (1/2))` onto the punctured manifold. -/
noncomputable def apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
    {M : Type} (Φ : apm_t00A01_LargeDisk3 → M) (t : unitInterval) (z : M) : M := by
  classical
  exact if h : ∃ x : apm_t00A01_LargeDisk3, Φ x = z ∧ dist x.1 0 < 1 then
    (if hv : (1 - (t : ℝ)) • h.choose.1 + (t : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 then
      Φ ⟨_, hv⟩ else z)
  else z

/-- LEAF: the collar homotopy is continuous on `I × U`, where
`U = M \ Φ(closedBall 0 (1/2))`. Glue two pieces. On the open set
`Φ(ball 0 2) ∩ U` it is `Φ ∘ G ∘ Φ⁻¹` (transport through the embedding `Φ`),
where `G t x` is `(1-t)•x + t•(x/‖x‖)` for `‖x‖ < 1` and `x` for `‖x‖ ≥ 1`;
`G` is continuous on `1/2 < ‖x‖ < 2` because the two formulas agree at
`‖x‖ = 1`. On the closed set `M \ Φ(ball 0 1)` (closed because `Φ(ball 0 1)`
is open: `Φ` restricted to the open set `Φ(ball 0 2)` is an open embedding) it
is the identity. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_open
    {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 1}) := by
  let s : Set apm_t00A01_LargeDisk3 := {x | dist x.1 0 < 1}
  let u : Set apm_t00A01_LargeDisk3 := {x | dist x.1 0 < 2}
  have hs : IsOpen s := by
    have hd : Continuous (fun x : apm_t00A01_LargeDisk3 => dist x.1 0) :=
      continuous_subtype_val.dist (continuous_const : Continuous (fun _ : apm_t00A01_LargeDisk3 =>
        (0 : EuclideanSpace ℝ (Fin 3))))
    exact isOpen_lt hd continuous_const
  obtain ⟨v, hv, hvpre⟩ := hΦ.isInducing.isOpen_iff.mp hs
  have hsu : s ⊆ u := by
    intro x hx
    change dist x.1 0 < 1 at hx
    change dist x.1 0 < 2
    linarith
  have himage : Φ '' s = v ∩ Φ '' u := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hvx : Φ x ∈ v := by
        have : x ∈ Φ ⁻¹' v := by simpa [hvpre] using hx
        exact this
      exact ⟨hvx, ⟨x, hsu hx, rfl⟩⟩
    · rintro ⟨hzv, x, hxu, rfl⟩
      refine ⟨x, ?_, rfl⟩
      have : x ∈ Φ ⁻¹' v := hzv
      simpa [hvpre] using this
  rw [himage]
  exact hv.inter hΦo

/-- `Φ` of a closed sub-ball `{‖x‖ ≤ r}` is closed in `M`: the sub-ball is
compact, and `M` is Hausdorff. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_closed
    {M : Type} [TopologicalSpace M] [T2Space M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Continuous Φ) (r : ℝ) :
    IsClosed (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ r}) := by
  haveI : CompactSpace apm_t00A01_LargeDisk3 :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : IsClosed {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ r} :=
    isClosed_le (continuous_subtype_val.dist continuous_const) continuous_const
  exact (hc.isCompact.image hΦ).isClosed

/-- Off `Φ(ball 0 1)` the collar homotopy is the identity. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_eq_self
    {M : Type} (Φ : apm_t00A01_LargeDisk3 → M) (t : unitInterval) (z : M)
    (hz : z ∉ Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 1}) :
    apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ t z = z := by
  unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
  rw [dif_neg]
  rintro ⟨x, hx, hx1⟩
  exact hz ⟨x, hx1, hx⟩

/-- LEAF: the radial deformation of Euclidean space, `x ↦ (1-t)•x + t•(x/‖x‖)`
for `‖x‖ < 1` and `x ↦ x` otherwise, is jointly continuous away from the
radius-one-half ball. Use `ContinuousOn.if`: each formula is continuous on
`‖x‖ > 1/2` (the first because `‖x‖ ≠ 0`), and on the frontier `‖x‖ = 1` of
`{‖x‖ < 1}` the two formulas agree. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_radial :
    ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦
        if ‖p.2‖ < 1 then (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2) else p.2)
      (univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 1 / 2 < ‖x‖}) := by
  let s : Set (unitInterval × EuclideanSpace ℝ (Fin 3)) :=
    univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 1 / 2 < ‖x‖}
  let f : unitInterval × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun p ↦ (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2)
  let g : unitInterval × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun p ↦ p.2
  have ht : Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ p.2) :=
    continuous_snd
  have hn : Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖) :=
    continuous_norm.comp hx
  have hne : ∀ p ∈ s, ‖p.2‖ ≠ 0 := by
    intro p hp
    have hp' : 1 / 2 < ‖p.2‖ := hp.2
    positivity
  have hinv : ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖⁻¹) s :=
    hn.continuousOn.inv₀ hne
  have hf : ContinuousOn f s := by
    exact ((continuous_const.sub ht).continuousOn.smul hx.continuousOn).add
      (ht.continuousOn.smul (hinv.smul hx.continuousOn))
  have hg : ContinuousOn g s := hx.continuousOn
  have hboundary : ∀ p ∈ s ∩ frontier
      {p : unitInterval × EuclideanSpace ℝ (Fin 3) | ‖p.2‖ < 1}, f p = g p := by
    intro p hp
    have heq : ‖p.2‖ = 1 :=
      (frontier_lt_subset_eq hn continuous_const) hp.2
    simp only [f, g, heq, inv_one, one_smul]
    rw [← add_smul, sub_add_cancel, one_smul]
  exact ContinuousOn.if hboundary
    (hf.mono inter_subset_left) (hg.mono inter_subset_left)

/-- LEAF: the collar homotopy is continuous on `I × (Φ(ball 0 2) \ Φ(closedBall 0 (1/2)))`.
There `Φ` restricted to `{‖x‖ < 2}` is a homeomorphism onto the open set
`Φ(ball 0 2)` (`hΦ` is an embedding), and for `z = Φ x` the homotopy is
`Φ (G t x)` with `G` the radial map of
`apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_radial`
(the `closedBall 0 2` test in the definition always holds: for `‖x‖ < 1` the
moving point has norm `(1-t)‖x‖ + t ≤ 1`). Transport the continuity of `G`
through the homeomorphism. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball_aux_radial :
    ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦
        if ‖p.2‖ < 1 then (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2) else p.2)
      (univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 1 / 2 < ‖x‖}) := by
  let s : Set (unitInterval × EuclideanSpace ℝ (Fin 3)) :=
    univ ×ˢ {x | 1 / 2 < ‖x‖}
  let P : unitInterval × EuclideanSpace ℝ (Fin 3) → Prop := fun p ↦ ‖p.2‖ < 1
  apply ContinuousOn.if (p := P)
  · intro p hp
    have hpcl : p ∈ closure {q | P q} := frontier_subset_closure hp.2
    have hnle : ¬ ‖p.2‖ < 1 := by
      have hc : p ∈ closure {q | ¬ P q} := by
        apply frontier_subset_closure
        have : p ∈ frontier ({q | P q}ᶜ) := by simpa only [frontier_compl] using hp.2
        simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using this
      have hsub : closure {q | ¬ P q} ⊆ {q | 1 ≤ ‖q.2‖} :=
        closure_minimal (by intro q hq; exact le_of_not_gt hq)
          (isClosed_le continuous_const (continuous_norm.comp continuous_snd))
      exact not_lt_of_ge (hsub hc)
    have hle : ‖p.2‖ ≤ 1 := by
      simpa [P] using (show p ∈ {q | ‖q.2‖ ≤ 1} from
        closure_minimal (by intro q hq; change ‖q.2‖ < 1 at hq; exact le_of_lt hq)
          (isClosed_le (continuous_norm.comp continuous_snd) continuous_const) hpcl)
    have heq : ‖p.2‖ = 1 := le_antisymm hle (le_of_not_gt hnle)
    rw [heq, inv_one, one_smul, ← add_smul]
    norm_num
  · have hnorm : ContinuousOn (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖⁻¹)
        (s ∩ closure {q | P q}) := by
      apply (continuous_norm.comp continuous_snd).continuousOn.inv₀
      intro p hp hzero
      have hp' : 1 / 2 < ‖p.2‖ := by simpa [s] using hp.1.2
      have : (0 : ℝ) < ‖p.2‖ := lt_of_lt_of_le (by norm_num) (le_of_lt hp')
      exact (ne_of_gt this) hzero
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      continuous_snd).continuousOn.add
        ((continuous_subtype_val.comp continuous_fst).continuousOn.smul
          (hnorm.smul continuous_snd.continuousOn)))
  · exact continuous_snd.continuousOn

lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball
    {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    ContinuousOn
      (fun p : unitInterval × M ↦
        apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2)
      (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2} ∩
        (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ)) := by
  let S : Set (unitInterval × M) := univ ×ˢ
    (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2} ∩
      (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ)
  let inv : S → apm_t00A01_LargeDisk3 := fun p ↦
    hΦ.toHomeomorph.symm ⟨p.1.2, by
      rcases p.2.2.1 with ⟨x, hx, hxp⟩
      exact ⟨x, hxp⟩⟩
  have hinv : Continuous inv := by
    let rangeMap : S → Set.range Φ := fun p ↦ ⟨p.1.2, by
      rcases p.2.2.1 with ⟨x, hx, hxp⟩
      exact ⟨x, hxp⟩⟩
    have hrange : Continuous rangeMap :=
      Continuous.subtype_mk ((continuous_snd : Continuous (fun p : unitInterval × M ↦ p.2)).comp
        continuous_subtype_val) _
    exact hΦ.toHomeomorph.symm.continuous.comp hrange
  have hinv_eq (p : S) : Φ (inv p) = p.1.2 := by
    exact congrArg Subtype.val (hΦ.toHomeomorph.apply_symm_apply _)
  have hinv_lt (p : S) : dist (inv p).1 0 < 2 := by
    rcases p.2.2.1 with ⟨x, hx, hxp⟩
    have : inv p = x := hΦ.injective (by rw [hinv_eq p, hxp])
    simpa [this] using hx
  have hinv_half (p : S) : 1 / 2 < ‖(inv p).1‖ := by
    by_contra hn
    apply p.2.2.2
    refine ⟨inv p, ?_, hinv_eq p⟩
    change dist (inv p).1 0 ≤ 1 / 2
    simpa [dist_eq_norm] using le_of_not_gt hn
  let Q : S → unitInterval × EuclideanSpace ℝ (Fin 3) := fun p ↦ (p.1.1, (inv p).1)
  have hQ : Continuous Q := by
    dsimp [Q]
    fun_prop
  have hmaps : MapsTo Q univ (univ ×ˢ {x | 1 / 2 < ‖x‖}) := by
    intro p hp
    exact ⟨trivial, hinv_half p⟩
  have hrad : Continuous (fun p : S ↦
      if ‖(Q p).2‖ < 1 then (1 - ((Q p).1 : ℝ)) • (Q p).2 +
        ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2) else (Q p).2) := by
    rw [← continuousOn_univ]
    exact apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball_aux_radial.comp
      hQ.continuousOn hmaps
  let R : S → apm_t00A01_LargeDisk3 := fun p ↦ ⟨
    if ‖(Q p).2‖ < 1 then (1 - ((Q p).1 : ℝ)) • (Q p).2 +
      ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2) else (Q p).2, by
    change dist _ 0 ≤ 2
    rw [dist_zero_right]
    by_cases hlt : ‖(Q p).2‖ < 1
    · rw [if_pos hlt]
      have hnpos : 0 < ‖(Q p).2‖ := by
        have := hinv_half p
        simpa [Q] using lt_trans (by norm_num : (0 : ℝ) < 1 / 2) this
      have hn : ‖(Q p).2‖ ≠ 0 := ne_of_gt hnpos
      have ht0 : 0 ≤ ((Q p).1 : ℝ) := (Q p).1.2.1
      have ht1 : ((Q p).1 : ℝ) ≤ 1 := (Q p).1.2.2
      calc
        ‖(1 - ((Q p).1 : ℝ)) • (Q p).2 +
            ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2)‖ ≤
            ‖(1 - ((Q p).1 : ℝ)) • (Q p).2‖ +
              ‖((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2)‖ := norm_add_le _ _
        _ = (1 - ((Q p).1 : ℝ)) * ‖(Q p).2‖ + ((Q p).1 : ℝ) := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
          simp [abs_inv, abs_of_nonneg (norm_nonneg (Q p).2), hn]
        _ ≤ 2 := by nlinarith [norm_nonneg (Q p).2]
    · rw [if_neg hlt]
      exact le_of_lt (by simpa [Q, dist_eq_norm] using hinv_lt p)⟩
  have hR : Continuous R := by
    apply Continuous.subtype_mk hrad
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.congr (hΦ.continuous.comp hR)
  intro p
  symm
  change apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1.1 p.1.2 = _
  rw [← hinv_eq p]
  unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
  by_cases hlt : ‖(inv p).1‖ < 1
  · have hex : ∃ x : apm_t00A01_LargeDisk3, Φ x = Φ (inv p) ∧ dist x.1 0 < 1 :=
      ⟨inv p, rfl, by simpa [dist_eq_norm] using hlt⟩
    rw [dif_pos hex]
    have hchoose : hex.choose = inv p := hΦ.injective hex.choose_spec.1
    simp only [hchoose, Q, hlt, if_pos]
    have hv : (1 - (p.1.1 : ℝ)) • (hex.choose).1 +
        (p.1.1 : ℝ) • (‖(hex.choose).1‖⁻¹ • (hex.choose).1) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
      rw [hchoose]
      simpa [R, Q, hlt] using (R p).2
    rw [dif_pos hv]
    apply congrArg Φ
    apply Subtype.ext
    simp [R, Q, hlt]
  · have hnone : ¬ ∃ x : apm_t00A01_LargeDisk3,
        Φ x = Φ (inv p) ∧ dist x.1 0 < 1 := by
      rintro ⟨x, hx, hx1⟩
      have hxeq : x = inv p := hΦ.injective hx
      apply hlt
      simpa [hxeq, dist_eq_norm] using hx1
    rw [dif_neg hnone]
    simp [R, Q, hlt]

/-- The collar homotopy is continuous on `I × U`, `U = M \ Φ(closedBall 0 (1/2))`:
near a point of `Φ(ball 0 2)` use the `_aux_ball` leaf on that open set; any other
point lies in the open set `M \ Φ(closedBall 0 1)`, where the homotopy is the
identity. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn
    {M : Type} [TopologicalSpace M] [T2Space M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    ContinuousOn
      (fun p : unitInterval × M ↦
        apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2)
      (univ ×ˢ (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ) := by
  intro p hp
  have hU : IsOpen (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ :=
    (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_closed
      Φ hΦ.continuous (1 / 2)).isOpen_compl
  by_cases hb : p.2 ∈ Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2}
  · have hA : IsOpen (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2} ∩
        (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ) : Set (unitInterval × M)) :=
      isOpen_univ.prod (hΦo.inter hU)
    exact ((apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_ball
      Φ hΦ hΦo).continuousAt (hA.mem_nhds ⟨trivial, hb, hp.2⟩)).continuousWithinAt
  · have hB : IsOpen (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ 1})ᶜ :
        Set (unitInterval × M)) :=
      isOpen_univ.prod
        (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_closed
          Φ hΦ.continuous 1).isOpen_compl
    have hpB : p ∈ (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ 1})ᶜ :
        Set (unitInterval × M)) := by
      refine ⟨trivial, ?_⟩
      rintro ⟨x, hx, hxp⟩
      refine hb ⟨x, ?_, hxp⟩
      change dist x.1 0 ≤ 1 at hx
      change dist x.1 0 < 2
      linarith
    have heq : (fun q : unitInterval × M ↦
        apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ q.1 q.2)
          =ᶠ[nhds p] Prod.snd := by
      filter_upwards [hB.mem_nhds hpB] with q hq
      apply apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_eq_self
      rintro ⟨x, hx, hxq⟩
      refine hq.2 ⟨x, ?_, hxq⟩
      change dist x.1 0 < 1 at hx
      change dist x.1 0 ≤ 1
      exact le_of_lt hx
    exact (continuous_snd.continuousAt.congr heq.symm).continuousWithinAt

/-- LEAF: the collar homotopy keeps `U = M \ Φ(closedBall 0 (1/2))` inside `U`,
and at time `1` lands in the punctured manifold. For `z = Φ x ∈ U` with
`‖x‖ < 1` one has `‖x‖ > 1/2`, and the moving point has norm
`(1-t)‖x‖ + t ∈ (1/2, 1]`, equal to `1` at `t = 1`; injectivity of `Φ` and
`φ '' {‖y‖ < 1} = Φ '' {‖x‖ < 1}`
(`apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image`) finish. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_mapsTo
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦ : Function.Injective Φ) (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ) :
    (∀ t : unitInterval,
      MapsTo (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ t)
        (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ
        (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ) ∧
    MapsTo (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ 1)
      (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ
      {z | z ∉ φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}} := by
  classical
  have radial_bounds (t : unitInterval) (x : EuclideanSpace ℝ (Fin 3))
      (hx : 1 / 2 < ‖x‖) (hx1 : ‖x‖ < 1) :
      1 / 2 < ‖(1 - (t : ℝ)) • x + (t : ℝ) • (‖x‖⁻¹ • x)‖ ∧
        ‖(1 - (t : ℝ)) • x + (t : ℝ) • (‖x‖⁻¹ • x)‖ ≤ 1 := by
    have hx0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have heq :
        (1 - (t : ℝ)) • x + (t : ℝ) • (‖x‖⁻¹ • x) =
          ((1 - (t : ℝ)) + (t : ℝ) * ‖x‖⁻¹) • x := by
      rw [add_smul, mul_smul]
    rw [heq, norm_smul, Real.norm_eq_abs]
    have hi0 : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
    have hc0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ‖x‖⁻¹ :=
      add_nonneg (sub_nonneg.mpr ht1) (mul_nonneg ht0 hi0)
    rw [abs_of_nonneg hc0]
    have hcalc :
        ((1 - (t : ℝ)) + (t : ℝ) * ‖x‖⁻¹) * ‖x‖ =
          (1 - (t : ℝ)) * ‖x‖ + (t : ℝ) := by
      field_simp
    rw [hcalc]
    constructor <;> nlinarith
  constructor
  · intro t z hz
    unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
    split_ifs with h hv
    · rintro ⟨y, hy, heq⟩
      have hxhalf : 1 / 2 < ‖h.choose.1‖ := by
        by_contra hn
        apply hz
        refine ⟨h.choose, ?_, h.choose_spec.1⟩
        simpa [dist_eq_norm] using (not_lt.mp hn)
      have hx1 : ‖h.choose.1‖ < 1 := by
        simpa [dist_eq_norm] using h.choose_spec.2
      have hb := (radial_bounds t h.choose.1 hxhalf hx1).1
      have hy' : ‖y.1‖ ≤ 1 / 2 := by
        simpa [dist_eq_norm] using hy
      have hxy : y.1 =
          (1 - (t : ℝ)) • h.choose.1 +
            (t : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) := by
        exact congrArg Subtype.val (hΦ heq)
      rw [hxy] at hy'
      linarith
    · exact hz
    · exact hz
  · intro z hz
    unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
    split_ifs with h hv
    · have hxhalf : 1 / 2 < ‖h.choose.1‖ := by
        by_contra hn
        apply hz
        refine ⟨h.choose, ?_, h.choose_spec.1⟩
        simpa [dist_eq_norm] using (not_lt.mp hn)
      have hx1 : ‖h.choose.1‖ < 1 := by
        simpa [dist_eq_norm] using h.choose_spec.2
      rw [apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image
          φ Φ hΦφ]
      rintro ⟨y, hy, heq⟩
      have hxy : y.1 =
            (1 - (1 : ℝ)) • h.choose.1 +
              (1 : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) := by
          exact congrArg Subtype.val (hΦ heq)
      have hnorm : ‖(1 - (1 : ℝ)) • h.choose.1 +
              (1 : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1)‖ = 1 := by
        rw [show (1 : ℝ) - 1 = 0 by norm_num, zero_smul, zero_add, one_smul,
          norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg h.choose.1))]
        exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) hxhalf))
      have hy' : ‖y.1‖ < 1 := by simpa [dist_eq_norm] using hy
      rw [hxy, hnorm] at hy'
      exact (lt_irrefl 1 hy')
    · have hxhalf : 1 / 2 < ‖h.choose.1‖ := by
        by_contra hn
        apply hz
        refine ⟨h.choose, ?_, h.choose_spec.1⟩
        simpa [dist_eq_norm] using (not_lt.mp hn)
      exfalso
      apply hv
      change ‖(1 - (1 : ℝ)) • h.choose.1 +
            (1 : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) - 0‖ ≤ 2
      rw [show (1 : ℝ) - 1 = 0 by norm_num, zero_smul, zero_add, one_smul,
        sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg h.choose.1))]
      rw [inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) hxhalf))]
      norm_num
    · rw [apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image
          φ Φ hΦφ]
      rintro ⟨x, hx, hxz⟩
      exact h ⟨x, hxz, hx⟩

lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_zero
    {M : Type} (Φ : apm_t00A01_LargeDisk3 → M) (z : M) :
    apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ 0 z = z := by
  classical
  unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
  split_ifs with h hv
  · have hx := h.choose_spec.1
    convert hx using 2
    apply Subtype.ext
    simp
  · rfl
  · rfl

lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_one
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ) (z : M)
    (hz : z ∉ φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}) :
    apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ 1 z = z := by
  classical
  unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
  rw [dif_neg]
  rintro ⟨x, hxz, hx⟩
  rw [apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image
    φ Φ hΦφ] at hz
  exact hz ⟨x, hx, hxz⟩

/-- The punctured manifold is a deformation retract of the slightly
enlarged punctured part `M \ Φ(closedBall 0 (1/2))`, by pushing the shell
`1/2 < ‖x‖ < 1` radially out to the unit sphere inside the collar. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv
    {M : Type} [TopologicalSpace M] [T2Space M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦ : Topology.IsEmbedding Φ) (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ)
    (hΦo : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    Nonempty (ContinuousMap.HomotopyEquiv (apm_t00A01_punctured φ)
      ↥(apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ) := by
  obtain ⟨hmap, hmap1⟩ :=
    apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_mapsTo
      φ Φ hΦ.injective hΦφ
  have hcont :=
    apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn
      Φ hΦ hΦo
  have hHc : Continuous (fun p : unitInterval ×
      ↥(apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ ↦
      apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1) :=
    hcont.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p ↦ ⟨mem_univ _, p.2.2⟩)
  let i : C(apm_t00A01_punctured φ,
      ↥(apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ) :=
    ⟨apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_inclusion φ Φ hΦφ,
      apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_inclusion_continuous
        φ Φ hΦφ⟩
  let r : C(↥(apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ,
      apm_t00A01_punctured φ) :=
    ⟨fun z ↦ ⟨apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ 1 z.1,
      hmap1 z.2⟩,
      (hHc.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let F : ContinuousMap.Homotopy (ContinuousMap.id _) (i.comp r) :=
    { toFun := fun p ↦
        ⟨apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1,
          hmap p.1 p.2.2⟩
      continuous_toFun := hHc.subtype_mk _
      map_zero_left := fun z ↦ Subtype.ext
        (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_zero Φ z.1)
      map_one_left := fun z ↦ rfl }
  have hri : r.comp i = ContinuousMap.id _ := by
    ext z
    exact apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_one
      φ Φ hΦφ z.1 z.2
  exact ⟨{ toFun := i, invFun := r
           left_inv := by rw [hri]
           right_inv := ⟨F.symm⟩ }⟩

/-- LEAF: the open shell `Φ(1/2 < ‖x‖ < 2)` is homeomorphic to a Euclidean
shell, hence homotopy equivalent to `S²`, hence simply connected
(`ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected`). -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_shell_simplyConnected_aux_euclidean :
    SimplyConnectedSpace
      ↥{x : EuclideanSpace ℝ (Fin 3) | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2} := by
  let E := EuclideanSpace ℝ (Fin 3)
  let S : Set E := {x | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2}
  let sphere := Metric.sphere (0 : E) 1
  let i : C(sphere, S) :=
    { toFun := fun x => ⟨x.1, by
        have hx : ‖x.1‖ = 1 := by
          simpa [Metric.mem_sphere, dist_zero_right] using x.2
        constructor <;> dsimp [S] <;> rw [hx] <;> norm_num⟩
      continuous_toFun := by
        apply Continuous.subtype_mk continuous_subtype_val }
  let r : C(S, sphere) :=
    { toFun := fun x => ⟨NormedSpace.normalize x.1, by
        have hx0 : x.1 ≠ 0 := by
          intro hx
          have := x.2.1
          change (1 / 2 : ℝ) < ‖x.1‖ at this
          have hn := norm_nonneg x.1
          rw [hx, norm_zero] at this
          linarith
        dsimp [sphere]
        rw [Metric.mem_sphere, dist_zero_right]
        exact NormedSpace.norm_normalize hx0⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hn : Continuous (fun x : S => ‖x.1‖) :=
          continuous_norm.comp continuous_subtype_val
        exact (hn.inv₀ (fun x => by
          apply norm_ne_zero_iff.mpr
          intro hx
          have := x.2.1
          change (1 / 2 : ℝ) < ‖x.1‖ at this
          rw [hx, norm_zero] at this
          norm_num at this)).smul continuous_subtype_val }
  have hri : r.comp i = ContinuousMap.id sphere := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change NormedSpace.normalize x.1 = x.1
    apply NormedSpace.normalize_eq_self_of_norm_eq_one
    simpa [Metric.mem_sphere, dist_zero_right] using x.2
  let H : ContinuousMap.Homotopy (i.comp r) (ContinuousMap.id S) :=
    { toFun := fun tx => by
        let t : ℝ := tx.1
        let x : E := tx.2.1
        let a : ℝ := (1 - t) / ‖x‖ + t
        refine ⟨a • x, ?_⟩
        have ht0 : 0 ≤ t := tx.1.2.1
        have ht1 : t ≤ 1 := tx.1.2.2
        have hxlo : (1 / 2 : ℝ) < ‖x‖ := tx.2.2.1
        have hxhi : ‖x‖ < 2 := tx.2.2.2
        have hx0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) hxlo)
        have hxpos : 0 < ‖x‖ := lt_trans (by norm_num) hxlo
        have ha0 : 0 ≤ a := by
          dsimp [a]
          exact add_nonneg (div_nonneg (sub_nonneg.mpr ht1) hxpos.le) ht0
        change (1 / 2 : ℝ) < ‖a • x‖ ∧ ‖a • x‖ < 2
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
        dsimp [a]
        field_simp [hx0]
        constructor <;> nlinarith
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hn : Continuous (fun tx : unitInterval × S => ‖tx.2.1‖) :=
          continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
        have hn0 : ∀ tx : unitInterval × S, ‖tx.2.1‖ ≠ 0 := fun tx => by
          apply norm_ne_zero_iff.mpr
          intro hx
          have := tx.2.2.1
          change (1 / 2 : ℝ) < ‖tx.2.1‖ at this
          rw [hx, norm_zero] at this
          norm_num at this
        have ht : Continuous (fun tx : unitInterval × S => (tx.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        exact (((continuous_const.sub ht).div hn hn0).add ht).smul
          (continuous_subtype_val.comp continuous_snd)
      map_zero_left := fun x => by
        apply Subtype.ext
        change ((1 - (0 : ℝ)) / ‖x.1‖ + 0) • x.1 = NormedSpace.normalize x.1
        simp [NormedSpace.normalize]
      map_one_left := fun x => by
        apply Subtype.ext
        change ((1 - (1 : ℝ)) / ‖x.1‖ + 1) • x.1 = x.1
        simp }
  let e : ContinuousMap.HomotopyEquiv sphere S :=
    { toFun := i
      invFun := r
      left_inv := by rw [hri]
      right_inv := ⟨H⟩ }
  letI : SimplyConnectedSpace sphere :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 2 (by omega)
  exact e.symm.simplyConnectedSpace

lemma apm_t00A01_punctured_fundamentalGroup_aux_shell_simplyConnected
    {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ) :
    SimplyConnectedSpace
      ↥((apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ ∩
        apm_t00A01_punctured_fundamentalGroup_aux_ball Φ) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let S : Set E := {x | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2}
  let T : Set M :=
    (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ ∩
      apm_t00A01_punctured_fundamentalGroup_aux_ball Φ
  let f : S → T := fun x => ⟨Φ ⟨x.1, by
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt x.2.2⟩, by
      constructor
      · intro hx
        rcases hx with ⟨y, hy, heq⟩
        have hxy : y.1 = x.1 := Subtype.ext_iff.mp (hΦ.injective heq)
        have hy' : ‖y.1‖ ≤ (1 / 2 : ℝ) := by
          simpa [dist_zero_right] using hy
        rw [hxy] at hy'
        exact (not_le_of_gt x.2.1) hy'
      · refine ⟨⟨x.1, by
          simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt x.2.2⟩, ?_, rfl⟩
        simpa [dist_zero_right] using x.2.2⟩
  have hf : Topology.IsEmbedding f := by
    let g : S → apm_t00A01_LargeDisk3 := fun x => ⟨x.1, by
      simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt x.2.2⟩
    have hg : Topology.IsEmbedding g := by
      apply Topology.IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
      exact (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (fun x : S => x.1))
    apply Topology.IsEmbedding.of_comp
      (Continuous.subtype_mk (hΦ.continuous.comp hg.continuous) _) continuous_subtype_val
    exact hΦ.comp hg
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rcases hz.2 with ⟨x, hx, rfl⟩
    have hxlo : (1 / 2 : ℝ) < ‖x.1‖ := by
      apply lt_of_not_ge
      intro hle
      exact hz.1 ⟨x, by simpa [dist_zero_right] using hle, rfl⟩
    refine ⟨⟨x.1, hxlo, ?_⟩, ?_⟩
    · simpa [dist_zero_right] using hx
    · rfl
  let e : S ≃ₜ T := hf.toHomeomorphOfSurjective hsurj
  haveI : SimplyConnectedSpace S :=
    apm_t00A01_punctured_fundamentalGroup_aux_shell_simplyConnected_aux_euclidean
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- LEAF: the open collar ball is homeomorphic to a convex open ball, hence
simply connected. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_ball_simplyConnected
    {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ) :
    SimplyConnectedSpace ↥(apm_t00A01_punctured_fundamentalGroup_aux_ball Φ) := by
  let S : Set apm_t00A01_LargeDisk3 := {x | dist x.1 0 < 2}
  have himage : ((fun x : apm_t00A01_LargeDisk3 ↦ x.1) '' S) =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change dist y.1 0 < 2 at hy
      simpa [Metric.mem_ball] using hy
    · intro hx
      have hx' : dist x 0 < 2 := by
        simpa [Metric.mem_ball, dist_comm] using hx
      refine ⟨⟨x, ?_⟩, hx', rfl⟩
      simpa [Metric.mem_closedBall, dist_comm] using le_of_lt hx'
  let e : S ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage S).trans (Homeomorph.setCongr himage)
  letI : ContractibleSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2) :=
    Metric.contractibleSpace_ball (by norm_num)
  letI : ContractibleSpace S := e.contractibleSpace
  letI : ContractibleSpace ↥(apm_t00A01_punctured_fundamentalGroup_aux_ball Φ) :=
    (hΦ.homeomorphImage S).symm.contractibleSpace
  exact SimplyConnectedSpace.ofContractible _

/-- LEAF: the enlarged punctured part is path connected (`H₀ M ≅ ℤ` makes `M`
path connected; a path through the small ball detours around it inside the
collar). -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_pathConnected
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2}))
    (hM : apm_t00A01_isHomology3Sphere M) :
    PathConnectedSpace ↥(apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ := by
  sorry

/-- A free product with a trivial factor is the other factor. -/
noncomputable def apm_t00A01_punctured_fundamentalGroup_aux_coprod_trivial
    (G H : Type) [Group G] [Group H] [Subsingleton H] :
    Monoid.Coprod G H ≃* G where
  toFun := Monoid.Coprod.lift (MonoidHom.id G) 1
  invFun := Monoid.Coprod.inl
  left_inv x := by
    have h : (Monoid.Coprod.inl : G →* Monoid.Coprod G H).comp
        (Monoid.Coprod.lift (MonoidHom.id G) 1) = MonoidHom.id _ := by
      apply Monoid.Coprod.hom_ext
      · ext g; simp
      · ext h; simp [Subsingleton.elim h 1]
    exact DFunLike.congr_fun h x
  right_inv g := by simp
  map_mul' := map_mul _

lemma apm_t00A01_punctured_fundamentalGroup_aux_subsingleton
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (FundamentalGroup X x) :=
  ⟨fun a b => by
    unfold FundamentalGroup at a b ⊢
    exact Subsingleton.elim (α := Path.Homotopic.Quotient x x) a b⟩

theorem apm_t00A01_punctured_fundamentalGroup
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (m : M) (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    Nonempty
      (FundamentalGroup (apm_t00A01_punctured φ)
          (apm_t00A01_boundaryMap φ hφ.injective (Classical.choice inferInstance)) ≃*
        FundamentalGroup M m) := by
  obtain ⟨Φ, hΦ, hΦφ, hΦo⟩ := hcollar
  let U : Set M := (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ
  let V : Set M := apm_t00A01_punctured_fundamentalGroup_aux_ball Φ
  have hU : IsOpen U := by
    haveI : CompactSpace apm_t00A01_LargeDisk3 :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    have hK : IsCompact {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ 1 / 2} :=
      (isClosed_le (continuous_subtype_val.dist continuous_const)
        continuous_const).isCompact
    exact (hK.image hΦ.continuous).isClosed.isOpen_compl
  have hV : IsOpen V := hΦo
  have hcover : U ∪ V = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ apm_t00A01_punctured_fundamentalGroup_aux_inner Φ
    · right
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      change dist y.1 0 < 2
      exact lt_of_le_of_lt (show dist y.1 0 ≤ 1 / 2 from hy) (by norm_num)
    · exact Or.inl hx
  let s₀ : apm_t00A01_Sphere2 := Classical.choice inferInstance
  let p₀ := apm_t00A01_boundaryMap φ hφ.injective s₀
  have hs₀ : dist s₀.1 0 = 1 := by simpa [Metric.mem_sphere] using s₀.2
  let d₀ : apm_t00A01_Disk3 :=
    ⟨s₀.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s₀.2⟩
  have hp₀ : p₀.val = Φ (apm_t00A01_unitToLarge d₀) := by
    change φ d₀ = Φ (apm_t00A01_unitToLarge d₀)
    exact (congrFun hΦφ d₀).symm
  have hw₀U : p₀.val ∈ U := by
    rintro ⟨y, hy, hyeq⟩
    rw [hp₀] at hyeq
    have : y.1 = s₀.1 := Subtype.ext_iff.mp (hΦ.injective hyeq)
    change dist y.1 0 ≤ 1 / 2 at hy
    rw [this, hs₀] at hy
    norm_num at hy
  have hw₀V : p₀.val ∈ V := by
    refine ⟨apm_t00A01_unitToLarge d₀, ?_, hp₀.symm⟩
    change dist s₀.1 0 < 2
    rw [hs₀]; norm_num
  haveI : PathConnectedSpace U :=
    apm_t00A01_punctured_fundamentalGroup_aux_enlarged_pathConnected M Φ hΦ hΦo hM
  haveI : SimplyConnectedSpace V :=
    apm_t00A01_punctured_fundamentalGroup_aux_ball_simplyConnected Φ hΦ
  haveI : SimplyConnectedSpace (U ∩ V : Set M) :=
    apm_t00A01_punctured_fundamentalGroup_aux_shell_simplyConnected Φ hΦ
  haveI : PathConnectedSpace M := by
    rw [pathConnectedSpace_iff_univ, ← hcover]
    exact (isPathConnected_iff_pathConnectedSpace.mpr inferInstance).union
      (isPathConnected_iff_pathConnectedSpace.mpr inferInstance) ⟨p₀.val, hw₀U, hw₀V⟩
  haveI := apm_t00A01_punctured_fundamentalGroup_aux_subsingleton
    (⟨p₀.val, hw₀V⟩ : V)
  let w : (U ∩ V : Set M) := ⟨p₀.val, hw₀U, hw₀V⟩
  let G := ConstructionTargets.TwoOpenFreeProductMapping.chosenGroupEquivalence
    hU hV hcover w (⟨p₀.val, hw₀U⟩ : U) (⟨p₀.val, hw₀V⟩ : V)
  obtain ⟨eA⟩ := apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv φ Φ hΦ hΦφ hΦo
  obtain ⟨g₁⟩ := apm_t00A01_punctured_fundamentalGroup_aux_of_hequiv p₀
    (⟨p₀.val, hw₀U⟩ : U) eA (PathConnectedSpace.somePath _ _)
  exact ⟨g₁.trans (((apm_t00A01_punctured_fundamentalGroup_aux_coprod_trivial _ _).symm.trans
    G.symm).trans (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (PathConnectedSpace.somePath p₀.val m)))⟩

/-- LIBRARY: the long exact sequence of the pair, excision in the collar,
and the local orientation class make the punctured homology sphere a homology
ball. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_H0
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    Nonempty (apm_t00A01_H 0 (apm_t00A01_punctured φ) ≅ ModuleCat.of ℤ ℤ) := by
  letI : PathConnectedSpace (apm_t00A01_punctured φ) :=
    apm_t00A01_punctured_pathConnected M φ hφ hM hcollar
  let p : apm_t00A01_punctured φ := Classical.choice inferInstance
  let q := ConstructionTargets.T02A06SphereH0.singularVertexH0Class p
  letI : Epi q :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_epi p
  letI : Mono q :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_mono p
  letI : IsIso q := isIso_of_mono_of_epi q
  exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of (apm_t00A01_punctured φ)) 0
      (ModuleCat.of ℤ ℤ) (asIso q).symm⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    ∀ k : ℕ, k ≠ 0 → Limits.IsZero (apm_t00A01_H k (apm_t00A01_punctured φ)) := by
  sorry

theorem apm_t00A01_punctured_isHomologyBall
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    apm_t00A01_isHomologyBall (apm_t00A01_punctured φ) := by
  exact ⟨apm_t00A01_punctured_isHomologyBall_aux_H0 M φ hφ hM hcollar,
    apm_t00A01_punctured_isHomologyBall_aux_positive M φ hφ hM hcollar⟩

/-- LIBRARY: radial collar coordinates thicken both quotient pieces to an
open cover, identify their overlap with `S²`, and give continuity of both
boundary inclusions. -/
lemma apm_t00A01_collared_standardCover_aux_boundary_continuous
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ) :
    Continuous (apm_t00A01_boundaryMap φ hφ.injective) := by
  apply Continuous.subtype_mk
  exact hφ.continuous.comp (continuous_subtype_val.subtype_mk _)

/-- Points of the punctured manifold lying in the open radius-two collar ball. -/
def apm_t00A01_collarSet {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M) :
    Set (apm_t00A01_punctured φ) :=
  {x | x.1 ∈ Φ '' {y : apm_t00A01_LargeDisk3 | dist y.1 0 < 2}}

/-- The open thickening of the first piece: all of it, plus a collar `C` of
the second piece. -/
def apm_t00A01_thickLeft {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (C : Set B) :
    Set (apm_t00A01_connectedSum iA iB) :=
  (fun z : Sum A B ↦ Quotient.mk
    (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) z) ''
      (Set.range Sum.inl ∪ Sum.inr '' C)

/-- The open thickening of the second piece: a collar `C` of the first piece,
plus all of the second. -/
def apm_t00A01_thickRight {A B : Type}
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (C : Set A) :
    Set (apm_t00A01_connectedSum iA iB) :=
  (fun z : Sum A B ↦ Quotient.mk
    (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) z) ''
      (Sum.inl '' C ∪ Set.range Sum.inr)

/-- The collar is open in the punctured manifold and contains the boundary
sphere (radius one is inside the open radius-two ball). -/
lemma apm_t00A01_collared_standardCover_aux_collar
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (Φ : apm_t00A01_LargeDisk3 → M)
    (hext : Φ ∘ apm_t00A01_unitToLarge = φ)
    (hopen : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    IsOpen (apm_t00A01_collarSet φ Φ) ∧
      ∀ s, apm_t00A01_boundaryMap φ hφ.injective s ∈ apm_t00A01_collarSet φ Φ := by
  refine ⟨hopen.preimage continuous_subtype_val, fun s ↦ ?_⟩
  refine ⟨apm_t00A01_unitToLarge
    ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩, ?_, ?_⟩
  · have hs : dist s.1 0 = 1 := by simpa [Metric.mem_sphere, dist_comm] using s.2
    change dist s.1 0 < 2
    linarith
  · exact congrFun hext _

/-- LEAF. Both thickenings are open and together cover the connected sum.
Proof sketch: the preimage of each under the quotient map is the displayed
set itself (it is saturated, because every glued pair has its `inr` end
`iB s ∈ CB`, resp. its `inl` end `iA s ∈ CA`), and that set is open in the
sum; the union contains every class. -/
lemma apm_t00A01_collared_standardCover_aux_open {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (CA : Set A) (CB : Set B) (hCA : IsOpen CA) (hCB : IsOpen CB)
    (hiA : ∀ s, iA s ∈ CA) (hiB : ∀ s, iB s ∈ CB) :
    IsOpen (apm_t00A01_thickLeft iA iB CB) ∧
      IsOpen (apm_t00A01_thickRight iA iB CA) ∧
      apm_t00A01_thickLeft iA iB CB ∪ apm_t00A01_thickRight iA iB CA = Set.univ := by
  let q : Sum A B → apm_t00A01_connectedSum iA iB := fun z ↦ Quotient.mk _ z
  let L : Set (Sum A B) := Set.range Sum.inl ∪ Sum.inr '' CB
  let R : Set (Sum A B) := Sum.inl '' CA ∪ Set.range Sum.inr
  have hL_invariant {x y : Sum A B}
      (hxy : Relation.EqvGen (apm_t00A01_glueRel iA iB) x y) :
      x ∈ L ↔ y ∈ L := by
    induction hxy with
    | rel x y h =>
        cases h with
        | glue s =>
            constructor
            · intro _
              exact Or.inr ⟨iB s, hiB s, rfl⟩
            · intro _
              exact Or.inl ⟨iA s, rfl⟩
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hR_invariant {x y : Sum A B}
      (hxy : Relation.EqvGen (apm_t00A01_glueRel iA iB) x y) :
      x ∈ R ↔ y ∈ R := by
    induction hxy with
    | rel x y h =>
        cases h with
        | glue s =>
            constructor
            · intro _
              exact Or.inr ⟨iB s, rfl⟩
            · intro _
              exact Or.inl ⟨iA s, hiA s, rfl⟩
    | refl => exact Iff.rfl
    | symm x y h ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  have hpreL : q ⁻¹' (q '' L) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, hq⟩
      exact (hL_invariant (Quotient.exact hq)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hpreR : q ⁻¹' (q '' R) = R := by
    ext x
    constructor
    · rintro ⟨y, hy, hq⟩
      exact (hR_invariant (Quotient.exact hq)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hopenL : IsOpen L :=
    IsOpen.union isOpen_range_inl (isOpenMap_inr _ hCB)
  have hopenR : IsOpen R :=
    IsOpen.union (isOpenMap_inl _ hCA) isOpen_range_inr
  constructor
  · change IsOpen (q '' L)
    rw [isOpen_coinduced]
    exact hpreL.symm ▸ hopenL
  constructor
  · change IsOpen (q '' R)
    rw [isOpen_coinduced]
    exact hpreR.symm ▸ hopenR
  · apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | _ x =>
        cases x with
        | inl a =>
            left
            exact ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, rfl⟩
        | inr b =>
            right
            exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, rfl⟩

/-- Banked by lemma-3: every collar preimage of a punctured point has radius
at least one. -/
lemma apm_t00A01_collared_standardCover_aux_left_aux_norm_ge_one
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hext : Φ ∘ apm_t00A01_unitToLarge = φ)
    (z : apm_t00A01_punctured φ) (x : apm_t00A01_LargeDisk3)
    (hx : Φ x = z.1) : 1 ≤ ‖x.1‖ := by
  by_contra hn
  have hxlt : ‖x.1‖ < 1 := lt_of_not_ge hn
  apply z.2
  let y : apm_t00A01_Disk3 := ⟨x.1, by
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hxlt⟩
  refine ⟨y, ?_, ?_⟩
  · simpa [y, dist_zero_right] using hxlt
  · rw [← hx]
    exact (congrFun hext y).symm

/-- LEAF. The open collar strong-deformation-retracts onto the boundary
sphere, radially. Proof sketch: a collar point is `Φ y` with `1 ≤ ‖y‖ < 2`
(`_aux_norm_ge_one`); `y` depends continuously on the point because `Φ` is
an embedding. Take `r = y / ‖y‖` and `H (x, t) = Φ ((1 - t) • y + t • (y / ‖y‖))`;
the radius stays in `[1, ‖y‖]`, so `H` stays in the collar and off the open
unit ball, and points with `‖y‖ = 1` (the boundary sphere) are fixed. -/
lemma apm_t00A01_collared_standardCover_aux_left_aux_radial
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hext : Φ ∘ apm_t00A01_unitToLarge = φ) :
    ∃ (r : C(↥(apm_t00A01_collarSet φ Φ), apm_t00A01_Sphere2))
      (H : C(↥(apm_t00A01_collarSet φ Φ) × unitInterval, apm_t00A01_punctured φ)),
      (∀ s (h : apm_t00A01_boundaryMap φ hφ.injective s ∈ apm_t00A01_collarSet φ Φ),
        r ⟨_, h⟩ = s) ∧
      (∀ x, H (x, 0) = x.1) ∧
      (∀ x, H (x, 1) = apm_t00A01_boundaryMap φ hφ.injective (r x)) ∧
      (∀ p, H p ∈ apm_t00A01_collarSet φ Φ) ∧
      (∀ s (h : apm_t00A01_boundaryMap φ hφ.injective s ∈ apm_t00A01_collarSet φ Φ) t,
        H (⟨_, h⟩, t) = apm_t00A01_boundaryMap φ hφ.injective s) := by
  sorry

/-- LEAF. Generic quotient step: if an open collar `C ⊇ iB '' univ` of the
second piece strong-deformation-retracts onto the glued sphere, the left
thickening is homotopy equivalent to the first piece. Proof sketch: `f` sends
`[inl a] ↦ a`, `[inr c] ↦ iA (r c)` (well defined by `hr`), `g a = [inl a]`;
`f ∘ g = id`, and `g ∘ f ≃ id` by `[inl a] ↦ [inl a]`, `[inr c] ↦ [inr H (c, t)]`
(compatible on glued points by `hHfix`). Continuity: the preimage
`range inl ∪ inr '' C` is open and saturated, so the restricted quotient map is
a quotient map (`IsQuotientMap.restrictPreimage_isOpen`); times `unitInterval`
it stays a quotient map since `unitInterval` is locally compact. -/
lemma apm_t00A01_collared_standardCover_aux_left_aux_quotient {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (hiA : Continuous iA) (C : Set B) (hC : IsOpen C) (hiB : ∀ s, iB s ∈ C)
    (r : C(↥C, apm_t00A01_Sphere2)) (H : C(↥C × unitInterval, B))
    (hr : ∀ s, r ⟨iB s, hiB s⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1) (hH1 : ∀ x, H (x, 1) = iB (r x))
    (hHC : ∀ p, H p ∈ C) (hHfix : ∀ s t, H (⟨iB s, hiB s⟩, t) = iB s) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(apm_t00A01_thickLeft iA iB C) A) := by
  sorry

/-- ASSEMBLY (from `_aux_radial`, `_aux_quotient`). The left thickening
deformation retracts onto the first punctured piece: push the second collar `1 ≤ r < 2` radially onto `r = 1`, which is
glued to the boundary sphere of the first piece. -/
lemma apm_t00A01_collared_standardCover_aux_left
    {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (Φ₂ : apm_t00A01_LargeDisk3 → M₂) (hΦ₂ : Topology.IsEmbedding Φ₂)
    (hext₂ : Φ₂ ∘ apm_t00A01_unitToLarge = φ₂)
    (hopen₂ : IsOpen (Φ₂ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥(apm_t00A01_thickLeft (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
        (apm_t00A01_boundaryMap φ₂ hφ₂.injective) (apm_t00A01_collarSet φ₂ Φ₂))
      (apm_t00A01_punctured φ₁)) := by
  obtain ⟨hCopen, hCmem⟩ :=
    apm_t00A01_collared_standardCover_aux_collar φ₂ hφ₂ Φ₂ hext₂ hopen₂
  obtain ⟨r, H, hr, hH0, hH1, hHC, hHfix⟩ :=
    apm_t00A01_collared_standardCover_aux_left_aux_radial φ₂ hφ₂ Φ₂ hΦ₂ hext₂
  exact apm_t00A01_collared_standardCover_aux_left_aux_quotient
    (apm_t00A01_boundaryMap φ₁ hφ₁.injective) (apm_t00A01_boundaryMap φ₂ hφ₂.injective)
    (apm_t00A01_collared_standardCover_aux_boundary_continuous φ₁ hφ₁)
    _ hCopen hCmem r H (fun s ↦ hr s (hCmem s)) hH0 hH1 hHC
    (fun s t ↦ hHfix s (hCmem s) t)

/-- LEAF. Mirror image of `_aux_left_aux_quotient`: if an open collar
`C ⊇ iA '' univ` of the first piece strong-deformation-retracts onto the glued
sphere, the right thickening is homotopy equivalent to the second piece. Same
proof with the roles of `inl` and `inr` exchanged: `f` sends `[inr b] ↦ b`,
`[inl c] ↦ iB (r c)`, `g b = [inr b]`; the homotopy moves `[inl c]` along `H`.
Continuity through the open saturated preimage `inl '' C ∪ range inr`
(`IsQuotientMap.restrictPreimage_isOpen`), times the locally compact
`unitInterval`. -/
lemma apm_t00A01_collared_standardCover_aux_right_aux_quotient {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (hiB : Continuous iB) (C : Set A) (hC : IsOpen C) (hiA : ∀ s, iA s ∈ C)
    (r : C(↥C, apm_t00A01_Sphere2)) (H : C(↥C × unitInterval, A))
    (hr : ∀ s, r ⟨iA s, hiA s⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1) (hH1 : ∀ x, H (x, 1) = iA (r x))
    (hHC : ∀ p, H p ∈ C) (hHfix : ∀ s t, H (⟨iA s, hiA s⟩, t) = iA s) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(apm_t00A01_thickRight iA iB C) B) := by
  sorry

/-- ASSEMBLY (from `_aux_left_aux_radial` applied to the first piece, and
`_aux_right_aux_quotient`). Mirror image of `_aux_left`: the right thickening
deformation retracts onto the second punctured piece. -/
lemma apm_t00A01_collared_standardCover_aux_right
    {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (Φ₁ : apm_t00A01_LargeDisk3 → M₁) (hΦ₁ : Topology.IsEmbedding Φ₁)
    (hext₁ : Φ₁ ∘ apm_t00A01_unitToLarge = φ₁)
    (hopen₁ : IsOpen (Φ₁ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥(apm_t00A01_thickRight (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
        (apm_t00A01_boundaryMap φ₂ hφ₂.injective) (apm_t00A01_collarSet φ₁ Φ₁))
      (apm_t00A01_punctured φ₂)) := by
  obtain ⟨hCopen, hCmem⟩ :=
    apm_t00A01_collared_standardCover_aux_collar φ₁ hφ₁ Φ₁ hext₁ hopen₁
  obtain ⟨r, H, hr, hH0, hH1, hHC, hHfix⟩ :=
    apm_t00A01_collared_standardCover_aux_left_aux_radial φ₁ hφ₁ Φ₁ hΦ₁ hext₁
  exact apm_t00A01_collared_standardCover_aux_right_aux_quotient
    (apm_t00A01_boundaryMap φ₁ hφ₁.injective) (apm_t00A01_boundaryMap φ₂ hφ₂.injective)
    (apm_t00A01_collared_standardCover_aux_boundary_continuous φ₂ hφ₂)
    _ hCopen hCmem r H (fun s ↦ hr s (hCmem s)) hH0 hH1 hHC
    (fun s t ↦ hHfix s (hCmem s) t)

/-- LEAF. The overlap is the two half-open collars `1 ≤ r < 2` glued along
`r = 1`, i.e. `S² × (-1, 1)`, which retracts radially onto the glued `S²`
(at radius one the copies agree by `apm_t00A01_mk_inl_eq_mk_inr`). -/
lemma apm_t00A01_collared_standardCover_aux_inter_aux_collar_coord
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦ : Topology.IsEmbedding Φ)
    (hext : Φ ∘ apm_t00A01_unitToLarge = φ)
    (x : apm_t00A01_punctured φ) (hx : x ∈ apm_t00A01_collarSet φ Φ) :
    ∃! y : apm_t00A01_LargeDisk3,
      Φ y = x.1 ∧ 1 ≤ dist y.1 0 ∧ dist y.1 0 < 2 := by
  rcases hx with ⟨y, hy2, hyx⟩
  have hy1 : 1 ≤ dist y.1 0 := by
    by_contra h
    have hylt : dist y.1 0 < 1 := lt_of_not_ge h
    apply x.2
    let z : apm_t00A01_Disk3 :=
      ⟨y.1, by simpa [Metric.mem_closedBall] using le_of_lt hylt⟩
    refine ⟨z, ?_, ?_⟩
    · exact hylt
    · rw [← congrFun hext z]
      exact (congrArg Φ (Subtype.ext rfl)).trans hyx
  refine ⟨y, ⟨hyx, hy1, hy2⟩, ?_⟩
  intro y' hy'
  exact hΦ.injective (hy'.1.trans hyx.symm)

lemma apm_t00A01_collared_standardCover_aux_inter
    {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
    (φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (Φ₁ : apm_t00A01_LargeDisk3 → M₁) (hΦ₁ : Topology.IsEmbedding Φ₁)
    (hext₁ : Φ₁ ∘ apm_t00A01_unitToLarge = φ₁)
    (hopen₁ : IsOpen (Φ₁ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2}))
    (Φ₂ : apm_t00A01_LargeDisk3 → M₂) (hΦ₂ : Topology.IsEmbedding Φ₂)
    (hext₂ : Φ₂ ∘ apm_t00A01_unitToLarge = φ₂)
    (hopen₂ : IsOpen (Φ₂ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥(apm_t00A01_thickLeft (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
          (apm_t00A01_boundaryMap φ₂ hφ₂.injective) (apm_t00A01_collarSet φ₂ Φ₂) ∩
        apm_t00A01_thickRight (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
          (apm_t00A01_boundaryMap φ₂ hφ₂.injective) (apm_t00A01_collarSet φ₁ Φ₁))
      apm_t00A01_Sphere2) := by
  sorry
lemma apm_t00A01_collared_standardCover_aux_cover
    (M₁ M₂ : Type) [TopologicalSpace M₁] [TopologicalSpace M₂]
    (φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : apm_t00A01_HasBallCollar φ₁)
    (hcollar₂ : apm_t00A01_HasBallCollar φ₂) :
    apm_t00A01_hasStandardCover
      (apm_t00A01_connectedSum (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
        (apm_t00A01_boundaryMap φ₂ hφ₂.injective))
      (apm_t00A01_punctured φ₁) (apm_t00A01_punctured φ₂) := by
  obtain ⟨Φ₁, hΦ₁, hext₁, hopen₁⟩ := hcollar₁
  obtain ⟨Φ₂, hΦ₂, hext₂, hopen₂⟩ := hcollar₂
  obtain ⟨hC₁, hb₁⟩ :=
    apm_t00A01_collared_standardCover_aux_collar φ₁ hφ₁ Φ₁ hext₁ hopen₁
  obtain ⟨hC₂, hb₂⟩ :=
    apm_t00A01_collared_standardCover_aux_collar φ₂ hφ₂ Φ₂ hext₂ hopen₂
  obtain ⟨hU, hV, hUV⟩ := apm_t00A01_collared_standardCover_aux_open
    (apm_t00A01_boundaryMap φ₁ hφ₁.injective) (apm_t00A01_boundaryMap φ₂ hφ₂.injective)
    _ _ hC₁ hC₂ hb₁ hb₂
  exact ⟨_, _, hU, hV, hUV,
    apm_t00A01_collared_standardCover_aux_left φ₁ φ₂ hφ₁ hφ₂ Φ₂ hΦ₂ hext₂ hopen₂,
    apm_t00A01_collared_standardCover_aux_right φ₁ φ₂ hφ₁ hφ₂ Φ₁ hΦ₁ hext₁ hopen₁,
    apm_t00A01_collared_standardCover_aux_inter φ₁ φ₂ hφ₁ hφ₂
      Φ₁ hΦ₁ hext₁ hopen₁ Φ₂ hΦ₂ hext₂ hopen₂⟩

theorem apm_t00A01_collared_standardCover
    (M₁ M₂ : Type) [TopologicalSpace M₁] [TopologicalSpace M₂]
    (φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hcollar₁ : apm_t00A01_HasBallCollar φ₁)
    (hcollar₂ : apm_t00A01_HasBallCollar φ₂) :
    Continuous (apm_t00A01_boundaryMap φ₁ hφ₁.injective) ∧
    Continuous (apm_t00A01_boundaryMap φ₂ hφ₂.injective) ∧
    apm_t00A01_hasStandardCover
      (apm_t00A01_connectedSum (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
        (apm_t00A01_boundaryMap φ₂ hφ₂.injective))
      (apm_t00A01_punctured φ₁) (apm_t00A01_punctured φ₂) := by
  exact ⟨apm_t00A01_collared_standardCover_aux_boundary_continuous φ₁ hφ₁,
    apm_t00A01_collared_standardCover_aux_boundary_continuous φ₂ hφ₂,
    apm_t00A01_collared_standardCover_aux_cover M₁ M₂ φ₁ φ₂ hφ₁ hφ₂ hcollar₁ hcollar₂⟩

theorem apm_t00a01
    (M₁ M₂ : Type)
    [TopologicalSpace M₁] [TopologicalSpace M₂]
    [T2Space M₁] [T2Space M₂]
    [SecondCountableTopology M₁] [SecondCountableTopology M₂]
    [CompactSpace M₁] [CompactSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [IsManifold apm_t00A01_Model3 ∞ M₁]
    [IsManifold apm_t00A01_Model3 ∞ M₂]
    [BoundarylessManifold apm_t00A01_Model3 M₁]
    [BoundarylessManifold apm_t00A01_Model3 M₂]
    (m₁ : M₁) (m₂ : M₂)
    (φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
    (hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
    (hM₁ : apm_t00A01_isHomology3Sphere M₁)
    (hM₂ : apm_t00A01_isHomology3Sphere M₂)
    (hcollar₁ : apm_t00A01_HasBallCollar φ₁)
    (hcollar₂ : apm_t00A01_HasBallCollar φ₂) :
    Nonempty
      (@FundamentalGroup
          (apm_t00A01_connectedSum (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
            (apm_t00A01_boundaryMap φ₂ hφ₂.injective))
          (apm_t00A01_connectedSumTopology (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
            (apm_t00A01_boundaryMap φ₂ hφ₂.injective))
          (apm_t00A01_basepoint (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
            (apm_t00A01_boundaryMap φ₂ hφ₂.injective)
            (apm_t00A01_boundaryMap φ₁ hφ₁.injective (Classical.choice inferInstance))) ≃*
        Monoid.Coprod (FundamentalGroup M₁ m₁) (FundamentalGroup M₂ m₂)) ∧
    @apm_t00A01_isHomology3Sphere
      (apm_t00A01_connectedSum (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
        (apm_t00A01_boundaryMap φ₂ hφ₂.injective))
      (apm_t00A01_connectedSumTopology (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
        (apm_t00A01_boundaryMap φ₂ hφ₂.injective)) := by
  let A := apm_t00A01_punctured φ₁
  let B := apm_t00A01_punctured φ₂
  let s : apm_t00A01_Sphere2 := Classical.choice inferInstance
  have hconn₁ := apm_t00A01_punctured_pathConnected M₁ φ₁ hφ₁ hM₁ hcollar₁
  have hconn₂ := apm_t00A01_punctured_pathConnected M₂ φ₂ hφ₂ hM₂ hcollar₂
  have hπ₁ := apm_t00A01_punctured_fundamentalGroup M₁ m₁ φ₁ hφ₁ hM₁ hcollar₁
  have hπ₂ := apm_t00A01_punctured_fundamentalGroup M₂ m₂ φ₂ hφ₂ hM₂ hcollar₂
  have hball₁ := apm_t00A01_punctured_isHomologyBall M₁ φ₁ hφ₁ hM₁ hcollar₁
  have hball₂ := apm_t00A01_punctured_isHomologyBall M₂ φ₂ hφ₂ hM₂ hcollar₂
  obtain ⟨hi₁, hi₂, hcover⟩ :=
    apm_t00A01_collared_standardCover M₁ M₂ φ₁ φ₂ hφ₁ hφ₂ hcollar₁ hcollar₂
  exact ⟨apm_t00A01_bridge_fundamentalGroup_coprod M₁ M₂ A B m₁ m₂
      (apm_t00A01_boundaryMap φ₁ hφ₁.injective s)
      (apm_t00A01_boundaryMap φ₂ hφ₂.injective s)
      (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
      (apm_t00A01_boundaryMap φ₂ hφ₂.injective)
      hπ₁ hπ₂ hconn₁ hconn₂
      hi₁ hi₂ hcover,
    apm_t00A01_bridge_connectedSum_isHomology3Sphere A B
      (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
      (apm_t00A01_boundaryMap φ₂ hφ₂.injective) hball₁ hball₂ hcover⟩

#print axioms apm_t00a01
