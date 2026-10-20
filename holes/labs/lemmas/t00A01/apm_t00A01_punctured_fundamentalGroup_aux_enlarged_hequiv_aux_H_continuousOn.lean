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
  sorry

/-- LEAF: the collar makes the image of the open unit ball open in `M`. -/
lemma apm_t00A01_punctured_pathConnected_aux_inner_open
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (hcollar : apm_t00A01_HasBallCollar φ) :
    IsOpen (φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}) := by
  sorry

/-- LEAF: first entrance into a closed set. In a path-connected space, a point
outside an open set `O` contained in a nonempty closed set `K` is joined,
without entering `O`, to a point of `K \ O`. -/
lemma apm_t00A01_punctured_pathConnected_aux_first_entry
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    {O K : Set X} (hO : IsOpen O) (hK : IsClosed K) (hOK : O ⊆ K)
    {x k : X} (hx : x ∉ O) (hk : k ∈ K) :
    ∃ z ∈ K \ O, JoinedIn Oᶜ x z := by
  sorry

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
-- BEGIN SEAT AREA
lemma apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn
    {M : Type} [TopologicalSpace M] [T2Space M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    ContinuousOn
      (fun p : unitInterval × M ↦
        apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2)
      (univ ×ˢ (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ) := by
  sorry
-- END SEAT AREA

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
  sorry

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
lemma apm_t00A01_punctured_fundamentalGroup_aux_shell_simplyConnected
    {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ) :
    SimplyConnectedSpace
      ↥((apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ ∩
        apm_t00A01_punctured_fundamentalGroup_aux_ball Φ) := by
  sorry

/-- LEAF: the open collar ball is homeomorphic to a convex open ball, hence
simply connected. -/
lemma apm_t00A01_punctured_fundamentalGroup_aux_ball_simplyConnected
    {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ) :
    SimplyConnectedSpace ↥(apm_t00A01_punctured_fundamentalGroup_aux_ball Φ) := by
  sorry

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
theorem apm_t00A01_punctured_isHomologyBall
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    apm_t00A01_isHomologyBall (apm_t00A01_punctured φ) := by
  sorry

/-- LIBRARY: radial collar coordinates thicken both quotient pieces to an
open cover, identify their overlap with `S²`, and give continuity of both
boundary inclusions. -/
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
  sorry

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
