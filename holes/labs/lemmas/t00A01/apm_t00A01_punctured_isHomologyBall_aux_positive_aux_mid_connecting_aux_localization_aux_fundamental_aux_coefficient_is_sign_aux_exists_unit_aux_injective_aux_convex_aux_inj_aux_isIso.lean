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
import ConstructionTargets.ManifoldFundamentalClass
import ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison
import ConstructionTargets.CoefficientCompactComplementUnionToRelative
import ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare
import ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso

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
  let φ : apm_t00A01_Disk3 → M := Φ ∘ apm_t00A01_unitToLarge
  have hu : Topology.IsEmbedding apm_t00A01_unitToLarge := by
    apply Topology.IsEmbedding.of_comp
      (Continuous.subtype_mk continuous_subtype_val _) continuous_subtype_val
    exact (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (fun x : apm_t00A01_Disk3 ↦ x.1))
  have hφ : Topology.IsEmbedding φ := hΦ.comp hu
  have hcollar : apm_t00A01_HasBallCollar φ := ⟨Φ, hΦ, rfl, hΦo⟩
  letI : PathConnectedSpace (apm_t00A01_punctured φ) :=
    apm_t00A01_punctured_pathConnected M φ hφ hM hcollar
  obtain ⟨e⟩ := apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv
    φ Φ hΦ rfl hΦo
  obtain ⟨H⟩ := e.right_inv
  refine ⟨⟨e (Classical.choice (inferInstance : Nonempty (apm_t00A01_punctured φ)))⟩, ?_⟩
  intro x y
  let p : Path (e.invFun x) (e.invFun y) :=
    PathConnectedSpace.somePath (e.invFun x) (e.invFun y)
  exact ⟨(H.evalAt x).symm.trans ((p.map e.continuous).trans (H.evalAt y))⟩

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

/-- LEAF (geometry). `M` has a standard cover by the punctured piece and a
disk: `U = M \ Φ(closedBall 0 (1/2))`, homotopy equivalent to the punctured
piece by `apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv`;
`V = Φ(ball 0 2)` (`apm_t00A01_punctured_fundamentalGroup_aux_ball`), which
is contractible, hence homotopy equivalent to the closed unit disk; and
`U ∩ V = Φ(1/2 < ‖x‖ < 2)`, which retracts radially onto the unit sphere. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_cover_aux_shell :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥{x : EuclideanSpace ℝ (Fin 3) | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2}
      apm_t00A01_Sphere2) := by
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
          have h := x.2.1
          change (1 / 2 : ℝ) < ‖x.1‖ at h
          rw [hx, norm_zero] at h
          norm_num at h
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
          have h := x.2.1
          change (1 / 2 : ℝ) < ‖x.1‖ at h
          rw [hx, norm_zero] at h
          norm_num at h)).smul continuous_subtype_val }
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
        have ha0 : 0 ≤ a := add_nonneg
          (div_nonneg (sub_nonneg.mpr ht1) hxpos.le) ht0
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
          have h := tx.2.2.1
          change (1 / 2 : ℝ) < ‖tx.2.1‖ at h
          rw [hx, norm_zero] at h
          norm_num at h
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
  exact ⟨{ toFun := r, invFun := i, left_inv := ⟨H⟩, right_inv := by rw [hri] }⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_cover
    (M : Type) [TopologicalSpace M] [T2Space M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    apm_t00A01_hasStandardCover M (apm_t00A01_punctured φ) apm_t00A01_Disk3 := by
  obtain ⟨Φ, hΦ, hΦφ, hΦo⟩ := hcollar
  let U : Set M := (apm_t00A01_punctured_fundamentalGroup_aux_inner Φ)ᶜ
  let V : Set M := apm_t00A01_punctured_fundamentalGroup_aux_ball Φ
  have hU : IsOpen U := by
    haveI : CompactSpace apm_t00A01_LargeDisk3 :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    have hK : IsCompact {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ 1 / 2} :=
      (isClosed_le (continuous_subtype_val.dist continuous_const) continuous_const).isCompact
    exact (hK.image hΦ.continuous).isClosed.isOpen_compl
  have hV : IsOpen V := hΦo
  have hcover : U ∪ V = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ apm_t00A01_punctured_fundamentalGroup_aux_inner Φ
    · right
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, ?_, rfl⟩
      change dist y.1 0 < 2
      exact lt_of_le_of_lt hy (by norm_num)
    · exact Or.inl hx
  refine ⟨U, V, hU, hV, hcover, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ :=
      apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv φ Φ hΦ hΦφ hΦo
    exact ⟨e.symm⟩
  · let S : Set apm_t00A01_LargeDisk3 := {x | dist x.1 0 < 2}
    have himage : ((fun x : apm_t00A01_LargeDisk3 ↦ x.1) '' S) =
        Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change dist y.1 0 < 2 at hy
        simpa [Metric.mem_ball] using hy
      · intro hx
        have hx' : dist x 0 < 2 := by simpa [Metric.mem_ball, dist_comm] using hx
        exact ⟨⟨x, by simpa [Metric.mem_closedBall, dist_comm] using le_of_lt hx'⟩,
          hx', rfl⟩
    let e : S ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 :=
      (Topology.IsEmbedding.subtypeVal.homeomorphImage S).trans (Homeomorph.setCongr himage)
    letI : ContractibleSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2) :=
      Metric.contractibleSpace_ball (by norm_num)
    letI : ContractibleSpace S := e.contractibleSpace
    letI : ContractibleSpace V := (hΦ.homeomorphImage S).symm.contractibleSpace
    letI : ContractibleSpace apm_t00A01_Disk3 :=
      Metric.contractibleSpace_closedBall (by norm_num)
    exact ContractibleSpace.hequiv V apm_t00A01_Disk3
  · let E := EuclideanSpace ℝ (Fin 3)
    let S : Set E := {x | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2}
    let T : Set M := U ∩ V
    let f : S → T := fun x => ⟨Φ ⟨x.1, by
      simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt x.2.2⟩, by
        constructor
        · rintro ⟨y, hy, heq⟩
          have hxy : y.1 = x.1 := Subtype.ext_iff.mp (hΦ.injective heq)
          have hy' : ‖y.1‖ ≤ (1 / 2 : ℝ) := by simpa [dist_zero_right] using hy
          rw [hxy] at hy'
          exact (not_le_of_gt x.2.1) hy'
        · refine ⟨⟨x.1, ?_⟩, ?_, rfl⟩
          · simpa [Metric.mem_closedBall, dist_zero_right] using (le_of_lt x.2.2)
          · simpa [dist_zero_right] using x.2.2⟩
    have hf : Topology.IsEmbedding f := by
      let g : S → apm_t00A01_LargeDisk3 := fun x => ⟨x.1, by
        simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt x.2.2⟩
      have hg : Topology.IsEmbedding g := by
        apply Topology.IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
        exact (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (fun x : S => x.1))
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
      exact ⟨⟨x.1, hxlo, by simpa [dist_zero_right] using hx⟩, rfl⟩
    let e : S ≃ₜ T := hf.toHomeomorphOfSurjective hsurj
    obtain ⟨q⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_cover_aux_shell
    simpa [T] using (show Nonempty (ContinuousMap.HomotopyEquiv T apm_t00A01_Sphere2)
      from ⟨e.symm.toHomotopyEquiv.trans q⟩)

/-- LEAF. The closed unit three-disk is a homology ball: it is convex, hence
contractible, so it is homotopy equivalent to a point. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_disk :
    apm_t00A01_isHomologyBall apm_t00A01_Disk3 := by
  letI : ContractibleSpace apm_t00A01_Disk3 :=
    Metric.contractibleSpace_closedBall (by norm_num)
  constructor
  · let p : apm_t00A01_Disk3 := ⟨0, by simp⟩
    let q := ConstructionTargets.T02A06SphereH0.singularVertexH0Class p
    letI : Epi q :=
      ConstructionTargets.T02A06SphereH0.singularVertexH0Class_epi p
    letI : Mono q :=
      ConstructionTargets.T02A06SphereH0.singularVertexH0Class_mono p
    letI : IsIso q := isIso_of_mono_of_epi q
    exact ⟨ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of apm_t00A01_Disk3) 0
        (ModuleCat.of ℤ ℤ) (asIso q).symm⟩
  · intro k hk
    exact ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
        (TopCat.of apm_t00A01_Disk3) k
        (ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
          apm_t00A01_Disk3 k hk)

/-- LEAF (algebra). Mayer--Vietoris for a standard cover of a homology
3-sphere `X` by `A` and a homology ball `B`, overlapping in `S²`. In degree
`k = 1` and in degrees `k > 3` both `Hₖ(S²)` and `Hₖ(X)` vanish, so exactness
of `Hₖ(U ∩ V) → Hₖ(U) ⊕ Hₖ(V) → Hₖ(X)` forces `Hₖ(U) = 0`, and `U ≃ A`.
The same Mayer--Vietoris interfaces as in
`apm_t00A01_bridge_connectedSum_isHomology3Sphere` apply. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mv
    (X A B : Type) [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (hX : apm_t00A01_isHomology3Sphere X) (hB : apm_t00A01_isHomologyBall B)
    (hcover : apm_t00A01_hasStandardCover X A B)
    (k : ℕ) (hk : k = 1 ∨ 3 < k) :
    Limits.IsZero (apm_t00A01_H k A) := by
  open ConstructionTargets.ProductionOpenCoverMayerVietoris in
   open ConstructionTargets.T00A01MayerVietorisAdapters in
   open ConstructionTargets.IntegralSingularHomologyComparison in
   open ConstructionTargets.SingularHomologyConcrete in
   open ConstructionTargets.SphereHomology in
   rcases hcover with ⟨U, V, hU, hV, hUV, ⟨eUA⟩, ⟨eVB⟩, ⟨eIS⟩⟩
   rcases hX with ⟨-, -, hXz⟩
   rcases hB with ⟨-, hBz⟩
   have hk0 : k ≠ 0 := by omega
   have hk2 : k ≠ 2 := by omega
   have hk3 : k ≠ 3 := by omega
   have hIz : Limits.IsZero
       (SingularHomology k (TopCat.of (U ∩ V : Set X))) :=
     (groupHomologyIsZeroOfModuleHomologyIsZero
       (TopCat.of apm_t00A01_Sphere2) k
       (sphereModuleHomology_isZero_of_ne_zero_top 2 k hk0 hk2)).of_iso
       (singularHomologyIsoOfHomotopyEquiv eIS k)
   have hXzg : Limits.IsZero
       (SingularHomology k (TopCat.of X)) :=
     groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of X) k (hXz k hk0 hk3)
   have hpieces : Limits.IsZero
       (SingularHomology k (TopCat.of U) ⊞
        SingularHomology k (TopCat.of V)) :=
     (productionMayerVietoris_exact_pieces U V hU hV hUV k).isZero_X₂
       (hIz.eq_of_src _ _) (hXzg.eq_of_tgt _ _)
   have hUg : Limits.IsZero
       (SingularHomology k (TopCat.of U)) :=
     ((Limits.biprod_isZero_iff _ _).mp hpieces).1
   have hUm : Limits.IsZero (apm_t00A01_H k U) :=
     singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of U) k hUg
   exact hUm.of_iso (moduleHomologyIsoOfHomotopyEquiv eUA k).symm

/-- LEAF (algebra, independent of the manifold argument).  If the degree-two
connecting map for a standard cover is an isomorphism, exactness and the
known homology of the union, overlap, and right-hand piece force the
left-hand piece to vanish in degrees two and three. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_algebra
    (X A B : Type) [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (hX : apm_t00A01_isHomology3Sphere X) (hB : apm_t00A01_isHomologyBall B)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (eUA : ContinuousMap.HomotopyEquiv U A)
    (eVB : ContinuousMap.HomotopyEquiv V B)
    (eIS : ContinuousMap.HomotopyEquiv (U ∩ V : Set X) apm_t00A01_Sphere2)
    (hconn : IsIso
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionConnecting
        U V hU hV hUV 2))
    (k : ℕ) (hk : k = 2 ∨ k = 3) :
    Limits.IsZero (apm_t00A01_H k A) := by
  open ConstructionTargets.ProductionOpenCoverMayerVietoris in
   open ConstructionTargets.T00A01MayerVietorisAdapters in
   open ConstructionTargets.IntegralSingularHomologyComparison in
   open ConstructionTargets.SingularHomologyConcrete in
   open ConstructionTargets.SphereHomology in
   open ConstructionTargets.MayerVietorisExactnessIsZero in
   rcases hX with ⟨-, -, hXz⟩
   rcases hB with ⟨-, hBz⟩
   haveI : IsIso (productionConnecting U V hU hV hUV 2) := hconn
   have hI3 : Limits.IsZero (SingularHomology 3 (TopCat.of (U ∩ V : Set X))) :=
     (groupHomologyIsZeroOfModuleHomologyIsZero
       (TopCat.of apm_t00A01_Sphere2) 3
       (sphereModuleHomology_isZero_of_ne_zero_top 2 3 (by omega) (by omega))).of_iso
       (singularHomologyIsoOfHomotopyEquiv eIS 3)
   have hV3 : Limits.IsZero (SingularHomology 3 (TopCat.of V)) :=
     (groupHomologyIsZeroOfModuleHomologyIsZero
       (TopCat.of B) 3 (hBz 3 (by omega))).of_iso
       (singularHomologyIsoOfHomotopyEquiv eVB 3)
   have hV2 : Limits.IsZero (SingularHomology 2 (TopCat.of V)) :=
     (groupHomologyIsZeroOfModuleHomologyIsZero
       (TopCat.of B) 2 (hBz 2 (by omega))).of_iso
       (singularHomologyIsoOfHomotopyEquiv eVB 2)
   have hX2 : Limits.IsZero (SingularHomology 2 (TopCat.of X)) :=
     groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of X) 2
       (hXz 2 (by omega) (by omega))
   have finish (n : ℕ) (hU : Limits.IsZero (SingularHomology n (TopCat.of U))) :
       Limits.IsZero (apm_t00A01_H n A) :=
     (singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of U) n hU).of_iso
       (moduleHomologyIsoOfHomotopyEquiv eUA n).symm
   rcases hk with rfl | rfl
   · have hinter : productionIntersectionArrow U V 2 = 0 := by
       exact (productionMayerVietoris_exact_intersection U V hU hV hUV 2).epi_f_iff.mp
         (by infer_instance)
     have hreassembly : productionReassemblyArrow U V 2 = 0 :=
       hX2.eq_of_tgt _ _
     have hpieces := (productionMayerVietoris_exact_pieces U V hU hV hUV 2).isZero_X₂
       hinter hreassembly
     exact finish 2 ((Limits.biprod_isZero_iff _ _).mp hpieces).1
   · have hpieces : Limits.IsZero
         (SingularHomology 3 (TopCat.of U) ⊞ SingularHomology 3 (TopCat.of V)) := by
       apply isZero_middle_of_two_exact_of_isZero_left_of_mono_right
         (productionIntersectionArrow U V 3)
         (productionReassemblyArrow U V 3)
         (productionConnecting U V hU hV hUV 2)
         _ _
         (productionMayerVietoris_exact_pieces U V hU hV hUV 3)
         (productionMayerVietoris_exact_union U V hU hV hUV 2) hI3
     exact finish 3 ((Limits.biprod_isZero_iff _ _).mp hpieces).1

/-- LIBRARY LEAF (global fundamental class plus collar comparison).  For the
specific standard cover supplied by the collar, its Mayer--Vietoris boundary
`H₃(M) → H₂(U ∩ V)` is an isomorphism.  This is the exact formal boundary
left by the missing global-to-local fundamental-class theorem and the
comparison of its localization map with the open-cover connecting map. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_source
    (M : Type) [TopologicalSpace M]
    (hM : apm_t00A01_isHomology3Sphere M) :
    Nonempty ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of M)).homology 3 ≅ AddCommGrpCat.of ℤ) := by
  open ConstructionTargets.IntegralSingularHomologyComparison in
    rcases hM.2.1 with ⟨e⟩
    exact ⟨(singularHomologyComparison (TopCat.of M) 3).symm ≪≫
      (forgetIntModules.mapIso e)⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_target
    {M : Type} [TopologicalSpace M] (U V : Set M)
    (eIS : ContinuousMap.HomotopyEquiv (U ∩ V : Set M) apm_t00A01_Sphere2) :
    Nonempty ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of (U ∩ V : Set M))).homology 2 ≅ AddCommGrpCat.of ℤ) := by
  open ConstructionTargets.SingularHomologyConcrete in
   open ConstructionTargets.SphereHomology in
    exact ⟨singularHomologyIsoOfHomotopyEquiv eIS 2 ≪≫
      sphereTopHomologyIsoInt 2 (by omega)⟩

/-- LIBRARY: the top-dimensional global class of a closed connected
three-manifold restricts to a generator of local homology at every point. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_coeff
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) :
    ∃ r : ℤ, r •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) x =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 hM.2.1.some) := by
  simpa using
    (ConstructionTargets.ManifoldFundamentalClass.localizationMap_groupGlobalGenerator_eq_zsmul_ambientLocalGenerator
        1 hM.2.1.some x)

/-- The local degree of the global generator at `y`: its image in
`H₃(M, M ∖ y)`, read through the chart normalization of that group as `ℤ`. -/
noncomputable def apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hM : apm_t00A01_isHomology3Sphere M) (y : M) : ℤ :=
  (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 y).hom.hom
    (ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3
      (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 hM.2.1.some))

/-- PROVED: the coefficient `r` of `hr` is the local degree at `x`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree_spec
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) (r : ℤ)
    (hr : r •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) x =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 hM.2.1.some)) :
    r = apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM x := by
  have h := congrArg
    (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 x).hom.hom hr
  rw [map_zsmul,
    ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator] at h
  change r * (1 : ℤ) = _ at h
  rw [mul_one] at h
  exact h

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_natAbs_eq
    (a b : ℤ) (h : a = b ∨ a = -b) : a.natAbs = b.natAbs := by
  rcases h with h | h
  · exact congrArg Int.natAbs h
  · rw [h, Int.natAbs_neg]

/-- PROVED: two identifications of one group with `ℤ` differ by a unit `±1`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_units
    {G : AddCommGrpCat} (f g : G ≅ AddCommGrpCat.of ℤ) (a : G) :
    f.hom.hom a = g.hom.hom a ∨ f.hom.hom a = -g.hom.hom a := by
  let e : AddCommGrpCat.of ℤ ≅ AddCommGrpCat.of ℤ := g.symm ≪≫ f
  have hmul : ∀ (h : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (n : ℤ),
      h.hom n = n * h.hom 1 := fun h n => by
    have := h.hom.map_zsmul 1 n
    simpa [smul_eq_mul] using this
  have h1 : e.inv.hom (e.hom.hom 1) = 1 := ConcreteCategory.congr_hom e.hom_inv_id 1
  rw [hmul e.inv] at h1
  have hu : IsUnit (e.hom.hom 1) := ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hf : f.hom.hom a = e.hom.hom (g.hom.hom a) := by
    have : g.inv.hom (g.hom.hom a) = a := ConcreteCategory.congr_hom g.hom_inv_id a
    change f.hom.hom a = f.hom.hom (g.inv.hom (g.hom.hom a))
    rw [this]
  rw [hf, hmul e.hom]
  rcases Int.isUnit_iff.1 hu with h | h
  · left; rw [h, mul_one]
  · right; rw [h, mul_neg_one]

/-- PROVED: the identity of `M` sends `M ∖ K` into `M ∖ z` when `z ∈ K`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
    {M : Type} [TopologicalSpace M] (K : Set M) (z : M) (hz : z ∈ K) :
    Set.MapsTo (ContinuousMap.id M) Kᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) :=
  fun y hy hyz => hy (by
    have hyz' : y = z := hyz
    exact hyz' ▸ hz)

/-- PROVED: for `z ∈ K`, localization at `z` factors through `H_n(M, M ∖ K)`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_factor
    {M : Type} [TopologicalSpace M] (K : Set M) (z : M) (hz : z ∈ K) (n : ℕ) :
    ConstructionTargets.ManifoldFundamentalClass.localizationMap z n =
      HomologicalComplex.homologyMap
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ) n ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
            (ContinuousMap.id M)
            (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
              K z hz)) n := by
  have h := ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality Kᶜ
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) (ContinuousMap.id M)
    (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
      K z hz)
  have hid : (TopCat.ofHom (ContinuousMap.id M) : TopCat.of M ⟶ TopCat.of M) = 𝟙 _ := rfl
  have hab : ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap
      (ContinuousMap.id M) = 𝟙 _ := by
    simp [ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap, hid]
  have h' : ConstructionTargets.ManifoldFundamentalClass.absoluteSingularMap (ContinuousMap.id M) ≫
      ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) =
    ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ ≫
      ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z) (ContinuousMap.id M)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          K z hz) := h
  rw [hab, Category.id_comp] at h'
  show HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)) n = _
  rw [h', HomologicalComplex.homologyMap_comp]

/-- PROVED (lemma-1, banked from its `_aux_ball` PARTIAL, 2026-10-20): excision
of a closed set inside the interior of `Kᶜ` is an isomorphism on `H₃`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_excision
    {X : Type} [TopologicalSpace X] (K U : Set X)
    (hU : IsOpen U) (hKU : Uᶜ ⊆ interior Kᶜ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeExcisionMap Kᶜ Uᶜ) 3) := by
  exact ConstructionTargets.SingularExcision.relativeExcisionMap_homologyMap_isIso_succ
    Kᶜ Uᶜ hU.isClosed_compl hKU 2

/-- PROVED (lemma-1, banked from its `_aux_ball` PARTIAL, 2026-10-20): a
homeomorphism of pairs induces an isomorphism on relative `H₃`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_chart
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap A B
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap e)
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
          e A B hAB)) 3) := by
  exact ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularMap_homeomorphPair_isIso
    e A B hAB 3

/-- LEAF (split from `_convex_aux_inj_aux_model` after lemma-1's PARTIAL,
job 181, 2026-10-20): radial deformation.  For compact convex `K ⊆ ℝ³` and
`u ∈ K`, the inclusion `ℝ³ ∖ K ↪ ℝ³ ∖ u` is a homotopy equivalence.  Route:
pick `R` with `K ⊆ ball u R` (`_aux_bounding_ball`) and let
`ρ p = u + R • (p - u) / ‖p - u‖`.  For `p ∉ K` the segment from `p` to `ρ p`
avoids `K`: the ray from `u` through `p` meets `K` in an interval containing
`u` (convexity) and `p` lies beyond it.  So `ρ : ℝ³ ∖ u → ℝ³ ∖ K` is a homotopy
inverse of the inclusion: on both sides the straight-line homotopy to `ρ`
stays in the complement. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_hequiv
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : EuclideanSpace ℝ (Fin 3)) (hu : u ∈ K) :
    ∃ e : ContinuousMap.HomotopyEquiv (Kᶜ : Set (EuclideanSpace ℝ (Fin 3)))
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u),
      ∀ x, ((e.toFun x : EuclideanSpace ℝ (Fin 3))) = (x : EuclideanSpace ℝ (Fin 3)) := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 1 u
  let j : C((Kᶜ : Set (EuclideanSpace ℝ (Fin 3))),
      ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u) :=
    { toFun := fun x => ⟨x.1, by
        intro hx
        apply x.2
        have : x.1 = u := by
          simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint] using hx
        simpa [this] using hu⟩
      continuous_toFun := by fun_prop }
  let ρ : C(ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u,
      (Kᶜ : Set (EuclideanSpace ℝ (Fin 3)))) :=
    { toFun := fun x => ⟨u + (1 + R / ‖x.1 - u‖) • (x.1 - u), by
        intro hxK
        have hxne : x.1 - u ≠ 0 := sub_ne_zero.mpr (by
          intro hxu
          exact x.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint,
            hxu]))
        have hn : 0 < ‖x.1 - u‖ := norm_pos_iff.mpr hxne
        have ha : 0 ≤ 1 + R / ‖x.1 - u‖ := by positivity
        have hdist : dist (u + (1 + R / ‖x.1 - u‖) • (x.1 - u)) u =
            ‖x.1 - u‖ + R := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg ha]
          field_simp
        have hb := hKR hxK
        rw [Metric.mem_ball, hdist] at hb
        linarith⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hv : Continuous (fun x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u =>
            x.1 - u) := continuous_subtype_val.sub continuous_const
        have hn : Continuous (fun x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u =>
            ‖x.1 - u‖) := continuous_norm.comp hv
        have hn0 : ∀ x : ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u,
            ‖x.1 - u‖ ≠ 0 := fun x => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
              intro hxu
              exact x.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint,
                hxu])))
        exact continuous_const.add
          ((continuous_const.add (continuous_const.div hn hn0)).smul hv) }
  let Hout : ContinuousMap.Homotopy (j.comp ρ) (ContinuousMap.id _) :=
    { toFun := fun tx => ⟨(1 - (tx.1 : ℝ)) • ((j.comp ρ) tx.2).1 +
          (tx.1 : ℝ) • tx.2.1, by
        intro heq
        have hxne : tx.2.1 ≠ u := by
          intro hx
          exact tx.2.2 (by simpa [ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint, hx])
        have hvne : tx.2.1 - u ≠ 0 := sub_ne_zero.mpr hxne
        have hn : 0 < ‖tx.2.1 - u‖ := norm_pos_iff.mpr hvne
        have hcoef : 0 < (1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) + (tx.1 : ℝ) := by
          have ht0 := tx.1.2.1
          have ht1 := tx.1.2.2
          have : 0 < R := lt_trans (by norm_num) hR
          have hq : 0 ≤ R / ‖tx.2.1 - u‖ := by positivity
          nlinarith
        apply hvne
        have hzero : ((1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) +
            (tx.1 : ℝ)) • (tx.2.1 - u) = 0 := by
          calc
            _ = (1 - (tx.1 : ℝ)) • ((j.comp ρ) tx.2).1 +
                (tx.1 : ℝ) • tx.2.1 - u := by dsimp [j, ρ]; module
            _ = 0 := sub_eq_zero.mpr heq
        exact (smul_eq_zero.mp hzero).resolve_left hcoef.ne'⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp [j, ρ]
      map_one_left := by intro x; apply Subtype.ext; simp }
  let Hin : ContinuousMap.Homotopy (ρ.comp j) (ContinuousMap.id _) :=
    { toFun := fun tx => ⟨(1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
          (tx.1 : ℝ) • tx.2.1, by
        intro hz
        have ht0 : 0 ≤ (tx.1 : ℝ) := tx.1.2.1
        have ht1 : (tx.1 : ℝ) ≤ 1 := tx.1.2.2
        have hvne : tx.2.1 - u ≠ 0 := sub_ne_zero.mpr (by
          intro hxu
          exact tx.2.2 (by simpa [hxu] using hu))
        have hn : 0 < ‖tx.2.1 - u‖ := norm_pos_iff.mpr hvne
        let c : ℝ := (1 - (tx.1 : ℝ)) * (1 + R / ‖tx.2.1 - u‖) + (tx.1 : ℝ)
        have hc : 1 ≤ c := by
          dsimp [c]
          have hRp : 0 ≤ R / ‖tx.2.1 - u‖ := by positivity
          nlinarith
        have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
        have hzform : (1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
              (tx.1 : ℝ) • tx.2.1 = u + c • (tx.2.1 - u) := by
          dsimp [c, ρ, j]
          module
        have hp : tx.2.1 = (1 - c⁻¹) • u + c⁻¹ •
            ((1 - (tx.1 : ℝ)) • ((ρ.comp j) tx.2).1 +
              (tx.1 : ℝ) • tx.2.1) := by
          rw [hzform]
          rw [smul_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
          module
        have hc_inv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
        have hc_sub : 0 ≤ 1 - c⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hc0).2 hc)
        have hmem := hconv hu hz hc_sub hc_inv (by ring)
        exact tx.2.2 (hp.symm ▸ hmem)⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp [ρ, j]
      map_one_left := by intro x; apply Subtype.ext; simp }
  refine ⟨{ toFun := j, invFun := ρ, left_inv := ⟨Hin⟩, right_inv := ⟨Hout⟩ }, ?_⟩
  intro x
  rfl

/-- PROVED (lemma-1, job 181, 2026-10-20). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_bounding_ball
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ R : ℝ, 1 < R ∧ K ⊆ Metric.ball u R := by
  exact hK.isBounded.subset_ball_lt 1 u

/-- PROVED from `_aux_hequiv` (claude-14, 2026-10-20): the inclusion of
complements induces isomorphisms on singular homology in every degree. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_sub
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : EuclideanSpace ℝ (Fin 3)) (hu : u ∈ K) (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (ConstructionTargets.SingularExcision.subspaceMap Kᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
          (ContinuousMap.id (EuclideanSpace ℝ (Fin 3)))
          (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu))) i) := by
  obtain ⟨e, he⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_hequiv K hK hconv u hu
  have hmap : ConstructionTargets.SingularExcision.subspaceMap Kᶜ
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
      (ContinuousMap.id (EuclideanSpace ℝ (Fin 3)))
      (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu) = TopCat.ofHom e.toFun := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (he x).symm
  change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat i).obj
    (AddCommGrpCat.of ℤ)).map _)
  rw [hmap, ← ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom e i]
  infer_instance

/-- PROVED from `_aux_model_aux_hequiv` (claude-14, 2026-10-20; split from
`_convex_aux_inj` after lemma-1's PARTIAL): the convex model in `ℝ³`.  For compact convex `K ⊆ ℝ³` and
`u ∈ K`, the identity induces an isomorphism
`H_(n+1)(ℝ³, ℝ³ ∖ K) → H_(n+1)(ℝ³, ℝ³ ∖ u)`.  Route: pick `R` with
`K ⊆ ball u R`.  For `p ∉ K` the ray from `u` through `p` meets `K` in an
interval containing `u` (convexity), so the straight-line homotopy from `p` to
`u + R • (p - u) / ‖p - u‖` stays outside `K`; the same formula deformation
retracts `ℝ³ ∖ u` onto that sphere.  Hence `ℝ³ ∖ K ↪ ℝ³ ∖ u` is a homotopy
equivalence; `ℝ³` is contractible; the five lemma on the long exact sequences
of the two pairs gives the iso.  `_ball_aux_model` is the case
`K = closedBall c r`, `n = 2`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : EuclideanSpace ℝ (Fin 3)) (hu : u ∈ K) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
        (ContinuousMap.id (EuclideanSpace ℝ (Fin 3)))
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K u hu)) (n + 1)) := by
  have hamb : ∀ j, IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (ContinuousMap.id (EuclideanSpace ℝ (Fin 3))))) j) := by
    intro j
    change IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin 3))))) j)
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
    infer_instance
  apply ConstructionTargets.SingularExcision.relativeSingularMap_homologyMap_isIso
  · exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_sub K hK hconv u hu (n + 1)
  · exact hamb (n + 1)
  · intro j _
    exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model_aux_sub K hK hconv u hu j
  · intro j _
    exact hamb j

/-- PROVED from `_convex_aux_inj_aux_model` (claude-14, 2026-10-20; split from
`_aux_ball` after lemma-1's PARTIAL): moving a puncture inside a closed ball of `ℝ³`.  For `u` in the open ball
`ball c r`, the identity induces an isomorphism
`H₃(ℝ³, ℝ³ ∖ closedBall c r) → H₃(ℝ³, ℝ³ ∖ u)`.  Route: `ℝ³ ∖ closedBall c r`
and `ℝ³ ∖ u` both deformation retract radially (about `u`) onto the sphere of
radius `R = r + 1` about `u`, so the inclusion `ℝ³ ∖ closedBall c r ↪ ℝ³ ∖ u`
is a homotopy equivalence; `ℝ³` is contractible; the five lemma on the long
exact sequences of the two pairs gives the iso in degree 3. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_model
    (c u : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hu : dist u c < r) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (Metric.closedBall c r)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint u)
        (ContinuousMap.id (EuclideanSpace ℝ (Fin 3)))
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          (Metric.closedBall c r) u (Metric.mem_closedBall.2 hu.le))) 3) := by
  exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model (Metric.closedBall c r) (isCompact_closedBall c r)
    (convex_closedBall c r) u (Metric.mem_closedBall.2 hu.le) 2

/-- LIBRARY LEAF (split from `_aux_ball` after lemma-1's PARTIAL, 2026-10-20):
reduction of `_aux_ball` to the model.  Let `e` be the chart at `x` and
`closedBall (e x) r ⊆ e.target`; put `K = e.source ∩ e ⁻¹' closedBall (e x) r`
(`= e.symm '' closedBall`, compact, so closed in `M`).  For `z` in the chart
source with `e z ∈ ball (e x) r`, the identity induces an isomorphism
`H₃(M, M ∖ K) → H₃(M, M ∖ z)`.  Route: both pairs excise `M ∖ e.source`
(`_aux_excision`, as in `neighborhoodInclusion_Hsucc_isIso`); the chart
`e.source ≃ₜ e.target` transports the excised pairs (`_aux_chart`); the
inclusion `e.target ↪ ℝ³` excises `ℝ³ ∖ e.target` (`_aux_excision` again,
`closedBall ⊆ e.target`); the resulting map is `_aux_model` with `c = e x`,
`u = e z`.  The squares commute by naturality of `relativeSingularMap`
(`relativeSingularMap_comp`). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_reduce
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (x : M) (r : ℝ)
    (hr : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 3)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 3)) x).target)
    (z : M) (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source)
    (hzr : dist (chartAt (EuclideanSpace ℝ (Fin 3)) x z) (chartAt (EuclideanSpace ℝ (Fin 3)) x x) < r) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap ((chartAt (EuclideanSpace ℝ (Fin 3)) x).source ∩
          chartAt (EuclideanSpace ℝ (Fin 3)) x ⁻¹' Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 3)) x x) r)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
        (ContinuousMap.id M)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          ((chartAt (EuclideanSpace ℝ (Fin 3)) x).source ∩
          chartAt (EuclideanSpace ℝ (Fin 3)) x ⁻¹' Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 3)) x x) r) z ⟨hz, Metric.mem_closedBall.2 hzr.le⟩)) 3) := by
  sorry

/-- PROVED from `_aux_reduce` (split after lemma-1's PARTIAL, 2026-10-20).
Near `x` there is a set `K`, the chart preimage of a closed ball about the
chart point of `x` lying in the chart target, such that, for every `z` near
`x`, `z ∈ K` and the map `H₃(M, M ∖ K) → H₃(M, M ∖ z)` induced by the identity
is an isomorphism.  `K` is not `M`: that would make the statement the
orientability of `M`, which is what this chain is proving. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_ball
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (x : M) :
    ∃ K : Set M, ∀ᶠ z in nhds x, ∃ hz : z ∈ K,
      IsIso (HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
          (ContinuousMap.id M)
          (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
            K z hz)) 3) := by
  set e := chartAt (EuclideanSpace ℝ (Fin 3)) x
  obtain ⟨r, hr0, hr⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (e.open_target.mem_nhds (mem_chart_target (EuclideanSpace ℝ (Fin 3)) x))
  refine ⟨e.source ∩ e ⁻¹' Metric.closedBall (e x) r, ?_⟩
  have hev : ∀ᶠ z in nhds x, z ∈ e.source ∩ e ⁻¹' Metric.ball (e x) r :=
    (e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball).mem_nhds
      ⟨mem_chart_source (EuclideanSpace ℝ (Fin 3)) x, Metric.mem_ball_self hr0⟩
  filter_upwards [hev] with z hz
  exact ⟨⟨hz.1, Metric.ball_subset_closedBall hz.2⟩, apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_ball_aux_reduce M x r hr z hz.1 hz.2⟩

/-- PROVED from `_aux_ball`, `_aux_factor` and `_aux_units`: near each `x`, the
local degree at `y` is `±` the local degree at `x`.  Both localizations factor
through `H₃(M, M ∖ K)`; composing each iso `H₃(M, M ∖ K) ≅ H₃(M, M ∖ z)` with
the chart normalization gives two identifications of `H₃(M, M ∖ K)` with `ℤ`,
which differ by `±1`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) :
    ∀ᶠ y in nhds x, apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM y = apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM x ∨
      apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM y = -apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM x := by
  obtain ⟨K, hK⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_ball M x
  obtain ⟨hxK, hxI⟩ := hK.self_of_nhds
  let c := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection Kᶜ) 3
    (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
      (TopCat.of M) 3 hM.2.1.some)
  have key : ∀ (w : M) (hw : w ∈ K) [IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint w)
        (ContinuousMap.id M)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
          K w hw)) 3)],
      apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM w =
        (asIso (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint w)
            (ContinuousMap.id M)
            (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo
              K w hw)) 3) ≪≫
          ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 w).hom.hom c := by
    intro w hw _
    unfold apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree
    rw [apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_factor
      K w hw 3]
    rfl
  refine hK.mono fun z hz => ?_
  obtain ⟨hzK, hzI⟩ := hz
  rw [key z hzK, key x hxK]
  exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_units _ _ c

/-- PROVED from `_aux_eventually_sign` (orientation double cover is locally trivial): the absolute
local degree `|deg_y|` is locally constant in `y`.  Near `y`, a chart ball `B`
gives `H₃(M) → H₃(M, M ∖ B) ≅ H₃(M, M ∖ z)` for every `z ∈ B`
(`neighborhoodInclusion_Hsucc_isIso`, `localizationMap_naturality`), and the
chart normalizations at `y` and `z` differ by a transition unit `±1`
(`integralOverlapTransitionUnit_eq_one_or_neg_one`). True for every closed
3-manifold, orientable or not. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) :
    IsLocallyConstant (fun y : M => (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM y).natAbs) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  exact (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign M hM x).mono fun y hy =>
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_natAbs_eq _ _ hy

/-- `A` is good for `M` (Hatcher Lemma 3.27, integer coefficients):
`H_i(M, M ∖ A)` vanishes above degree 3, and a class of `H₃(M, M ∖ A)` whose
image in `H₃(M, M ∖ y)` vanishes for every `y ∈ A` is zero.  Split from
`_aux_injective` after lemma-1's PARTIAL (2026-10-20), whose leaf `_aux_detect`
was the contrapositive of `_aux_injective`. -/
def apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good (M : Type) [TopologicalSpace M] (A : Set M) : Prop :=
  (∀ i : ℕ, 3 < i → Subsingleton
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i)) ∧
    ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology 3,
      (∀ (y : M) (hy : y ∈ A),
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) 3 c = 0) →
      c = 0

/-- PROVED (lemma-1, banked from its `_aux_convex` PARTIAL, 2026-10-20): the
empty set is good (last line fixed by claude-14). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_empty
    (M : Type) [TopologicalSpace M] :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M ∅ := by
  constructor
  · intro i hi
    have hz :=
      ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero M i
    simpa using (AddCommGrpCat.isZero_iff_subsingleton.mp hz)
  · intro c hc
    have hz :=
      ConstructionTargets.SingularHomologyConcrete.selfRelativeSingularHomology_isZero M 3
    have hz' : IsZero
        ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (∅ : Set M)ᶜ).homology 3) := by
      simpa using hz
    exact @Subsingleton.elim _ (AddCommGrpCat.isZero_iff_subsingleton.mp hz') c 0

/-- LIBRARY LEAF (Hatcher 3.27, point case of the vanishing): in a 3-manifold,
`H_i(M, M ∖ y) = 0` for `i > 3`.  Split from `_aux_convex` after lemma-1's
PARTIAL (2026-10-20).  Route: excise `M ∖ U` for a chart ball `U` about `y`
(`HigherChartLocalGenerator.ambientChartMap_Hn_isIso` does this transport for
the top degree; the same excision works in every degree), then
`H_i(D, D ∖ 0) ≅ H_{i-1}(D ∖ 0)` for `i ≥ 2` by the pair sequence of the
contractible disk, and `D ∖ 0 ≃ S²` has no homology above degree 2
(`SphereHomology`). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_point
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (y : M) (i : ℕ) (hi : 3 < i) :
    Subsingleton ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)).homology i) := by
  open ConstructionTargets.SingularHomologyConcrete
    ConstructionTargets.SingularExcision
    ConstructionTargets.LocalHomologyNeighborhoodExcision
    ConstructionTargets.T02A06HemisphereExcision
    ConstructionTargets.T02A06DiskRadialComparison
    ConstructionTargets.SphereHomology
    ConstructionTargets.ChartPairRelativeHomologyTransport
    ConstructionTargets.HigherChartLocalGenerator in
  have hmodel : Limits.IsZero
      ((RelativeSingularChains (P 1)).homology i) := by
    have hamb : Limits.IsZero
        ((SingularChains (TopCat.of (D 1))).homology i) := by
      letI : ContractibleSpace (D 1) := Metric.contractibleSpace_ball (by norm_num)
      exact contractibleHigherHomology_isZero _ i (by omega)
    have hpunct : Limits.IsZero
        ((SingularChains (TopCat.of (P 1))).homology (i - 1)) := by
      exact (sphereHomology_isZero_of_gt 2 (i - 1) (by omega)).of_iso
        (singularHomologyIsoOfHomotopyEquiv
          (sphereHomotopyEquivPuncturedOpenDisk 3) (i - 1)).symm
    have hi' : i - 1 + 1 = i := by omega
    rw [← hi'] at hamb
    have hz := (singularPairHomology_exact_relative (P 1) (i - 1)).isZero_X₂
      (hamb.eq_of_src _ _) (hpunct.eq_of_tgt _ _)
    simpa [hi'] using hz
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap (P 1) (deletedPoint y)
      (ambientChartMap (k := 1) y) (ambientChartMap_mapsTo (k := 1) y)) i
  have hf : IsIso f := by
    letI := relativeSingularMap_homeomorphPair_isIso (modelChart (k := 1) y) (P 1)
      (neighborhoodDeletedPoint (chartNeighborhood (k := 1) y) y)
      (modelChart_deletedPoint_iff (k := 1) y) i
    have hn : IsIso (HomologicalComplex.homologyMap
        (relativeSingularMap
          (neighborhoodDeletedPoint (chartNeighborhood (k := 1) y) y)
          (deletedPoint y) (neighborhoodInclusion (chartNeighborhood (k := 1) y))
          (neighborhoodInclusion_mapsTo (chartNeighborhood (k := 1) y) y)) i) := by
      have hn' := neighborhoodInclusion_Hn_isIso (i - 2)
        (chartNeighborhood (k := 1) y) y (chartNeighborhood_open (k := 1) y)
        (mem_chartNeighborhood (k := 1) y)
      rw [show i - 2 + 2 = i by omega] at hn'
      exact hn'
    letI := hn
    change IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (P 1) (deletedPoint y)
        (ambientChartMap (k := 1) y) (ambientChartMap_mapsTo (k := 1) y)) i)
    rw [ambientChartMap_chain_eq (k := 1), HomologicalComplex.homologyMap_comp]
    infer_instance
  letI := hf
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (hmodel.of_iso (asIso f).symm)

/-- LEAF (split from `_convex_aux_inj` after lemma-1's PARTIAL, 2026-10-20):
reduction to the convex model.  For compact `A` in the chart at `x` with
convex chart image and `y ∈ A`, the localization
`H_i(M, M ∖ A) → H_i(M, M ∖ y)` is an isomorphism for `i > 0`.  Route, as in
`_ball_aux_reduce`: both pairs excise `M ∖ e.source` (`_aux_excision`; `A` is
compact, hence closed); the chart `e.source ≃ₜ e.target` transports the excised
pairs (`_aux_chart`); the inclusion `e.target ↪ ℝ³` excises `ℝ³ ∖ e.target`
(`e '' A` is compact inside the open `e.target`); the resulting map is
`_convex_aux_inj_aux_model` with `K = e '' A`, `u = e y`.  The squares commute
by `relativeSingularMap_comp`.  `_aux_excision` and `_aux_chart` are stated in
degree 3; the ConstructionTargets theorems they call
(`relativeExcisionMap_homologyMap_isIso_succ`,
`relativeSingularMap_homeomorphPair_isIso`) take any degree `n + 1`. -/
-- BEGIN SEAT AREA
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso_aux_excision
    {X : Type} [TopologicalSpace X] (K U : Set X)
    (hU : IsOpen U) (hKU : Uᶜ ⊆ interior Kᶜ) (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeExcisionMap Kᶜ Uᶜ) i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact ConstructionTargets.SingularExcision.relativeExcisionMap_homologyMap_isIso_succ
    Kᶜ Uᶜ hU.isClosed_compl hKU n

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso_aux_chart
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap A B
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap e)
        (ConstructionTargets.ChartPairRelativeHomologyTransport.pairContinuousMap_mapsTo
          e A B hAB)) i) := by
  exact ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularMap_homeomorphPair_isIso
    e A B hAB i

/-- LIBRARY LEAF (split by claude-14 from `_inj_aux_isIso` after lemma-1's PARTIAL,
job 200, 2026-10-21): localization can be computed in an open subspace.  For open
`U ⊆ X` and closed `B ⊆ A ⊆ U`, the identity `H_i(X, X ∖ A) → H_i(X, X ∖ B)` is an
isomorphism iff the identity `H_i(U, U ∖ A) → H_i(U, U ∖ B)` is.  Route: the inclusion
`U ↪ X` gives a commuting square (`relativeSingularMap_comp`, both composites are the
inclusion); its two vertical maps are excisions of `X ∖ U` (`_aux_excision`, after the
identification `U ≃ₜ (Uᶜ)ᶜ` as in `neighborhoodInclusion_chain_eq`), so both are
isomorphisms for `i > 0`, and two-out-of-three gives the iff. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso_aux_restrict
    {X : Type} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAU : A ⊆ U) (hBA : B ⊆ A)
    (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ Bᶜ
        (ContinuousMap.id X) (fun _ hx hb => hx (hBA hb))) i) ↔
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        {u : U | u.1 ∉ A} {u : U | u.1 ∉ B}
        (ContinuousMap.id U) (fun _ hx hb => hx (hBA hb))) i) := by
  sorry

/-- LIBRARY LEAF (split by claude-14 from `_inj_aux_isIso` after lemma-1's PARTIAL,
job 200, 2026-10-21): localization is invariant under homeomorphism.  If
`e : X ≃ₜ Y` carries `A` to `A'` and `B` to `B'`, the identity
`H_i(X, A) → H_i(X, B)` is an isomorphism iff `H_i(Y, A') → H_i(Y, B')` is.
Route: the square with horizontal maps the pair homeomorphisms
(`_aux_chart`, isomorphisms in every degree) commutes by `relativeSingularMap_comp`
(both composites are `e`); two-out-of-three. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso_aux_homeo
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (A B : Set X) (A' B' : Set Y)
    (hA : ∀ x, x ∈ A ↔ e x ∈ A') (hB : ∀ x, x ∈ B ↔ e x ∈ B')
    (hAB : Set.MapsTo (ContinuousMap.id X) A B)
    (hAB' : Set.MapsTo (ContinuousMap.id Y) A' B') (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap A B
        (ContinuousMap.id X) hAB) i) ↔
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap A' B'
        (ContinuousMap.id Y) hAB') i) := by
  sorry

/-- LIBRARY LEAF (split by claude-14 from `_inj_aux_isIso` after lemma-1's PARTIAL,
job 200, 2026-10-21): the chart reduction shared by `_inj_aux_isIso` and
`_ball_aux_reduce`.  For compact `K` in the chart source of `e = chartAt x` and
`z ∈ K`, if `H_i(ℝ³, ℝ³ ∖ e '' K) → H_i(ℝ³, ℝ³ ∖ e z)` is an isomorphism, so is
`H_i(M, M ∖ K) → H_i(M, M ∖ z)`.  Route: `_aux_restrict` with `U = e.source`
(`K` compact in a Hausdorff space, hence closed; points are closed); `_aux_homeo`
along `e.toHomeomorphSourceTarget`, whose membership conditions are
`u ∈ K ↔ e u ∈ e '' K` (`e` injective on the source) and `u = z ↔ e u = e z`;
`_aux_restrict` again in `ℝ³` with `U = e.target` (`e '' K` compact). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso_aux_reduce
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (x : M) (K : Set M) (hK : IsCompact K)
    (hsub : K ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source)
    (z : M) (hz : z ∈ K) (i : ℕ) (hi : 0 < i)
    (hmodel : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap
        ((chartAt (EuclideanSpace ℝ (Fin 3)) x) '' K)ᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
          (chartAt (EuclideanSpace ℝ (Fin 3)) x z))
        (ContinuousMap.id (EuclideanSpace ℝ (Fin 3)))
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo ((chartAt (EuclideanSpace ℝ (Fin 3)) x) '' K) (chartAt (EuclideanSpace ℝ (Fin 3)) x z)
          (Set.mem_image_of_mem _ hz))) i)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Kᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint z)
        (ContinuousMap.id M)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo K z hz)) i) := by
  sorry

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source)
    (hconv : Convex ℝ ((chartAt (EuclideanSpace ℝ (Fin 3)) x) '' A))
    (y : M) (hy : y ∈ A) (i : ℕ) (hi : 0 < i) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso_aux_reduce M x A hA hsub y hy (n + 1) hi
    (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_model _ (hA.image_of_continuousOn
        ((chartAt (EuclideanSpace ℝ (Fin 3)) x).continuousOn.mono hsub))
      hconv _ (Set.mem_image_of_mem _ hy) n)
-- END SEAT AREA

/-- PROVED from `_convex_aux_inj_aux_isIso` (lemma-1, job 177, 2026-10-20):
for compact `A` in one chart with convex chart image and `y ∈ A`, the
localization `H_i(M, M ∖ A) → H_i(M, M ∖ y)` is injective for `i > 0`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source)
    (hconv : Convex ℝ ((chartAt (EuclideanSpace ℝ (Fin 3)) x) '' A))
    (y : M) (hy : y ∈ A) (i : ℕ) (hi : 0 < i) (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i)
    (hc : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y) (ContinuousMap.id M) (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) i c = 0) :
    c = 0 := by
  letI := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj_aux_isIso
    M x A hA hsub hconv y hy i hi
  exact (AddCommGrpCat.mono_iff_injective (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) i)).1 inferInstance
    (hc.trans (map_zero _).symm)

/-- PROVED from `_aux_convex_aux_point`, `_aux_convex_aux_inj` (Hatcher 3.27, step 1): a compact `A` inside one chart whose
chart image is convex is good.  Route: excise `M ∖ U` for the chart source `U`
(`A` is closed, `M ∖ U ⊆ M ∖ A`), transport to `ℝ³` through the chart; there
`ℝ³ ∖ A ↪ ℝ³ ∖ {y}` is a homotopy equivalence for `y ∈ A` (radial deformation
onto a large sphere about `y`), so by the five lemma
`H_i(ℝ³, ℝ³ ∖ A) ≅ H_i(ℝ³, ℝ³ ∖ y)`, which is `0` for `i > 3`
(`HigherModelLocalHomology`).  Degree 3 detection follows because that map is
an isomorphism.  The empty set is a (vacuous) instance. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source)
    (hconv : Convex ℝ ((chartAt (EuclideanSpace ℝ (Fin 3)) x) '' A)) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_empty M
  refine ⟨fun i hi => ?_, fun c hc => ?_⟩
  · have key : ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology i, c = 0 := fun c =>
      apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj M x A hA hsub hconv y hy i (by omega) c
        (@Subsingleton.elim _ (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_point M y i hi) _ _)
    exact ⟨fun c d => (key c).trans (key d).symm⟩
  · exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_convex_aux_inj M x A hA hsub hconv y hy 3 (by norm_num) c (hc y hy)

/-- PROVED (lemma-2, banked from its `_aux_union` PARTIAL, 2026-10-20):
complement identities for the Mayer--Vietoris step. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left
    {M : Type} (A B : Set M) : (A ∪ B)ᶜ ⊆ Aᶜ := by
  intro x hx hxa
  exact hx (Or.inl hxa)

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right
    {M : Type} (A B : Set M) : (A ∪ B)ᶜ ⊆ Bᶜ := by
  intro x hx hxb
  exact hx (Or.inr hxb)

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_inter
    {M : Type} (A B : Set M) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, not_and_or]

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union
    {M : Type} (A B : Set M) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, not_or]

/-- LIBRARY LEAF (Hatcher 3.27, relative Mayer--Vietoris, joint injectivity):
for closed `A`, `B`, if `H_{n+1}(M, M ∖ (A ∩ B))` vanishes then a class of
`H_n(M, M ∖ (A ∪ B))` whose images in `H_n(M, M ∖ A)` and `H_n(M, M ∖ B)` both
vanish is zero.  Split from `_aux_union` after lemma-2's PARTIAL (2026-10-20).
Route (lemma-2's diagnosis): `CoefficientSubcomplexRelativeHomologySequence`
for the subcomplexes `P = range (M ∖ A)`, `Q = range (M ∖ B)` of the singular
simplicial set of `M` is exact at the intersection term
`H_{n+1}(S, P ∪ Q) → H_n(S, P ∩ Q) → H_n(S, P) ⊕ H_n(S, Q)`.  Transport it
to the literal relative chains: `P ∩ Q` is `range ((A ∪ B)ᶜ)`
(`CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap`),
`P`, `Q` are `range Aᶜ`, `range Bᶜ` (`rangeRelativeCokernelMap`); `P ∪ Q` is
the `{Aᶜ, Bᶜ}`-small chains of `(A ∩ B)ᶜ`, whose relative homology agrees with
`H_{n+1}(M, M ∖ (A ∩ B))` because `Aᶜ`, `Bᶜ` are open (small chains, as in
`CoefficientCompactComplementUnionComparison`, plus the five lemma).  Check that
the transported piece maps are `relativeSingularMap` of the identity, and pass
from `ModuleCat ℤ` to the `AddCommGrpCat` complexes here.
Ingredients already in this file (lemma-1's BLOCKED-ON, job 192, named a module
`IntegralRelativeSingularHomologyComparison` that does not exist; 2026-10-20):
exactness is `_aux_divide_aux_union_aux_glue_aux_exact_degree` (with `S = Aᶜ`,
`T = Bᶜ`); the `ModuleCat ℤ` → `AddCommGrpCat` relative comparison is
`ManifoldFundamentalClass.integralRelativeHomologyComparison`; the piece maps are
identified with `relativeSingularMap` by `_aux_divide_aux_union_aux_glue_aux_sq_inter`;
`h` reaches the union term through `CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso`
(`Aᶜ`, `Bᶜ` open).  `Aᶜ ∩ Bᶜ` vs `(A ∪ B)ᶜ`: generalise to sets equal to them and `subst`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_joint
    (M : Type) [TopologicalSpace M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (n : ℕ) (h : Subsingleton ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∩ B)ᶜ).homology (n + 1)))
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∪ B)ᶜ).homology n)
    (hcA : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Aᶜ (ContinuousMap.id M)
        (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)) n c = 0)
    (hcB : HomologicalComplex.homologyMap
      (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Bᶜ (ContinuousMap.id M)
        (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)) n c = 0) :
    c = 0 := by
  sorry

/-- PROVED from `_aux_union_aux_joint` (Hatcher 3.27, Mayer--Vietoris step): if closed `A`, `B` and
`A ∩ B` are good, so is `A ∪ B`.  Route: the relative Mayer--Vietoris sequence
of the pairs `(M, M ∖ A)`, `(M, M ∖ B)` (open cover `M ∖ A`, `M ∖ B` of
`M ∖ (A ∩ B)`; the absolute sequence is
`CoefficientCompactComplementCoverSequence`, compare with the sequence of `M`
itself by the five lemma)
`H_{i+1}(M|A∩B) → H_i(M|A∪B) → H_i(M|A) ⊕ H_i(M|B)`.  For `i > 3` both ends
vanish; for `i = 3`, `H₄(M|A∩B) = 0` gives injectivity, and the images of a
class in `H₃(M|A)`, `H₃(M|B)` still vanish at every point (the maps to
`H₃(M|y)` compose).  No compactness or manifold structure is used. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union
    (M : Type) [TopologicalSpace M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (gA : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M A) (gB : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M B) (gAB : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M (A ∩ B)) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M (A ∪ B) := by
  refine ⟨fun i hi => ?_, fun c hc => ?_⟩
  · have key : ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∪ B)ᶜ).homology i, c = 0 := fun c =>
      apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_joint M A B hA hB i (gAB.1 (i + 1) (by omega)) c
        (@Subsingleton.elim _ (gA.1 i hi) _ _) (@Subsingleton.elim _ (gB.1 i hi) _ _)
    exact ⟨fun c d => (key c).trans (key d).symm⟩
  · refine apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_joint M A B hA hB 3 (gAB.1 4 (by norm_num)) c ?_ ?_
    · refine gA.2 _ fun y hy => ?_
      have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
        (A ∪ B)ᶜ Aᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M) (ContinuousMap.id M)
        (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx) (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inl hy)) 3
      have := congrArg (fun f => f c) e
      simp only [ConcreteCategory.comp_apply] at this
      rw [this]; exact hc y (Or.inl hy)
    · refine gB.2 _ fun y hy => ?_
      have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
        (A ∪ B)ᶜ Bᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
        (ContinuousMap.id M) (ContinuousMap.id M)
        (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx) (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inr hy)) 3
      have := congrArg (fun f => f c) e
      simp only [ConcreteCategory.comp_apply] at this
      rw [this]; exact hc y (Or.inr hy)

/-- LIBRARY LEAF (Hatcher 3.27, steps 2--3): every compact subset of one chart
source is good.  Route: excise to the chart target, an open subset of `ℝ³`.
A finite union of compact convex sets is good by `_aux_convex` and
`_aux_union` (intersections of convex sets are convex; induct on the number
of pieces).  For general compact `A`: represent a class of `H_i(ℝ³|A)` by a
relative cycle whose boundary avoids a neighbourhood `V` of `A`; cover `A` by
finitely many closed balls inside `V`, let `K` be their union; the class lifts
to `H_i(ℝ³|K)` and vanishes there by the convex-union case (Hatcher p. 237). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_inChart
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M A := by
  sorry

/-- LIBRARY LEAF (Hatcher 3.27, step 4): every compact `A ⊆ M` is good.
Route: cover `A` by finitely many compact `K_j`, each inside a chart source
(closed chart balls; `M` is locally compact).  Write `A = A₁ ∪ ⋯ ∪ A_m` with
`A_j = A ∩ K_j` and induct on `m` using `_aux_union`: `A_m` and
`(A₁ ∪ ⋯ ∪ A_{m-1}) ∩ A_m` are compact subsets of the chart source of `K_m`,
so both are good by `_aux_inChart`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_compact
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (A : Set M) (hA : IsCompact A) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M A := by
  sorry

/-- LIBRARY LEAF: `H_n(M) → H_n(M, ∅)` is an isomorphism (the subcomplex of
chains in the empty set is zero).  `T02A06SphereShift`'s
`singularPairProjection_isIso_of_subspace_isZero` is one route. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ_aux_chains
    (M : Type) [TopologicalSpace M] (n : ℕ) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of ↑((Set.univ : Set M)ᶜ))).X n) := by
  letI : IsEmpty ↑((Set.univ : Set M)ᶜ) :=
    ⟨fun x ↦ by simpa using x.2⟩
  letI : IsEmpty (ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of ↑((Set.univ : Set M)ᶜ)) n) :=
    ⟨fun σ ↦ by
      let p : SimplexCategory.toTop.obj (SimplexCategory.mk n) :=
        Classical.choice inferInstance
      exact isEmptyElim (σ.down.hom p)⟩
  letI := Classical.decEq
    (ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of ↑((Set.univ : Set M)ᶜ)) n)
  have h : IsZero (AddCommGrpCat.of
      (DirectSum (ConstructionTargets.SingularSubdivision.SingularSimplex
          (TopCat.of ↑((Set.univ : Set M)ᶜ)) n)
        (fun _ ↦ ℤ))) := by
    apply AddCommGrpCat.isZero_of_subsingleton
  exact h.of_iso (ConstructionTargets.SingularSubdivision.addCommGrpCoproductIsoDirectSum
    (ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of ↑((Set.univ : Set M)ᶜ)) n))

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ_aux_homology
    (M : Type) [TopologicalSpace M] (n : ℕ) :
    IsZero ((ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of ↑((Set.univ : Set M)ᶜ))).homology n) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  exact ShortComplex.exact_of_isZero_X₂ _
    (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ_aux_chains M n)

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ (M : Type) [TopologicalSpace M] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (Set.univ : Set M)ᶜ) n) := by
  cases n with
  | zero =>
      letI : Mono (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
            (Set.univ : Set M)ᶜ) 0) :=
        (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_absolute
          ((Set.univ : Set M)ᶜ) 0).mono_g
          ((apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ_aux_homology M 0).eq_of_src _ _)
      letI : Epi (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
            (Set.univ : Set M)ᶜ) 0) := by
        letI : Epi
            ((ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
              ((Set.univ : Set M)ᶜ)).f 0) := by
          dsimp [ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection]
          exact Functor.map_epi
            (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) 0)
            (cokernel.π
              (ConstructionTargets.SingularHomologyConcrete.relativeSingularSubcomplex.ι
                ((Set.univ : Set M)ᶜ)))
        apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
        intro j hj
        simp at hj
      exact isIso_of_mono_of_epi _
  | succ q =>
      exact ConstructionTargets.T02A06SphereShift.singularPairProjection_isIso_of_subspace_isZero
        ((Set.univ : Set M)ᶜ) q
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ_aux_homology M (q + 1))
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ_aux_homology M q)

/-- PROVED from `_aux_compact` with `A = M`, `_aux_univ` and `_aux_factor`:
Hatcher Lemma 3.27(b) with `A = M`.  A class of `H₃(M)` whose image in every
`H₃(M, M ∖ y)` vanishes is zero.  Do not go through `localizationMap x 3` being
an iso: that is the grandparent `_aux_mid_connecting_aux_localization`
(circular). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (z : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of M)).homology 3)
    (hz : ∀ y : M, ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 z = 0) :
    z = 0 := by
  set f := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
      (Set.univ : Set M)ᶜ) 3
  haveI := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ M 3
  have hc : f z = 0 := by
    refine (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_compact M Set.univ isCompact_univ).2 _ fun y hy => ?_
    rw [← ConcreteCategory.comp_apply, ← apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_factor Set.univ y hy 3]
    exact hz y
  calc z = inv f (f z) := by
        rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
    _ = 0 := by rw [hc, map_zero]

/-- PROVED (lemma-2, banked from its `_aux_divide` PARTIAL, 2026-10-20): at
each point the local image of `z` is `m` times a signed normalized local
generator. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_local
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (z : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of M)).homology 3) (m : ℤ)
    (hz : ∀ y : M,
      ((ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 y).hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 z)).natAbs =
        m.natAbs) :
    ∀ y : M, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      m • (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 y).inv.hom e =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 z := by
  intro y
  let N := ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 y
  have hsign : N.hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 z) = m ∨
      N.hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 z) = -m :=
    Int.natAbs_eq_natAbs_iff.mp (hz y)
  rcases hsign with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso N.hom).1
    have hinv : N.hom.hom (N.inv.hom (1 : ℤ)) = 1 :=
      ConcreteCategory.congr_hom N.inv_hom_id 1
    rw [map_zsmul, hinv, hpos]
    simp
  · refine ⟨-1, Or.inr rfl, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso N.hom).1
    have hinv : N.hom.hom (N.inv.hom (-1 : ℤ)) = -1 :=
      ConcreteCategory.congr_hom N.inv_hom_id (-1)
    rw [map_zsmul, hinv, hneg]
    simp

/-- `A` admits division by `m` (existence half of Hatcher Lemma 3.27, integer
coefficients): a class of `H₃(M, M ∖ A)` whose image in `H₃(M, M ∖ y)` is
divisible by `m` at every `y ∈ A` has the same local images as `m • μ` for one
class `μ` of `H₃(M, M ∖ A)`.  Split from `_aux_divide` after lemma-2's PARTIAL
(2026-10-20).  Stated without a section of the orientation cover: the
divisibility hypothesis replaces it. -/
def apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good (M : Type) [TopologicalSpace M] (m : ℤ) (A : Set M) : Prop :=
  ∀ c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology 3,
    (∀ (y : M) (hy : y ∈ A), ∃ g, m • g =
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) 3 c) →
      ∃ μ : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology 3,
        ∀ (y : M) (hy : y ∈ A), m •
          HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) 3 μ =
          HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M) (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) 3 c

/-- LIBRARY LEAF (Hatcher 3.27(a), step 1): a compact `A` inside one chart whose
chart image is convex admits division by `m`.  Route: as in
`_aux_injective_aux_convex`, `H₃(M, M ∖ A) → H₃(M, M ∖ y)` is an isomorphism
for each `y ∈ A` (excise `M ∖ U`, transport to `ℝ³`, radial deformation, five
lemma).  Fix `y ∈ A` with `m • g = r_y c`; put `μ = r_y⁻¹ g`.  Then
`r_y (m • μ) = r_y c`, so `m • μ = c` and every point follows.  Empty `A`:
take `μ = 0`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_convex
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source)
    (hconv : Convex ℝ ((chartAt (EuclideanSpace ℝ (Fin 3)) x) '' A)) (m : ℤ) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m A := by
  sorry

/-- PROVED (lemma-3, banked from its `_aux_divide_aux_union` PARTIAL,
2026-10-20): restrict `c` to `A` and to `B` and divide there. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_restrict
    (M : Type) [TopologicalSpace M] (m : ℤ) (A B : Set M)
    (gA : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m A)
    (gB : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m B)
    (c : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
      (A ∪ B)ᶜ).homology 3)
    (hc : ∀ (y : M) (hy : y ∈ A ∪ B), ∃ g, m • g =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ
          (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
          (ContinuousMap.id M)
          (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y hy)) 3 c) :
    (∃ μA : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology 3,
      ∀ (y : M) (hy : y ∈ A), m •
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) 3 μA =
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)) 3
          (HomologicalComplex.homologyMap
            (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Aᶜ
              (ContinuousMap.id M)
              (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)) 3 c)) ∧
    (∃ μB : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Bᶜ).homology 3,
      ∀ (y : M) (hy : y ∈ B), m •
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)) 3 μB =
        HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ
            (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
            (ContinuousMap.id M)
            (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)) 3
          (HomologicalComplex.homologyMap
            (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Bᶜ
              (ContinuousMap.id M)
              (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)) 3 c)) := by
  constructor
  · apply gA
    intro y hy
    obtain ⟨g, hg⟩ := hc y (Or.inl hy)
    refine ⟨g, ?_⟩
    have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Aᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)
      (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo A y hy)
      (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inl hy)) 3
    exact hg.trans (by
      simpa only [ConcreteCategory.comp_apply] using
        (congrArg (fun f => f c) e).symm)
  · apply gB
    intro y hy
    obtain ⟨g, hg⟩ := hc y (Or.inr hy)
    refine ⟨g, ?_⟩
    have e := ConstructionTargets.SingularExcision.relativeSingularHomologyMap_comp
      (A ∪ B)ᶜ Bᶜ (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)
      (ContinuousMap.id M) (ContinuousMap.id M)
      (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)
      (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo B y hy)
      (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_mapsTo (A ∪ B) y (Or.inr hy)) 3
    exact hg.trans (by
      simpa only [ConcreteCategory.comp_apply] using
        (congrArg (fun f => f c) e).symm)

/-- LIBRARY LEAF: `H₃(M, M ∖ y)` is torsion-free.  Split from `_aux_union` after
lemma-3's PARTIAL (2026-10-20).  Route: `ambientLocalNormalization 1 y` is an
isomorphism onto `ℤ` (see `_aux_divide_aux_local`); apply its `hom`, use
`map_zsmul`, cancel `m ≠ 0` in `ℤ`, and pull back by injectivity. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_torsion
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (y : M) (m : ℤ) (hm : m ≠ 0)
    (x : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint y)).homology 3) (h : m • x = 0) : x = 0 := by
  let e := ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 y
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have he : m • e.hom.hom x = 0 := by
    rw [← map_zsmul, h, map_zero]
  simpa using (eq_zero_or_eq_zero_of_smul_eq_zero he).resolve_left hm

/-- PROVED (lemma-3, banked from its `_aux_glue` PARTIAL, job 187, 2026-10-20):
middle exactness of the coefficient-subcomplex relative Mayer--Vietoris sequence for
the subspaces `Aᶜ`, `Bᶜ`.  `_aux_glue` still has to transport it to the literal
relative chains (`relativeSingularMap`). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_exact
    (M : Type) [TopologicalSpace M] (A B : Set M) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToPiecesRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) (n + 1))
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.piecesToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) (n + 1))
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.relative_arrows_zero,
          HomologicalComplex.homologyMap_zero])).Exact := by
  exact
    ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence.exact_intersection_pieces_union
      ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ) n

/-- PROVED (lemma-3, banked from its third `_aux_glue` PARTIAL, job 189, 2026-10-20):
`_aux_glue_aux_exact` at every degree `n`, `0` included, from `homology_exact₂` of the
degreewise short exact sequence. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_exact_degree
    (M : Type) [TopologicalSpace M] (A B : Set M) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToPiecesRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n)
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.piecesToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.relative_arrows_zero,
          HomologicalComplex.homologyMap_zero])).Exact := by
  exact
    (ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact.shortComplex_shortExact
      ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange Aᶜ)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange Bᶜ)).homology_exact₂ n

/-- LIBRARY LEAF (split by claude-14 from `_aux_glue` after lemma-3's third PARTIAL,
job 189, 2026-10-20): naturality of the comparison isomorphisms for the intersection
arrows.  Write `Φ_S` for `forget (rangeRelativeIso ℤ S n).hom ≫
integralRelativeHomologyComparison S n` (range-subcomplex relative homology →
literal `H_n(M, S)`), and `Φ_∩` for the same through `intersectionRelativeIso`.
Then `intersectionToLeftRelative` / `…ToRightRelative` become the
`relativeSingularMap`s `(M, S ∩ T) → (M, S)` / `(M, S ∩ T) → (M, T)`.  Route: every
map is a `cokernel.map` of chain maps induced by inclusions; check the square on
chains after `cokernel.π` (epi), using `ambientSubspaceRangeChainsIso_hom_comp_subspaceMap`,
`integralRelativeChainsComparison`'s definition and
`coefficientRelativeProjection_mapHomologyIso_naturality` for the forgetful step. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_inter
    (M : Type) [TopologicalSpace M] (S T : Set M) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison S n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∩ T) n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (S ∩ T) S (ContinuousMap.id M)
          (fun _ hx => hx.1)) n ∧
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison T n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso ℤ S T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∩ T) n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (S ∩ T) T (ContinuousMap.id M)
          (fun _ hx => hx.2)) n := by
  sorry

/-- LIBRARY LEAF (split by claude-14 from `_aux_glue` after lemma-3's third PARTIAL,
job 189, 2026-10-20): the same naturality for the union arrows, with
`relativeComparisonIso ℤ S T hS hT n` (generated union `P S ⊔ P T` → literal `S ∪ T`,
needs `S`, `T` open) on the target.  `leftToUnionRelative` / `rightToUnionRelative`
become the `relativeSingularMap`s `(M, S) → (M, S ∪ T)` / `(M, T) → (M, S ∪ T)`.  Route as
for `_aux_sq_inter`; `relativeComparisonIso_hom` unfolds the target iso to a
`cokernel.map`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_transport
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport A).hom = 𝟙 _ := by
  apply (cancel_epi (cokernel.π _)).1
  simp [ConstructionTargets.ManifoldFundamentalClass.coefficientIntegralCokernelTransport]
  exact (Category.comp_id _).symm

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_comparison_eq
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison A n =
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport A n := by
  have hc : ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison A =
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport A := by
    ext1
    simp [ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparison,
      ConstructionTargets.ManifoldFundamentalClass.integralRelativeChainsComparisonWithTransport, apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_transport]
    exact (Category.id_comp _).symm
  simp only [ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison,
    ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport, hc]

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_left_chain
    (M : Type) [TopologicalSpace M] (S T : Set M) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
      cokernel.map
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedAmbientInclusion ℤ S T)
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∪ T))
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedToProduction ℤ S T)
        (𝟙 _)
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGenerated_relative_square ℤ S T) =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S ≫
      ConstructionTargets.CoefficientRadialPair.pairMap ℤ S (S ∪ T)
        (ContinuousMap.id M) (fun _ hx => Or.inl hx) := by
  have hid : ConstructionTargets.CoefficientRadialPair.absoluteMap ℤ (ContinuousMap.id M) = 𝟙 _ := by
    change (ConstructionTargets.CoefficientRadialPair.chains ℤ).map
      (TopCat.toSSet.map (𝟙 (TopCat.of M))) = _
    simp only [CategoryTheory.Functor.map_id]
  apply (cancel_epi (cokernel.π _)).1
  simp only [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative,
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap,
    ConstructionTargets.CoefficientRadialPair.pairMap, cokernel.map, cokernel.π_desc_assoc,
    Category.id_comp]
  erw [cokernel.π_desc, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [hid]
  exact (Category.id_comp _).symm

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_right_chain
    (M : Type) [TopologicalSpace M] (S T : Set M) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T) ≫
      cokernel.map
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedAmbientInclusion ℤ S T)
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap ℤ (S ∪ T))
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedToProduction ℤ S T)
        (𝟙 _)
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGenerated_relative_square ℤ S T) =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T ≫
      ConstructionTargets.CoefficientRadialPair.pairMap ℤ T (S ∪ T)
        (ContinuousMap.id M) (fun _ hx => Or.inr hx) := by
  have hid : ConstructionTargets.CoefficientRadialPair.absoluteMap ℤ (ContinuousMap.id M) = 𝟙 _ := by
    change (ConstructionTargets.CoefficientRadialPair.chains ℤ).map
      (TopCat.toSSet.map (𝟙 (TopCat.of M))) = _
    simp only [CategoryTheory.Functor.map_id]
  apply (cancel_epi (cokernel.π _)).1
  simp only [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative,
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap,
    ConstructionTargets.CoefficientRadialPair.pairMap, cokernel.map, cokernel.π_desc_assoc,
    Category.id_comp]
  erw [cokernel.π_desc, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [hid]
  exact (Category.id_comp _).symm

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_naturality
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (f : C(X, X)) (hf : Set.MapsTo f A B) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap ℤ A B f hf) n) ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison B n).hom =
    (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison A n).hom ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap A B f hf) n := by
  rw [apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_comparison_eq, apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_comparison_eq]
  exact ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparisonWithTransport_pairMap_naturality A B f hf n

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union
    (M : Type) [TopologicalSpace M] (S T : Set M) (hS : IsOpen S) (hT : IsOpen T) (n : ℕ) :
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso ℤ S T hS hT n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∪ T) n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ S n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison S n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap S (S ∪ T) (ContinuousMap.id M)
          (fun _ hx => Or.inl hx)) n ∧
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
          ℤ (ConstructionTargets.SingularExcision.ambientSubspaceRange S)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange T)) n) ≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso ℤ S T hS hT n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison (S ∪ T) n).hom =
    (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso ℤ T n).hom ≫
      (ConstructionTargets.ManifoldFundamentalClass.integralRelativeHomologyComparison T n).hom) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap T (S ∪ T) (ContinuousMap.id M)
          (fun _ hx => Or.inr hx)) n := by
  constructor
  · rw [ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso_hom]
    rw [← Category.assoc, ← Functor.map_comp]
    erw [← HomologicalComplex.homologyMap_comp]
    rw [apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_left_chain]
    erw [HomologicalComplex.homologyMap_comp]
    erw [Functor.map_comp]
    have h := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_naturality S (S ∪ T) (ContinuousMap.id M)
      (fun _ hx => Or.inl hx) n
    exact (congrArg (fun q =>
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ S) n) ≫ q)
      h).trans (Category.assoc _ _ _).symm
  · rw [ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso_hom]
    rw [← Category.assoc, ← Functor.map_comp]
    erw [← HomologicalComplex.homologyMap_comp]
    rw [apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_right_chain]
    erw [HomologicalComplex.homologyMap_comp]
    erw [Functor.map_comp]
    have h := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue_aux_sq_union_aux_naturality T (S ∪ T) (ContinuousMap.id M)
      (fun _ hx => Or.inr hx) n
    exact (congrArg (fun q =>
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap ℤ T) n) ≫ q)
      h).trans (Category.assoc _ _ _).symm

/-- LIBRARY LEAF (Hatcher 3.27, relative Mayer--Vietoris, existence half): for
closed `A`, `B`, classes of `H_n(M, M ∖ A)` and `H_n(M, M ∖ B)` with the same
image in `H_n(M, M ∖ (A ∩ B))` come from one class of `H_n(M, M ∖ (A ∪ B))`.
Split from `_aux_union` after lemma-3's PARTIAL (2026-10-20).  Route: exactness
of the same relative Mayer--Vietoris sequence as `_aux_injective_aux_union_aux_joint`,
at the middle term `H_n(S, P ∩ Q) → H_n(S, P) ⊕ H_n(S, Q) → H_n(S, P ∪ Q)`
(`CoefficientSubcomplexRelativeHomologySequence`; transport to the literal
relative chains with `CoefficientSubcomplexRelativeLiteralComparison` and
`CoefficientCompactComplementUnionToRelative`).  The sign convention of the
difference map does not matter here: equality of the two images is the kernel
condition.  ASSEMBLY (claude-14's split after lemma-3's third PARTIAL, job 189):
apply `_aux_glue_aux_exact_degree` and transport through `_aux_glue_aux_sq_inter`,
`_aux_glue_aux_sq_union` with `S = Aᶜ`, `T = Bᶜ` (open by `hA.isOpen_compl`,
`hB.isOpen_compl`).  The squares are stated for `S ∩ T`, `S ∪ T`, while this lemma has
`(A ∪ B)ᶜ`, `(A ∩ B)ᶜ`: first prove the version for arbitrary sets `Z`, `W` with
`Z = Aᶜ ∩ Bᶜ`, `W = Aᶜ ∪ Bᶜ` and arbitrary `MapsTo` proofs, `subst`, then specialise
(`Set.compl_union`, `Set.compl_inter`).  The middle term is the homology of the
biproduct complex `cokernel (leftAmbient) ⊞ cokernel (rightAmbient)`; take its two
components with `biprod.fst`/`biprod.snd` (both commute with `homologyMap`). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union_aux_glue
    (M : Type) [TopologicalSpace M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (n : ℕ) (μA : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Aᶜ).homology n) (μB : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains Bᶜ).homology n)
    (h : HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Aᶜ (A ∩ B)ᶜ (ContinuousMap.id M) (fun x hx hab => hx hab.1)) n μA =
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap Bᶜ (A ∩ B)ᶜ (ContinuousMap.id M) (fun x hx hab => hx hab.2)) n μB) :
    ∃ μ : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains (A ∪ B)ᶜ).homology n,
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Aᶜ (ContinuousMap.id M)
          (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_left A B hx)) n μ = μA ∧
      HomologicalComplex.homologyMap
        (ConstructionTargets.SingularExcision.relativeSingularMap (A ∪ B)ᶜ Bᶜ (ContinuousMap.id M)
          (fun x hx => apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_union_aux_compl_union_right A B hx)) n μ = μB := by
  sorry

/-- ASSEMBLY from `_aux_union_aux_restrict`, `_aux_torsion`, `_aux_glue` and
`gAB.2` (Hatcher 3.27(a), Mayer--Vietoris step): if closed `A`, `B`
admit division by `m ≠ 0` and `A ∩ B` is good in the sense of
`_aux_injective_aux_good`, then `A ∪ B` admits division by `m`.  Route:
restrict `c` to `H₃(M|A)`, `H₃(M|B)` (the local maps compose,
`relativeSingularMap_comp`) and divide there: `μ_A`, `μ_B`.  On `A ∩ B` the
difference `d` of their restrictions has `m • r_y d = 0`, so `r_y d = 0`
(`H₃(M|y) ≅ ℤ` by `ambientLocalNormalization 1 y`, torsion-free), so `d = 0`
by `gAB.2`.  Exactness of the relative Mayer--Vietoris sequence at
`H₃(M|A) ⊕ H₃(M|B)` (`CoefficientSubcomplexRelativeMayerVietoris*`) lifts
`(μ_A, μ_B)` to `μ ∈ H₃(M|A ∪ B)`, whose local images are those of `μ_A`
on `A` and of `μ_B` on `B`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_union
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (m : ℤ) (hm : m ≠ 0) (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (gA : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m A) (gB : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m B)
    (gAB : apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_good M (A ∩ B)) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m (A ∪ B) := by
  sorry

/-- LIBRARY LEAF (Hatcher 3.27(a), steps 2--3): every compact subset of one
chart source admits division by `m ≠ 0`.  Route: the existence counterpart of
`_aux_injective_aux_inChart` (same excision to the chart target, induction on
finite unions of convex sets by `_aux_convex`, `_aux_union` and
`_aux_injective_aux_convex` for the intersections).  General compact `A`:
`c` comes from `H₃(ℝ³|K)` for `K` a finite union of closed balls inside a
neighbourhood of `A`, each ball meeting `A`; on such a ball the local images
of `c` are `m`-divisible at one point of `A`, hence at all its points
(`H₃(ℝ³|ball) ≅ H₃(ℝ³|y)`).  Divide on `K` and restrict to `A`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_inChart
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (x : M) (A : Set M) (hA : IsCompact A)
    (hsub : A ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) x).source)
    (m : ℤ) (hm : m ≠ 0) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m A := by
  sorry

/-- LIBRARY LEAF (Hatcher 3.27(a), step 4): every compact `A ⊆ M` admits
division by `m ≠ 0`.  Route: the same finite chart cover and induction as
`_aux_injective_aux_compact`, with `_aux_union`, `_aux_inChart` and
`_aux_injective_aux_inChart` (for the intersections, which are compact
subsets of the last chart source). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_compact
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (A : Set M) (hA : IsCompact A) (m : ℤ) (hm : m ≠ 0) :
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_good M m A := by
  sorry

/-- PROVED from `_aux_local`, `_aux_compact` with `A = M`, `_aux_univ` and
`_aux_factor`: Hatcher Lemma 3.27(a) with `A = M`.  If the local degree of `z`
has absolute value `|m| ≠ 0` at every point, then `z`'s local images are all
divisible by `m` through ONE global class. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (z : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of M)).homology 3) (m : ℤ) (hm : m ≠ 0)
    (hz : ∀ y : M,
      ((ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 y).hom.hom
        (ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 z)).natAbs =
        m.natAbs) :
    ∃ μ : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of M)).homology 3,
      ∀ y : M, m • ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 μ =
        ConstructionTargets.ManifoldFundamentalClass.localizationMap y 3 z := by
  haveI := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective_aux_univ M 3
  obtain ⟨μ', hμ'⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_compact M Set.univ isCompact_univ m hm
    (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (Set.univ : Set M)ᶜ) 3 z) fun y hy => by
    obtain ⟨e, -, he⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide_aux_local M z m hz y
    refine ⟨_, he.trans ?_⟩
    rw [apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_factor Set.univ y hy 3, ConcreteCategory.comp_apply]
  refine ⟨inv (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        (Set.univ : Set M)ᶜ) 3) μ', fun y => ?_⟩
  rw [apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant_aux_eventually_sign_aux_factor Set.univ y (Set.mem_univ y) 3, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (inv _), IsIso.inv_hom_id,
    ConcreteCategory.id_apply]
  exact hμ' y (Set.mem_univ y)

/-- PROVED from `_aux_injective`, `_aux_divide` and `_aux_locallyConstant`:
the global generator `g` is nonzero, so (injective) its local degree `d` at
some `x` is nonzero; `|deg|` is constant (connected), so (divide)
`d • μ` and `g` have the same local images, hence (injective) `g = d • μ`;
`g` generates `H₃(M) ≅ ℤ`, so `d = ±1`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) :
    ∃ y : M, (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM y).natAbs = 1 := by
  letI : PathConnectedSpace M := apm_t00A01_punctured_pathConnected_aux_ambient M hM
  set g := ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
    (TopCat.of M) 3 hM.2.1.some with hgdef
  -- `φ : H₃(M) → ℤ` sends `g` to `1`.
  let φ : (ConstructionTargets.SingularHomologyConcrete.SingularChains
      (TopCat.of M)).homology 3 →+ ℤ :=
    hM.2.1.some.hom.hom.toAddMonoidHom.comp
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of M) 3).inv.hom
  have hφg : φ g = 1 := by
    change hM.2.1.some.hom.hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of M) 3).inv.hom
        ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
          (TopCat.of M) 3).hom.hom (hM.2.1.some.inv.hom 1))) = 1
    have hc := ConcreteCategory.congr_hom
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of M) 3).hom_inv_id (hM.2.1.some.inv.hom 1)
    change (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of M) 3).inv.hom
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of M) 3).hom.hom (hM.2.1.some.inv.hom 1)) = hM.2.1.some.inv.hom 1 at hc
    rw [hc]
    exact ConcreteCategory.congr_hom hM.2.1.some.inv_hom_id (1 : ℤ)
  have hg0 : g ≠ 0 := by
    intro h; rw [h, map_zero] at hφg; exact zero_ne_one hφg
  obtain ⟨x, hx⟩ : ∃ x : M,
      ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3 g ≠ 0 := by
    by_contra h; push_neg at h
    exact hg0 (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective M g h)
  set d := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM x with hd
  have hd0 : d ≠ 0 := by
    intro h0; apply hx
    apply (ConcreteCategory.bijective_of_isIso
      (ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 x).hom).1
    rw [map_zero]; exact h0
  have hall : ∀ y : M, (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM y).natAbs = d.natAbs := fun y =>
    (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant M hM).apply_eq_of_isPreconnected
      isPreconnected_univ (Set.mem_univ y) (Set.mem_univ x)
  obtain ⟨μ, hμ⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_divide M g d hd0 hall
  have hgμ : d • μ - g = 0 := by
    apply apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit_aux_injective M
    intro y
    rw [map_sub, map_zsmul, hμ y, sub_self]
  have h1 : d * φ μ = 1 := by
    rw [← hφg, ← smul_eq_mul, ← map_zsmul, sub_eq_zero.mp hgμ]
  exact ⟨x, by rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h <;> simp [← hd, h]⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) (r : ℤ)
    (hr : r •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) x =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 hM.2.1.some)) :
    r = 1 ∨ r = -1 := by
  letI : PathConnectedSpace M := apm_t00A01_punctured_pathConnected_aux_ambient M hM
  obtain ⟨y, hy⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_exists_unit M hM
  have hxy := (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_locallyConstant M hM).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ x) (Set.mem_univ y)
  have hx : (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree M hM x).natAbs = 1 := hxy.trans hy
  rw [apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign_aux_degree_spec M hM x r hr]
  exact Int.natAbs_eq_iff.mp hx

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_assemble
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) (r : ℤ)
    (hr : r •
        ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 1) x =
      ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 hM.2.1.some))
    (hsign : r = 1 ∨ r = -1) :
    ∃ μ : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of M)).homology 3,
      ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3 μ =
          ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) x ∨
        ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3 μ =
          -ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) x := by
  refine ⟨ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
    (TopCat.of M) 3 hM.2.1.some, ?_⟩
  rcases hsign with rfl | rfl
  · left
    simpa using hr.symm
  · right
    simpa using hr.symm

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) :
    ∃ μ : (ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of M)).homology 3,
      ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3 μ =
          ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) x ∨
        ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3 μ =
          -ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) x := by
  obtain ⟨r, hr⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_coeff
      M hM x
  exact
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_assemble
      M hM x r hr
        (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign
          M hM x r hr)

/-- PROVED (lemma-2, job 156): localization at `x` is an isomorphism once
the global generator maps to `± ambientLocalGenerator x`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_injective_aux_of_sign
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (e : apm_t00A01_H 3 M ≅ ModuleCat.of ℤ ℤ) (x : M) (s : ℤ)
    (hs : s = 1 ∨ s = -1)
    (hmap : ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3
        (ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 e) =
      s • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 1) x) :
    IsIso (ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3) := by
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro a b hab
    obtain ⟨m, rfl⟩ :=
      ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator_generates
        (TopCat.of M) 3 e a
    obtain ⟨n, rfl⟩ :=
      ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator_generates
        (TopCat.of M) 3 e b
    simp only [map_zsmul, hmap, smul_smul] at hab
    have hmn : m = n := by
      apply ConstructionTargets.ManifoldFundamentalClass.ambientLocalGenerator_zsmul_injective
        1 x
      rcases hs with rfl | rfl
      · simpa [mul_comm] using hab
      · simpa [mul_comm] using hab
    rw [hmn]
  · intro z
    obtain ⟨n, rfl⟩ :=
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates
        (k := 1) x z
    rcases hs with rfl | rfl
    · refine ⟨n • ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 e, ?_⟩
      simp [hmap]
    · refine ⟨(-n) • ConstructionTargets.ManifoldFundamentalClass.groupGlobalGenerator
          (TopCat.of M) 3 e, ?_⟩
      simp [hmap]

/-- PROVED from `_aux_fundamental`'s sign leaf: localization at `x` is
injective (indeed an isomorphism). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_injective
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) :
    Function.Injective
      (ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3) := by
  obtain ⟨r, hr⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_coeff M hM x
  letI := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_injective_aux_of_sign M hM.2.1.some x r
    (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental_aux_coefficient_is_sign M hM x r hr) hr.symm
  exact (ConcreteCategory.bijective_of_isIso
    (ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3)).1

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_target_generates
    (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (x : M) :
    ∀ z : (ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint x)).homology 3,
      ∃ r : ℤ, r •
          ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
            (k := 1) x = z := by
  intro z
  let e := ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization 1 x
  refine ⟨e.hom.hom z, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [map_zsmul,
    ConstructionTargets.ManifoldFundamentalClass.ambientLocalNormalization_generator]
  change e.hom.hom z • (1 : ℤ) = e.hom.hom z
  rw [smul_eq_mul, mul_one]

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M) :
    IsIso (ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3) := by
  let f := ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3
  have hinj :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_injective
      M hM x
  obtain ⟨μ, hμ | hμ⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_fundamental
      M hM x
  · have hsurj : Function.Surjective f := by
      intro z
      obtain ⟨r, rfl⟩ :=
        apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_target_generates
          M x z
      refine ⟨r • μ, ?_⟩
      simpa only [f, map_zsmul, hμ]
    letI := ConcreteCategory.mono_of_injective f hinj
    letI := ConcreteCategory.epi_of_surjective f hsurj
    exact isIso_of_mono_of_epi f
  · have hsurj : Function.Surjective f := by
      intro z
      obtain ⟨r, rfl⟩ :=
        apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization_aux_target_generates
          M x z
      refine ⟨(-r) • μ, ?_⟩
      simp only [f]
      rw [map_zsmul, hμ, smul_neg, neg_smul, neg_neg]
    letI := ConcreteCategory.mono_of_injective f hinj
    letI := ConcreteCategory.epi_of_surjective f hsurj
    exact isIso_of_mono_of_epi f

/-- PROVED (lemma-2, job 138): for a homology 3-sphere `M`, if localization at
`x` is an iso in degree 3 then `H₂(M ∖ {x}) = 0`. The pair sequence of
`(M, M ∖ {x})` makes the connecting map out of `H₃(M, M ∖ {x})` zero, so
`H₂(M ∖ {x}) → H₂(M) = 0` is injective. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_deleted
    (M : Type) [TopologicalSpace M]
    (hM : apm_t00A01_isHomology3Sphere M) (x : M)
    (hloc : IsIso
      (ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3)) :
    Limits.IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
        (TopCat.of (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint x))) := by
  have hM2 : Limits.IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2 (TopCat.of M)) :=
    ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of M) 2
      (hM.2.2 2 (by omega) (by omega))
  letI : IsIso (ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3) := hloc
  have hconnecting : ConstructionTargets.SingularHomologyConcrete.singularPairConnecting
      (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint x) 2 = 0 := by
    apply (cancel_epi
      (ConstructionTargets.ManifoldFundamentalClass.localizationMap x 3)).mp
    exact
      ((ConstructionTargets.SingularHomologyConcrete.singularPairShortComplex_shortExact
        (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint x)).comp_δ
          (2 + 1) 2 rfl)
  exact (ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_subspace
    (ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint x) 2).isZero_X₂
    hconnecting (hM2.eq_of_tgt _ _)

/-- LEAF (split from `_aux_H2`, 2026-10-20): the punctured piece
`M ∖ φ(int B)` is homotopy equivalent to `M ∖ {φ 0}`. Route: take the radius-2
collar `Φ` from `hcollar` and push `M ∖ {φ 0}` radially out of the open unit
ball (`z ↦ (1-t) z + t z/‖z‖` in collar coordinates, identity elsewhere), with
the inclusion `M ∖ φ(int B) ⊆ M ∖ {φ 0}` as the other map. The same radial
homotopy is already built and proved continuous in
`apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv` (`_aux_H`,
`_aux_H_mapsTo`, `_aux_H_continuousOn`); reuse those pieces rather than
re-proving continuity. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_radial :
    ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦
        if ‖p.2‖ < 1 then
          (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2)
        else p.2)
      (Set.univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 0 < ‖x‖}) := by
  let s : Set (unitInterval × EuclideanSpace ℝ (Fin 3)) :=
    Set.univ ×ˢ {x : EuclideanSpace ℝ (Fin 3) | 0 < ‖x‖}
  let f : unitInterval × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) := fun p ↦
    (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • (‖p.2‖⁻¹ • p.2)
  let g : unitInterval × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) := fun p ↦ p.2
  have ht : Continuous
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ p.2) :=
    continuous_snd
  have hn : Continuous
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖) :=
    continuous_norm.comp hx
  have hne : ∀ p ∈ s, ‖p.2‖ ≠ 0 := by
    intro p hp
    exact ne_of_gt hp.2
  have hinv : ContinuousOn
      (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ ‖p.2‖⁻¹) s :=
    hn.continuousOn.inv₀ hne
  have hf : ContinuousOn f s := by
    exact ((continuous_const.sub ht).continuousOn.smul hx.continuousOn).add
      (ht.continuousOn.smul (hinv.smul hx.continuousOn))
  have hg : ContinuousOn g s := hx.continuousOn
  have hboundary : ∀ p ∈ s ∩ frontier
      {p : unitInterval × EuclideanSpace ℝ (Fin 3) | ‖p.2‖ < 1},
      f p = g p := by
    intro p hp
    have heq : ‖p.2‖ = 1 :=
      (frontier_lt_subset_eq hn continuous_const) hp.2
    simp only [f, g, heq, inv_one, one_smul]
    rw [← add_smul, sub_add_cancel, one_smul]
  exact ContinuousOn.if hboundary
    (hf.mono inter_subset_left) (hg.mono inter_subset_left)


/-- Norm of the radial push for `0 < ‖x‖`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_norm (t : unitInterval) (x : EuclideanSpace ℝ (Fin 3))
    (hx : 0 < ‖x‖) :
    ‖(1 - (t : ℝ)) • x + (t : ℝ) • (‖x‖⁻¹ • x)‖ = (1 - (t : ℝ)) * ‖x‖ + (t : ℝ) := by
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt hx
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
  field_simp

/-- The collar homotopy is continuous on `I × (Φ(ball 0 2) \ {Φ 0})`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_ball
    {M : Type} [TopologicalSpace M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ) :
    ContinuousOn
      (fun p : unitInterval × M ↦
        apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2)
      (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2} ∩
        {Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ)) := by
  let S : Set (unitInterval × M) := univ ×ˢ
    (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2} ∩
      {Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ)
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
  have hinv_pos (p : S) : 0 < ‖(inv p).1‖ := by
    rcases (norm_nonneg (inv p).1).lt_or_eq with h | h
    · exact h
    · exfalso
      apply p.2.2.2
      have h0 : inv p = ⟨0, by simp [apm_t00A01_LargeDisk3]⟩ :=
        Subtype.ext (norm_eq_zero.mp h.symm)
      change p.1.2 = _
      rw [← hinv_eq p, h0]
  let Q : S → unitInterval × EuclideanSpace ℝ (Fin 3) := fun p ↦ (p.1.1, (inv p).1)
  have hQ : Continuous Q := by
    dsimp [Q]
    fun_prop
  have hmaps : MapsTo Q univ (univ ×ˢ {x | 0 < ‖x‖}) := by
    intro p hp
    exact ⟨trivial, hinv_pos p⟩
  have hrad : Continuous (fun p : S ↦
      if ‖(Q p).2‖ < 1 then (1 - ((Q p).1 : ℝ)) • (Q p).2 +
        ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2) else (Q p).2) := by
    rw [← continuousOn_univ]
    exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_radial.comp hQ.continuousOn hmaps
  let R : S → apm_t00A01_LargeDisk3 := fun p ↦ ⟨
    if ‖(Q p).2‖ < 1 then (1 - ((Q p).1 : ℝ)) • (Q p).2 +
      ((Q p).1 : ℝ) • (‖(Q p).2‖⁻¹ • (Q p).2) else (Q p).2, by
    change dist _ 0 ≤ 2
    rw [dist_zero_right]
    by_cases hlt : ‖(Q p).2‖ < 1
    · rw [if_pos hlt, apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_norm _ _ (hinv_pos p)]
      have ht0 : 0 ≤ ((Q p).1 : ℝ) := (Q p).1.2.1
      have ht1 : ((Q p).1 : ℝ) ≤ 1 := (Q p).1.2.2
      nlinarith [norm_nonneg (Q p).2]
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

/-- The collar homotopy is continuous on `I × (M \ {Φ 0})`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_continuousOn
    {M : Type} [TopologicalSpace M] [T2Space M]
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦo : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    ContinuousOn
      (fun p : unitInterval × M ↦
        apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2)
      (univ ×ˢ {Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ) := by
  intro p hp
  have hU : IsOpen ({Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ : Set M) :=
    isOpen_compl_singleton
  by_cases hb : p.2 ∈ Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2}
  · have hA : IsOpen (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2} ∩
        {Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ) : Set (unitInterval × M)) :=
      isOpen_univ.prod (hΦo.inter hU)
    exact ((apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_ball Φ hΦ).continuousAt
      (hA.mem_nhds ⟨trivial, hb, hp.2⟩)).continuousWithinAt
  · have hB : IsOpen (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ 1})ᶜ :
        Set (unitInterval × M)) :=
      isOpen_univ.prod
        (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_closed Φ hΦ.continuous 1).isOpen_compl
    have hpB : p ∈ (univ ×ˢ (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 ≤ 1})ᶜ :
        Set (unitInterval × M)) := by
      refine ⟨trivial, ?_⟩
      rintro ⟨x, hx, hxp⟩
      refine hb ⟨x, ?_, hxp⟩
      change dist x.1 0 ≤ 1 at hx
      change dist x.1 0 < 2
      linarith
    have heq : (fun q : unitInterval × M ↦
        apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ q.1 q.2) =ᶠ[nhds p] Prod.snd := by
      filter_upwards [hB.mem_nhds hpB] with q hq
      apply apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_continuousOn_aux_eq_self
      rintro ⟨x, hx, hxq⟩
      refine hq.2 ⟨x, ?_, hxq⟩
      change dist x.1 0 < 1 at hx
      change dist x.1 0 ≤ 1
      exact le_of_lt hx
    exact (continuous_snd.continuousAt.congr heq.symm).continuousWithinAt

/-- The collar homotopy keeps `M \ {Φ 0}` inside itself, and at time `1`
lands in the punctured manifold. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_mapsTo
    {M : Type} [TopologicalSpace M]
    (φ : apm_t00A01_Disk3 → M) (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦ : Function.Injective Φ) (hΦφ : Φ ∘ apm_t00A01_unitToLarge = φ) :
    (∀ t : unitInterval,
      MapsTo (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ t)
        {Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ
        {Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ) ∧
    MapsTo (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ 1)
      {Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ
      {z | z ∉ φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}} := by
  have hpos (z : M) (hz : z ∈ ({Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ : Set M))
      (x : apm_t00A01_LargeDisk3) (hxz : Φ x = z) : 0 < ‖x.1‖ := by
    rcases (norm_nonneg x.1).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hz
      have h0 : x = ⟨0, by simp [apm_t00A01_LargeDisk3]⟩ :=
        Subtype.ext (norm_eq_zero.mp h.symm)
      rw [← hxz, h0]
      rfl
  constructor
  · intro t z hz
    unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
    split_ifs with h hv
    · intro heq
      have hx0 := hpos z hz h.choose h.choose_spec.1
      have hx1 : ‖h.choose.1‖ < 1 := by
        simpa [dist_eq_norm] using h.choose_spec.2
      have hv0 : (1 - (t : ℝ)) • h.choose.1 +
          (t : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) = 0 :=
        congrArg Subtype.val (hΦ heq)
      have hn := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_norm t _ hx0
      rw [hv0, norm_zero] at hn
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      nlinarith
    · exact hz
    · exact hz
  · intro z hz
    unfold apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H
    split_ifs with h hv
    · have hx0 := hpos z hz h.choose h.choose_spec.1
      rw [apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image φ Φ hΦφ]
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
        exact inv_mul_cancel₀ (ne_of_gt hx0)
      have hy' : ‖y.1‖ < 1 := by simpa [dist_eq_norm] using hy
      rw [hxy, hnorm] at hy'
      exact lt_irrefl 1 hy'
    · have hx0 := hpos z hz h.choose h.choose_spec.1
      exfalso
      apply hv
      change ‖(1 - ((1 : unitInterval) : ℝ)) • h.choose.1 +
          ((1 : unitInterval) : ℝ) • (‖h.choose.1‖⁻¹ • h.choose.1) - 0‖ ≤ 2
      rw [sub_zero, apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_norm 1 _ hx0]
      norm_num
    · rw [apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_image φ Φ hΦφ]
      rintro ⟨x, hx, hxz⟩
      exact h ⟨x, hxz, hx⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (hcollar : apm_t00A01_HasBallCollar phi) :
    Nonempty (ContinuousMap.HomotopyEquiv (apm_t00A01_punctured phi)
      ↥(ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint
        (phi ⟨0, by simp [apm_t00A01_Disk3]⟩))) := by
  obtain ⟨Φ, hΦ, hΦφ, hΦo⟩ := hcollar
  have hp0 : phi ⟨0, by simp [apm_t00A01_Disk3]⟩ =
      Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩ := by
    rw [← hΦφ]
    rfl
  rw [hp0]
  change Nonempty (ContinuousMap.HomotopyEquiv (apm_t00A01_punctured phi)
    ↥({Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ : Set M))
  obtain ⟨hmap, hmap1⟩ := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_mapsTo phi Φ hΦ.injective hΦφ
  have hcont := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_continuousOn Φ hΦ hΦo
  have hHc : Continuous (fun p : unitInterval ×
      ↥({Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ : Set M) ↦
      apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1) :=
    hcont.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p ↦ ⟨mem_univ _, p.2.2⟩)
  let i : C(apm_t00A01_punctured phi,
      ↥({Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ : Set M)) :=
    ⟨fun x ↦ ⟨x.1, fun hx ↦ x.2 ⟨⟨0, by simp [apm_t00A01_Disk3]⟩, by simp,
      by rw [hp0]; exact hx.symm⟩⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩
  let r : C(↥({Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩}ᶜ : Set M),
      apm_t00A01_punctured phi) :=
    ⟨fun z ↦ ⟨apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ 1 z.1, hmap1 z.2⟩,
      (hHc.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let F : ContinuousMap.Homotopy (ContinuousMap.id _) (i.comp r) :=
    { toFun := fun p ↦ ⟨apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1, hmap p.1 p.2.2⟩
      continuous_toFun := hHc.subtype_mk _
      map_zero_left := fun z ↦ Subtype.ext (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_zero Φ z.1)
      map_one_left := fun z ↦ rfl }
  have hri : r.comp i = ContinuousMap.id _ := by
    ext z
    exact apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_one phi Φ hΦφ z.1 z.2
  exact ⟨{ toFun := i, invFun := r
           left_inv := by rw [hri]
           right_inv := ⟨F.symm⟩ }⟩

/-- LIBRARY: collar excision and the pair exact sequence turn invertibility of
localization at the centre into vanishing of degree two of the complement.
The homology-sphere hypothesis is needed: the pair sequence only makes
`H₂(M ∖ x) → H₂(M)` injective (false without it for `S² × S¹`). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2
    (M : Type) [TopologicalSpace M] [T2Space M]
    (hM : apm_t00A01_isHomology3Sphere M)
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (hcollar : apm_t00A01_HasBallCollar phi)
    (hloc : IsIso (ConstructionTargets.ManifoldFundamentalClass.localizationMap
      (phi ⟨0, by simp [apm_t00A01_Disk3]⟩) 3)) :
    Limits.IsZero (apm_t00A01_H 2 (apm_t00A01_punctured phi)) := by
  let x : apm_t00A01_Disk3 := ⟨0, by simp [apm_t00A01_Disk3]⟩
  have hdeleted :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_deleted
      M hM (phi x) (by simpa [x] using hloc)
  obtain ⟨e⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv
      M phi hphi hcollar
  have hgroup : Limits.IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
        (TopCat.of (apm_t00A01_punctured phi))) :=
    hdeleted.of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv e 2)
  exact
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
      (TopCat.of (apm_t00A01_punctured phi)) 2 hgroup

/-- Pair-sequence algebra (banked from lemma-3, job 140): if `H₄(X,A) = 0`
and `H₃(X) → H₃(X,A)` is invertible, then `H₃(A) = 0`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_les
    {X : Type} [TopologicalSpace X] (A : Set X)
    (hrel4 : Limits.IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains A).homology 4))
    (hloc : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection A) 3)) :
    Limits.IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology 3 (TopCat.of A)) := by
  open ConstructionTargets.SingularHomologyConcrete in
    letI : IsIso (HomologicalComplex.homologyMap
        (relativeSingularProjection A) 3) := hloc
    have hiMono : Mono (HomologicalComplex.homologyMap
        (singularSubspaceMap A) 3) :=
      (singularPairHomology_exact_subspace A 3).mono_g (hrel4.eq_of_src _ _)
    have hi : HomologicalComplex.homologyMap (singularSubspaceMap A) 3 = 0 :=
      (singularPairHomology_exact_absolute A 3).mono_g_iff.mp (by infer_instance)
    exact @Limits.IsZero.of_mono_eq_zero AddCommGrpCat _ _ _ _
      (HomologicalComplex.homologyMap (singularSubspaceMap A) 3) hiMono hi

/-- LIBRARY (excision across the collar): `H₄(M, M ∖ int B) = 0`.
Excise `M ∖ Φ(open radius-2 ball)`, which is closed and lies in the interior of
the complement (`φ(B)` is compact, so closed in the Hausdorff `M`); what is
left is the pair (open radius-2 ball, radius-2 ball minus the open unit ball),
whose relative homology vanishes above degree 3. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_model :
    Limits.IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 3)).homology 4) := by
  open ConstructionTargets.SingularHomologyConcrete in
   open ConstructionTargets.T02A06DiskRadialComparison in
    have hamb : Limits.IsZero
        ((SingularChains (TopCat.of (T02A06.euclideanClosedDisk 3))).homology 4) := by
      letI : ContractibleSpace (T02A06.euclideanClosedDisk 3) :=
        Metric.contractibleSpace_closedBall (by norm_num)
      exact contractibleHigherHomology_isZero _ 4 (by omega)
    have hbdry : Limits.IsZero
        ((SingularChains (TopCat.of (closedDiskBoundarySet 3))).homology 3) := by
      exact (ConstructionTargets.SphereHomology.sphereHomology_isZero_of_gt 2 3
        (by omega)).of_iso
          (singularHomologyIsoOfHomotopyEquiv
            (closedDiskBoundaryHomeomorph 3).toHomotopyEquiv 3)
    exact (singularPairHomology_exact_relative (closedDiskBoundarySet 3) 3).isZero_X₂
      (hamb.eq_of_src _ _) (hbdry.eq_of_tgt _ _)

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_general
    {X : Type} [TopologicalSpace X] (A Z : Set X)
    (hZclosed : IsClosed Z) (hZ : Z ⊆ interior A) :
    Nonempty
      (((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains A).homology 4) ≅
        ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.SingularExcision.excisedSubspace A Z)).homology 4)) := by
  open ConstructionTargets.SingularExcision in
    have hi : IsIso (HomologicalComplex.homologyMap
        (relativeExcisionMap A Z) 4) := by
      simpa using relativeExcisionMap_homologyMap_isIso_succ A Z hZclosed hZ 3
    exact ⟨(@asIso _ _ _ _
      (HomologicalComplex.homologyMap (relativeExcisionMap A Z) 4) hi).symm⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_radial :
    Nonempty
      (((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.T02A06HemisphereExcision.puncturedOpenDiskSet 3)).homology 4) ≅
        ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 3)).homology 4)) := by
  open ConstructionTargets.SingularHomologyConcrete in
   open ConstructionTargets.SingularExcision in
    open ConstructionTargets.T02A06HemisphereExcision in
    open ConstructionTargets.T02A06DiskRadialComparison in
      have hi : IsIso (HomologicalComplex.homologyMap
          (relativeSingularMap (closedDiskBoundarySet 3) (puncturedOpenDiskSet 3)
            (halfDiskMap 3) (halfDiskMap_mapsTo 3)) 4) :=
        closedDiskPair_to_openDiskPair_homologyMap_isIso 3 4 (by omega)
      exact ⟨(@asIso _ _ _ _
        (HomologicalComplex.homologyMap
          (relativeSingularMap (closedDiskBoundarySet 3) (puncturedOpenDiskSet 3)
            (halfDiskMap 3) (halfDiskMap_mapsTo 3)) 4) hi).symm⟩

/-- LIBRARY (collar coordinates): a closed set `Z` inside the interior of
`M ∖ φ(int B)` whose excision leaves a pair with the degree-four relative homology
of the punctured open 3-disk pair. Route (seat's note): take `Z` the complement of
`Φ(int B₂)` for the collar `Φ`; identify the excised pair through collar
coordinates, including the set-membership equivalence. -/
-- BANKED (lemma-1): the complement `Z` of the open collar ball is closed and lies
-- in the interior of the complement of the open unit ball.
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_Z
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (Φ : apm_t00A01_LargeDisk3 → M)
    (hΦphi : Φ ∘ apm_t00A01_unitToLarge = phi)
    (hO : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    IsClosed (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})ᶜ ∧
      (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})ᶜ ⊆
        interior {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}} := by
  refine ⟨hO.isClosed_compl, ?_⟩
  have hcompact : IsCompact (Set.range phi) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hphi.continuous
  have hopen : IsOpen (Set.range phi)ᶜ := hcompact.isClosed.isOpen_compl
  have hsubset : (Set.range phi)ᶜ ⊆
      {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}} := by
    intro z hz
    rintro ⟨y, hy, heq⟩
    exact hz ⟨y, heq⟩
  intro z hz
  apply interior_maximal hsubset hopen
  intro hzrange
  rcases hzrange with ⟨y, rfl⟩
  apply hz
  refine ⟨apm_t00A01_unitToLarge y, ?_, ?_⟩
  · change dist y.1 0 < 2
    have hy : dist y.1 0 ≤ 1 := Metric.mem_closedBall.mp y.2
    linarith
  · exact congrFun hΦphi y

/-- LEAF (collar coordinates): `Φ` restricts to a homeomorphism of pairs from the
open radius-two ball, relative to the shell `1 ≤ ‖x‖ < 2`, onto the excised pair
`(Φ(ball 0 2), Φ(ball 0 2) ∖ φ(ball 0 1))`; hence their relative `H₄` agree.
Expected route: build the homeomorphism from `hΦ` and `hO`, check the pair
condition from `hΦphi`, and apply
`ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularHomologyIsoOfHomeomorphPair`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_coords
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M)
    (Φ : apm_t00A01_LargeDisk3 → M) (hΦ : Topology.IsEmbedding Φ)
    (hΦphi : Φ ∘ apm_t00A01_unitToLarge = phi)
    (hO : IsOpen (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})) :
    Nonempty
      (((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.SingularExcision.excisedSubspace
            {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}}
            (Φ '' {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})ᶜ)).homology 4) ≅
        ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          {x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 | 1 ≤ ‖x.1‖}).homology 4)) := by
  let U : Set apm_t00A01_LargeDisk3 := {x | dist x.1 0 < 2}
  let e₀ : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 ≃ₜ U := {
    toFun := fun (x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2) =>
      (⟨⟨x.1, by
        change dist x.1 0 ≤ 2
        exact le_of_lt x.2⟩, x.2⟩ :
        {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2})
    invFun := fun (x : {x : apm_t00A01_LargeDisk3 | dist x.1 0 < 2}) =>
      (⟨x.1.1, x.2⟩ : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have himage : Φ '' U = ((Φ '' U)ᶜ)ᶜ := by simp
  let e : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 ≃ₜ
      ↥(((Φ '' U)ᶜ)ᶜ : Set M) :=
    e₀.trans ((hΦ.homeomorphImage U).trans (Homeomorph.setCongr himage))
  have he_apply (x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2) :
      (e x).1 = Φ ⟨x.1, by
        change dist x.1 0 ≤ 2
        exact le_of_lt x.2⟩ := rfl
  have hpair (x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2) :
      x ∈ {x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 | 1 ≤ ‖x.1‖} ↔
        e x ∈ ConstructionTargets.SingularExcision.excisedSubspace
          {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}}
          (Φ '' U)ᶜ := by
    change 1 ≤ ‖x.1‖ ↔ (e x).1 ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}
    rw [he_apply]
    constructor
    · intro hx
      rintro ⟨y, hy, heq⟩
      have heq' : (⟨x.1, by
          change dist x.1 0 ≤ 2
          exact le_of_lt x.2⟩ : apm_t00A01_LargeDisk3) =
          apm_t00A01_unitToLarge y := by
        apply hΦ.injective
        exact heq.symm.trans (congrFun hΦphi y).symm
      have hxy : x.1 = y.1 := congrArg Subtype.val heq'
      change dist y.1 0 < 1 at hy
      have : ‖y.1‖ < 1 := by simpa [dist_eq_norm] using hy
      apply (not_lt_of_ge hx)
      simpa [hxy] using this
    · intro hx
      by_contra hn
      have hlt : ‖x.1‖ < 1 := lt_of_not_ge hn
      let y : apm_t00A01_Disk3 := ⟨x.1, by
        simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hlt⟩
      apply hx
      refine ⟨y, ?_, ?_⟩
      · change dist y.1 0 < 1
        simpa [y, dist_eq_norm] using hlt
      · rw [← congrFun hΦphi y]
        rfl
  exact ⟨(ConstructionTargets.ChartPairRelativeHomologyTransport.relativeSingularHomologyIsoOfHomeomorphPair
    e _ _ hpair 4).symm⟩

/-- LEAF (`H₃` of the shell): the shell `1 ≤ ‖x‖ < 2` in the open radius-two ball
has vanishing `H₃`.  Route: the radial map `x ↦ x/‖x‖` is a deformation retraction onto
`S²` (`singularHomologyIsoOfHomotopyEquiv`), and `H₃(S²) = 0`
(`SphereHomology.sphereHomology_isZero_of_gt`). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_shell_aux_shellH3 :
    Limits.IsZero
      ((ConstructionTargets.SingularHomologyConcrete.SingularChains
        (TopCat.of {x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 | 1 ≤ ‖x.1‖})).homology 3) := by
  let S := {x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 | 1 ≤ ‖x.1‖}
  let U := T02A06.euclideanUnitSphere 3
  let r : C(S, U) :=
    { toFun := fun x ↦ ⟨NormedSpace.normalize x.1.1, by
        have hx0 : x.1.1 ≠ 0 := by
          intro hx
          have hmem := x.2
          change 1 ≤ ‖x.1.1‖ at hmem
          rw [hx, norm_zero] at hmem
          norm_num at hmem
        simpa [U, Metric.mem_sphere, dist_zero_right] using
          NormedSpace.norm_normalize hx0⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        rw [continuous_iff_continuousAt]
        intro x
        have hc : Continuous (fun y : S ↦ ‖y.1.1‖) :=
          continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val)
        have hx0 : ‖x.1.1‖ ≠ 0 := by
          apply ne_of_gt
          have hmem := x.2
          change 1 ≤ ‖x.1.1‖ at hmem
          linarith
        exact ((hc.continuousAt.inv₀ hx0).smul
          (continuous_subtype_val.comp continuous_subtype_val).continuousAt) }
  let i : C(U, S) :=
    { toFun := fun x ↦ ⟨⟨x.1, by
          change dist x.1 0 < 2
          have hx : ‖x.1‖ = 1 := by
            simpa [U, Metric.mem_sphere, dist_zero_right] using x.2
          simpa [dist_zero_right, hx]⟩, by
            have hx : ‖x.1‖ = 1 := by
              simpa [U, Metric.mem_sphere, dist_zero_right] using x.2
            exact hx.ge⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val }
  let H : ContinuousMap.Homotopy (i.comp r) (ContinuousMap.id S) :=
    { toFun := fun tx ↦ by
        let t : ℝ := tx.1
        let x : EuclideanSpace ℝ (Fin 3) := tx.2.1.1
        let a : ℝ := (1 - t) * ‖x‖⁻¹ + t
        refine ⟨⟨a • x, ?_⟩, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
          have hx0 : 0 < ‖x‖ := by
            have hmem := tx.2.2
            change 1 ≤ ‖tx.2.1.1‖ at hmem
            dsimp [x]
            linarith
          have hx2 : ‖x‖ < 2 := by
            have h := tx.2.1.2
            change dist x 0 < 2 at h
            simpa [dist_zero_right] using h
          have ht0 : 0 ≤ t := tx.1.2.1
          have ht1 : t ≤ 1 := tx.1.2.2
          have ha0 : 0 ≤ a := add_nonneg
            (mul_nonneg (sub_nonneg.mpr ht1) (inv_nonneg.mpr (norm_nonneg x))) ht0
          rw [abs_of_nonneg ha0]
          have hxne : ‖x‖ ≠ 0 := hx0.ne'
          dsimp [a]
          field_simp
          nlinarith
        · change 1 ≤ ‖a • x‖
          rw [norm_smul, Real.norm_eq_abs]
          have hx0 : 0 < ‖x‖ := by
            have hmem := tx.2.2
            change 1 ≤ ‖tx.2.1.1‖ at hmem
            dsimp [x]
            linarith
          have ht0 : 0 ≤ t := tx.1.2.1
          have ht1 : t ≤ 1 := tx.1.2.2
          have ha0 : 0 ≤ a := add_nonneg
            (mul_nonneg (sub_nonneg.mpr ht1) (inv_nonneg.mpr (norm_nonneg x))) ht0
          rw [abs_of_nonneg ha0]
          have hxne : ‖x‖ ≠ 0 := hx0.ne'
          have hx1 : 1 ≤ ‖x‖ := by
            have hmem := tx.2.2
            change 1 ≤ ‖tx.2.1.1‖ at hmem
            simpa [x] using hmem
          dsimp [a]
          field_simp
          nlinarith
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        have hn : Continuous (fun tx : unitInterval × S ↦ ‖tx.2.1.1‖) :=
          continuous_norm.comp
            (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
        have hne : ∀ tx : unitInterval × S, ‖tx.2.1.1‖ ≠ 0 := by
          intro tx
          apply ne_of_gt
          have hmem := tx.2.2
          change 1 ≤ ‖tx.2.1.1‖ at hmem
          linarith
        have ht : Continuous (fun tx : unitInterval × S ↦ (tx.1 : ℝ)) :=
          continuous_subtype_val.comp continuous_fst
        have hx : Continuous (fun tx : unitInterval × S ↦ tx.2.1.1) :=
          continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
        exact (((continuous_const.sub ht).mul (hn.inv₀ hne)).add ht).smul hx
      map_zero_left := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        simp [i, r, NormedSpace.normalize]
      map_one_left := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        simp }
  let e : ContinuousMap.HomotopyEquiv U S :=
    { toFun := i
      invFun := r
      left_inv := by
        rw [show r.comp i = ContinuousMap.id U by
          apply ContinuousMap.ext
          intro x
          apply Subtype.ext
          exact NormedSpace.normalize_eq_self_of_norm_eq_one (by
            dsimp [i]
            have hx : dist x.1 0 = 1 := by
              exact x.2
            simpa [dist_zero_right] using hx)]
      right_inv := ⟨H⟩ }
  exact (ConstructionTargets.SphereHomology.sphereHomology_isZero_of_gt 2 3
    (by omega)).of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv e.symm 3)

/-- (shell vs puncture, purely Euclidean): the open radius-two ball relative to
the shell `1 ≤ ‖x‖ < 2` and the open unit disk relative to its punctured part have
isomorphic relative `H₄`.  Routes: rescale by `1/2` onto `euclideanOpenDisk 3`
(shell ↦ `1/2 ≤ ‖x‖ < 1`), then compare that shell with the punctured disk by the
radial deformation retraction and the five lemma on the two long exact sequences. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_shell :
    Nonempty
      (((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          {x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 | 1 ≤ ‖x.1‖}).homology 4) ≅
        ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.T02A06HemisphereExcision.puncturedOpenDiskSet 3)).homology 4)) := by
  open ConstructionTargets.SingularHomologyConcrete in
   open ConstructionTargets.T02A06DiskRadialComparison in
    have hshell : Limits.IsZero ((SingularChains (TopCat.of
          {x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 | 1 ≤ ‖x.1‖})).homology 3) :=
      apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_shell_aux_shellH3
    have hamb : Limits.IsZero ((SingularChains (TopCat.of
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2))).homology 4) := by
      letI : ContractibleSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2) :=
        Metric.contractibleSpace_ball (by norm_num)
      exact contractibleHigherHomology_isZero _ 4 (by omega)
    have hleft : Limits.IsZero ((RelativeSingularChains
        {x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 2 | 1 ≤ ‖x.1‖}).homology 4) :=
      (singularPairHomology_exact_relative _ 3).isZero_X₂ (hamb.eq_of_src _ _) (hshell.eq_of_tgt _ _)
    have hright : Limits.IsZero ((RelativeSingularChains
        (ConstructionTargets.T02A06HemisphereExcision.puncturedOpenDiskSet 3)).homology 4) := by
      have hi : IsIso (HomologicalComplex.homologyMap
          (ConstructionTargets.SingularExcision.relativeSingularMap (closedDiskBoundarySet 3)
            (ConstructionTargets.T02A06HemisphereExcision.puncturedOpenDiskSet 3)
            (halfDiskMap 3) (halfDiskMap_mapsTo 3)) 4) :=
        closedDiskPair_to_openDiskPair_homologyMap_isIso 3 4 (by omega)
      have hz : Limits.IsZero ((RelativeSingularChains (closedDiskBoundarySet 3)).homology 4) :=
        apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_model
      exact hz.of_iso (@asIso _ _ _ _ _ hi).symm
    exact ⟨hleft.isoZero ≪≫ hright.isoZero.symm⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (hcollar : apm_t00A01_HasBallCollar phi) :
    ∃ Z : Set M, IsClosed Z ∧
      Z ⊆ interior {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}} ∧
      Nonempty
        (((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
            (ConstructionTargets.SingularExcision.excisedSubspace
              {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}} Z)).homology 4) ≅
          ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
            (ConstructionTargets.T02A06HemisphereExcision.puncturedOpenDiskSet 3)).homology 4)) := by
  obtain ⟨Φ, hΦ, hΦphi, hO⟩ := hcollar
  obtain ⟨hZ, hZsub⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_Z
      M phi hphi Φ hΦphi hO
  obtain ⟨e₁⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_coords
      M phi Φ hΦ hΦphi hO
  obtain ⟨e₂⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar_aux_shell
  exact ⟨_, hZ, hZsub, ⟨e₁ ≪≫ e₂⟩⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (hcollar : apm_t00A01_HasBallCollar phi) :
    Nonempty
      (((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}}).homology 4) ≅
        ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
          (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 3)).homology 4)) := by
  obtain ⟨Z, hZc, hZ, ⟨e⟩⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_collar
      M phi hphi hcollar
  obtain ⟨g⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_general
      _ Z hZc hZ
  obtain ⟨r⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision_aux_radial
  exact ⟨g ≪≫ e ≪≫ r⟩

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (hcollar : apm_t00A01_HasBallCollar phi) :
    Limits.IsZero
      ((ConstructionTargets.SingularHomologyConcrete.RelativeSingularChains
        {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}}).homology 4) := by
  rcases apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_excision
    M phi hphi hcollar with ⟨e⟩
  exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4_aux_model.of_iso
    e
/-- LIBRARY (comparison with local homology at the centre): the pair projection
`H₃(M) → H₃(M, M ∖ int B)` is invertible when localization at `phi 0` is.
Route: the identity is a map of pairs `(M, M ∖ int B) → (M, M ∖ {phi 0})`;
`M ∖ int B ↪ M ∖ {phi 0}` is a homotopy equivalence (radial deformation of
`phi(B ∖ 0)` onto the boundary sphere, glued with the identity along the closed
cover), so `SingularExcision.relativeSingularMap_homologyMap_isIso` makes the
relative map invertible, and `relativeSingularMap_projection_naturality`
factors `localizationMap (phi 0) 3` through the projection. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_proj
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (hcollar : apm_t00A01_HasBallCollar phi)
    (hloc : IsIso (ConstructionTargets.ManifoldFundamentalClass.localizationMap
      (phi ⟨0, by simp [apm_t00A01_Disk3]⟩) 3)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection
        {x : M | x ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}}) 3) := by
  obtain ⟨Φ, hΦ, hΦφ, hΦo⟩ := hcollar
  have hp0 : phi ⟨0, by simp [apm_t00A01_Disk3]⟩ =
      Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩ := by
    rw [← hΦφ]
    rfl
  let x : M := Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩
  let A : Set M := {z | z ∉ phi '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1}}
  let B : Set M := ConstructionTargets.LocalHomologyNeighborhoodExcision.deletedPoint x
  let f : C(M, M) := ContinuousMap.id M
  have hf : Set.MapsTo f A B := by
    intro z hz
    change z ≠ x
    intro hzx
    apply hz
    refine ⟨⟨0, by simp [apm_t00A01_Disk3]⟩, by simp, ?_⟩
    exact hp0.trans (by simpa [x] using hzx.symm)
  obtain ⟨hmap, hmap1⟩ :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_mapsTo
      phi Φ hΦ.injective hΦφ
  have hcont :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2_aux_hequiv_aux_continuousOn
      Φ hΦ hΦo
  have hHc : Continuous (fun p : unitInterval × ↑B ↦
      apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1) :=
    hcont.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p ↦ ⟨mem_univ _, p.2.2⟩)
  let i : C(apm_t00A01_punctured phi, ↑B) :=
    ⟨fun z ↦ ⟨z.1, fun hz ↦ z.2 ⟨⟨0, by simp [apm_t00A01_Disk3]⟩, by simp,
      by rw [hp0]; exact hz.symm⟩⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩
  let rinv : C(↑B, apm_t00A01_punctured phi) :=
    ⟨fun z ↦ ⟨apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ 1 z.1,
        hmap1 z.2⟩,
      (hHc.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let F : ContinuousMap.Homotopy (ContinuousMap.id _) (i.comp rinv) :=
    { toFun := fun p ↦
        ⟨apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H Φ p.1 p.2.1,
          hmap p.1 p.2.2⟩
      continuous_toFun := hHc.subtype_mk _
      map_zero_left := fun z ↦ Subtype.ext
        (apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_zero Φ z.1)
      map_one_left := fun z ↦ rfl }
  have hri : rinv.comp i = ContinuousMap.id _ := by
    ext z
    exact apm_t00A01_punctured_fundamentalGroup_aux_enlarged_hequiv_aux_H_one
      phi Φ hΦφ z.1 z.2
  let e : ContinuousMap.HomotopyEquiv (apm_t00A01_punctured phi) ↑B :=
    { toFun := i
      invFun := rinv
      left_inv := by rw [hri]
      right_inv := ⟨F.symm⟩ }
  have he : TopCat.ofHom e.toFun =
      ConstructionTargets.SingularExcision.subspaceMap A B f hf := by
    ext z
    rfl
  have hsub (n : ℕ) : IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
          (ConstructionTargets.SingularExcision.subspaceMap A B f hf)) n) := by
    rw [← he]
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom e.toFun))
    rw [← ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom e n]
    infer_instance
  let r := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularExcision.relativeSingularMap A B f hf) 3
  have hr : IsIso r := by
    apply ConstructionTargets.SingularExcision.relativeSingularMap_homologyMap_isIso A B f hf 3
    · exact hsub 3
    · change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 3).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f))
      change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 3).obj
          (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of M)))
      infer_instance
    · intro j hj
      exact hsub j
    · intro j hj
      change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat j).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f))
      change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat j).obj
          (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of M)))
      infer_instance
  letI : IsIso r := hr
  let qA := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection A) 3
  let qB := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.relativeSingularProjection B) 3
  have hqB : IsIso qB := by
    change IsIso (ConstructionTargets.ManifoldFundamentalClass.localizationMap
      (Φ ⟨0, by simp [apm_t00A01_LargeDisk3]⟩) 3)
    exact hp0 ▸ hloc
  letI : IsIso qB := hqB
  let a := ((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)
  have hnat := congrArg
      (fun k ↦ HomologicalComplex.homologyMap k 3)
      (ConstructionTargets.SingularExcision.relativeSingularMap_projection_naturality A B f hf)
  haveI : IsIso (HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)) 3) := by
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of M)))
    infer_instance
  simp only [HomologicalComplex.homologyMap_comp] at hnat
  haveI : IsIso (qA ≫ r) := by
    dsimp [qA, r]
    rw [← hnat]
    change IsIso (HomologicalComplex.homologyMap a 3 ≫ qB)
    have ha : IsIso (HomologicalComplex.homologyMap a 3) := by
      dsimp [a]
      change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 3).obj
        (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of M)))
      infer_instance
    letI : IsIso (HomologicalComplex.homologyMap a 3) := ha
    infer_instance
  have : IsIso qA := IsIso.of_isIso_comp_right qA r
  dsimp [qA, A] at this
  exact this

/-- LIBRARY: the same collar/pair comparison in the adjacent degree gives
vanishing of degree three of the punctured manifold. Assembled from `_aux_les`, `_aux_rel4`, `_aux_proj`. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3
    (M : Type) [TopologicalSpace M] [T2Space M]
    (phi : apm_t00A01_Disk3 → M) (hphi : Topology.IsEmbedding phi)
    (hcollar : apm_t00A01_HasBallCollar phi)
    (hloc : IsIso (ConstructionTargets.ManifoldFundamentalClass.localizationMap
      (phi ⟨0, by simp [apm_t00A01_Disk3]⟩) 3)) :
    Limits.IsZero (apm_t00A01_H 3 (apm_t00A01_punctured phi)) :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
    _ 3
    (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_les _
      (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_rel4 M phi hphi hcollar)
      (apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3_aux_proj M phi hphi hcollar hloc))

lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ)
    (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (eUA : ContinuousMap.HomotopyEquiv U (apm_t00A01_punctured φ))
    (eVB : ContinuousMap.HomotopyEquiv V apm_t00A01_Disk3)
    (eIS : ContinuousMap.HomotopyEquiv (U ∩ V : Set M) apm_t00A01_Sphere2) :
    IsIso (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionConnecting
      U V hU hV hUV 2) :=
  open ConstructionTargets.T00A01MayerVietorisAdapters
    ConstructionTargets.SingularHomologyConcrete in by
  let x : apm_t00A01_Disk3 := ⟨0, by simp [apm_t00A01_Disk3]⟩
  have hloc :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_localization
      M hM (φ x)
  have hA2 :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H2
      M hM φ hφ hcollar (by simpa [x] using hloc)
  have hA3 :=
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting_aux_H3
      M φ hφ hcollar (by simpa [x] using hloc)
  have hU2 : Limits.IsZero (SingularHomology 2 (TopCat.of U)) :=
    (groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of (apm_t00A01_punctured φ)) 2 hA2).of_iso
      (singularHomologyIsoOfHomotopyEquiv eUA 2)
  have hU3 : Limits.IsZero (SingularHomology 3 (TopCat.of U)) :=
    (groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of (apm_t00A01_punctured φ)) 3 hA3).of_iso
      (singularHomologyIsoOfHomotopyEquiv eUA 3)
  have hD := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_disk
  have hV2 : Limits.IsZero (SingularHomology 2 (TopCat.of V)) :=
    (groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of apm_t00A01_Disk3) 2 (hD.2 2 (by omega))).of_iso
      (singularHomologyIsoOfHomotopyEquiv eVB 2)
  have hV3 : Limits.IsZero (SingularHomology 3 (TopCat.of V)) :=
    (groupHomologyIsZeroOfModuleHomologyIsZero
      (TopCat.of apm_t00A01_Disk3) 3 (hD.2 3 (by omega))).of_iso
      (singularHomologyIsoOfHomotopyEquiv eVB 3)
  exact productionConnecting_isIso_of_pieces_isZero
    U V hU hV hUV 2 hU3 hV3 hU2 hV2

/-- ASSEMBLY.  The only topology used here is the separately stated fact that
the collar-cover connecting map is invertible; the remaining step is the
abstract Mayer--Vietoris algebra above. -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) (k : ℕ)
    (hk : k = 2 ∨ k = 3) :
    Limits.IsZero (apm_t00A01_H k (apm_t00A01_punctured φ)) := by
  let hcover := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_cover
    M φ hφ hcollar
  rcases hcover with ⟨U, V, hU, hV, hUV, ⟨eUA⟩, ⟨eVB⟩, ⟨eIS⟩⟩
  have hconn := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting
    M φ hφ hM hcollar U V hU hV hUV eUA eVB eIS
  apply apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_algebra
    M (apm_t00A01_punctured φ) apm_t00A01_Disk3 hM
    apm_t00A01_punctured_isHomologyBall_aux_positive_aux_disk
    U V hU hV hUV eUA eVB eIS hconn k hk

/-- ASSEMBLY (from `_aux_cover`, `_aux_disk`, `_aux_mv`, `_aux_mid`). -/
lemma apm_t00A01_punctured_isHomologyBall_aux_positive
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold apm_t00A01_Model3 ∞ M]
    [BoundarylessManifold apm_t00A01_Model3 M]
    (φ : apm_t00A01_Disk3 → M) (hφ : Topology.IsEmbedding φ)
    (hM : apm_t00A01_isHomology3Sphere M)
    (hcollar : apm_t00A01_HasBallCollar φ) :
    ∀ k : ℕ, k ≠ 0 → Limits.IsZero (apm_t00A01_H k (apm_t00A01_punctured φ)) := by
  intro k hk
  have hcov := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_cover M φ hφ hcollar
  have hD := apm_t00A01_punctured_isHomologyBall_aux_positive_aux_disk
  by_cases hmid : k = 2 ∨ k = 3
  · exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid
      M φ hφ hM hcollar k hmid
  · exact apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mv
      M _ _ hM hD hcov k (by omega)

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
  classical
  let C := apm_t00A01_collarSet φ Φ
  let j : C → Set.range Φ := fun x ↦
    ⟨x.1.1, by
      rcases x.2 with ⟨y, hy, hxy⟩
      exact ⟨y, hxy⟩⟩
  let c : C → apm_t00A01_LargeDisk3 := fun x ↦ hΦ.toHomeomorph.symm (j x)
  have hj : Continuous j := by
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have hc : Continuous c := hΦ.toHomeomorph.symm.continuous.comp hj
  have hc_image (x : C) : Φ (c x) = x.1.1 := by
    exact congrArg Subtype.val (hΦ.toHomeomorph.apply_symm_apply (j x))
  have hc_norm (x : C) : 1 ≤ ‖(c x).1‖ :=
    apm_t00A01_collared_standardCover_aux_left_aux_norm_ge_one φ Φ hext x.1 (c x)
      (hc_image x)
  have hc_ne (x : C) : ‖(c x).1‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hc_norm x))
  let rv : C → EuclideanSpace ℝ (Fin 3) := fun x ↦ (‖(c x).1‖)⁻¹ • (c x).1
  have hrv_norm (x : C) : ‖rv x‖ = 1 := by
    simp [rv, norm_smul, Real.norm_of_nonneg (norm_nonneg _), hc_ne x]
  let r : C( C, apm_t00A01_Sphere2) :=
    ⟨fun x ↦ ⟨rv x, by simpa [Metric.mem_sphere, dist_zero_right] using hrv_norm x⟩, by
      apply Continuous.subtype_mk
      exact ((continuous_norm.comp
        (continuous_subtype_val.comp hc)).inv₀ (fun x ↦ hc_ne x)).smul
          (continuous_subtype_val.comp hc)⟩
  let v : C × unitInterval → EuclideanSpace ℝ (Fin 3) := fun p ↦
    ((1 - (p.2 : ℝ)) + (p.2 : ℝ) * (‖(c p.1).1‖)⁻¹) • (c p.1).1
  have hv_norm (p : C × unitInterval) :
      ‖v p‖ = (1 - (p.2 : ℝ)) * ‖(c p.1).1‖ + (p.2 : ℝ) := by
    have hn : 0 < ‖(c p.1).1‖ := lt_of_lt_of_le zero_lt_one (hc_norm p.1)
    have ht0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
    have ht1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
    have hinv : 0 < (‖(c p.1).1‖)⁻¹ := inv_pos.mpr hn
    have ha : 0 ≤ (1 - (p.2 : ℝ)) + (p.2 : ℝ) * (‖(c p.1).1‖)⁻¹ := by
      have hprod : 0 ≤ (p.2 : ℝ) * (‖(c p.1).1‖)⁻¹ :=
        mul_nonneg ht0 hinv.le
      linarith
    simp only [v, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg ha]
    field_simp
  have hv_ge (p : C × unitInterval) : 1 ≤ ‖v p‖ := by
    rw [hv_norm]
    nlinarith [hc_norm p.1, p.2.2.1, p.2.2.2]
  have hv_le (p : C × unitInterval) : ‖v p‖ ≤ 2 := by
    rw [hv_norm]
    have hn2 : ‖(c p.1).1‖ ≤ 2 := by
      have hh := (c p.1).2
      change dist (c p.1).1 0 ≤ 2 at hh
      simpa [dist_zero_right] using hh
    nlinarith [p.2.2.1, p.2.2.2]
  let w : C × unitInterval → apm_t00A01_LargeDisk3 := fun p ↦
    ⟨v p, by simpa [Metric.mem_closedBall, dist_zero_right] using hv_le p⟩
  have hw_cont : Continuous w := by
    apply Continuous.subtype_mk
    exact (((continuous_const.sub
      (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_snd).mul
          ((continuous_norm.comp
            (continuous_subtype_val.comp (hc.comp continuous_fst))).inv₀
              (fun p ↦ hc_ne p.1)))).smul
        (continuous_subtype_val.comp (hc.comp continuous_fst)))
  have hw_punctured (p : C × unitInterval) :
      Φ (w p) ∉ φ '' {y : apm_t00A01_Disk3 | dist y.1 0 < 1} := by
    rintro ⟨y, hy, heq⟩
    have heq' : w p = apm_t00A01_unitToLarge y := by
      apply hΦ.injective
      exact heq.symm.trans (congrFun hext y).symm
    have : ‖v p‖ < 1 := by
      have hv : v p = y.1 := congrArg Subtype.val heq'
      rw [hv]
      simpa [dist_zero_right] using hy
    exact (not_lt_of_ge (hv_ge p)) this
  let H : C(C × unitInterval, apm_t00A01_punctured φ) :=
    ⟨fun p ↦ ⟨Φ (w p), hw_punctured p⟩,
      Continuous.subtype_mk (hΦ.continuous.comp hw_cont) _⟩
  refine ⟨r, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    apply Subtype.ext
    change rv ⟨apm_t00A01_boundaryMap φ hφ.injective s, hs⟩ = s.1
    have hc_eq : c ⟨apm_t00A01_boundaryMap φ hφ.injective s, hs⟩ =
        apm_t00A01_unitToLarge
          ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩ := by
      apply hΦ.injective
      rw [hc_image]
      exact (congrFun hext _).symm
    have hs_norm : ‖s.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using s.2
    simp [rv, hc_eq, apm_t00A01_unitToLarge, hs_norm]
  · intro x
    apply Subtype.ext
    change Φ (w (x, 0)) = x.1.1
    rw [show w (x, 0) = c x by
      apply Subtype.ext
      simp [w, v]]
    exact hc_image x
  · intro x
    apply Subtype.ext
    change Φ (w (x, 1)) = φ _
    rw [show w (x, 1) = apm_t00A01_unitToLarge
        ⟨rv x, by simpa [Metric.mem_closedBall, dist_zero_right] using (hrv_norm x).le⟩ by
      apply Subtype.ext
      change v (x, 1) = rv x
      simp [v, rv]]
    exact congrFun hext _
  · intro p
    change Φ (w p) ∈ Φ '' {y : apm_t00A01_LargeDisk3 | dist y.1 0 < 2}
    refine ⟨w p, ?_, rfl⟩
    have hc_lt : ‖(c p.1).1‖ < 2 := by
      rcases p.1.2 with ⟨y, hy, hyeq⟩
      have : c p.1 = y := hΦ.injective ((hc_image p.1).trans hyeq.symm)
      simpa [this, dist_zero_right] using hy
    have hvlt : ‖v p‖ < 2 := by
      rw [hv_norm]
      have hprod : 0 ≤ (p.2 : ℝ) * (‖(c p.1).1‖ - 1) :=
        mul_nonneg p.2.2.1 (sub_nonneg.mpr (hc_norm p.1))
      nlinarith
    simpa [w, dist_zero_right] using hvlt
  · intro s hs t
    apply Subtype.ext
    change Φ (w (⟨_, hs⟩, t)) = φ _
    have hc_eq : c ⟨apm_t00A01_boundaryMap φ hφ.injective s, hs⟩ =
        apm_t00A01_unitToLarge
          ⟨s.1, by simpa [Metric.mem_closedBall, dist_comm] using le_of_eq s.2⟩ := by
      apply hΦ.injective
      rw [hc_image]
      exact (congrFun hext _).symm
    have hs_norm : ‖s.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using s.2
    rw [show w (⟨_, hs⟩, t) = apm_t00A01_unitToLarge
        ⟨s.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hs_norm.le⟩ by
      apply Subtype.ext
      simp [w, v, hc_eq, apm_t00A01_unitToLarge, hs_norm]]
    exact congrFun hext _

/-- LEAF. Continuity through the gluing quotient, with a time parameter. If
`P` is an open set of representatives and `S` the corresponding (saturated)
set of glued points, a map out of `unitInterval × S` is continuous as soon as
its pullback to `unitInterval × P` is. Proof: the quotient map restricted to
`P → S` is a quotient map (`Topology.IsQuotientMap.restrictPreimage_isOpen`,
after `Homeomorph.setCongr hsat`), and `unitInterval` is locally compact, so
`Topology.IsQuotientMap.continuous_lift_prod_right` applies. The time-free
case follows by precomposing with `fun x ↦ (0, x)`. Used for the left, right
and overlap quotient steps. -/
lemma apm_t00A01_collared_standardCover_aux_quotient_continuous {A B Z : Type}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (S : Set (apm_t00A01_connectedSum iA iB)) (P : Set (Sum A B)) (hP : IsOpen P)
    (hsat : (fun z : Sum A B ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) z) ⁻¹' S = P)
    (F : unitInterval × ↥S → Z)
    (hF : Continuous fun p : unitInterval × ↥P ↦
      F (p.1, ⟨Quotient.mk (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) p.2.1,
        (Set.ext_iff.mp hsat p.2.1).mpr p.2.2⟩)) :
    Continuous F := by
  let q : Sum A B → apm_t00A01_connectedSum iA iB := fun z ↦ Quotient.mk _ z
  have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
  have hS : IsOpen S := by
    rw [← hq.isOpen_preimage]
    change IsOpen ((fun z : Sum A B ↦ Quotient.mk
      (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) z) ⁻¹' S)
    rw [hsat]
    exact hP
  have hqS : Topology.IsQuotientMap (S.restrictPreimage q) :=
    hq.restrictPreimage_isOpen hS
  let e : ↥P ≃ₜ ↥(q ⁻¹' S) := Homeomorph.setCongr hsat.symm
  have he : Topology.IsQuotientMap e := e.isQuotientMap
  have hcomp : S.restrictPreimage q ∘ e = fun x : ↥P ↦
      (⟨Quotient.mk (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) x.1,
        (Set.ext_iff.mp hsat x.1).mpr x.2⟩ : ↥S) := by
    funext x
    rfl
  apply (hqS.comp he).continuous_lift_prod_right
  simpa only [hcomp] using hF

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
  classical
  let q : Sum A B → apm_t00A01_connectedSum iA iB := fun z => Quotient.mk _ z
  let U := apm_t00A01_thickLeft iA iB C
  have hU : IsOpen U :=
    (apm_t00A01_collared_standardCover_aux_open iA iB Set.univ C
      isOpen_univ hC (fun _ => Set.mem_univ _) hiB).1
  have hpre : q ⁻¹' U = Set.range Sum.inl ∪ Sum.inr '' C := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, heq⟩
      have hinv {x y : Sum A B}
          (hxy : Relation.EqvGen (apm_t00A01_glueRel iA iB) x y) :
          (x ∈ Set.range Sum.inl ∪ Sum.inr '' C) ↔
            y ∈ Set.range Sum.inl ∪ Sum.inr '' C := by
        induction hxy with
        | rel x y h =>
            cases h with
            | glue s => simp [hiB s]
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
      have hrel : Relation.EqvGen (apm_t00A01_glueRel iA iB) z w :=
        (Quotient.exact heq).symm
      exact (hinv hrel).2 hw
    · intro z hz
      exact ⟨z, hz, rfl⟩
  let s0 : apm_t00A01_Sphere2 :=
    ⟨(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)), by
      simp [Metric.mem_sphere, dist_zero_right]⟩
  let rb : B → apm_t00A01_Sphere2 := fun b =>
    if hb : b ∈ C then r ⟨b, hb⟩ else s0
  have hrb (s : apm_t00A01_Sphere2) : rb (iB s) = s := by
    simp [rb, hiB s, hr s]
  let f0 : apm_t00A01_connectedSum iA iB → A :=
    Quotient.lift (Sum.elim id (fun b => iA (rb b))) (by
      intro x y hxy
      induction hxy with
      | rel x y h =>
          cases h with
          | glue s => simp [hrb s]
      | refl => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)
  let f : U → A := fun x => f0 x.1
  have hf : Continuous f := by
    have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
    let e : (Set.range Sum.inl ∪ Sum.inr '' C : Set (Sum A B)) ≃ₜ q ⁻¹' U :=
      Homeomorph.setCongr hpre.symm
    have hn : Continuous (fun z : (Set.range Sum.inl ∪ Sum.inr '' C : Set (Sum A B)) =>
        f ((U.restrictPreimage q) (e z))) := by
      let eL : A → (Set.range Sum.inl ∪ Sum.inr '' C : Set (Sum A B)) :=
        fun a => ⟨(@Sum.inl A B) a, Or.inl ⟨a, rfl⟩⟩
      let eR : C → (Set.range Sum.inl ∪ Sum.inr '' C : Set (Sum A B)) :=
        fun b => ⟨(@Sum.inr A B) b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
      have heL : Topology.IsOpenEmbedding eL := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inl
        · intro a a' h
          exact Sum.inl.inj (congrArg Subtype.val h)
        · exact (Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.codRestrict _
      have heR : Topology.IsOpenEmbedding eR := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inr.comp continuous_subtype_val
        · intro b b' h
          exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.comp
            hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have hcL : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) := by
        change Continuous (fun a : A => a)
        exact continuous_id
      have hcR : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) := by
        rw [show ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) =
            fun b : C => iA (r b) by
          funext b
          change iA (if hb : b.1 ∈ C then r ⟨b.1, hb⟩ else s0) = iA (r b)
          simp [b.2]]
        exact hiA.comp r.continuous
      rw [← continuousOn_univ]
      have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
        ext ⟨z, hz⟩
        cases z with
        | inl a => simp [eL]
        | inr b =>
            rcases hz with ⟨_, h⟩ | ⟨b', hb', h⟩
            · cases h
            · have : b = b' := Sum.inr.inj h.symm
              subst b'
              simp [eR, hb']
      rw [← hcover]
      have hcLi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eL '' Set.univ) := heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
      have hcRi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eR '' Set.univ) := heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
      have hoL : IsOpen (eL '' Set.univ) := by
        simpa only [Set.image_univ] using heL.isOpen_range
      have hoR : IsOpen (eR '' Set.univ) := by
        simpa only [Set.image_univ] using heR.isOpen_range
      simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi hoL hoR
    rw [show f ∘ U.restrictPreimage q =
        (fun z => f ((U.restrictPreimage q) (e z))) ∘ e.symm by
      funext x
      rfl]
    exact hn.comp e.symm.continuous
  let g : A → U := fun a => ⟨q (.inl a), ⟨.inl a, Or.inl ⟨a, rfl⟩, rfl⟩⟩
  have hg : Continuous g := by
    exact Continuous.subtype_mk
      (continuous_coinduced_rng.comp continuous_inl) _
  let Kraw : unitInterval × apm_t00A01_connectedSum iA iB →
      apm_t00A01_connectedSum iA iB := fun p =>
    Quotient.lift (Sum.elim (fun a => q (.inl a))
      (fun b => q (.inr (if hb : b ∈ C then H (⟨b, hb⟩, p.1) else b)))) (by
        intro x y hxy
        change (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)).r x y at hxy
        change Relation.EqvGen (apm_t00A01_glueRel iA iB) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | glue s =>
                simp [hiB s, hHfix s p.1, q]
                exact apm_t00A01_mk_inl_eq_mk_inr iA iB s
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    rcases p.2.2 with ⟨z, hz, heq⟩
    rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨Sum.inl a, Or.inl ⟨a, rfl⟩, by rw [← heq]; simp [Kraw, q]⟩
    · exact ⟨Sum.inr (H (⟨b, hb⟩, p.1)),
        Or.inr ⟨_, hHC (⟨b, hb⟩, p.1), rfl⟩, by rw [← heq]; simp [Kraw, q, hb]⟩⟩
  have hK : Continuous K := by
    let P : Set (Sum A B) := Set.range Sum.inl ∪ Sum.inr '' C
    have hP : IsOpen P :=
      (Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpen_range.union
        ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap C hC)
    apply apm_t00A01_collared_standardCover_aux_quotient_continuous
      iA iB U P hP hpre K
    let jL : A → P := fun a => ⟨Sum.inl a, Or.inl ⟨a, rfl⟩⟩
    let jR : C → P := fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
    have hjL : Topology.IsOpenEmbedding jL := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk
        exact continuous_inl
      · intro a a' h
        exact Sum.inl.inj (congrArg Subtype.val h)
      · exact (Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.codRestrict _
    have hjR : Topology.IsOpenEmbedding jR := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk
        exact continuous_inr.comp continuous_subtype_val
      · intro b b' h
        exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
      · exact ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.comp
          hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
    let eL : unitInterval × A → unitInterval × P := fun p => (p.1, jL p.2)
    let eR : unitInterval × C → unitInterval × P := fun p => (p.1, jR p.2)
    have heL : Topology.IsOpenEmbedding eL := by
      exact Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
    have heR : Topology.IsOpenEmbedding eR := by
      exact Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
    let L := fun p : unitInterval × P =>
      K (p.1, ⟨q p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)
    have hcL : Continuous (L ∘ eL) := by
      apply Continuous.subtype_mk
      change Continuous (fun p : unitInterval × A => q (Sum.inl p.2))
      exact continuous_coinduced_rng.comp (continuous_inl.comp continuous_snd)
    have hcR : Continuous (L ∘ eR) := by
      apply Continuous.subtype_mk
      simpa [Function.comp_def, L, eR, jR, K, Kraw, q] using
        continuous_coinduced_rng.comp (continuous_inr.comp
          (H.continuous.comp (continuous_snd.prodMk continuous_fst)))
    rw [show (fun p : unitInterval × P =>
      K (p.1, ⟨Quotient.mk _ p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)) = L by
        rfl]
    rw [← continuousOn_univ]
    have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
      ext ⟨t, z, hz⟩
      rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
      · simp [eL, jL]
      · simp [eR, jR, hb]
    rw [← hcover]
    have hcLi : ContinuousOn L (eL '' Set.univ) :=
      heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
    have hcRi : ContinuousOn L (eR '' Set.univ) :=
      heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
    have hoL : IsOpen (eL '' Set.univ) := by
      simpa only [Set.image_univ] using heL.isOpen_range
    have hoR : IsOpen (eR '' Set.univ) := by
      simpa only [Set.image_univ] using heR.isOpen_range
    simpa only [Set.image_univ] using hcLi.union_of_isOpen hcRi hoL hoR
  let F : C(U, A) := ⟨f, hf⟩
  let G : C(A, U) := ⟨g, hg⟩
  refine ⟨{ toFun := F, invFun := G, left_inv := ?_, right_inv := ?_ }⟩
  · apply ContinuousMap.Homotopic.symm
    exact ⟨{
      toFun := fun p => K (p.1, p.2)
      continuous_toFun := hK
      map_zero_left := by
        intro x
        rcases x.2 with ⟨z, hz, heq⟩
        apply Subtype.ext
        simp only [Prod.fst, Prod.snd]
        change Kraw (0, x.1) = x.1
        rw [← heq]
        rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
        · simp [Kraw, q]
        · simp [Kraw, q, hb, hH0]
      map_one_left := by
        intro x
        rcases x.2 with ⟨z, hz, heq⟩
        apply Subtype.ext
        simp only [Prod.fst, Prod.snd]
        change Kraw (1, x.1) = (G.comp F x).1
        rw [← heq]
        rcases hz with ⟨a, rfl⟩ | ⟨b, hb, rfl⟩
        · have fx : f x = a := by
            change f0 x.1 = a
            rw [← heq]
            rfl
          simp [Kraw, G, F, g, q, fx]
        · have fx : f x = iA (r ⟨b, hb⟩) := by
            change f0 x.1 = iA (r ⟨b, hb⟩)
            rw [← heq]
            simp [f0, rb, hb]
          simp [Kraw, G, F, g, q, hb, hH1, fx]
          exact (apm_t00A01_mk_inl_eq_mk_inr iA iB (r ⟨b, hb⟩)).symm }⟩
  · have heq : F.comp G = ContinuousMap.id A := by
      ext a
      rfl
    rw [heq]

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
private lemma apm_t00A01_collared_standardCover_aux_right_aux_quotient_mem
    {A B : Type} (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (C : Set A) (hiA : ∀ s, iA s ∈ C) {x y : Sum A B}
    (hxy : Relation.EqvGen (apm_t00A01_glueRel iA iB) x y) :
    (x ∈ Sum.inl '' C ∪ Set.range Sum.inr) ↔
      (y ∈ Sum.inl '' C ∪ Set.range Sum.inr) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | glue s =>
          constructor <;> intro h
          · exact Or.inr ⟨iB s, rfl⟩
          · exact Or.inl ⟨iA s, hiA s, rfl⟩
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

private lemma apm_t00A01_collared_standardCover_aux_right_aux_quotient_preimage
    {A B : Type} (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (C : Set A) (hiA : ∀ s, iA s ∈ C) :
    (fun z : Sum A B ↦ Quotient.mk
      (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)) z) ⁻¹'
        apm_t00A01_thickRight iA iB C =
      Sum.inl '' C ∪ Set.range Sum.inr := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (apm_t00A01_collared_standardCover_aux_right_aux_quotient_mem
      iA iB C hiA (Quotient.exact heq.symm)).mpr hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- LEAF (split of job 119, claude-14 2026-10-20). A map out of
`unitInterval × (inl '' C ∪ range inr)` (C open) is continuous if it is continuous
on both pieces: `unitInterval × C` and `unitInterval × B` embed openly and cover.
Same argument as `hf` in `_aux_right_aux_quotient` (IsOpenEmbedding.inl/inr,
`IsOpenEmbedding.of_continuous_injective_isOpenMap`, `ContinuousOn.union_of_isOpen`),
times `unitInterval` (`IsOpenMap.prodMap`, `isOpenMap_id`). -/
lemma apm_t00A01_collared_standardCover_aux_right_aux_quotient_aux_cont
    {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (C : Set A) (hC : IsOpen C)
    (F : unitInterval × ↥((@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)) → X)
    (hL : Continuous fun p : unitInterval × ↥C =>
      F (p.1, ⟨Sum.inl p.2.1, Or.inl ⟨p.2.1, p.2.2, rfl⟩⟩))
    (hR : Continuous fun p : unitInterval × B =>
      F (p.1, ⟨Sum.inr p.2, Or.inr ⟨p.2, rfl⟩⟩)) :
    Continuous F := by
  let P : Set (Sum A B) :=
    (@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)
  let jL : C → P := fun a =>
    ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
  let jR : B → P := fun b =>
    ⟨Sum.inr b, Or.inr ⟨b, rfl⟩⟩
  have hjL : Topology.IsOpenEmbedding jL := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk
        ((continuous_inl (X := A) (Y := B)).comp continuous_subtype_val) _
    · intro a a' h
      exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    · exact ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.comp
          hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
  have hjR : Topology.IsOpenEmbedding jR := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Continuous.subtype_mk (continuous_inr (X := A) (Y := B)) _
    · intro b b' h
      exact Sum.inr.inj (congrArg Subtype.val h)
    · exact (Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.codRestrict _
  let eL : unitInterval × C → unitInterval × P := fun p => (p.1, jL p.2)
  let eR : unitInterval × B → unitInterval × P := fun p => (p.1, jR p.2)
  have heL : Topology.IsOpenEmbedding eL := by
    exact Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
  have heR : Topology.IsOpenEmbedding eR := by
    exact Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
  have hcL : Continuous (F ∘ eL) := by
    simpa [Function.comp_def, eL, jL, P] using hL
  have hcR : Continuous (F ∘ eR) := by
    simpa [Function.comp_def, eR, jR, P] using hR
  rw [← continuousOn_univ]
  have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
    ext ⟨t, z, hz⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
    · simp [eL, jL, P, ha]
    · simp [eR, jR, P]
  rw [← hcover]
  have hcLi : ContinuousOn F (eL '' Set.univ) :=
    heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
  have hcRi : ContinuousOn F (eR '' Set.univ) :=
    heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
  simpa only [Set.image_univ] using
    hcLi.union_of_isOpen hcRi
      (by simpa only [Set.image_univ] using heL.isOpen_range)
      (by simpa only [Set.image_univ] using heR.isOpen_range)

lemma apm_t00A01_collared_standardCover_aux_right_aux_quotient {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (hiB : Continuous iB) (C : Set A) (hC : IsOpen C) (hiA : ∀ s, iA s ∈ C)
    (r : C(↥C, apm_t00A01_Sphere2)) (H : C(↥C × unitInterval, A))
    (hr : ∀ s, r ⟨iA s, hiA s⟩ = s)
    (hH0 : ∀ x, H (x, 0) = x.1) (hH1 : ∀ x, H (x, 1) = iA (r x))
    (hHC : ∀ p, H p ∈ C) (hHfix : ∀ s t, H (⟨iA s, hiA s⟩, t) = iA s) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(apm_t00A01_thickRight iA iB C) B) := by
  classical
  let q : Sum A B → apm_t00A01_connectedSum iA iB := fun z => Quotient.mk _ z
  let U := apm_t00A01_thickRight iA iB C
  have hpre : q ⁻¹' U = Sum.inl '' C ∪ Set.range Sum.inr := by
    simpa [q, U] using
      (apm_t00A01_collared_standardCover_aux_right_aux_quotient_preimage
        iA iB C hiA)
  have hU : IsOpen U := by
    have hop : IsOpen (q ⁻¹' U) := by
      rw [hpre]
      exact ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap _ hC).union
        (by simpa only [Set.image_univ] using
          ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap _ isOpen_univ))
    exact ((isQuotientMap_quotient_mk' : Topology.IsQuotientMap q).isOpen_preimage).mp hop
  let s0 : apm_t00A01_Sphere2 :=
    ⟨(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)), by
      simp [Metric.mem_sphere, dist_zero_right]⟩
  let ra : A → apm_t00A01_Sphere2 := fun a =>
    if ha : a ∈ C then r ⟨a, ha⟩ else s0
  have hra (s : apm_t00A01_Sphere2) : ra (iA s) = s := by
    simp [ra, hiA s, hr s]
  let f0 : apm_t00A01_connectedSum iA iB → B :=
    Quotient.lift (Sum.elim (fun a => iB (ra a)) id) (by
      intro x y hxy
      induction hxy with
      | rel x y h =>
          cases h with
          | glue s => simp [hra s]
      | refl => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)
  let f : U → B := fun x => f0 x.1
  have hf : Continuous f := by
    have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
    let e : (Sum.inl '' C ∪ Set.range Sum.inr : Set (Sum A B)) ≃ₜ q ⁻¹' U :=
      Homeomorph.setCongr hpre.symm
    have hn : Continuous (fun z : (Sum.inl '' C ∪ Set.range Sum.inr : Set (Sum A B)) =>
        f ((U.restrictPreimage q) (e z))) := by
      let eL : C → (Sum.inl '' C ∪ Set.range Sum.inr : Set (Sum A B)) :=
        fun a => ⟨(@Sum.inl A B) a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
      let eR : B → (Sum.inl '' C ∪ Set.range Sum.inr : Set (Sum A B)) :=
        fun b => ⟨(@Sum.inr A B) b, Or.inr ⟨b, rfl⟩⟩
      have heL : Topology.IsOpenEmbedding eL := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · exact Continuous.subtype_mk
            ((continuous_inl (X := A) (Y := B)).comp continuous_subtype_val) _
        · intro a a' h
          exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.comp
            hC.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have heR : Topology.IsOpenEmbedding eR := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · exact Continuous.subtype_mk (continuous_inr (X := A) (Y := B)) _
        · intro b b' h
          exact Sum.inr.inj (congrArg Subtype.val h)
        · exact (Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.codRestrict _
      have hcL : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) := by
        convert hiB.comp r.continuous using 1
        funext a
        dsimp [Function.comp_def, f, f0, q, ra, e, eL]
        simp [Homeomorph.setCongr, Equiv.setCongr_apply, a.2]
      have hcR : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) := by
        convert (continuous_id : Continuous (fun b : B => b)) using 1 <;>
          simp [Function.comp_def, f, f0, q, e, eR]
      rw [← continuousOn_univ]
      have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
        ext ⟨z, hz⟩
        cases z with
        | inl a =>
            rcases hz with ⟨a', ha', h⟩ | ⟨_, h⟩
            · have : a = a' := Sum.inl.inj h.symm
              subst a'
              simp [eL, ha']
            · cases h
        | inr b => simp [eR]
      rw [← hcover]
      have hcLi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eL '' Set.univ) := heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
      have hcRi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eR '' Set.univ) := heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
      simpa only [Set.image_univ] using
        hcLi.union_of_isOpen hcRi
          (by simpa only [Set.image_univ] using heL.isOpen_range)
          (by simpa only [Set.image_univ] using heR.isOpen_range)
    simpa [Function.comp_def] using hn.comp e.symm.continuous
  let g : B → U := fun b => ⟨q (.inr b), ⟨.inr b, Or.inr ⟨b, rfl⟩, rfl⟩⟩
  have hg : Continuous g := by
    exact Continuous.subtype_mk
      (continuous_coinduced_rng.comp continuous_inr) _
  let Kraw : unitInterval × apm_t00A01_connectedSum iA iB →
      apm_t00A01_connectedSum iA iB := fun p =>
    Quotient.lift (Sum.elim
      (fun a => q (.inl (if ha : a ∈ C then H (⟨a, ha⟩, unitInterval.symm p.1) else a)))
      (fun b => q (.inr b))) (by
        intro x y hxy
        change (Relation.EqvGen.setoid (apm_t00A01_glueRel iA iB)).r x y at hxy
        change Relation.EqvGen (apm_t00A01_glueRel iA iB) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | glue s =>
                simp [hiA s, hHfix s (unitInterval.symm p.1), q]
                exact apm_t00A01_mk_inl_eq_mk_inr iA iB s
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    rcases p.2.2 with ⟨z, hz, heq⟩
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨Sum.inl (H (⟨a, ha⟩, unitInterval.symm p.1)),
        Or.inl ⟨_, hHC (⟨a, ha⟩, unitInterval.symm p.1), rfl⟩, by
          rw [← heq]
          simp [Kraw, q, ha]⟩
    · exact ⟨Sum.inr b, Or.inr ⟨b, rfl⟩, by rw [← heq]; simp [Kraw, q]⟩⟩
  have hK : Continuous K := by
    apply Continuous.subtype_mk
    let qU : (q ⁻¹' U) → U := U.restrictPreimage q
    have hqU : Topology.IsQuotientMap qU :=
      (isQuotientMap_quotient_mk' : Topology.IsQuotientMap q).restrictPreimage_isOpen hU
    apply hqU.continuous_lift_prod_right
    let ep : (q ⁻¹' U) ≃ₜ
        ↥((@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)) :=
      Homeomorph.setCongr hpre
    have hc : Continuous (fun p : unitInterval ×
        ↥((@Sum.inl A B) '' C ∪ Set.range (@Sum.inr A B)) =>
        Kraw (p.1, q p.2.1)) := by
      apply apm_t00A01_collared_standardCover_aux_right_aux_quotient_aux_cont C hC
      · have : (fun p : unitInterval × ↥C => Kraw (p.1, q (Sum.inl p.2.1))) =
            fun p => q (Sum.inl (H (p.2, unitInterval.symm p.1))) := by
          funext p; simp [Kraw, q, p.2.2]
        simpa using this ▸ (continuous_coinduced_rng.comp (continuous_inl.comp
          (H.continuous.comp (continuous_snd.prodMk
            (unitInterval.continuous_symm.comp continuous_fst)))))
      · have : (fun p : unitInterval × B => Kraw (p.1, q (Sum.inr p.2))) =
            fun p => q (Sum.inr p.2) := by
          funext p; simp [Kraw, q]
        simpa using this ▸ (continuous_coinduced_rng.comp
          (continuous_inr.comp continuous_snd))
    exact hc.comp (continuous_fst.prodMk (ep.continuous.comp continuous_snd))
  let F : C(U, B) := ⟨f, hf⟩
  let G : C(B, U) := ⟨g, hg⟩
  refine ⟨{ toFun := F, invFun := G, left_inv := ?_, right_inv := ?_ }⟩
  · exact ⟨{
      toFun := K
      continuous_toFun := hK
      map_zero_left := by
        intro x
        apply Subtype.ext
        rcases x.2 with ⟨z, hz, heq⟩
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
        · change Kraw (0, x.1) = q (.inr (f0 x.1))
          rw [← heq]
          simp [Kraw, q, f0, ra, ha, hH1]
          exact apm_t00A01_mk_inl_eq_mk_inr iA iB (r ⟨a, ha⟩)
        · change Kraw (0, x.1) = q (.inr (f0 x.1))
          rw [← heq]
          simp [Kraw, q, f0]
      map_one_left := by
        intro x
        apply Subtype.ext
        rcases x.2 with ⟨z, hz, heq⟩
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, rfl⟩
        · change Kraw (1, x.1) = x.1
          rw [← heq]
          simp [Kraw, q, ha, hH0]
        · change Kraw (1, x.1) = x.1
          rw [← heq]
          simp [Kraw, q] }⟩
  · have heq : F.comp G = ContinuousMap.id B := by
      ext b
      rfl
    rw [heq]
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

/- The quotient-topology core of the overlap argument.  Each of the two open
collars strongly deformation retracts, relative to its boundary copy, onto the
same sphere.  After gluing those boundary copies, their union (which is exactly
the overlap of the two standard thickenings) therefore deformation retracts
onto that sphere. -/
lemma apm_t00A01_collared_standardCover_aux_inter_aux_quotient_aux_saturated
    {A B : Type} (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (CA : Set A) (CB : Set B) (hiA : ∀ s, iA s ∈ CA) (hiB : ∀ s, iB s ∈ CB)
    {x y : Sum A B} (hxy : Relation.EqvGen (apm_t00A01_glueRel iA iB) x y) :
    (x ∈ Sum.inl '' CA ∪ Sum.inr '' CB) ↔
      (y ∈ Sum.inl '' CA ∪ Sum.inr '' CB) := by
  induction hxy with
  | rel x y h =>
      cases h with
      | glue s => simp [hiA s, hiB s]
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

lemma apm_t00A01_collared_standardCover_aux_inter_aux_quotient
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B)
    (CA : Set A) (CB : Set B) (hCA : IsOpen CA) (hCB : IsOpen CB)
    (hiA : ∀ s, iA s ∈ CA) (hiB : ∀ s, iB s ∈ CB)
    (hiAc : Continuous iA)
    (rA : C(↥CA, apm_t00A01_Sphere2)) (HA : C(↥CA × unitInterval, A))
    (rB : C(↥CB, apm_t00A01_Sphere2)) (HB : C(↥CB × unitInterval, B))
    (hrA : ∀ s, rA ⟨iA s, hiA s⟩ = s)
    (hrB : ∀ s, rB ⟨iB s, hiB s⟩ = s)
    (hHA0 : ∀ x, HA (x, 0) = x.1) (hHB0 : ∀ x, HB (x, 0) = x.1)
    (hHA1 : ∀ x, HA (x, 1) = iA (rA x))
    (hHB1 : ∀ x, HB (x, 1) = iB (rB x))
    (hHACA : ∀ p, HA p ∈ CA) (hHBCB : ∀ p, HB p ∈ CB)
    (hHAfix : ∀ s t, HA (⟨iA s, hiA s⟩, t) = iA s)
    (hHBfix : ∀ s t, HB (⟨iB s, hiB s⟩, t) = iB s) :
    Nonempty (ContinuousMap.HomotopyEquiv
      ↥(apm_t00A01_thickLeft iA iB CB ∩ apm_t00A01_thickRight iA iB CA)
      apm_t00A01_Sphere2) := by
  classical
  let q : Sum A B → apm_t00A01_connectedSum iA iB := fun z => Quotient.mk _ z
  let U := apm_t00A01_thickLeft iA iB CB ∩ apm_t00A01_thickRight iA iB CA
  have hU : IsOpen U :=
    (apm_t00A01_collared_standardCover_aux_open iA iB CA CB hCA hCB hiA hiB).1.inter
      (apm_t00A01_collared_standardCover_aux_open iA iB CA CB hCA hCB hiA hiB).2.1
  have hpreL : q ⁻¹' apm_t00A01_thickLeft iA iB CB =
      Set.range Sum.inl ∪ Sum.inr '' CB := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, heq⟩
      have hrel : Relation.EqvGen (apm_t00A01_glueRel iA iB) z w :=
        (Quotient.exact heq).symm
      have hinv : (z ∈ Set.range Sum.inl ∪ Sum.inr '' CB) ↔
          w ∈ Set.range Sum.inl ∪ Sum.inr '' CB := by
        simpa [Set.image_univ] using
          apm_t00A01_collared_standardCover_aux_inter_aux_quotient_aux_saturated
            iA iB Set.univ CB (fun _ => Set.mem_univ _) hiB hrel
      exact hinv.2 hw
    · intro z hz
      exact ⟨z, hz, rfl⟩
  have hpreR : q ⁻¹' apm_t00A01_thickRight iA iB CA =
      Sum.inl '' CA ∪ Set.range Sum.inr := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, hw, heq⟩
      have hrel : Relation.EqvGen (apm_t00A01_glueRel iA iB) z w :=
        (Quotient.exact heq).symm
      have hinv : (z ∈ Sum.inl '' CA ∪ Set.range Sum.inr) ↔
          w ∈ Sum.inl '' CA ∪ Set.range Sum.inr := by
        simpa [Set.image_univ] using
          apm_t00A01_collared_standardCover_aux_inter_aux_quotient_aux_saturated
            iA iB CA Set.univ hiA (fun _ => Set.mem_univ _) hrel
      exact hinv.2 hw
    · intro z hz
      exact ⟨z, hz, rfl⟩
  have hpre : q ⁻¹' U = Sum.inl '' CA ∪ Sum.inr '' CB := by
    rw [Set.preimage_inter, hpreL, hpreR]
    ext z
    cases z <;> simp
  let s0 : apm_t00A01_Sphere2 :=
    ⟨(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)), by
      simp [Metric.mem_sphere, dist_zero_right]⟩
  let ra : A → apm_t00A01_Sphere2 := fun a =>
    if ha : a ∈ CA then rA ⟨a, ha⟩ else s0
  let rb : B → apm_t00A01_Sphere2 := fun b =>
    if hb : b ∈ CB then rB ⟨b, hb⟩ else s0
  have hra (s) : ra (iA s) = s := by simp [ra, hiA s, hrA s]
  have hrb (s) : rb (iB s) = s := by simp [rb, hiB s, hrB s]
  let f0 : apm_t00A01_connectedSum iA iB → apm_t00A01_Sphere2 :=
    Quotient.lift (Sum.elim ra rb) (by
      intro x y hxy
      induction hxy with
      | rel x y h => cases h with | glue s => simp [hra s, hrb s]
      | refl => rfl
      | symm x y h ih => exact ih.symm
      | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz)
  let f : U → apm_t00A01_Sphere2 := fun x => f0 x.1
  have hf : Continuous f := by
    have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen hU).continuous_iff.mpr
    let e : (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum A B)) ≃ₜ q ⁻¹' U :=
      Homeomorph.setCongr hpre.symm
    have hn : Continuous (fun z : (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum A B)) =>
        f ((U.restrictPreimage q) (e z))) := by
      let eL : CA → (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum A B)) :=
        fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
      let eR : CB → (Sum.inl '' CA ∪ Sum.inr '' CB : Set (Sum A B)) :=
        fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
      have heL : Topology.IsOpenEmbedding eL := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inl.comp continuous_subtype_val
        · intro a a' h
          exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.comp
            hCA.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have heR : Topology.IsOpenEmbedding eR := by
        apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        · apply Continuous.subtype_mk
          exact continuous_inr.comp continuous_subtype_val
        · intro b b' h
          exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
        · exact ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.comp
            hCB.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
      have hcL : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) := by
        rw [show ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eL) = rA by
          funext a
          change Sum.elim ra rb (e (eL a)).1 = rA a
          rw [show (e (eL a)).1 = Sum.inl a.1 by rfl]
          simp [ra, a.2]]
        exact rA.continuous
      have hcR : Continuous ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) := by
        rw [show ((fun z => f ((U.restrictPreimage q) (e z))) ∘ eR) = rB by
          funext b
          change Sum.elim ra rb (e (eR b)).1 = rB b
          rw [show (e (eR b)).1 = Sum.inr b.1 by rfl]
          simp [rb, b.2]]
        exact rB.continuous
      rw [← continuousOn_univ]
      have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
        ext ⟨z, hz⟩
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp [eL, eR, *]
      rw [← hcover]
      have hcLi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eL '' Set.univ) := heL.isInducing.continuousOn_image_iff.mpr hcL.continuousOn
      have hcRi : ContinuousOn (fun z => f ((U.restrictPreimage q) (e z)))
          (eR '' Set.univ) := heR.isInducing.continuousOn_image_iff.mpr hcR.continuousOn
      have hoL : IsOpen (eL '' Set.univ) := by
        simpa only [Set.image_univ] using heL.isOpen_range
      have hoR : IsOpen (eR '' Set.univ) := by
        simpa only [Set.image_univ] using heR.isOpen_range
      simpa only [Set.image_univ] using
        hcLi.union_of_isOpen hcRi hoL hoR
    rw [show f ∘ U.restrictPreimage q =
        (fun z => f ((U.restrictPreimage q) (e z))) ∘ e.symm by funext x; rfl]
    exact hn.comp e.symm.continuous
  let g : apm_t00A01_Sphere2 → U := fun s =>
    ⟨q (.inl (iA s)),
      ⟨⟨.inl (iA s), Or.inl ⟨iA s, rfl⟩, rfl⟩,
       ⟨.inl (iA s), Or.inl ⟨iA s, hiA s, rfl⟩, rfl⟩⟩⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_coinduced_rng.comp (continuous_inl.comp
      hiAc)
  let Kraw : unitInterval × apm_t00A01_connectedSum iA iB →
      apm_t00A01_connectedSum iA iB := fun p =>
    Quotient.lift (Sum.elim
      (fun a => q (.inl (if ha : a ∈ CA then HA (⟨a, ha⟩, p.1) else a)))
      (fun b => q (.inr (if hb : b ∈ CB then HB (⟨b, hb⟩, p.1) else b)))) (by
        intro x y hxy
        change Relation.EqvGen (apm_t00A01_glueRel iA iB) x y at hxy
        induction hxy with
        | rel x y h =>
            cases h with
            | glue s =>
                simp [hiA s, hiB s, hHAfix s p.1, hHBfix s p.1, q]
                exact apm_t00A01_mk_inl_eq_mk_inr iA iB s
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz) p.2
  let K : unitInterval × U → U := fun p => ⟨Kraw (p.1, p.2.1), by
    obtain ⟨z, heq⟩ := Quotient.exists_rep p.2.1
    have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
      rw [← hpre]
      change Quotient.mk _ z ∈ U
      rw [heq]
      exact p.2.2
    rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · refine ⟨⟨Sum.inl (HA (⟨a, ha⟩, p.1)),
          Or.inl ⟨_, rfl⟩, ?_⟩,
        ⟨Sum.inl (HA (⟨a, ha⟩, p.1)),
          Or.inl ⟨_, hHACA _, rfl⟩, ?_⟩⟩
      all_goals rw [← heq]; simp [Kraw, q, ha]
    · refine ⟨⟨Sum.inr (HB (⟨b, hb⟩, p.1)),
          Or.inr ⟨_, hHBCB _, rfl⟩, ?_⟩,
        ⟨Sum.inr (HB (⟨b, hb⟩, p.1)),
          Or.inr ⟨_, rfl⟩, ?_⟩⟩
      all_goals rw [← heq]; simp [Kraw, q, hb]
    ⟩
  have hK : Continuous K := by
    let P : Set (Sum A B) := Sum.inl '' CA ∪ Sum.inr '' CB
    have hP : IsOpen P :=
      ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap CA hCA).union
        ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap CB hCB)
    apply apm_t00A01_collared_standardCover_aux_quotient_continuous
      iA iB U P hP hpre K
    let jL : CA → P := fun a => ⟨Sum.inl a.1, Or.inl ⟨a.1, a.2, rfl⟩⟩
    let jR : CB → P := fun b => ⟨Sum.inr b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩
    have hjL : Topology.IsOpenEmbedding jL := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk; exact continuous_inl.comp continuous_subtype_val
      · intro a a' h; exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
      · exact ((Topology.IsOpenEmbedding.inl (X := A) (Y := B)).isOpenMap.comp
          hCA.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
    have hjR : Topology.IsOpenEmbedding jR := by
      apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      · apply Continuous.subtype_mk; exact continuous_inr.comp continuous_subtype_val
      · intro b b' h; exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
      · exact ((Topology.IsOpenEmbedding.inr (X := A) (Y := B)).isOpenMap.comp
          hCB.isOpenEmbedding_subtypeVal.isOpenMap).codRestrict _
    let eL : unitInterval × CA → unitInterval × P := fun p => (p.1, jL p.2)
    let eR : unitInterval × CB → unitInterval × P := fun p => (p.1, jR p.2)
    have heL : Topology.IsOpenEmbedding eL :=
      Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjL
    have heR : Topology.IsOpenEmbedding eR :=
      Topology.IsOpenEmbedding.prodMap Topology.IsOpenEmbedding.id hjR
    let L := fun p : unitInterval × P =>
      K (p.1, ⟨q p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)
    have hcL : Continuous (L ∘ eL) := by
      apply Continuous.subtype_mk
      simpa [Function.comp_def, L, eL, jL, K, Kraw, q] using
        continuous_coinduced_rng.comp (continuous_inl.comp
          (HA.continuous.comp (continuous_snd.prodMk continuous_fst)))
    have hcR : Continuous (L ∘ eR) := by
      apply Continuous.subtype_mk
      simpa [Function.comp_def, L, eR, jR, K, Kraw, q] using
        continuous_coinduced_rng.comp (continuous_inr.comp
          (HB.continuous.comp (continuous_snd.prodMk continuous_fst)))
    rw [show (fun p : unitInterval × P =>
      K (p.1, ⟨Quotient.mk _ p.2.1, (Set.ext_iff.mp hpre p.2.1).mpr p.2.2⟩)) = L by rfl]
    rw [← continuousOn_univ]
    have hcover : Set.range eL ∪ Set.range eR = Set.univ := by
      ext ⟨t, z, hz⟩
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp [eL, eR, jL, jR, *]
    rw [← hcover]
    have hcLi := (heL.isInducing.continuousOn_image_iff (g := L) (s := Set.univ)).mpr hcL.continuousOn
    have hcRi := (heR.isInducing.continuousOn_image_iff (g := L) (s := Set.univ)).mpr hcR.continuousOn
    simpa only [Set.image_univ] using
      hcLi.union_of_isOpen hcRi (by simpa only [Set.image_univ] using heL.isOpen_range) (by simpa only [Set.image_univ] using heR.isOpen_range)
  let F : C(U, apm_t00A01_Sphere2) := ⟨f, hf⟩
  let G : C(apm_t00A01_Sphere2, U) := ⟨g, hg⟩
  refine ⟨{ toFun := F, invFun := G, left_inv := ?_, right_inv := ?_ }⟩
  · apply ContinuousMap.Homotopic.symm
    exact ⟨{
      toFun := fun p => K (p.1, p.2)
      continuous_toFun := hK
      map_zero_left := by
        intro x
        obtain ⟨z, heq⟩ := Quotient.exists_rep x.1
        have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
          rw [← hpre]
          change Quotient.mk _ z ∈ U
          rw [heq]
          exact x.2
        apply Subtype.ext
        change Kraw (0, x.1) = x.1
        rw [← heq]
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · simp [Kraw, q, ha, hHA0]
        · simp [Kraw, q, hb, hHB0]
      map_one_left := by
        intro x
        obtain ⟨z, heq⟩ := Quotient.exists_rep x.1
        have hz : z ∈ Sum.inl '' CA ∪ Sum.inr '' CB := by
          rw [← hpre]
          change Quotient.mk _ z ∈ U
          rw [heq]
          exact x.2
        apply Subtype.ext
        change Kraw (1, x.1) = (G.comp F x).1
        rw [← heq]
        rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · have fx : f x = rA ⟨a, ha⟩ := by
            change f0 x.1 = _
            rw [← heq]
            simp [f0, ra, ha]
          simp [Kraw, G, F, g, q, ha, hHA1, fx]
        · have fx : f x = rB ⟨b, hb⟩ := by
            change f0 x.1 = _
            rw [← heq]
            simp [f0, rb, hb]
          simp [Kraw, G, F, g, q, hb, hHB1, fx]
          exact (apm_t00A01_mk_inl_eq_mk_inr iA iB (rB ⟨b, hb⟩)).symm }⟩
  · have heq : F.comp G = ContinuousMap.id apm_t00A01_Sphere2 := by
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      exact congrArg Subtype.val (hra s)
    rw [heq]



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
  obtain ⟨hC₁open, hC₁mem⟩ :=
    apm_t00A01_collared_standardCover_aux_collar φ₁ hφ₁ Φ₁ hext₁ hopen₁
  obtain ⟨hC₂open, hC₂mem⟩ :=
    apm_t00A01_collared_standardCover_aux_collar φ₂ hφ₂ Φ₂ hext₂ hopen₂
  obtain ⟨r₁, H₁, hr₁, hH₁zero, hH₁one, hH₁C, hH₁fix⟩ :=
    apm_t00A01_collared_standardCover_aux_left_aux_radial φ₁ hφ₁ Φ₁ hΦ₁ hext₁
  obtain ⟨r₂, H₂, hr₂, hH₂zero, hH₂one, hH₂C, hH₂fix⟩ :=
    apm_t00A01_collared_standardCover_aux_left_aux_radial φ₂ hφ₂ Φ₂ hΦ₂ hext₂
  exact apm_t00A01_collared_standardCover_aux_inter_aux_quotient
    (apm_t00A01_boundaryMap φ₁ hφ₁.injective)
    (apm_t00A01_boundaryMap φ₂ hφ₂.injective)
    _ _ hC₁open hC₂open hC₁mem hC₂mem
    (apm_t00A01_collared_standardCover_aux_boundary_continuous φ₁ hφ₁) r₁ H₁ r₂ H₂
    (fun s ↦ hr₁ s (hC₁mem s)) (fun s ↦ hr₂ s (hC₂mem s))
    hH₁zero hH₂zero hH₁one hH₂one hH₁C hH₂C
    (fun s t ↦ hH₁fix s (hC₁mem s) t)
    (fun s t ↦ hH₂fix s (hC₂mem s) t)
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
