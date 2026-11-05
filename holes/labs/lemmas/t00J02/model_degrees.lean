import Mathlib
import ConstructionTargets.RelativeSingularConnectingNaturality
import ConstructionTargets.CollaredConnectedSumHomology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CircleHomology
import ConstructionTargets.IntegerCyclic
import ConstructionTargets.DiskBoundaryHomology
import ConstructionTargets.DiskBoundedPreimageDuality
import ConstructionTargets.EmbeddedCircleLift
import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.TransversePreimageDuality
import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.TransversePreimageGeometry
import ConstructionTargets.OrientedSurfacePreimageDuality
import ConstructionTargets.t00J02Closure
import ConstructionTargets.CircleActualLocalization
import ConstructionTargets.HigherChartLocalGenerator
import ConstructionTargets.OneDimensionalChartLocalGenerator

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.RelativeSingularHomologyHomotopy

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision

abbrev Fch := (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
  (AddCommGrpCat.of ℤ)

lemma chainHomology_eq_of_homotopic {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    {a b : C(P, Q)} (h : ContinuousMap.Homotopic a b) (n : ℕ) :
    HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom a)) n =
      HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom b)) n := by
  have := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
    AddCommGrpCat (AddCommGrpCat.of ℤ) h n
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using this

lemma chainHomology_isIso_of_section {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (q : C(P, Q)) (s : C(Q, P)) (hqs : q.comp s = ContinuousMap.id Q)
    (hsq : ContinuousMap.Homotopic (s.comp q) (ContinuousMap.id P)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom q)) n) := by
  refine ⟨⟨HomologicalComplex.homologyMap (Fch.map (TopCat.ofHom s)) n, ?_, ?_⟩⟩
  · rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have : TopCat.ofHom q ≫ TopCat.ofHom s = TopCat.ofHom (s.comp q) := rfl
    rw [this, chainHomology_eq_of_homotopic hsq n]
    rw [show TopCat.ofHom (ContinuousMap.id P) = 𝟙 _ from rfl]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  · rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    have : TopCat.ofHom s ≫ TopCat.ofHom q = TopCat.ofHom (q.comp s) := rfl
    rw [this, hqs, show TopCat.ofHom (ContinuousMap.id Q) = 𝟙 _ from rfl]
    simp only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

/-- Relative homotopy invariance for maps of pairs. -/
theorem relativeSingularHomologyMap_eq_of_homotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) {f₀ f₁ : C(X, Y)}
    (H : ContinuousMap.Homotopy f₀ f₁)
    (hH : ∀ t : unitInterval, ∀ x ∈ A, H (t, x) ∈ B)
    (h₀ : Set.MapsTo f₀ A B) (h₁ : Set.MapsTo f₁ A B) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeSingularMap A B f₀ h₀) n =
      HomologicalComplex.homologyMap (relativeSingularMap A B f₁ h₁) n := by
  let A' : Set (X × unitInterval) := A ×ˢ univ
  let p : C(X × unitInterval, X) := ContinuousMap.fst
  have hp : Set.MapsTo p A' A := fun q hq => hq.1
  let ι : unitInterval → C(X, X × unitInterval) := fun t =>
    ⟨fun x => (x, t), continuous_id.prodMk continuous_const⟩
  have hι : ∀ t, Set.MapsTo (ι t) A A' := fun t x hx => ⟨hx, trivial⟩
  let Hc : C(X × unitInterval, Y) :=
    ⟨fun q => H (q.2, q.1), H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  have hHc : Set.MapsTo Hc A' B := fun q hq => hH q.2 q.1 hq.1
  -- p is an isomorphism on relative homology
  have hpiso : ∀ m, IsIso (HomologicalComplex.homologyMap (relativeSingularMap A' A p hp) m) := by
    intro m
    -- the deformation retraction of the cylinder onto its bottom
    have hdef : ∀ {Z : Set X},
        ContinuousMap.Homotopic
          ((⟨fun z : (Z ×ˢ (univ : Set unitInterval) : Set _) =>
              (⟨((z : X × unitInterval).1, 0), ⟨z.2.1, trivial⟩⟩ :
                (Z ×ˢ (univ : Set unitInterval) : Set _)),
            by fun_prop⟩ : C(_, _)))
          (ContinuousMap.id _) := by
      intro Z
      refine ⟨{ toFun := fun r => ⟨((r.2 : X × unitInterval).1,
                  ⟨(r.1 : ℝ) * ((r.2 : X × unitInterval).2 : ℝ),
                    unitInterval.mul_mem r.1.2 (r.2 : X × unitInterval).2.2⟩),
                  ⟨r.2.2.1, trivial⟩⟩
                continuous_toFun := by fun_prop
                map_zero_left := by intro z; ext <;> simp
                map_one_left := by intro z; ext <;> simp }⟩
    have hdefX : ContinuousMap.Homotopic ((ι 0).comp p) (ContinuousMap.id _) := by
      refine ⟨{ toFun := fun r => ((r.2).1,
                  ⟨(r.1 : ℝ) * ((r.2).2 : ℝ), unitInterval.mul_mem r.1.2 (r.2).2.2⟩)
                continuous_toFun := by fun_prop
                map_zero_left := by intro z; ext <;> simp [ι, p]
                map_one_left := by intro z; ext <;> simp }⟩
    apply relativeSingularMap_homologyMap_isIso
    · exact chainHomology_isIso_of_section _
        ⟨fun a : A => (⟨((a : X), 0), ⟨a.2, trivial⟩⟩ : A'), by fun_prop⟩
        (by ext; rfl) (by simpa using hdef (Z := A)) m
    · exact chainHomology_isIso_of_section p (ι 0) (by ext; rfl) hdefX m
    · intro j _
      exact chainHomology_isIso_of_section _
        ⟨fun a : A => (⟨((a : X), 0), ⟨a.2, trivial⟩⟩ : A'), by fun_prop⟩
        (by ext; rfl) (by simpa using hdef (Z := A)) j
    · intro j _
      exact chainHomology_isIso_of_section p (ι 0) (by ext; rfl) hdefX j
  have hsec : ∀ t, HomologicalComplex.homologyMap (relativeSingularMap A A' (ι t) (hι t)) n =
      inv (HomologicalComplex.homologyMap (relativeSingularMap A' A p hp) n) := by
    intro t
    haveI := hpiso n
    apply IsIso.eq_inv_of_inv_hom_id
    rw [← HomologicalComplex.homologyMap_comp,
      relativeSingularMap_comp A A' A (ι t) p (hι t) hp (by
        intro x hx; exact hx)]
    have : p.comp (ι t) = ContinuousMap.id X := by ext; rfl
    have hcongr : ∀ (F G : C(X, X)) (hFG : F = G) hF hG,
        relativeSingularMap A A F hF = relativeSingularMap A A G hG := by
      intro F G hFG _ _; subst hFG; rfl
    rw [hcongr _ _ this _ (fun x hx => hx), relativeSingularMap_id,
      HomologicalComplex.homologyMap_id]
  have hfac : ∀ t (f : C(X, Y)) (hf : Set.MapsTo f A B), Hc.comp (ι t) = f →
      HomologicalComplex.homologyMap (relativeSingularMap A B f hf) n =
        HomologicalComplex.homologyMap (relativeSingularMap A A' (ι t) (hι t)) n ≫
          HomologicalComplex.homologyMap (relativeSingularMap A' B Hc hHc) n := by
    intro t f hf hfe
    subst hfe
    rw [← HomologicalComplex.homologyMap_comp, relativeSingularMap_comp]
  rw [hfac 0 f₀ h₀ (by ext x; simp [Hc, ι]), hfac 1 f₁ h₁ (by ext x; simp [Hc, ι]),
    hsec 0, hsec 1]

end ConstructionTargets.RelativeSingularHomologyHomotopy

namespace t00J02_ModelProduct

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.LocalHomologyNeighborhoodExcision

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def horizontal (u : ℝ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then u else 0)

lemma horizontal_zero : horizontal 0 = 0 := by
  ext i
  simp [horizontal]

def horizontalSlice (U : Set E2) : Set ℝ := {u | horizontal u ∈ U}

def productMap (g : C(E2, ℝ)) : C(E2, E2) where
  toFun p := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => if i = 0 then g p else p 1)
  continuous_toFun := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa using g.continuous
    · simpa using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1

def splitProductMap (g : C(E2, ℝ)) : C(E2, E2) :=
  productMap ⟨fun p => g (horizontal (p 0)),
    g.continuous.comp (by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      apply continuous_pi; intro i; fin_cases i
      · simpa [horizontal] using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
      · exact continuous_const)⟩

def sliceMap (U : Set E2) (g : C(E2, ℝ)) : C(horizontalSlice U, ℝ) where
  toFun u := g (horizontal u)
  continuous_toFun := g.continuous.comp <| by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi; intro i; fin_cases i
    · simpa [horizontal] using
        (continuous_subtype_val : Continuous (fun u : horizontalSlice U => (u : ℝ)))
    · exact continuous_const

def restrictedMap (U : Set E2) (F : C(E2, E2)) : C(U, E2) :=
  F.comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The degree of a map from an open neighborhood of the origin, expressed
exactly as in `t00J02_IsLocalDegree`: a neighborhood class restricts to the
standard ambient local generator and its pushforward is `n` times the target
generator. -/
def IsLocalDegreeTwo (U : Set E2) (F : C(E2, E2))
    (hzero : ∀ p : U, F p = 0 ↔ (p : E2) = 0) (n : ℤ) : Prop :=
  ∃ a : (RelativeSingularChains (neighborhoodDeletedPoint U (0 : E2))).homology 2,
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (neighborhoodInclusion U)
          (neighborhoodInclusion_mapsTo U 0)) 2 a =
      ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2) ∧
    HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
          (deletedPoint (0 : E2)) (restrictedMap U F) (by
            intro p hp hFp
            exact hp ((hzero p).mp hFp))) 2 a =
      n • ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
        (k := 0) (0 : E2)

def identityScalar : C(E2, ℝ) where
  toFun p := p 0
  continuous_toFun := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0

def reflectionScalar : C(E2, ℝ) where
  toFun p := -(p 0)
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).neg

def positiveFoldScalar : C(E2, ℝ) where
  toFun p := (p 0) ^ 2
  continuous_toFun := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2

def negativeFoldScalar : C(E2, ℝ) where
  toFun p := -((p 0) ^ 2)
  continuous_toFun := ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).pow 2).neg

lemma identity_productMap_zero_iff (U : Set E2) (p : U) :
    productMap identityScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 0) h
    · simpa [productMap, identityScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, identityScalar]

lemma reflection_productMap_zero_iff (U : Set E2) (p : U) :
    productMap reflectionScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · have h0 := congrArg (fun q : E2 => q 0) h
      simpa [productMap, reflectionScalar] using neg_eq_zero.mp h0
    · simpa [productMap, reflectionScalar] using congrArg (fun q : E2 => q 1) h
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, reflectionScalar]

lemma positiveFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap positiveFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : (p.1 0) ^ 2 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 0) h
    have hp0 : p.1 0 = 0 := eq_zero_of_pow_eq_zero h0
    have hp1 : p.1 1 = 0 := by
      simpa [productMap, positiveFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i
    fin_cases i <;> simp [hp0, hp1]
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, positiveFoldScalar]

lemma negativeFold_productMap_zero_iff (U : Set E2) (p : U) :
    productMap negativeFoldScalar p = 0 ↔ (p : E2) = 0 := by
  constructor
  · intro h
    have h0 : -((p.1 0) ^ 2) = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 0) h
    have hp0 : p.1 0 = 0 := eq_zero_of_pow_eq_zero (neg_eq_zero.mp h0)
    have hp1 : p.1 1 = 0 := by
      simpa [productMap, negativeFoldScalar] using congrArg (fun q : E2 => q 1) h
    ext i
    fin_cases i <;> simp [hp0, hp1]
  · intro hp
    rw [hp]
    ext i
    fin_cases i <;> simp [productMap, negativeFoldScalar]

/-- The identity map carries the ambient local generator to itself.  The
neighborhood generator is obtained by inverting the neighborhood-inclusion
isomorphism.  Estimated size: 35--60 lines. -/
theorem identity_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap identityScalar)
      (identity_productMap_zero_iff U) 1 := by
  have hres : restrictedMap U (productMap identityScalar) = neighborhoodInclusion U := by
    ext p i
    fin_cases i <;> rfl
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  have hι : ∀ b, ι ((asIso ι).inv b) = b := fun b =>
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id b
  refine ⟨(asIso ι).inv
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)), hι _, ?_⟩
  rw [one_smul]
  have hcongr : ∀ (F G : C(U, E2)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) F hF =
        relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hG := by
    intro F G hFG _ _; subst hFG; rfl
  rw [hcongr _ _ hres _ (neighborhoodInclusion_mapsTo U 0)]
  exact hι _

def firstCoordinateReflection : C(E2, E2) where
  toFun := ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)
  continuous_toFun :=
    (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).continuous

lemma firstCoordinateReflection_mapsTo_deletedPoint :
    MapsTo firstCoordinateReflection (deletedPoint (0 : E2)) (deletedPoint (0 : E2)) := by
  intro p hp hRp
  apply hp
  exact (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).injective
    (hRp.trans
      (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)).map_zero.symm)

/-- The first-coordinate reflection acts as minus the identity on integral
first homology of the Euclidean unit circle, computed in additive groups.
The natural integral coefficient comparison transports the module computation. -/
lemma firstCoordinateReflection_circle_H1 :
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
      (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
          (0 : Fin 2))) = -𝟙 _ := by
  let e := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
    (TopCat.of (T02A06.euclideanUnitSphere 2)) 1
  apply (cancel_epi e.hom).mp
  have h := ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
    (TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
      (0 : Fin 2))) 1
  rw [ConstructionTargets.CoefficientFirstReflection.circle_negative ℤ] at h
  simpa only [Functor.map_neg, Functor.map_id, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.id_comp, Category.comp_id] using h.symm

/-- Radial normalization intertwines reflection of the punctured plane with
reflection of its unit circle, since a linear isometry preserves norms. -/
lemma firstCoordinateReflection_radial_naturality :
    (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2).comp
      (⟨fun x : deletedPoint (0 : E2) =>
        ⟨firstCoordinateReflection x, firstCoordinateReflection_mapsTo_deletedPoint x.property⟩,
        firstCoordinateReflection.continuous.comp continuous_subtype_val |>.subtype_mk _⟩) =
    (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 2)).comp
      (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize
      (ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2) x.val) =
    ConstructionTargets.CoefficientCoordinateReflections.reflection (0 : Fin 2)
      (NormedSpace.normalize x.val)
  simp only [NormedSpace.normalize, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.map_smul]

/-- The first-coordinate reflection negates the standard ambient local
two-dimensional generator.  Radial naturality identifies the relative local
map with the reflection of the unit circle, where
`CoefficientFirstReflection.all_reflections_negative` computes the sign.
Estimated size: 70--110 lines. -/
lemma firstCoordinateReflection_ambientLocalGenerator :
    HomologicalComplex.homologyMap
        (relativeSingularMap (deletedPoint (0 : E2)) (deletedPoint (0 : E2))
          firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
        (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (0 : E2)) =
      -ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
          (k := 0) (0 : E2) := by
  let H := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
    (AddCommGrpCat.of ℤ)
  let A := deletedPoint (0 : E2)
  let q := ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize E2
  let j := ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.unitSphereInclusion E2
  let d := singularPairConnecting A 1
  haveI : Mono d := by
    apply (singularPairHomology_exact_relative A 1).mono_g
    exact (contractibleHigherHomology_isZero E2 2 (by decide)).eq_of_src _ _
  haveI : IsIso (H.map (TopCat.ofHom q)) := by
    exact ConstructionTargets.RelativeSingularHomologyHomotopy.chainHomology_isIso_of_section
      q j (by
        apply ContinuousMap.ext
        intro x
        exact ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize_unitSphereInclusion E2 x)
      ⟨ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.puncturedRadialHomotopy E2⟩ 1
  have hd : Function.Injective d := (AddCommGrpCat.mono_iff_injective d).mp inferInstance
  have hq : Function.Injective (H.map (TopCat.ofHom q)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  apply hd
  apply hq
  let ρ := HomologicalComplex.homologyMap
    (relativeSingularMap A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
  let r := subspaceMap A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint
  have hn : d ≫ H.map r = ρ ≫ d :=
    ConstructionTargets.RelativeSingularConnectingNaturality.singularPairConnecting_naturality
      A A firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint 1
  have hr : r ≫ TopCat.ofHom q = TopCat.ofHom q ≫
      TopCat.ofHom (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap (0 : Fin 2)) := by
    exact congrArg TopCat.ofHom firstCoordinateReflection_radial_naturality
  have hs : H.map r ≫ H.map (TopCat.ofHom q) = -(H.map (TopCat.ofHom q)) := by
    rw [← H.map_comp, hr]
    erw [H.map_comp]
    change H.map (TopCat.ofHom q) ≫
      ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map _ = _
    rw [firstCoordinateReflection_circle_H1, Preadditive.comp_neg, Category.comp_id]
  have he : ρ ≫ d ≫ H.map (TopCat.ofHom q) = -(d ≫ H.map (TopCat.ofHom q)) := by
    rw [← Category.assoc, ← hn]
    erw [Category.assoc, hs, Preadditive.comp_neg]
    rfl
  have hv := ConcreteCategory.congr_hom he
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2))
  change (H.map (TopCat.ofHom q)) (d (ρ _)) =
    -((H.map (TopCat.ofHom q)) (d _)) at hv
  change (H.map (TopCat.ofHom q)).hom (d.hom (ρ.hom _)) =
    (H.map (TopCat.ofHom q)).hom (d.hom (-_))
  rw [map_neg]
  erw [map_neg]
  exact hv

/-- Reflection in the first coordinate acts by `-1` on two-dimensional local
homology.  This follows by transporting `all_reflections_negative` through
the radial local-homology isomorphism.  Estimated size: 70--110 lines. -/
theorem reflection_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap reflectionScalar)
      (reflection_productMap_zero_iff U) (-1) := by
  have hres : restrictedMap U (productMap reflectionScalar) =
      firstCoordinateReflection.comp (neighborhoodInclusion U) := by
    ext p i
    fin_cases i <;> simp [restrictedMap, productMap, reflectionScalar,
      firstCoordinateReflection, neighborhoodInclusion,
      ConstructionTargets.CoefficientCoordinateReflections.reflection_apply]
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) 2
  let ρ := HomologicalComplex.homologyMap
    (relativeSingularMap (deletedPoint (0 : E2)) (deletedPoint (0 : E2))
      firstCoordinateReflection firstCoordinateReflection_mapsTo_deletedPoint) 2
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso
    0 U (0 : E2) hU h0
  let z := ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator
    (k := 0) (0 : E2)
  have hι : ∀ b, ι ((asIso ι).inv b) = b := fun b =>
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id b
  refine ⟨(asIso ι).inv z, hι _, ?_⟩
  have hcongr : ∀ (F G : C(U, E2)) (hFG : F = G) hF hG,
      relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) F hF =
        relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hG := by
    intro F G hFG _ _
    subst hFG
    rfl
  have hcompMaps : MapsTo (firstCoordinateReflection.comp (neighborhoodInclusion U))
      (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) :=
    firstCoordinateReflection_mapsTo_deletedPoint.comp
      (neighborhoodInclusion_mapsTo U 0)
  rw [hcongr _ _ hres _ hcompMaps]
  have hcomp := relativeSingularHomologyMap_comp
    (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
    (deletedPoint (0 : E2)) (neighborhoodInclusion U) firstCoordinateReflection
    (neighborhoodInclusion_mapsTo U 0) firstCoordinateReflection_mapsTo_deletedPoint
    hcompMaps 2
  rw [← hcomp]
  change ρ (ι ((asIso ι).inv z)) = (-1 : ℤ) • z
  rw [hι, firstCoordinateReflection_ambientLocalGenerator]
  simp
  rfl


/-- A map of the neighbourhood that misses the origin entirely is zero on local homology:
it factors through the self-pair of `U`. -/
lemma homologyMap_eq_zero_of_avoids (U : Set E2) (G : C(U, E2)) (hG : ∀ p, G p ≠ 0)
    (hGm : Set.MapsTo G (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))) :
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) G hGm) 2 = 0 := by
  have hfac := relativeSingularMap_comp (neighborhoodDeletedPoint U (0 : E2)) (Set.univ : Set U)
    (deletedPoint (0 : E2)) (ContinuousMap.id U) G (fun _ _ => trivial) (fun p _ => hG p) hGm
  show HomologicalComplex.homologyMap (relativeSingularMap _ _ (G.comp (ContinuousMap.id U)) hGm) 2 = 0
  rw [← hfac, HomologicalComplex.homologyMap_comp]
  rw [(selfRelativeSingularHomology_isZero U 2).eq_zero_of_tgt
    (HomologicalComplex.homologyMap (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2))
      (Set.univ : Set U) (ContinuousMap.id U) (fun _ _ => trivial)) 2), Limits.zero_comp]

/-- The fold `(σ·u², v)` (σ = ±1) has local degree 0: it deforms through maps of pairs to
`(σ·(u²+1), v)`, whose image misses the origin. -/
lemma fold_localDegree_zero (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U)
    (σ : ℝ) (hσ : σ ≠ 0) (g : C(E2, ℝ)) (hg : ∀ p, g p = σ * (p 0) ^ 2)
    (hzero : ∀ p : U, productMap g p = 0 ↔ (p : E2) = 0) :
    IsLocalDegreeTwo U (productMap g) hzero 0 := by
  let cpt : C(unitInterval × U, ℝ × ℝ) :=
    ⟨fun r => (σ * (((r.2 : E2) 0) ^ 2 + (r.1 : ℝ)), (r.2 : E2) 1), by fun_prop⟩
  let Hf : C(unitInterval × U, E2) :=
    ⟨fun r => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => if i = 0 then (cpt r).1 else (cpt r).2),
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (by
        apply continuous_pi; intro i; fin_cases i
        · simpa using (continuous_fst.comp cpt.continuous)
        · simpa using (continuous_snd.comp cpt.continuous))⟩
  let G1 : C(U, E2) := ⟨fun p => Hf (1, p), Hf.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H : ContinuousMap.Homotopy (restrictedMap U (productMap g)) G1 :=
    { toContinuousMap := Hf
      map_zero_left := by
        intro p; ext i; fin_cases i <;> simp [Hf, cpt, restrictedMap, productMap, hg]
      map_one_left := by intro p; rfl }
  have hG1 : ∀ p, G1 p ≠ 0 := by
    intro p h
    have := congrArg (fun q : E2 => q 0) h
    simp [G1, Hf, cpt] at this
    rcases this with h1 | h1
    · exact hσ h1
    · nlinarith [sq_nonneg ((p : E2) 0)]
  have hHm : ∀ t : unitInterval, ∀ p ∈ neighborhoodDeletedPoint U (0 : E2), H (t, p) ∈ deletedPoint (0 : E2) := by
    intro t p hp hHp
    apply hp
    have h0' := congrArg (fun q : E2 => q 0) hHp
    have h1' := congrArg (fun q : E2 => q 1) hHp
    simp [H, Hf, cpt] at h0' h1'
    have h0'' : σ * (((p : E2) 0) ^ 2 + (t : ℝ)) = 0 := by
      exact h0'
    have hu : (p : E2) 0 = 0 := by
      rcases mul_eq_zero.mp h0'' with h | h
      · exact absurd h hσ
      · nlinarith [sq_nonneg ((p : E2) 0), t.2.1]
    ext i; fin_cases i
    · simpa using hu
    · simpa using h1'
  have hmap := ConstructionTargets.RelativeSingularHomologyHomotopy.relativeSingularHomologyMap_eq_of_homotopy
    (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2)) H hHm
    (by intro p hp hFp; exact hp ((hzero p).mp hFp)) (fun p _ => hG1 p) 2
  letI := ConstructionTargets.HigherChartLocalGenerator.neighborhoodInclusion_Hn_isIso 0 U (0 : E2) hU h0
  let ι := HomologicalComplex.homologyMap
    (relativeSingularMap (neighborhoodDeletedPoint U (0 : E2)) (deletedPoint (0 : E2))
      (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U 0)) (0+2)
  refine ⟨(asIso ι).inv
    (ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator (k := 0) (0 : E2)),
    ConcreteCategory.congr_hom (asIso ι).inv_hom_id _, ?_⟩
  rw [zero_smul]
  erw [hmap, homologyMap_eq_zero_of_avoids U G1 hG1]
  rfl

/-- The positive fold has zero local degree.  Its image lies in the closed
right half-plane; the relative `H₂` of that half-plane at the origin vanishes
because the half-plane and its puncture are contractible.  Estimated size:
90--150 lines. -/
theorem positiveFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap positiveFoldScalar)
      (positiveFold_productMap_zero_iff U) 0 :=
  fold_localDegree_zero U hU h0 1 one_ne_zero positiveFoldScalar
    (fun p => by simp [positiveFoldScalar]) _

/-- The negative fold has zero local degree by the identical half-plane
factorization through the closed left half-plane.  Estimated size: 25--45
lines once the positive half-plane calculation is available. -/
theorem negativeFold_productMap_localDegree
    (U : Set E2) (hU : IsOpen U) (h0 : (0 : E2) ∈ U) :
    IsLocalDegreeTwo U (productMap negativeFoldScalar)
      (negativeFold_productMap_zero_iff U) 0 :=
  fold_localDegree_zero U hU h0 (-1) (by norm_num) negativeFoldScalar
    (fun p => by simp [negativeFoldScalar]) _

end t00J02_ModelProduct

#print axioms t00J02_ModelProduct.firstCoordinateReflection_ambientLocalGenerator
