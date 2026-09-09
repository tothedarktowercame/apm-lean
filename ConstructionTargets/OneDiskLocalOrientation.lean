import ConstructionTargets.OneDiskIncreasingOrientation
/-!
# Integral local orientations of the pointed open one-disk

The local generators are exactly the banked class and its negative.
Reflection swaps interval endpoints, hence negates relative H1; two actual
commuting maps of pairs transport this calculation to the open model.
Increasing and decreasing pointed coordinate homeomorphisms have signs +1
and -1 through the production chart-pair relative homology map.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.OneDiskLocalOrientation
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.RelativeSingularConnectingNaturality
open ConstructionTargets.T02A06HemisphereExcision
open ConstructionTargets.T02A06DiskRadialComparison
open ConstructionTargets.T02A06SphereOne
open T02A06
open ConstructionTargets.ModelPairLocalHomologyOne

abbrev H0 := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)

theorem intervalGenerator_boundary_coordinates :
    intervalBoundaryRelativeH1IsoInt.inv ≫ singularPairConnecting intervalBoundary 0 ≫
      intervalBoundaryH0Iso.hom = boolIntDifference := by
  simp only [intervalBoundaryRelativeH1IsoInt, Iso.trans_inv, Category.assoc]
  have h1 : intervalRelativeH1IsoEndpointKernel.inv ≫
      singularPairConnecting intervalBoundary 0 = kernel.ι intervalEndpointH0Map := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero
  rw [← Category.assoc intervalRelativeH1IsoEndpointKernel.inv, h1]
  have h2 : intervalEndpointKernelIsoCodiagonalKernel.inv ≫
      kernel.ι intervalEndpointH0Map ≫ intervalBoundaryH0Iso.hom =
      kernel.ι boolIntCodiagonal := by
    simp [intervalEndpointKernelIsoCodiagonalKernel]
  erw [h2]
  exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

def intervalReflection : C(unitInterval, unitInterval) :=
  ⟨unitInterval.symm, unitInterval.continuous_symm⟩

theorem intervalReflection_mapsTo :
    Set.MapsTo intervalReflection intervalBoundary intervalBoundary := by
  intro x hx
  rcases hx with hx | hx
  · subst x; simp [intervalReflection, intervalBoundary]
  · have hx' : x = 1 := hx
    subst x; simp [intervalReflection, intervalBoundary]

def boolNot : TopCat.of Bool ⟶ TopCat.of Bool :=
  TopCat.ofHom ⟨Bool.not, continuous_of_discreteTopology⟩

noncomputable def boolSwap : BoolIntCoproduct ⟶ BoolIntCoproduct :=
  Sigma.map' Bool.not (fun _ => 𝟙 IntGroup)

theorem intervalReflection_H0_coordinates :
    intervalBoundaryH0Iso.inv ≫
      H0.map (subspaceMap intervalBoundary intervalBoundary intervalReflection intervalReflection_mapsTo) ≫
      intervalBoundaryH0Iso.hom = boolSwap := by
  let e : TopCat.of Bool ≅ TopCat.of intervalBoundary := TopCat.isoOfHomeo boolHomeomorphIntervalBoundary
  let r := subspaceMap intervalBoundary intervalBoundary intervalReflection intervalReflection_mapsTo
  have he : e.hom ≫ r ≫ e.inv = boolNot := by
    ext b : 1
    cases b <;> simp [e, r, boolNot, subspaceMap, intervalReflection,
      boolHomeomorphIntervalBoundary, boolEquivIntervalBoundary, unitInterval.symm]
  change (directDiscreteH0Iso AddCommGrpCat IntGroup Bool).inv ≫
    H0.map e.hom ≫ H0.map r ≫ H0.map e.inv ≫
    (directDiscreteH0Iso AddCommGrpCat IntGroup Bool).hom = boolSwap
  have hmap : H0.map e.hom ≫ H0.map r ≫ H0.map e.inv = H0.map boolNot := by
    rw [← Functor.map_comp, ← Functor.map_comp, he]
  slice_lhs 2 4 => erw [hmap]
  have h := directDiscreteH0Iso_naturality AddCommGrpCat IntGroup boolNot
  change (directDiscreteH0Iso AddCommGrpCat IntGroup Bool).inv ≫ H0.map boolNot =
    boolSwap ≫ (directDiscreteH0Iso AddCommGrpCat IntGroup Bool).inv at h
  rw [← Category.assoc, h]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem boolDifference_swap : boolIntDifference ≫ boolSwap = -boolIntDifference := by
  simp [boolIntDifference, boolSwap, sub_eq_add_neg, add_comm]

theorem intervalReflection_H1_eq_neg_id :
    HomologicalComplex.homologyMap
      (relativeSingularMap intervalBoundary intervalBoundary intervalReflection intervalReflection_mapsTo) 1 =
      -𝟙 _ := by
  let R := HomologicalComplex.homologyMap
    (relativeSingularMap intervalBoundary intervalBoundary intervalReflection intervalReflection_mapsTo) 1
  let r := H0.map
    (subspaceMap intervalBoundary intervalBoundary intervalReflection intervalReflection_mapsTo)
  have hn : R ≫ singularPairConnecting intervalBoundary 0 =
      singularPairConnecting intervalBoundary 0 ≫ r :=
    (singularPairConnecting_naturality _ _ _ intervalReflection_mapsTo 0).symm
  have hc : r ≫ intervalBoundaryH0Iso.hom = intervalBoundaryH0Iso.hom ≫ boolSwap := by
    apply (cancel_epi intervalBoundaryH0Iso.inv).1
    simpa only [Iso.inv_hom_id_assoc] using intervalReflection_H0_coordinates
  have hb : intervalBoundaryH0Iso.hom
      (singularPairConnecting intervalBoundary 0 intervalBoundaryRelativeH1Generator) =
      boolIntDifference 1 := ConcreteCategory.congr_hom intervalGenerator_boundary_coordinates 1
  have hg : R intervalBoundaryRelativeH1Generator = -intervalBoundaryRelativeH1Generator := by
    apply (AddCommGrpCat.mono_iff_injective (singularPairConnecting intervalBoundary 0)).mp inferInstance
    apply (AddCommGrpCat.mono_iff_injective intervalBoundaryH0Iso.hom).mp inferInstance
    calc
      intervalBoundaryH0Iso.hom (singularPairConnecting intervalBoundary 0
          (R intervalBoundaryRelativeH1Generator)) =
          intervalBoundaryH0Iso.hom (r (singularPairConnecting intervalBoundary 0
            intervalBoundaryRelativeH1Generator)) :=
        congrArg intervalBoundaryH0Iso.hom (ConcreteCategory.congr_hom hn _)
      _ = boolSwap (intervalBoundaryH0Iso.hom (singularPairConnecting intervalBoundary 0
            intervalBoundaryRelativeH1Generator)) := ConcreteCategory.congr_hom hc _
      _ = boolSwap (boolIntDifference 1) := by rw [hb]
      _ = -(boolIntDifference 1) := ConcreteCategory.congr_hom boolDifference_swap 1
      _ = intervalBoundaryH0Iso.hom (singularPairConnecting intervalBoundary 0
          (-intervalBoundaryRelativeH1Generator)) := by
            erw [map_neg, map_neg, hb]
  ext z
  have hz : z = (intervalBoundaryRelativeH1IsoInt.hom z) • intervalBoundaryRelativeH1Generator := by
    apply (AddCommGrpCat.mono_iff_injective intervalBoundaryRelativeH1IsoInt.hom).mp inferInstance
    erw [map_zsmul, intervalBoundaryRelativeH1IsoInt_generator]
    simp
  change R z = -z
  rw [hz, map_zsmul, hg, zsmul_neg]

abbrev RH {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :=
  HomologicalComplex.homologyMap (relativeSingularMap A B f hf) 1

theorem relativeH1_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (u : C(X,X)) (v : C(Y,Y)) (f : C(X,Y))
    (hu : Set.MapsTo u A A) (hv : Set.MapsTo v B B) (hf : Set.MapsTo f A B)
    (h : f.comp u = v.comp f) :
    RH A A u hu ≫ RH A B f hf = RH A B f hf ≫ RH B B v hv := by
  calc
    _ = RH A B (f.comp u) (hf.comp hu) := relativeSingularHomologyMap_comp _ _ _ _ _ _ _ _ 1
    _ = RH A B (v.comp f) (hv.comp hf) := by congr 1
    _ = _ := (relativeSingularHomologyMap_comp _ _ _ _ _ _ _ _ 1).symm

def closedReflection : C(euclideanClosedDisk 1, euclideanClosedDisk 1) where
  toFun x := ⟨-x.1, by
    have hx := x.2
    change dist x.1 0 ≤ 1 at hx
    change dist (-x.1) 0 ≤ 1
    simpa only [dist_zero_right, norm_neg] using hx⟩
  continuous_toFun := by fun_prop

theorem closedReflection_mapsTo :
    Set.MapsTo closedReflection (closedDiskBoundarySet 1) (closedDiskBoundarySet 1) := by
  intro x hx
  simpa [closedDiskBoundarySet, closedReflection, Metric.mem_sphere, dist_zero_right] using hx

def closedToInterval : C(euclideanClosedDisk 1, unitInterval) :=
  ⟨closedDiskOneHomeomorphUnitInterval, closedDiskOneHomeomorphUnitInterval.continuous⟩

theorem closedToInterval_mapsTo : Set.MapsTo closedToInterval (closedDiskBoundarySet 1) intervalBoundary :=
  fun x hx => (closedDiskOne_boundary_iff x).mp hx

theorem closedReflection_H1_eq_neg_id :
    RH (closedDiskBoundarySet 1) (closedDiskBoundarySet 1) closedReflection closedReflection_mapsTo = -𝟙 _ := by
  have hcomm : closedToInterval.comp closedReflection = intervalReflection.comp closedToInterval := by
    ext x : 1
    apply Subtype.ext
    change (-x.1 0 + 1) / 2 = 1 - (x.1 0 + 1) / 2
    ring
  have h := relativeH1_square _ _ _ _ _ closedReflection_mapsTo intervalReflection_mapsTo
    closedToInterval_mapsTo hcomm
  have he : RH (closedDiskBoundarySet 1) intervalBoundary closedToInterval closedToInterval_mapsTo =
      (closedDiskOneRelativeIsoInterval 1).hom := rfl
  have hi : RH intervalBoundary intervalBoundary intervalReflection intervalReflection_mapsTo = -𝟙 _ :=
    intervalReflection_H1_eq_neg_id
  rw [he, hi] at h
  apply (cancel_mono (closedDiskOneRelativeIsoInterval 1).hom).1
  simpa using h

def reflection : C(euclideanOpenDisk 1, euclideanOpenDisk 1) where
  toFun x := ⟨-x.1, by
    have hx := x.2
    change dist x.1 0 < 1 at hx
    change dist (-x.1) 0 < 1
    simpa only [dist_zero_right, norm_neg] using hx⟩
  continuous_toFun := by fun_prop

theorem reflection_mapsTo :
    Set.MapsTo reflection (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1) := by
  intro x hx
  change -x.1 ≠ 0
  exact neg_ne_zero.mpr hx

theorem reflection_H1_eq_neg_id :
    RH (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1) reflection reflection_mapsTo = -𝟙 _ := by
  have hcomm : (halfDiskMap 1).comp closedReflection = reflection.comp (halfDiskMap 1) := by
    ext x : 1
    apply Subtype.ext
    exact smul_neg _ _
  have h := relativeH1_square _ _ _ _ _ closedReflection_mapsTo reflection_mapsTo
    (halfDiskMap_mapsTo 1) hcomm
  letI := closedDiskPair_to_openDiskPair_homologyMap_isIso_one 1
  apply (cancel_epi (RH _ _ (halfDiskMap 1) (halfDiskMap_mapsTo 1))).1
  rw [closedReflection_H1_eq_neg_id] at h
  simpa using h.symm

theorem reflection_generator :
    RH (puncturedOpenDiskSet 1) (puncturedOpenDiskSet 1) reflection reflection_mapsTo
      openDiskOnePunctureRelativeH1Generator = -openDiskOnePunctureRelativeH1Generator := by
  rw [reflection_H1_eq_neg_id]
  rfl

open ConstructionTargets.OneDiskIncreasingOrientation

/-- A local orientation generator generates the whole integral local group. -/
def IsLocalOrientationGenerator
    (g : (RelativeSingularChains P).homology 1) : Prop :=
  ∀ z : (RelativeSingularChains P).homology 1, ∃ n : ℤ, n • g = z

theorem model_class_zsmul (z : (RelativeSingularChains P).homology 1) :
    (openDiskOnePunctureRelativeH1IsoInt.hom z) • openDiskOnePunctureRelativeH1Generator = z := by
  apply (AddCommGrpCat.mono_iff_injective openDiskOnePunctureRelativeH1IsoInt.hom).mp inferInstance
  erw [map_zsmul, openDiskOnePunctureRelativeH1IsoInt_generator]
  simp

theorem model_generators_exactly_two (g : (RelativeSingularChains P).homology 1) :
    IsLocalOrientationGenerator g ↔
      g = openDiskOnePunctureRelativeH1Generator ∨ g = -openDiskOnePunctureRelativeH1Generator := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h openDiskOnePunctureRelativeH1Generator
    have hm := congrArg openDiskOnePunctureRelativeH1IsoInt.hom hn
    erw [map_zsmul, openDiskOnePunctureRelativeH1IsoInt_generator] at hm
    change n * openDiskOnePunctureRelativeH1IsoInt.hom g = 1 at hm
    have hi := Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hm)
    rcases hi with hi | hi
    · left
      apply (AddCommGrpCat.mono_iff_injective openDiskOnePunctureRelativeH1IsoInt.hom).mp inferInstance
      erw [hi, openDiskOnePunctureRelativeH1IsoInt_generator]
    · right
      apply (AddCommGrpCat.mono_iff_injective openDiskOnePunctureRelativeH1IsoInt.hom).mp inferInstance
      erw [map_neg, openDiskOnePunctureRelativeH1IsoInt_generator, hi]
  · rintro (rfl | rfl) z
    · exact ⟨_, model_class_zsmul z⟩
    · refine ⟨-openDiskOnePunctureRelativeH1IsoInt.hom z, ?_⟩
      simpa only [neg_zsmul, zsmul_neg, neg_neg] using model_class_zsmul z

/-- The actual reflection is a pointed homeomorphism, with inverse itself. -/
def reflectionHomeomorph : D ≃ₜ D where
  toFun := reflection
  invFun := reflection
  left_inv x := by apply Subtype.ext; simp [reflection]
  right_inv x := by apply Subtype.ext; simp [reflection]
  continuous_toFun := reflection.continuous
  continuous_invFun := reflection.continuous

@[simp] theorem reflection_origin : reflection origin = origin := by
  apply Subtype.ext
  simp [reflection, origin]

def Decreasing (f : C(D,D)) : Prop :=
  ∀ x y : D, coord x < coord y → coord (f y) < coord (f x)

theorem reflected_decreasing_increasing (f : C(D,D)) (hdec : Decreasing f) :
    Increasing (reflection.comp f) := by
  intro x y hxy
  exact neg_lt_neg (hdec x y hxy)

theorem decreasing_mapsTo (f : C(D,D)) (hdec : Decreasing f) (hfix : f origin = origin) :
    Set.MapsTo f P P := by
  have hgfix : (reflection.comp f) origin = origin := by
    change reflection (f origin) = origin
    rw [hfix, reflection_origin]
  have hg := increasing_mapsTo (reflection.comp f) (reflected_decreasing_increasing f hdec) hgfix
  intro x hx hz
  apply hg hx
  change -(f x).1 = 0
  rw [hz, neg_zero]

theorem modelGenerator_map_of_decreasing (f : C(D,D))
    (hdec : Decreasing f) (hfix : f origin = origin) :
    RH P P f (decreasing_mapsTo f hdec hfix) openDiskOnePunctureRelativeH1Generator =
      -openDiskOnePunctureRelativeH1Generator := by
  have hgfix : (reflection.comp f) origin = origin := by
    change reflection (f origin) = origin
    rw [hfix, reflection_origin]
  have hg := modelGenerator_map_of_increasing (reflection.comp f)
    (reflected_decreasing_increasing f hdec) hgfix
  have hc := relativeSingularHomologyMap_comp P P P f reflection
    (decreasing_mapsTo f hdec hfix) reflection_mapsTo
    (increasing_mapsTo (reflection.comp f) (reflected_decreasing_increasing f hdec) hgfix) 1
  have he := ConcreteCategory.congr_hom hc openDiskOnePunctureRelativeH1Generator
  have hr : HomologicalComplex.homologyMap (relativeSingularMap P P reflection reflection_mapsTo) 1 = -𝟙 _ :=
    reflection_H1_eq_neg_id
  rw [hr] at he
  change -(RH P P f (decreasing_mapsTo f hdec hfix) openDiskOnePunctureRelativeH1Generator) = _ at he
  rw [hg] at he
  exact neg_eq_iff_eq_neg.mp he

open ConstructionTargets.ChartPairRelativeHomologyTransport

theorem mem_puncture_iff_ne_origin (x : D) : x ∈ P ↔ x ≠ origin := by
  change x.1 ≠ 0 ↔ x ≠ origin
  constructor
  · intro h hx
    exact h (congrArg Subtype.val hx)
  · intro h hx
    exact h (Subtype.ext hx)

theorem pointedHomeomorph_pair_iff (e : D ≃ₜ D) (hfix : e origin = origin) (x : D) :
    x ∈ P ↔ e x ∈ P := by
  rw [mem_puncture_iff_ne_origin, mem_puncture_iff_ne_origin]
  constructor
  · intro hx he
    exact hx (e.injective (he.trans hfix.symm))
  · intro hx he
    exact hx ((congrArg e he).trans hfix)

/-- Increasing pointed coordinate homeomorphisms preserve the model orientation
through the production chart-pair transport, with its pair witness constructed. -/
theorem increasing_homeomorph_generator (e : D ≃ₜ D) (hfix : e origin = origin)
    (hinc : Increasing (pairContinuousMap e)) :
    transportedOpenDiskOnePunctureGenerator e P (pointedHomeomorph_pair_iff e hfix) =
      openDiskOnePunctureRelativeH1Generator := by
  exact modelGenerator_map_of_increasing (pairContinuousMap e) hinc hfix

/-- Decreasing pointed coordinate homeomorphisms negate the model orientation. -/
theorem decreasing_homeomorph_generator (e : D ≃ₜ D) (hfix : e origin = origin)
    (hdec : Decreasing (pairContinuousMap e)) :
    transportedOpenDiskOnePunctureGenerator e P (pointedHomeomorph_pair_iff e hfix) =
      -openDiskOnePunctureRelativeH1Generator := by
  exact modelGenerator_map_of_decreasing (pairContinuousMap e) hdec hfix

/-- Identity and geometric reflection are concrete chart-pair computations. -/
theorem identity_homeomorph_generator :
    transportedOpenDiskOnePunctureGenerator (Homeomorph.refl D) P
      (pointedHomeomorph_pair_iff (Homeomorph.refl D) rfl) =
      openDiskOnePunctureRelativeH1Generator :=
  increasing_homeomorph_generator _ rfl (fun _ _ h => h)

theorem reflection_homeomorph_generator :
    transportedOpenDiskOnePunctureGenerator reflectionHomeomorph P
      (pointedHomeomorph_pair_iff reflectionHomeomorph reflection_origin) =
      -openDiskOnePunctureRelativeH1Generator :=
  reflection_generator

theorem chosen_generator_ne_negative :
    openDiskOnePunctureRelativeH1Generator ≠ -openDiskOnePunctureRelativeH1Generator := by
  intro h
  have hc := congrArg openDiskOnePunctureRelativeH1IsoInt.hom h
  erw [map_neg, openDiskOnePunctureRelativeH1IsoInt_generator] at hc
  norm_num at hc

/-- Identity induces the identity endomorphism on the entire local group. -/
theorem identity_H1_eq_id :
    RH P P (ContinuousMap.id D) (fun _ h => h) = 𝟙 _ := by
  unfold RH
  rw [relativeSingularMap_id, HomologicalComplex.homologyMap_id]

end ConstructionTargets.OneDiskLocalOrientation
#print axioms ConstructionTargets.OneDiskLocalOrientation.intervalGenerator_boundary_coordinates

#print axioms ConstructionTargets.OneDiskLocalOrientation.intervalReflection_H0_coordinates
#print axioms ConstructionTargets.OneDiskLocalOrientation.boolDifference_swap

#print axioms ConstructionTargets.OneDiskLocalOrientation.intervalReflection_H1_eq_neg_id

#print axioms ConstructionTargets.OneDiskLocalOrientation.reflection_H1_eq_neg_id
#print axioms ConstructionTargets.OneDiskLocalOrientation.reflection_generator

#print axioms ConstructionTargets.OneDiskLocalOrientation.model_generators_exactly_two
#print axioms ConstructionTargets.OneDiskLocalOrientation.reflectionHomeomorph
#print axioms ConstructionTargets.OneDiskLocalOrientation.modelGenerator_map_of_decreasing

#print axioms ConstructionTargets.OneDiskLocalOrientation.increasing_homeomorph_generator
#print axioms ConstructionTargets.OneDiskLocalOrientation.decreasing_homeomorph_generator
#print axioms ConstructionTargets.OneDiskLocalOrientation.identity_homeomorph_generator
#print axioms ConstructionTargets.OneDiskLocalOrientation.reflection_homeomorph_generator
#print axioms ConstructionTargets.OneDiskLocalOrientation.chosen_generator_ne_negative

#print axioms ConstructionTargets.OneDiskLocalOrientation.identity_H1_eq_id
