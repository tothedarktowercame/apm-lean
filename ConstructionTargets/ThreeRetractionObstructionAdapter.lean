import ConstructionTargets.CircleSingularHomology

/-! # Three reusable retraction obstructions -/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ThreeRetractionObstructionAdapter

open ConstructionTargets.SingularHomologyConcrete

noncomputable def integralH1Functor : TopCat ⥤ ModuleCat ℤ :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)

def categoricalIntegralH1Map {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) :=
  integralH1Functor.map (TopCat.ofHom i)

def integralH1Map {X Y : TopCat} (f : X ⟶ Y) :=
  (integralH1Functor.map f).hom

/-- A continuous map is a retract inclusion when it has a continuous left
inverse. -/
def HasRetraction {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) : Prop :=
  ∃ r : C(X, A), r.comp i = ContinuousMap.id A

/-- Applying integral singular homology to a retraction identity gives a left
inverse of the inclusion-induced map. -/
theorem integralH1Map_injective_of_retraction
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (h : HasRetraction i) :
    Function.Injective (integralH1Map (TopCat.ofHom i)) := by
  rcases h with ⟨r, hr⟩
  apply Function.LeftInverse.injective (g := integralH1Map (TopCat.ofHom r))
  intro x
  have hm : integralH1Functor.map
      (TopCat.ofHom i ≫ TopCat.ofHom r) =
      integralH1Functor.map (𝟙 (TopCat.of A)) := by
    apply congrArg integralH1Functor.map
    change TopCat.ofHom (r.comp i) = 𝟙 (TopCat.of A)
    rw [hr]
    rfl
  have hm' := congrArg ModuleCat.Hom.hom hm
  have hx := DFunLike.congr_fun hm' x
  simpa [integralH1Map, integralH1Functor] using hx

/-- A retraction makes the inclusion injective on fundamental groups. -/
theorem fundamentalGroupMap_injective_of_retraction
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A) (h : HasRetraction i) :
    Function.Injective (FundamentalGroup.map i a) := by
  rcases h with ⟨r, hr⟩
  intro p q hpq
  change (FundamentalGroupoid.map i).map p =
    (FundamentalGroupoid.map i).map q at hpq
  have hpq' := congrArg (fun z => (FundamentalGroupoid.map r).map z) hpq
  change ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map p) =
    ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map q) at hpq'
  have hfun : FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r =
      CategoryTheory.Functor.id (FundamentalGroupoid A) := by
    rw [← FundamentalGroupoid.map_comp, hr, FundamentalGroupoid.map_id]
  rw [hfun] at hpq'
  exact hpq'

/-- The compiled nonzero integral circle generator contradicts a zero `H₁`
map whenever the circle inclusion is claimed to be a retract. -/
theorem circle_noRetraction_of_integralH1Map_eq_zero
    {X : Type} [TopologicalSpace X] (i : C(Circle, X))
    (hi : integralH1Map (TopCat.ofHom i) = 0) :
    ¬ HasRetraction i := by
  intro hret
  have hinj := integralH1Map_injective_of_retraction i hret
  apply circleSingularH1Generator_ne_zero
  apply hinj
  rw [hi]
  simp

/-- Categorical-morphism version, matching the frozen `H₁map = 0` premise
literally. -/
theorem circle_noRetraction_of_categoricalIntegralH1Map_eq_zero
    {X : Type} [TopologicalSpace X] (i : C(Circle, X))
    (hi : categoricalIntegralH1Map i = 0) :
    ¬ HasRetraction i := by
  apply circle_noRetraction_of_integralH1Map_eq_zero i
  exact congrArg ModuleCat.Hom.hom hi

/-- Noninjectivity of the inclusion-induced fundamental-group map rules out a
retraction, with no presentation or wedge-specific assumption added. -/
theorem noRetraction_of_fundamentalGroupMap_not_injective
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A)
    (hi : ¬ Function.Injective (FundamentalGroup.map i a)) :
    ¬ HasRetraction i := by
  intro h
  exact hi (fundamentalGroupMap_injective_of_retraction i a h)

/-- A connected space cannot retract onto the disjoint union of two nonempty
circles. -/
theorem twoCircles_noRetraction_of_connected
    {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (i : C(Sum Circle Circle, S)) :
    ¬ HasRetraction i := by
  rintro ⟨r, hr⟩
  have hr_surj : Function.Surjective r := fun a => ⟨i a, by
    have := DFunLike.congr_fun hr a
    simpa using this⟩
  letI : ConnectedSpace (Sum Circle Circle) :=
    hr_surj.connectedSpace r.continuous
  have hclopen :=
    (connectedSpace_iff_clopen.mp
      (inferInstance : ConnectedSpace (Sum Circle Circle))).2
      (Set.range (Sum.inl : Circle → Sum Circle Circle)) isClopen_range_inl
  rcases hclopen with hempty | huniv
  · exact (Set.range_nonempty
      (Sum.inl : Circle → Sum Circle Circle)).ne_empty hempty
  · have hmem : (Sum.inr (1 : Circle) : Sum Circle Circle) ∈
        Set.range (Sum.inl : Circle → Sum Circle Circle) := by
      rw [huniv]
      trivial
    rcases hmem with ⟨z, hz⟩
    exact Sum.inl_ne_inr hz

/-- The exact three-way adapter used by frozen `t01A03`: zero integral `H₁`
on the middle circle, noninjective `π₁` on the wedge inclusion, and
connectedness of the ambient surface discharge the three conclusions. -/
theorem three_retraction_obstructions
    {S A X : Type} [TopologicalSpace S] [ConnectedSpace S]
    [TopologicalSpace A] [TopologicalSpace X]
    (middle : C(Circle, S)) (wedge : C(A, X)) (base : A)
    (twoCircles : C(Sum Circle Circle, S))
    (hmiddle : integralH1Map (TopCat.ofHom middle) = 0)
    (hwedge : ¬ Function.Injective (FundamentalGroup.map wedge base)) :
    ¬ HasRetraction middle ∧ ¬ HasRetraction wedge ∧
      ¬ HasRetraction twoCircles := by
  exact ⟨circle_noRetraction_of_integralH1Map_eq_zero middle hmiddle,
    noRetraction_of_fundamentalGroupMap_not_injective wedge base hwedge,
    twoCircles_noRetraction_of_connected twoCircles⟩

/-- Frozen-compatible form of the combined adapter, accepting the categorical
`ModuleCat` morphism equality directly. -/
theorem three_retraction_obstructions_categorical
    {S A X : Type} [TopologicalSpace S] [ConnectedSpace S]
    [TopologicalSpace A] [TopologicalSpace X]
    (middle : C(Circle, S)) (wedge : C(A, X)) (base : A)
    (twoCircles : C(Sum Circle Circle, S))
    (hmiddle : categoricalIntegralH1Map middle = 0)
    (hwedge : ¬ Function.Injective (FundamentalGroup.map wedge base)) :
    ¬ HasRetraction middle ∧ ¬ HasRetraction wedge ∧
      ¬ HasRetraction twoCircles := by
  exact ⟨circle_noRetraction_of_categoricalIntegralH1Map_eq_zero middle hmiddle,
    noRetraction_of_fundamentalGroupMap_not_injective wedge base hwedge,
    twoCircles_noRetraction_of_connected twoCircles⟩

#print axioms integralH1Map_injective_of_retraction
#print axioms fundamentalGroupMap_injective_of_retraction
#print axioms circle_noRetraction_of_integralH1Map_eq_zero
#print axioms circle_noRetraction_of_categoricalIntegralH1Map_eq_zero
#print axioms noRetraction_of_fundamentalGroupMap_not_injective
#print axioms twoCircles_noRetraction_of_connected
#print axioms three_retraction_obstructions
#print axioms three_retraction_obstructions_categorical

end ConstructionTargets.ThreeRetractionObstructionAdapter
