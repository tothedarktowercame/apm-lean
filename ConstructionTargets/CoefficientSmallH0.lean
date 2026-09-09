import ConstructionTargets.CoefficientSmallPath
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Simplicial
namespace ConstructionTargets.CoefficientSmallH0
open SingularSubdivision CoefficientSmallPath
variable (R : Type) [CommRing R]
variable {X α : Type} [TopologicalSpace X]
variable (U : α → Set X)
abbrev K := CoefficientSmallPath.coverSmallChains R U
abbrev L := CoefficientH0.SingularChains R (TopCat.of X)
abbrev inc := coverSmallInclusion R U
instance component_mono (n : ℕ) : Mono ((inc R U).f n) := by
  dsimp [inc, coverSmallInclusion, CoefficientSmallPath.coverSmallChains, CoefficientH0.SingularChains,
    AlgebraicTopology.singularChainComplexFunctor, AlgebraicTopology.SSet.singularChainComplexFunctor]
  apply Limits.MonoCoprod.mono_map'_of_injective
  exact Subtype.val_injective

def liftZero (hc : univ ⊆ ⋃ a, U a) : (L R (X := X)).X 0 ⟶ (K R U).X 0 := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) 0 => ModuleCat.of R R) ⟶ _
  change _ ⟶ ∐ fun _ : (coverSmallSSet U).obj (Opposite.op ⦋0⦌) => ModuleCat.of R R
  exact Limits.Sigma.desc fun s => Limits.Sigma.ι (fun _ : (coverSmallSSet U).obj (Opposite.op ⦋0⦌) => ModuleCat.of R R) ⟨s, singularZeroSimplex_mem_coverSmallSSet U hc s⟩
theorem liftZero_inc (hc : univ ⊆ ⋃ a, U a) : liftZero R U hc ≫ (inc R U).f 0 = 𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro s
  dsimp [L, K, liftZero, inc, coverSmallInclusion, CoefficientSmallPath.coverSmallChains, CoefficientH0.SingularChains,
    AlgebraicTopology.singularChainComplexFunctor, AlgebraicTopology.SSet.singularChainComplexFunctor]
  simp only [← Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_comp_map', Category.comp_id]
  rfl
instance component_epi_zero (hc : univ ⊆ ⋃ a, U a) : Epi ((inc R U).f 0) :=
  epi_of_epi_fac (liftZero_inc R U hc)

theorem edge_lift (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a)
    (s : SingularSimplex (TopCat.of X) 1) :
    ∃ c : ModuleCat.of R R ⟶ (K R U).X 1,
      c ≫ (inc R U).f 1 ≫ (L R (X := X)).d 1 0 =
        CoefficientH0.singularGenerator R (TopCat.of X) 1 s ≫ (L R (X := X)).d 1 0 := by
  let f := continuousMapOfSingularSimplex 1 s
  let p : Path (f (stdSimplexHomeomorphUnitInterval.symm 0))
      (f (stdSimplexHomeomorphUnitInterval.symm 1)) :=
    ⟨f.comp ⟨stdSimplexHomeomorphUnitInterval.symm, stdSimplexHomeomorphUnitInterval.symm.continuous⟩, rfl, rfl⟩
  have he : singularSimplexOfContinuousMap (TopCat.of X) 1 (T02A06SphereH0.singularEdgeOfPath p) = s := by
    have hf : T02A06SphereH0.singularEdgeOfPath p = f := by
      ext t
      simp [T02A06SphereH0.singularEdgeOfPath, p]
    rw [hf]
    exact (TopCat.toSSetObjEquiv (TopCat.of X) _).symm_apply_apply s
  obtain ⟨c, h⟩ := exists_small_path_chain R U ho hc p
  refine ⟨c, ?_⟩
  rw [← he, CoefficientH0.singularEdgeOfPath_boundary R]
  exact h

def liftOne (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    (L R (X := X)).X 1 ⟶ (K R U).X 1 := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) 1 => ModuleCat.of R R) ⟶ _
  exact Limits.Sigma.desc fun s => (edge_lift R U ho hc s).choose

theorem liftOne_boundary (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    liftOne R U ho hc ≫ (inc R U).f 1 ≫ (L R (X := X)).d 1 0 = (L R (X := X)).d 1 0 := by
  dsimp [liftOne, L, K, CoefficientH0.SingularChains,
    AlgebraicTopology.singularChainComplexFunctor, AlgebraicTopology.SSet.singularChainComplexFunctor]
  apply Limits.Sigma.hom_ext
  intro s
  rw [Limits.Sigma.ι_desc_assoc]
  exact (edge_lift R U ho hc s).choose_spec

theorem exists_boundary (C : ChainComplex (ModuleCat R) ℕ)
    (x : C.cycles 0) (h : C.homologyπ 0 x = 0) :
    ∃ b : C.X 1, C.d 1 0 b = C.iCycles 0 x := by
  let S := ShortComplex.mk (C.toCycles 1 0) (C.homologyπ 0)
    (C.toCycles_comp_homologyπ 1 0)
  have hS : S.Exact := S.exact_of_g_is_cokernel (C.homologyIsCokernel 1 0 (by simp))
  obtain ⟨b,hb⟩ := (S.moduleCat_exact_iff.mp hS) x h
  change C.toCycles 1 0 b = x at hb
  refine ⟨b, ?_⟩
  have hi := ConcreteCategory.congr_hom (C.toCycles_i 1 0) b
  simpa only [CategoryTheory.comp_apply, hb] using hi.symm

theorem h0_injective (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    Function.Injective (HomologicalComplex.homologyMap (inc R U) 0) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  letI : Epi ((K R U).homologyπ 0) :=
    epi_of_isColimit_cofork ((K R U).homologyIsCokernel 1 0 (by simp))
  obtain ⟨x,hx⟩ := (ModuleCat.epi_iff_surjective ((K R U).homologyπ 0)).mp inferInstance y
  let xp := HomologicalComplex.cyclesMap (inc R U) 0 x
  have hxp : (L R (X := X)).homologyπ 0 xp = 0 := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inc R U) 0) x
    simpa only [CategoryTheory.comp_apply, xp, hx, hy] using h.symm
  obtain ⟨b,hb⟩ := exists_boundary R (L R (X := X)) xp hxp
  let q := liftOne R U ho hc b
  have hqd : (K R U).d 1 0 q = (K R U).iCycles 0 x := by
    apply (ModuleCat.mono_iff_injective ((inc R U).f 0)).mp inferInstance
    have hcomm := ConcreteCategory.congr_hom ((inc R U).comm 1 0) q
    have hlift := ConcreteCategory.congr_hom (liftOne_boundary R U ho hc) b
    have hcycles := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (inc R U) 0) x
    simp only [CategoryTheory.comp_apply] at hcomm hlift hcycles
    calc
      (inc R U).f 0 ((K R U).d 1 0 q) = (L R).d 1 0 ((inc R U).f 1 q) := hcomm.symm
      _ = (L R).d 1 0 b := hlift
      _ = (L R).iCycles 0 xp := hb
      _ = (inc R U).f 0 ((K R U).iCycles 0 x) := hcycles
  have hqx : (K R U).toCycles 1 0 q = x := by
    apply (ModuleCat.mono_iff_injective ((K R U).iCycles 0)).mp inferInstance
    have h := ConcreteCategory.congr_hom ((K R U).toCycles_i 1 0) q
    simpa only [CategoryTheory.comp_apply, hqd] using h
  have hz := ConcreteCategory.congr_hom ((K R U).toCycles_comp_homologyπ 1 0) q
  simpa only [CategoryTheory.comp_apply, hqx, hx] using hz

theorem h0_isIso (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    IsIso (HomologicalComplex.homologyMap (inc R U) 0) := by
  letI := component_epi_zero R U hc
  letI : Epi (HomologicalComplex.homologyMap (inc R U) 0) := by
    apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    intro j hj
    simp at hj
  letI : Mono (HomologicalComplex.homologyMap (inc R U) 0) :=
    (ModuleCat.mono_iff_injective _).mpr (h0_injective R U ho hc)
  exact isIso_of_mono_of_epi _

/-- The actual inclusion isomorphism; R, X and the arbitrary cover index are Type 0. -/
def h0Iso (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    (K R U).homology 0 ≅ (L R (X := X)).homology 0 := by
  letI := h0_isIso R U ho hc
  exact asIso (HomologicalComplex.homologyMap (inc R U) 0)
theorem h0Iso_hom (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    (h0Iso R U ho hc).hom = HomologicalComplex.homologyMap (inc R U) 0 := rfl
theorem inverse_left (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    (h0Iso R U ho hc).inv ≫ HomologicalComplex.homologyMap (inc R U) 0 = 𝟙 _ :=
  (h0Iso R U ho hc).inv_hom_id
theorem inverse_right (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a) :
    HomologicalComplex.homologyMap (inc R U) 0 ≫ (h0Iso R U ho hc).inv = 𝟙 _ :=
  (h0Iso R U ho hc).hom_inv_id

def rational_interval := h0Iso ℚ intervalCover intervalCover_open intervalCover_covers
def integral_interval := h0Iso ℤ intervalCover intervalCover_open intervalCover_covers
theorem empty_cover : IsIso (HomologicalComplex.homologyMap
    (inc R (fun _ : Empty => (∅ : Set Empty))) 0) :=
  h0_isIso R _ (fun a => Empty.elim a) (by intro x; exact Empty.elim x)
#print axioms empty_cover
#print axioms edge_lift
#print axioms liftOne_boundary
#print axioms h0_isIso
#print axioms inverse_left
#print axioms inverse_right
#print axioms rational_interval
#print axioms integral_interval
end ConstructionTargets.CoefficientSmallH0
