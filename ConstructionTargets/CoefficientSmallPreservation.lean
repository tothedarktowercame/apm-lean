import ConstructionTargets.CoefficientFiniteOperators
import ConstructionTargets.CoefficientSmallH0
noncomputable section
namespace ConstructionTargets.CoefficientSmallPreservation
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
open CoefficientSmallH0
variable (R : Type) [CommRing R]
variable {X α : Type} [TopologicalSpace X] (U : α → Set X)

theorem subdivision_lift (n : ℕ)
    (s : (coverSmallSSet U).obj (Opposite.op ⦋n⦌)) :
    ∃ q : ModuleCat.of R R ⟶ (K R U).X n,
      q ≫ (inc R U).f n = CoefficientH0.singularGenerator R _ n s.val ≫
        (CoefficientSingularSubdivision.singularSubdivision R).f n := by
  let σ := continuousMapOfSingularSimplex n s.val
  obtain ⟨a, ha⟩ := range_subset_of_singularSimplex_mem_coverSmallSSet U s.val s.property
  have hp : ∀ τ ∈ (postcomposeFiniteVertexChain σ
      (finiteVertexSubdivision n (standardSimplexVertices n))).support,
      ∃ a, Set.range τ ⊆ U a := by
    intro τ hτ
    obtain ⟨v, _, rfl⟩ := postcomposeFiniteVertexChain_mem_support σ _ hτ
    refine ⟨a, ?_⟩
    rintro _ ⟨x,rfl⟩
    exact ha (Set.mem_range_self _)
  obtain ⟨q,hq⟩ := CoefficientFiniteRealization.finiteSingularChainRealize_factors R U n _ hp
  refine ⟨q, hq.trans ?_⟩
  rw [CoefficientFiniteOperators.subdivision_realize]
  congr 2

theorem prism_lift (n : ℕ)
    (s : (coverSmallSSet U).obj (Opposite.op ⦋n⦌)) :
    ∃ q : ModuleCat.of R R ⟶ (K R U).X (n+1),
      q ≫ (inc R U).f (n+1) = CoefficientH0.singularGenerator R _ n s.val ≫
        CoefficientSingularPrism.singularPrismDegree R n := by
  let σ := continuousMapOfSingularSimplex n s.val
  obtain ⟨a, ha⟩ := range_subset_of_singularSimplex_mem_coverSmallSSet U s.val s.property
  have hp : ∀ τ ∈ (postcomposedPrism n σ).support, ∃ a, Set.range τ ⊆ U a := by
    intro τ hτ
    exact ⟨a, postcomposedPrism_small n σ U ha hτ⟩
  obtain ⟨q,hq⟩ := CoefficientFiniteRealization.finiteSingularChainRealize_factors R U (n+1) _ hp
  refine ⟨q, hq.trans ?_⟩
  rw [CoefficientFiniteOperators.prism_realize]
  congr 2

def subdivisionDegree (n : ℕ) : (K R U).X n ⟶ (K R U).X n :=
  Limits.Sigma.desc fun s => Classical.choose (subdivision_lift R U n s)
def prismDegree (n : ℕ) : (K R U).X n ⟶ (K R U).X (n+1) :=
  Limits.Sigma.desc fun s => Classical.choose (prism_lift R U n s)

@[reassoc] theorem subdivision_inc (n : ℕ) :
    subdivisionDegree R U n ≫ (inc R U).f n =
      (inc R U).f n ≫ (CoefficientSingularSubdivision.singularSubdivision R).f n := by
  apply Limits.Sigma.hom_ext
  intro s
  change (Limits.Sigma.ι (fun _ : (coverSmallSSet U).obj (Opposite.op ⦋n⦌) => ModuleCat.of R R) s ≫
    Limits.Sigma.desc (fun t => Classical.choose (subdivision_lift R U n t))) ≫ _ = _
  rw [Limits.Sigma.ι_desc]
  rw [Classical.choose_spec (subdivision_lift R U n s)]
  change _ = (Limits.Sigma.ι (fun _ : (coverSmallSSet U).obj (Opposite.op ⦋n⦌) => ModuleCat.of R R) s ≫ (inc R U).f n) ≫ (CoefficientSingularSubdivision.singularSubdivision R).f n
  congr 1
  dsimp [inc, CoefficientSmallPath.coverSmallInclusion,
    CoefficientSmallPath.coverSmallChains, CoefficientH0.SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [Limits.Sigma.ι_comp_map']
  rfl

@[reassoc] theorem prism_inc (n : ℕ) :
    prismDegree R U n ≫ (inc R U).f (n+1) =
      (inc R U).f n ≫ CoefficientSingularPrism.singularPrismDegree R n := by
  apply Limits.Sigma.hom_ext
  intro s
  change (Limits.Sigma.ι (fun _ : (coverSmallSSet U).obj (Opposite.op ⦋n⦌) => ModuleCat.of R R) s ≫
    Limits.Sigma.desc (fun t => Classical.choose (prism_lift R U n t))) ≫ _ = _
  rw [Limits.Sigma.ι_desc]
  rw [Classical.choose_spec (prism_lift R U n s)]
  change _ = (Limits.Sigma.ι (fun _ : (coverSmallSSet U).obj (Opposite.op ⦋n⦌) => ModuleCat.of R R) s ≫ (inc R U).f n) ≫ CoefficientSingularPrism.singularPrismDegree R n
  congr 1
  dsimp [inc, CoefficientSmallPath.coverSmallInclusion,
    CoefficientSmallPath.coverSmallChains, CoefficientH0.SingularChains,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [Limits.Sigma.ι_comp_map']
  rfl


def subdivision : K R U ⟶ K R U where
  f := subdivisionDegree R U
  comm' i j _ := by
    apply (cancel_mono ((inc R U).f j)).1
    simp only [Category.assoc]
    rw [← (inc R U).comm i j]
    rw [subdivision_inc_assoc]
    rw [(CoefficientSingularSubdivision.singularSubdivision R).comm i j]
    rw [← Category.assoc, (inc R U).comm i j]
    simp only [Category.assoc, subdivision_inc]

theorem subdivision_inclusion : subdivision R U ≫ inc R U =
    inc R U ≫ CoefficientSingularSubdivision.singularSubdivision R := by
  apply HomologicalComplex.hom_ext
  intro n
  exact subdivision_inc R U n

theorem subdivision_zero : subdivisionDegree R U 0 = 𝟙 _ := by
  apply (cancel_mono ((inc R U).f 0)).1
  rw [subdivision_inc]
  change (inc R U).f 0 ≫ CoefficientBarycentricNaturality.degree R 0 = _
  rw [CoefficientSingularSubdivision.singularSubdivisionDegree_zero]
  simp

theorem prism_boundary_zero : prismDegree R U 0 ≫ (K R U).d 1 0 =
    subdivisionDegree R U 0 - 𝟙 _ := by
  apply (cancel_mono ((inc R U).f 0)).1
  simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
  rw [← (inc R U).comm 1 0, prism_inc_assoc]
  rw [CoefficientSingularPrism.degree_zero]
  simp only [Preadditive.comp_sub, Category.comp_id, subdivision_inc]

theorem prism_boundary_succ (n : ℕ) :
    prismDegree R U (n+1) ≫ (K R U).d (n+2) (n+1) +
      (K R U).d (n+1) n ≫ prismDegree R U n =
    subdivisionDegree R U (n+1) - 𝟙 _ := by
  apply (cancel_mono ((inc R U).f (n+1))).1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.id_comp, Category.assoc]
  rw [← (inc R U).comm (n+2) (n+1), prism_inc_assoc, prism_inc]
  rw [← Category.assoc ((K R U).d (n+1) n), ← (inc R U).comm (n+1) n]
  simp only [Category.assoc]
  rw [← Preadditive.comp_add]
  have h := CoefficientSingularPrism.singularPrism_identity R (X := X) (n+1)
  change _ + (L R (X := X)).d (n+1) n ≫ CoefficientSingularPrism.singularPrismDegree R n = _ at h
  rw [h]
  simp only [Preadditive.comp_sub, Category.comp_id, subdivision_inc]
  rfl

def components (i j : ℕ) : (K R U).X i ⟶ (K R U).X j :=
  if h : i+1=j then prismDegree R U i ≫ eqToHom (congrArg _ h) else 0
@[simp] theorem components_succ (i : ℕ) : components R U i (i+1) = prismDegree R U i := by
  simp [components]

def smallHomotopy : Homotopy (subdivision R U) (𝟙 _) where
  hom := components R U
  zero i j h := by
    have hij : i+1 ≠ j := by simpa using h
    simp [components, hij]
  comm n := by
    rw [Homotopy.prevD_chainComplex, components_succ]
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, zero_add]
      exact sub_eq_iff_eq_add.mp (prism_boundary_zero R U).symm
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, components_succ]
      change subdivisionDegree R U (n+1) = _ + 𝟙 _
      simpa only [add_comm] using sub_eq_iff_eq_add.mp (prism_boundary_succ R U n).symm


/-- All types are in universe zero. U is an arbitrary family of subsets;
empty spaces and empty index types require no additional cases or assumptions. -/
theorem homotopy_inclusion (n : ℕ) :
    (smallHomotopy R U).hom n (n+1) ≫ (inc R U).f (n+1) =
      (inc R U).f n ≫ (CoefficientSingularPrism.subdivisionHomotopy R).hom n (n+1) := by
  change components R U n (n+1) ≫ _ = _ ≫ CoefficientSingularPrism.prismComponents R n (n+1)
  rw [components_succ, CoefficientSingularPrism.prismComponents_succ]
  exact prism_inc R U n

def integral_interval_homotopy :
    Homotopy (subdivision ℤ CoefficientSmallPath.intervalCover) (𝟙 _) :=
  smallHomotopy ℤ CoefficientSmallPath.intervalCover

theorem integral_interval_inclusion (n : ℕ) :
    (integral_interval_homotopy).hom n (n+1) ≫
      (inc ℤ CoefficientSmallPath.intervalCover).f (n+1) =
    (inc ℤ CoefficientSmallPath.intervalCover).f n ≫
      (CoefficientSingularPrism.subdivisionHomotopy ℤ).hom n (n+1) :=
  homotopy_inclusion ℤ CoefficientSmallPath.intervalCover n

def rational_interval_homotopy :
    Homotopy (subdivision ℚ CoefficientSmallPath.intervalCover) (𝟙 _) :=
  smallHomotopy ℚ CoefficientSmallPath.intervalCover

theorem rational_interval_inclusion (n : ℕ) :
    (rational_interval_homotopy).hom n (n+1) ≫
      (inc ℚ CoefficientSmallPath.intervalCover).f (n+1) =
    (inc ℚ CoefficientSmallPath.intervalCover).f n ≫
      (CoefficientSingularPrism.subdivisionHomotopy ℚ).hom n (n+1) :=
  homotopy_inclusion ℚ CoefficientSmallPath.intervalCover n

#print axioms subdivision_lift
#print axioms prism_lift
#print axioms subdivision_inclusion
#print axioms subdivision_zero
#print axioms prism_boundary_zero
#print axioms prism_boundary_succ
#print axioms smallHomotopy
#print axioms homotopy_inclusion
#print axioms integral_interval_inclusion
#print axioms rational_interval_inclusion
end ConstructionTargets.CoefficientSmallPreservation
