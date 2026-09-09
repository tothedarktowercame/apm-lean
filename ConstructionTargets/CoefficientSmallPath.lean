import ConstructionTargets.CoefficientH0
import ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Simplicial
open scoped unitInterval
namespace ConstructionTargets.CoefficientSmallPath
open SingularSubdivision T02A06SphereH0
variable (R : Type) [CommRing R]
def coverSmallChains {X α : Type} [TopologicalSpace X] (U : α → Set X) :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)).obj (coverSmallSSet U : SSet)
def coverSmallInclusion {X α : Type} [TopologicalSpace X] (U : α → Set X) :
    coverSmallChains R U ⟶ CoefficientH0.SingularChains R (TopCat.of X) :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)).map (coverSmallSSet U).ι
noncomputable def coverSmallGenerator {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {n : ℕ}
    (sigSimplex : C(stdSimplex ℝ (Fin (n + 1)), X)) (a : α)
    (hsigSimplex : Set.range sigSimplex ⊆ U a) :
    ModuleCat.of R R ⟶ (coverSmallChains R U).X n := by
  let τ := singularSimplexOfContinuousMap (TopCat.of (U a)) n
    (liftSimplexToCover U sigSimplex a hsigSimplex)
  let f := TopCat.toSSet.map (coverSubspaceInclusion U a)
  have hmapped : f.app (Opposite.op ⦋n⦌) τ =
      singularSimplexOfContinuousMap (TopCat.of X) n sigSimplex := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U a, X)).comp
        (liftSimplexToCover U sigSimplex a hsigSimplex)) = _
    congr 1
  have hmem : singularSimplexOfContinuousMap (TopCat.of X) n sigSimplex ∈
      (coverSmallSSet U).obj (Opposite.op ⦋n⦌) := by
    rw [← hmapped]
    apply (le_iSup (fun a => SSet.Subcomplex.range
      (TopCat.toSSet.map (coverSubspaceInclusion U a))) a)
    exact ⟨τ, rfl⟩
  change ModuleCat.of R R ⟶
    ∐ fun _ : (coverSmallSSet U).obj (Opposite.op ⦋n⦌) => ModuleCat.of R R
  let sSmall : (coverSmallSSet U : SSet).obj (Opposite.op ⦋n⦌) :=
    ⟨singularSimplexOfContinuousMap (TopCat.of X) n sigSimplex, hmem⟩
  exact Limits.Sigma.ι
    (fun _ : (coverSmallSSet U : SSet).obj (Opposite.op ⦋n⦌) =>
      ModuleCat.of R R) sSmall

@[reassoc] theorem coverSmallGenerator_comp_ι
    {X α : Type} [TopologicalSpace X]
    (U : α → Set X) {n : ℕ}
    (sigSimplex : C(stdSimplex ℝ (Fin (n + 1)), X)) (a : α)
    (hsigSimplex : Set.range sigSimplex ⊆ U a) :
    coverSmallGenerator R U sigSimplex a hsigSimplex ≫ (coverSmallInclusion R U).f n =
      CoefficientH0.singularGenerator R (TopCat.of X) n
        (singularSimplexOfContinuousMap (TopCat.of X) n sigSimplex) := by
  dsimp [coverSmallGenerator, coverSmallInclusion, coverSmallChains,
    CoefficientH0.SingularChains, AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [Limits.Sigma.ι_comp_map']
  rfl


def vertex {X : Type} [TopologicalSpace X] (x : X) :=
  CoefficientH0.singularGenerator R (TopCat.of X) 0
    (singularSimplexOfContinuousMap _ 0 (singularVertexAt x))

theorem exists_small_path_edges {X α : Type} [TopologicalSpace X]
    (U : α → Set X) (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a)
    {x y : X} (p : Path x y) :
    ∃ (n : ℕ) (v : Fin (n+2) → X)
      (e : Fin (n+1) → (ModuleCat.of R R ⟶ (coverSmallChains R U).X 1)),
      v 0 = x ∧ v (Fin.last (n+1)) = y ∧
      ∀ i, e i ≫ (coverSmallInclusion R U).f 1 ≫
        (CoefficientH0.SingularChains R (TopCat.of X)).d 1 0 =
          vertex R (v i.succ) - vertex R (v i.castSucc) := by
  have hopen : ∀ a, IsOpen (p ⁻¹' U a) := fun a => (ho a).preimage p.continuous
  have hall : univ ⊆ ⋃ a, p ⁻¹' U a := by
    intro t _
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hc (mem_univ (p t)))
    exact mem_iUnion.mpr ⟨a, ha⟩
  obtain ⟨n, t, a, ht0, ht1, hm, hs⟩ :=
    exists_fin_Icc_subset_open_cover_unitInterval hopen hall
  let q (i : Fin (n+1)) := p.subpath (t i.castSucc) (t i.succ)
  have hq (i : Fin (n+1)) : range (singularEdgeOfPath (q i)) ⊆ U (a i) := by
    rintro z ⟨s, rfl⟩
    have hr : (singularEdgeOfPath (q i)) s ∈ range (q i) :=
      ⟨stdSimplexHomeomorphUnitInterval s, rfl⟩
    rw [Path.range_subpath_of_le p _ _ (hm i.castSucc_le_succ)] at hr
    obtain ⟨u, hu, he⟩ := hr
    rw [← he]
    exact hs i hu
  refine ⟨n, fun i => p (t i),
    fun i => coverSmallGenerator R U (singularEdgeOfPath (q i)) (a i) (hq i),
    ?_, ?_, ?_⟩
  · simp [ht0]
  · simp [ht1]
  · intro i
    rw [← Category.assoc, coverSmallGenerator_comp_ι]
    exact CoefficientH0.singularEdgeOfPath_boundary R (q i)
theorem telescoping {G : Type*} [AddCommGroup G] (n : ℕ) (v : Fin (n+1) → G) :
    (∑ i : Fin n, (v i.succ - v i.castSucc)) = v (Fin.last n) - v 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [← Fin.succ_castSucc]
    rw [ih (fun i => v i.succ)]
    simp only [Fin.succ_zero_eq_one, Fin.succ_last, Fin.castSucc_zero]
    abel

theorem exists_small_path_chain {X α : Type} [TopologicalSpace X]
    (U : α → Set X) (ho : ∀ a, IsOpen (U a)) (hc : univ ⊆ ⋃ a, U a)
    {x y : X} (p : Path x y) :
    ∃ c : ModuleCat.of R R ⟶ (coverSmallChains R U).X 1,
      c ≫ (coverSmallInclusion R U).f 1 ≫
        (CoefficientH0.SingularChains R (TopCat.of X)).d 1 0 = vertex R y - vertex R x := by
  obtain ⟨n,v,e,hx,hy,he⟩ := exists_small_path_edges R U ho hc p
  refine ⟨∑ i, e i, ?_⟩
  rw [Preadditive.sum_comp]
  simp_rw [he]
  rw [telescoping (n+1) (fun i => vertex R (v i)), hx, hy]

#print axioms coverSmallGenerator_comp_ι
#print axioms exists_small_path_edges
#print axioms exists_small_path_chain

def intervalCover (b : Bool) : Set ℝ := if b then Ioi 0 else Iio 1
theorem intervalCover_open (b : Bool) : IsOpen (intervalCover b) := by
  cases b
  · exact isOpen_Iio
  · exact isOpen_Ioi
theorem intervalCover_covers : univ ⊆ ⋃ b, intervalCover b := by
  intro x _
  by_cases h : x < 1
  · exact mem_iUnion.mpr ⟨false, h⟩
  · exact mem_iUnion.mpr ⟨true, by change 0 < x; linarith⟩
def unitPath : Path (0 : ℝ) 1 where
  toFun := fun t => t.val
  continuous_toFun := continuous_subtype_val
  source' := rfl
  target' := rfl
theorem rational_interval :
    ∃ c : ModuleCat.of ℚ ℚ ⟶ (coverSmallChains ℚ intervalCover).X 1,
      c ≫ (coverSmallInclusion ℚ intervalCover).f 1 ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of ℝ)).d 1 0 =
          vertex ℚ (1 : ℝ) - vertex ℚ (0 : ℝ) :=
  exists_small_path_chain ℚ intervalCover intervalCover_open intervalCover_covers unitPath
theorem integral_interval :
    ∃ c : ModuleCat.of ℤ ℤ ⟶ (coverSmallChains ℤ intervalCover).X 1,
      c ≫ (coverSmallInclusion ℤ intervalCover).f 1 ≫
        (CoefficientH0.SingularChains ℤ (TopCat.of ℝ)).d 1 0 =
          vertex ℤ (1 : ℝ) - vertex ℤ (0 : ℝ) :=
  exists_small_path_chain ℤ intervalCover intervalCover_open intervalCover_covers unitPath
#print axioms rational_interval
#print axioms integral_interval
end ConstructionTargets.CoefficientSmallPath
