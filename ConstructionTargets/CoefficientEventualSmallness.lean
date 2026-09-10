import ConstructionTargets.CoefficientChainSupport
import ConstructionTargets.CoefficientSmallPreservation
noncomputable section
namespace ConstructionTargets.CoefficientEventualSmallness
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
def vertexSubdivisionIterate {ι : Type} [Fintype ι] (n : ℕ) : ℕ → ((CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n ⟶ (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n) := fun k => Nat.rec (𝟙 _) (fun _ r => r ≫ CoefficientBarycentricNaturality.vertexSubdivision R n) k

theorem vertexRealization_comp_singularSubdivision
    {ι : Type} [Fintype ι] (n : ℕ) :
    CoefficientAffineRealization.vertexRealizationDegree R (ι := ι) n ≫ CoefficientBarycentricNaturality.degree R n =
      CoefficientBarycentricNaturality.vertexSubdivision R n ≫ CoefficientAffineRealization.vertexRealizationDegree R n := by
  classical
  apply Limits.Sigma.hom_ext
  intro v
  change (CoefficientVertexCone.vertexGenerator R _ n v ≫ CoefficientAffineRealization.vertexRealizationDegree R n) ≫ _ = _
  rw [CoefficientAffineRealization.vertexGenerator_vertexRealizationDegree R]
  dsimp [CoefficientAffineRealization.affineGenerator]
  rw [CoefficientBarycentricNaturality.generator_degree R]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  simp only [← Category.assoc]
  slice_lhs 3 4 => rw [CoefficientAffineNaturality.vertexRealization_affine_natural R]
  slice_lhs 2 3 => rw [CoefficientBarycentricNaturality.vertexSubdivision_affine_natural R]
  simp only [← Category.assoc]
  rw [CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R]
  have hv : affineSimplex v ∘ standardSimplexVertices n = v := by
    funext i
    change affineSimplex v (standardSimplexVertices n i) = v i
    ext j
    simp only [affineSimplex_apply, standardSimplexVertices]
    change ∑ q, (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) q * v q j = v i j
    simp [Pi.single_apply]
  change (CoefficientVertexCone.vertexGenerator R _ n
      ((fun x => affineSimplex v x) ∘ standardSimplexVertices n) ≫ _) ≫ _ = _
  rw [hv]
  change CoefficientVertexCone.vertexGenerator R _ n v ≫ CoefficientBarycentricNaturality.vertexSubdivision R n ≫
    CoefficientAffineRealization.vertexRealizationDegree R n = CoefficientVertexCone.vertexGenerator R _ n v ≫
      CoefficientBarycentricNaturality.vertexSubdivision R n ≫ CoefficientAffineRealization.vertexRealizationDegree R n
  rfl

def singularSubdivisionIterate {X : Type} [TopologicalSpace X] (n : ℕ) :
    ℕ → ((CoefficientH0.SingularChains R (TopCat.of X)).X n ⟶
      (CoefficientH0.SingularChains R (TopCat.of X)).X n) := fun k =>
  Nat.rec (𝟙 _) (fun _ r => r ≫ CoefficientBarycentricNaturality.degree R n) k

theorem vertexRealization_comp_singularSubdivisionIterate
    {ι : Type} [Fintype ι] (n k : ℕ) :
    CoefficientAffineRealization.vertexRealizationDegree R (ι := ι) n ≫ singularSubdivisionIterate R n k =
      vertexSubdivisionIterate R n k ≫ CoefficientAffineRealization.vertexRealizationDegree R n := by
  induction k with
  | zero => simp [singularSubdivisionIterate, vertexSubdivisionIterate]
  | succ k ih =>
      simp only [singularSubdivisionIterate, vertexSubdivisionIterate,
        ← Category.assoc]
      change (CoefficientAffineRealization.vertexRealizationDegree R n ≫ singularSubdivisionIterate R n k) ≫ _ = _
      rw [ih]
      simp only [Category.assoc]
      rw [vertexRealization_comp_singularSubdivision]
      rfl

theorem iteratedFiniteVertexSubdivision_realize {ι : Type} [Fintype ι]
    (n k : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι) :
    CoefficientFiniteOperators.realize R (iteratedFiniteVertexSubdivision n k v) =
      CoefficientVertexCone.vertexGenerator R _ n v ≫ vertexSubdivisionIterate R n k := by
  induction k with
  | zero => simp [iteratedFiniteVertexSubdivision, vertexSubdivisionIterate]
  | succ k ih =>
      rw [show iteratedFiniteVertexSubdivision n (k + 1) v =
        FiniteVertexChain.bind (iteratedFiniteVertexSubdivision n k v)
          (finiteVertexSubdivision n) from rfl]
      rw [CoefficientFiniteOperators.realize_bind R _ _ (CoefficientBarycentricNaturality.vertexSubdivision R n)
        (CoefficientFiniteOperators.finiteVertexSubdivision_realize R n)]
      rw [ih, Category.assoc]
      congr 1

theorem singularSubdivisionIterate_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n k : ℕ) :
    (CoefficientH0.singularPostcomposition R f).f n ≫ singularSubdivisionIterate R n k =
      singularSubdivisionIterate R n k ≫ (CoefficientH0.singularPostcomposition R f).f n := by
  induction k with
  | zero => simp [singularSubdivisionIterate]
  | succ k ih =>
      simp only [singularSubdivisionIterate, Category.assoc]
      change ((CoefficientH0.singularPostcomposition R f).f n ≫
        singularSubdivisionIterate R n k) ≫ _ = _
      rw [ih]
      slice_lhs 2 3 => rw [CoefficientSingularSubdivision.singularSubdivision_natural R]
      rfl

theorem singularGenerator_iteratedSubdivision_realize
    {X : Type} [TopologicalSpace X] (n k : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    CoefficientH0.singularGenerator R (TopCat.of X) n
          (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        singularSubdivisionIterate R n k =
      CoefficientFiniteRealization.finiteSingularChainRealize R n
        (postcomposedIteratedSubdivision n k σ) := by
  unfold postcomposedIteratedSubdivision
  rw [CoefficientFiniteOperators.postcomposeFiniteVertexChain_realize R]
  rw [iteratedFiniteVertexSubdivision_realize]
  rw [← CoefficientSingularSubdivision.standardVertexRealization_postcomposition R]
  simp only [Category.assoc]
  rw [singularSubdivisionIterate_natural]
  slice_lhs 2 3 => rw [vertexRealization_comp_singularSubdivisionIterate]
  rfl


variable {X α : Type} [TopologicalSpace X] (U : α → Set X)

theorem generator_eventual (n : ℕ) (s : SingularSimplex (TopCat.of X) n)
    (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) :
    ∃ N, ∀ k, N ≤ k → ∃ q : ModuleCat.of R R ⟶ (CoefficientSmallPath.coverSmallChains R U).X n,
      q ≫ (CoefficientSmallPath.coverSmallInclusion R U).f n =
        CoefficientH0.singularGenerator R _ n s ≫ singularSubdivisionIterate R n k := by
  let σ := continuousMapOfSingularSimplex n s
  obtain ⟨N,hN⟩ := eventually_postcomposedIteratedSubdivision_subordinate n σ U ho hc
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨q,hq⟩ := CoefficientFiniteRealization.finiteSingularChainRealize_factors R U n _ (hN k hk)
  refine ⟨q, hq.trans ?_⟩
  rw [← singularGenerator_iteratedSubdivision_realize]
  congr 2

theorem chain_factorization (n : ℕ)
    (c : (CoefficientH0.SingularChains R (TopCat.of X)).X n)
    (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) :
    ∃ N, ∃ q : (CoefficientSmallPath.coverSmallChains R U).X n,
      (CoefficientSmallPath.coverSmallInclusion R U).f n q =
        singularSubdivisionIterate R n N c := by
  classical
  let a := CoefficientChainSupport.coordinates R n c
  let P := fun N s => ∀ k, N ≤ k → ∃ q : ModuleCat.of R R ⟶ (CoefficientSmallPath.coverSmallChains R U).X n,
    q ≫ (CoefficientSmallPath.coverSmallInclusion R U).f n =
      CoefficientH0.singularGenerator R _ n s ≫ singularSubdivisionIterate R n k
  obtain ⟨N,hN⟩ := ConstructionTargets.SingularSubdivision.Finsupp.exists_uniform_depth a P
    (fun h hP k hk => hP k (h.trans hk)) (fun s _ => generator_eventual R U n s ho hc)
  have lifts : ∀ s ∈ a.support, ∃ q : (CoefficientSmallPath.coverSmallChains R U).X n,
      (CoefficientSmallPath.coverSmallInclusion R U).f n q =
        singularSubdivisionIterate R n N (CoefficientH0.singularGenerator R _ n s (a s)) := by
    intro s hs
    obtain ⟨q,hq⟩ := hN s hs N le_rfl
    exact ⟨q (a s), congrArg (fun f => f (a s)) hq⟩
  choose q hq using lifts
  refine ⟨N, ∑ s ∈ a.support.attach, q s.val s.property, ?_⟩
  simp only [map_sum]
  simp_rw [hq]
  rw [← map_sum]
  congr 1
  exact (Finset.sum_attach a.support
    (fun s => CoefficientH0.singularGenerator R (TopCat.of X) n s (a s))).trans
      (CoefficientChainSupport.finite_expansion R n c)

theorem eventual_factorization (n : ℕ)
    (c : (CoefficientH0.SingularChains R (TopCat.of X)).X n)
    (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) :
    ∃ N, ∀ k, N ≤ k → ∃ q : (CoefficientSmallPath.coverSmallChains R U).X n,
      (CoefficientSmallPath.coverSmallInclusion R U).f n q =
        singularSubdivisionIterate R n k c := by
  obtain ⟨N,q,hq⟩ := chain_factorization R U n c ho hc
  refine ⟨N, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨q,hq⟩
  | succ k hk ih =>
    obtain ⟨q,hq⟩ := ih
    refine ⟨(CoefficientSmallPreservation.subdivision R U).f n q, ?_⟩
    have h := congrArg (fun f => f q) (CoefficientSmallPreservation.subdivision_inc R U n)
    change (CoefficientSmallPath.coverSmallInclusion R U).f n
      ((CoefficientSmallPreservation.subdivision R U).f n q) =
      CoefficientBarycentricNaturality.degree R n ((CoefficientSmallPath.coverSmallInclusion R U).f n q) at h
    rw [h, hq]
    rfl

/-- All spaces, coefficient rings and cover index types are Type 0. -/
def subdivisionIterate (k : ℕ) :
    CoefficientH0.SingularChains R (TopCat.of X) ⟶ CoefficientH0.SingularChains R (TopCat.of X) :=
  Nat.rec (𝟙 _) (fun _ r => r ≫ CoefficientSingularSubdivision.singularSubdivision R) k

theorem subdivisionIterate_f (k n : ℕ) :
    (subdivisionIterate R (X := X) k).f n = singularSubdivisionIterate R n k := by
  induction k with
  | zero => rfl
  | succ k ih => change (subdivisionIterate R k).f n ≫ _ = _; rw [ih]; rfl

theorem actual_chain_eventual (n : ℕ)
    (c : (CoefficientH0.SingularChains R (TopCat.of X)).X n)
    (ho : ∀ a, IsOpen (U a)) (hc : Set.univ ⊆ ⋃ a, U a) :
    ∃ N, ∀ k, N ≤ k → ∃ q : (CoefficientSmallPath.coverSmallChains R U).X n,
      (CoefficientSmallPath.coverSmallInclusion R U).f n q = (subdivisionIterate R k).f n c := by
  simp_rw [subdivisionIterate_f]
  exact eventual_factorization R U n c ho hc

theorem integral_interval (n : ℕ)
    (c : (CoefficientH0.SingularChains ℤ (TopCat.of ℝ)).X n) :
    ∃ N, ∀ k, N ≤ k → ∃ q : (CoefficientSmallPath.coverSmallChains ℤ CoefficientSmallPath.intervalCover).X n,
      (CoefficientSmallPath.coverSmallInclusion ℤ CoefficientSmallPath.intervalCover).f n q =
        (subdivisionIterate ℤ k).f n c :=
  actual_chain_eventual ℤ _ n c CoefficientSmallPath.intervalCover_open CoefficientSmallPath.intervalCover_covers

theorem rational_interval (n : ℕ)
    (c : (CoefficientH0.SingularChains ℚ (TopCat.of ℝ)).X n) :
    ∃ N, ∀ k, N ≤ k → ∃ q : (CoefficientSmallPath.coverSmallChains ℚ CoefficientSmallPath.intervalCover).X n,
      (CoefficientSmallPath.coverSmallInclusion ℚ CoefficientSmallPath.intervalCover).f n q =
        (subdivisionIterate ℚ k).f n c :=
  actual_chain_eventual ℚ _ n c CoefficientSmallPath.intervalCover_open CoefficientSmallPath.intervalCover_covers

#print axioms singularGenerator_iteratedSubdivision_realize
#print axioms generator_eventual
#print axioms chain_factorization
#print axioms eventual_factorization
#print axioms subdivisionIterate
#print axioms actual_chain_eventual
#print axioms integral_interval
#print axioms rational_interval
end ConstructionTargets.CoefficientEventualSmallness
