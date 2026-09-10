import ConstructionTargets.CoefficientSmallPath
noncomputable section
namespace ConstructionTargets.CoefficientFiniteRealization
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
def finiteSingularChainRealize {X : Type} [TopologicalSpace X] (n : ℕ)
    (c : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ ℤ) :
    ModuleCat.of R R ⟶ (CoefficientH0.SingularChains R (TopCat.of X)).X n :=
  c.sum fun σ z => z • CoefficientH0.singularGenerator R (TopCat.of X) n
    (singularSimplexOfContinuousMap (TopCat.of X) n σ)

@[simp] theorem finiteSingularChainRealize_single
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (z : ℤ) :
    finiteSingularChainRealize R n (Finsupp.single σ z) =
      z • CoefficientH0.singularGenerator R (TopCat.of X) n
        (singularSimplexOfContinuousMap (TopCat.of X) n σ) := by
  classical
  simp [finiteSingularChainRealize]

@[simp] theorem finiteSingularChainRealize_add
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (c d : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ ℤ) :
    finiteSingularChainRealize R n (c + d) =
      finiteSingularChainRealize R n c + finiteSingularChainRealize R n d := by
  classical
  unfold finiteSingularChainRealize
  apply Finsupp.sum_add_index
  · intro a _
    simp
  · intro a _ b₁ b₂
    simp [add_smul]

theorem finiteSingularChainRealize_factors
    {X α : Type} [TopologicalSpace X] (U : α → Set X) (n : ℕ)
    (c : C(stdSimplex ℝ (Fin (n + 1)), X) →₀ ℤ)
    (hc : ∀ σ ∈ c.support, ∃ a, Set.range σ ⊆ U a) :
    ∃ q : ModuleCat.of R R ⟶ (CoefficientSmallPath.coverSmallChains R U).X n,
      q ≫ (CoefficientSmallPath.coverSmallInclusion R U).f n = finiteSingularChainRealize R n c := by
  classical
  induction c using Finsupp.induction with
  | zero => exact ⟨0, by simp [finiteSingularChainRealize]⟩
  | single_add σ z c hσc hz ih =>
      obtain ⟨a, ha⟩ := hc σ (by
        have hcσ : c σ = 0 := by
          simpa only [Finsupp.mem_support_iff, not_not] using hσc
        simp [Finsupp.mem_support_iff, hcσ, hz])
      have hc' : ∀ τ ∈ c.support, ∃ a, Set.range τ ⊆ U a := by
        intro τ hτ
        apply hc τ
        apply Finsupp.mem_support_iff.mpr
        have hτσ : τ ≠ σ := fun h => hσc (h ▸ hτ)
        have hct : c τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
        simp [hτσ, hct]
      obtain ⟨q, hq⟩ := ih hc'
      refine ⟨z • CoefficientSmallPath.coverSmallGenerator R U σ a ha + q, ?_⟩
      rw [Preadditive.add_comp, Preadditive.zsmul_comp,
        CoefficientSmallPath.coverSmallGenerator_comp_ι R, hq]
      rw [← finiteSingularChainRealize_single R,
        ← finiteSingularChainRealize_add R]



/-- R, X and the family index type are Type 0. Integer weights here encode
signed simplex formulas; the realized arrows are R-linear maps out of R.
No integral homology theorem or change-of-coefficients theorem is used. -/
def leftEdge : C(stdSimplex ℝ (Fin 2), ℝ) :=
  ⟨fun x => x.val 1 / 2, ((continuous_apply 1).comp continuous_subtype_val).div_const 2⟩
def rightEdge : C(stdSimplex ℝ (Fin 2), ℝ) :=
  ⟨fun x => (x.val 1 + 1) / 2, (((continuous_apply 1).comp continuous_subtype_val).add continuous_const).div_const 2⟩

theorem leftEdge_small : Set.range leftEdge ⊆ CoefficientSmallPath.intervalCover false := by
  rintro _ ⟨x, rfl⟩
  change x.val 1 / 2 < 1
  have h := stdSimplex.le_one x 1
  change x.val 1 ≤ 1 at h
  linarith

theorem rightEdge_small : Set.range rightEdge ⊆ CoefficientSmallPath.intervalCover true := by
  rintro _ ⟨x, rfl⟩
  change 0 < (x.val 1 + 1) / 2
  have h := x.property.1 1
  linarith

theorem interval_factorization :
    ∃ q : ModuleCat.of R R ⟶
      (CoefficientSmallPath.coverSmallChains R CoefficientSmallPath.intervalCover).X 1,
      q ≫ (CoefficientSmallPath.coverSmallInclusion R CoefficientSmallPath.intervalCover).f 1 =
        finiteSingularChainRealize R 1
          (Finsupp.single leftEdge (1 : ℤ) + Finsupp.single rightEdge (-1 : ℤ)) := by
  classical
  apply finiteSingularChainRealize_factors
  intro σ hσ
  have h := Finset.mem_of_subset Finsupp.support_add hσ
  simp only [Finsupp.support_single_ne_zero _ (by decide : (1 : ℤ) ≠ 0),
    Finsupp.support_single_ne_zero _ (by decide : (-1 : ℤ) ≠ 0),
    Finset.mem_union, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact ⟨false, leftEdge_small⟩
  · exact ⟨true, rightEdge_small⟩

theorem integral_interval :
    ∃ q : ModuleCat.of ℤ ℤ ⟶
      (CoefficientSmallPath.coverSmallChains ℤ CoefficientSmallPath.intervalCover).X 1,
      q ≫ (CoefficientSmallPath.coverSmallInclusion ℤ CoefficientSmallPath.intervalCover).f 1 =
        finiteSingularChainRealize ℤ 1
          (Finsupp.single leftEdge (1 : ℤ) + Finsupp.single rightEdge (-1 : ℤ)) := interval_factorization ℤ

theorem rational_interval :
    ∃ q : ModuleCat.of ℚ ℚ ⟶
      (CoefficientSmallPath.coverSmallChains ℚ CoefficientSmallPath.intervalCover).X 1,
      q ≫ (CoefficientSmallPath.coverSmallInclusion ℚ CoefficientSmallPath.intervalCover).f 1 =
        finiteSingularChainRealize ℚ 1
          (Finsupp.single leftEdge (1 : ℤ) + Finsupp.single rightEdge (-1 : ℤ)) := interval_factorization ℚ

#print axioms finiteSingularChainRealize_single
#print axioms finiteSingularChainRealize_add
#print axioms finiteSingularChainRealize_factors
#print axioms integral_interval
#print axioms rational_interval
end ConstructionTargets.CoefficientFiniteRealization
