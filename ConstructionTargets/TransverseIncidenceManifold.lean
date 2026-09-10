import ConstructionTargets.ChartedSpaceModelDerivativeTransport
import ConstructionTargets.ManifoldRegularFiberGlobalAtlas

open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.TransverseIncidenceManifold
variable {E G V M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [CompleteSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ,G) ∞ N]

abbrev Model := EuclideanSpace ℝ (Fin (Module.finrank ℝ E + Module.finrank ℝ G - Module.finrank ℝ V))

def incidenceHomeomorph (f : M → V) (g : N → V) :
    {p : M × N // f p.1 = g p.2} ≃ₜ
      {p : M × N // TransverseDifferenceRegularity.difference f g p = 0} where
  toFun p := ⟨p.val, sub_eq_zero.mpr p.property⟩
  invFun p := ⟨p.val, sub_eq_zero.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp] theorem incidenceHomeomorph_val (f : M → V) (g : N → V)
    (p : {p : M × N // f p.1 = g p.2}) :
    (incidenceHomeomorph f g p).val = p.val := rfl

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp] theorem incidenceHomeomorph_symm_val (f : M → V) (g : N → V)
    (p : {p : M × N // TransverseDifferenceRegularity.difference f g p = 0}) :
    ((incidenceHomeomorph f g).symm p).val = p.val := rfl

theorem exists_atlas (f : M → V) (g : N → V)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,V) ∞ g)
    (ht : ∀ x y, f x = g y →
      LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x).toLinearMap ⊔
      LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,V) g y).toLinearMap = ⊤) :
    ∃ charts : ChartedSpace (Model (E := E) (G := G) (V := V))
        {p : M × N // f p.1 = g p.2},
      letI := charts
      IsManifold 𝓘(ℝ,Model (E := E) (G := G) (V := V)) ∞ {p : M × N // f p.1 = g p.2} ∧
      ContMDiff 𝓘(ℝ,Model (E := E) (G := G) (V := V)) (𝓘(ℝ,E).prod 𝓘(ℝ,G)) ∞
        (Subtype.val : {p : M × N // f p.1 = g p.2} → M × N) := by
  letI := ChartedSpaceModelTransport.productChartedSpace (E := E) (G := G) (M := M) (N := N)
  letI := ChartedSpaceModelSmoothTransport.product_isManifold (A := E) (B := G) (X := M) (Y := N)
  let hsm := ChartedSpaceModelDerivativeTransport.difference_smooth f g hf hg
  let hreg := ChartedSpaceModelDerivativeTransport.difference_regular f g hf hg ht
  let q := TransverseDifferenceRegularity.difference f g
  have hp : ∃ charts : ChartedSpace (ManifoldRegularFiberCharts.Model (E := WithLp 2 (E × G)) (F := V)) {p : M × N // q p = 0},
      letI := charts
      IsManifold 𝓘(ℝ,ManifoldRegularFiberCharts.Model (E := WithLp 2 (E × G)) (F := V)) ∞ {p : M × N // q p = 0} ∧
      ContMDiff 𝓘(ℝ,ManifoldRegularFiberCharts.Model (E := WithLp 2 (E × G)) (F := V)) (𝓘(ℝ,E).prod 𝓘(ℝ,G)) ∞
        (Subtype.val : {p : M × N // q p = 0} → M × N) := by
    refine ⟨ManifoldRegularFiberGlobalAtlas.chartedSpace q 0 hsm hreg, ?_⟩
    letI := ManifoldRegularFiberGlobalAtlas.chartedSpace q 0 hsm hreg
    refine ⟨ManifoldRegularFiberGlobalAtlas.isManifold q 0 hsm hreg, ?_⟩
    exact (ChartedSpaceModelDerivativeTransport.product_identity_smooth (A := E) (B := G) (X := M) (Y := N)).2.comp
      (ManifoldRegularFiberGlobalAtlas.smooth_inclusion q 0 hsm hreg)
  have heq : (fun p : M × N => q p = 0) = (fun p : M × N => f p.1 = g p.2) := by
    funext p
    exact propext sub_eq_zero
  change (∃ charts : ChartedSpace (ManifoldRegularFiberCharts.Model (E := WithLp 2 (E × G)) (F := V)) (Subtype (fun p => q p = 0)), _) at hp
  rw [heq] at hp
  let P (n : ℕ) : Prop := ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) {p : M × N // f p.1 = g p.2},
    letI := charts
    IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ {p : M × N // f p.1 = g p.2} ∧
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) (𝓘(ℝ,E).prod 𝓘(ℝ,G)) ∞
      (Subtype.val : {p : M × N // f p.1 = g p.2} → M × N)
  change P (Module.finrank ℝ (WithLp 2 (E × G)) - Module.finrank ℝ V) at hp
  rw [ChartedSpaceModelTransport.product_dimension (E := E) (G := G)] at hp
  exact hp

#print axioms incidenceHomeomorph
#print axioms incidenceHomeomorph_val
#print axioms incidenceHomeomorph_symm_val
#print axioms exists_atlas
end ConstructionTargets.TransverseIncidenceManifold
