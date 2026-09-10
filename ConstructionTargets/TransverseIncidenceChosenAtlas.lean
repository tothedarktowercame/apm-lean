import ConstructionTargets.ChartedSpaceModelDerivativeTransport
import ConstructionTargets.ManifoldRegularFiberGlobalAtlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.PredicateSubtypeAtlasTransport
variable {X H : Type*} [TopologicalSpace X] [TopologicalSpace H]
  {P Q : X → Prop}

def homeomorph (h : P = Q) : Subtype P ≃ₜ Subtype Q := by
  cases h
  exact Homeomorph.refl _

@[reducible] def chartedSpace (h : P = Q) (c : ChartedSpace H (Subtype P)) :
    ChartedSpace H (Subtype Q) := h ▸ c

def chart (h : P = Q) (e : OpenPartialHomeomorph (Subtype P) H) :
    OpenPartialHomeomorph (Subtype Q) H := h ▸ e

theorem chartAt_eq (h : P = Q) (c : ChartedSpace H (Subtype P)) (x : Subtype Q) :
    letI := c
    letI := chartedSpace h c
    chartAt H x = chart h (chartAt H ((homeomorph h).symm x)) := by
  cases h
  rfl

theorem atlas_eq (h : P = Q) (c : ChartedSpace H (Subtype P)) :
    letI := c
    letI := chartedSpace h c
    atlas H (Subtype Q) = chart h '' atlas H (Subtype P) := by
  cases h
  change atlas H (Subtype P) = id '' atlas H (Subtype P)
  simp

theorem chart_apply (h : P = Q) (e : OpenPartialHomeomorph (Subtype P) H) (x : Subtype Q) :
    chart h e x = e ((homeomorph h).symm x) := by cases h; rfl

theorem chart_symm_apply (h : P = Q) (e : OpenPartialHomeomorph (Subtype P) H) (z : H) :
    (chart h e).symm z = homeomorph h (e.symm z) := by cases h; rfl

theorem homeomorph_val (h : P = Q) (x : Subtype P) :
    (homeomorph h x).val = x.val := by cases h; rfl

section Smooth
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [ChartedSpace F X]
  (h : P = Q) (c : ChartedSpace E (Subtype P))

theorem isManifold (hc : @IsManifold ℝ _ E _ _ E _ (𝓘(ℝ,E)) ∞ (Subtype P) _ c) :
    letI := chartedSpace h c
    IsManifold 𝓘(ℝ,E) ∞ (Subtype Q) := by
  cases h
  exact hc

theorem smooth_inclusion
    (hc : letI := c; ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (Subtype.val : Subtype P → X)) :
    letI := chartedSpace h c
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (Subtype.val : Subtype Q → X) := by
  cases h
  exact hc

theorem inclusion_derivative (x : Subtype Q) :
    letI := c
    letI := chartedSpace h c
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (Subtype.val : Subtype Q → X) x =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (Subtype.val : Subtype P → X) ((homeomorph h).symm x) := by
  cases h
  rfl
end Smooth
#print axioms chartedSpace
#print axioms chartAt_eq
#print axioms atlas_eq
#print axioms chart_apply
#print axioms chart_symm_apply
#print axioms homeomorph_val
#print axioms isManifold
#print axioms smooth_inclusion
#print axioms inclusion_derivative
end ConstructionTargets.PredicateSubtypeAtlasTransport

namespace ConstructionTargets.TransverseIncidenceChosenAtlas
open PredicateSubtypeAtlasTransport
variable {A B V M N : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [CompleteSpace B]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace A M] [IsManifold 𝓘(ℝ,A) ∞ M]
  [TopologicalSpace N] [ChartedSpace B N] [IsManifold 𝓘(ℝ,B) ∞ N]
  (f : M → V) (g : N → V)
  (hf : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,V) ∞ f)
  (hg : ContMDiff 𝓘(ℝ,B) 𝓘(ℝ,V) ∞ g)
  (ht : ∀ x y, f x = g y →
    LinearMap.range (mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x).toLinearMap ⊔
    LinearMap.range (mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g y).toLinearMap = ⊤)

abbrev Zero := {p : M × N // TransverseDifferenceRegularity.difference f g p = 0}
abbrev Incidence := {p : M × N // f p.1 = g p.2}
abbrev Model := ManifoldRegularFiberCharts.Model (E := WithLp 2 (A × B)) (F := V)

def predicate_eq : (fun p : M × N => TransverseDifferenceRegularity.difference f g p = 0) =
    (fun p : M × N => f p.1 = g p.2) := funext (fun _ => propext sub_eq_zero)

@[reducible] def zeroAtlas : ChartedSpace (Model (A := A) (B := B) (V := V)) (Zero f g) :=
  letI := ChartedSpaceModelTransport.productChartedSpace (E := A) (G := B) (M := M) (N := N)
  letI := ChartedSpaceModelSmoothTransport.product_isManifold (A := A) (B := B) (X := M) (Y := N)
  ManifoldRegularFiberGlobalAtlas.chartedSpace (TransverseDifferenceRegularity.difference f g) 0
    (ChartedSpaceModelDerivativeTransport.difference_smooth f g hf hg)
    (ChartedSpaceModelDerivativeTransport.difference_regular f g hf hg ht)

@[reducible] def chosenAtlas : ChartedSpace (Model (A := A) (B := B) (V := V)) (Incidence f g) :=
  chartedSpace (predicate_eq f g) (zeroAtlas f g hf hg ht)

theorem chosen_chartAt (x : Incidence f g) :
    letI := zeroAtlas f g hf hg ht
    letI := chosenAtlas f g hf hg ht
    chartAt (Model (A := A) (B := B) (V := V)) x =
      chart (predicate_eq f g) (chartAt (Model (A := A) (B := B) (V := V))
        ((homeomorph (predicate_eq f g)).symm x)) :=
  chartAt_eq _ _ _

theorem chosen_atlas :
    letI := zeroAtlas f g hf hg ht
    letI := chosenAtlas f g hf hg ht
    atlas (Model (A := A) (B := B) (V := V)) (Incidence f g) =
      chart (predicate_eq f g) '' atlas (Model (A := A) (B := B) (V := V)) (Zero f g) :=
  atlas_eq _ _

theorem chosen_isManifold :
    letI := chosenAtlas f g hf hg ht
    IsManifold 𝓘(ℝ,Model (A := A) (B := B) (V := V)) ∞ (Incidence f g) := by
  apply isManifold (predicate_eq f g) (zeroAtlas f g hf hg ht)
  letI := ChartedSpaceModelTransport.productChartedSpace (E := A) (G := B) (M := M) (N := N)
  letI := ChartedSpaceModelSmoothTransport.product_isManifold (A := A) (B := B) (X := M) (Y := N)
  exact ManifoldRegularFiberGlobalAtlas.isManifold _ _ _ _

theorem chosen_smooth_inclusion :
    letI := chosenAtlas f g hf hg ht
    ContMDiff 𝓘(ℝ,Model (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B)) ∞
      (Subtype.val : Incidence f g → M × N) := by
  letI : ChartedSpace (A × B) (M × N) := prodChartedSpace A M B N
  have hz : letI := zeroAtlas f g hf hg ht
      ContMDiff 𝓘(ℝ,Model (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B)) ∞
        (Subtype.val : Zero f g → M × N) := by
    letI := ChartedSpaceModelTransport.productChartedSpace (E := A) (G := B) (M := M) (N := N)
    letI := ChartedSpaceModelSmoothTransport.product_isManifold (A := A) (B := B) (X := M) (Y := N)
    letI := zeroAtlas f g hf hg ht
    exact (ChartedSpaceModelDerivativeTransport.product_identity_smooth (A := A) (B := B) (X := M) (Y := N)).2.comp
      (ManifoldRegularFiberGlobalAtlas.smooth_inclusion _ _ _ _)
  have hz' : letI := zeroAtlas f g hf hg ht
      ContMDiff 𝓘(ℝ,Model (A := A) (B := B) (V := V)) 𝓘(ℝ,A × B) ∞
        (Subtype.val : Zero f g → M × N) := by
    simpa only [modelWithCornersSelf_prod] using hz
  simpa only [modelWithCornersSelf_prod] using
    smooth_inclusion (F := A × B) (predicate_eq f g) (zeroAtlas f g hf hg ht) hz'

theorem chosen_inclusion_derivative (x : Incidence f g) :
    letI := zeroAtlas f g hf hg ht
    letI := chosenAtlas f g hf hg ht
    mfderiv 𝓘(ℝ,Model (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (Subtype.val : Incidence f g → M × N) x =
    mfderiv 𝓘(ℝ,Model (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (Subtype.val : Zero f g → M × N) ((homeomorph (predicate_eq f g)).symm x) := by
  letI : ChartedSpace (A × B) (M × N) := prodChartedSpace A M B N
  simpa only [modelWithCornersSelf_prod] using
    inclusion_derivative (F := A × B) (predicate_eq f g) (zeroAtlas f g hf hg ht) x

omit [CompleteSpace A] [CompleteSpace B] [FiniteDimensional ℝ V] in
theorem model_dimension : Module.finrank ℝ (Model (A := A) (B := B) (V := V)) =
    Module.finrank ℝ A + Module.finrank ℝ B - Module.finrank ℝ V := by
  simp [Model, ManifoldRegularFiberCharts.Model, RegularFiberFixedModelOverlaps.Model,
    RegularFiberFixedModel.Model, ChartedSpaceModelTransport.product_dimension]

#print axioms predicate_eq
#print axioms zeroAtlas
#print axioms chosenAtlas
#print axioms chosen_chartAt
#print axioms chosen_atlas
#print axioms chosen_isManifold
#print axioms chosen_smooth_inclusion
#print axioms chosen_inclusion_derivative
#print axioms model_dimension
end ConstructionTargets.TransverseIncidenceChosenAtlas
