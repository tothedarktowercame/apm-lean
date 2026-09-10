import ConstructionTargets.TransverseIncidenceTangent
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.TransverseIncidenceGeometry

section Transport
variable {X : Type*} [TopologicalSpace X] {m n : ℕ}
@[reducible] def castAtlas (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) X := h ▸ c

def castChart (h : m = n) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m))) :
    OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)) := h ▸ e

theorem cast_chartAt (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) (x : X) :
    letI := c
    letI := castAtlas h c
    chartAt (EuclideanSpace ℝ (Fin n)) x = castChart h (chartAt (EuclideanSpace ℝ (Fin m)) x) := by
  cases h
  rfl

theorem cast_atlas (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) :
    letI := c
    letI := castAtlas h c
    atlas (EuclideanSpace ℝ (Fin n)) X = castChart h '' atlas (EuclideanSpace ℝ (Fin m)) X := by
  cases h
  change atlas (EuclideanSpace ℝ (Fin m)) X = id '' atlas (EuclideanSpace ℝ (Fin m)) X
  simp

theorem cast_property (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X)
    (P : ∀ k : ℕ, ChartedSpace (EuclideanSpace ℝ (Fin k)) X → Prop) (hc : P m c) :
    P n (castAtlas h c) := by cases h; exact hc
end Transport

open TransverseIncidenceChosenAtlas
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
    LinearMap.range (R := ℝ) (mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x).toLinearMap ⊔
    LinearMap.range (R := ℝ) (mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g y).toLinearMap = ⊤)



abbrev dimension := Module.finrank ℝ A + Module.finrank ℝ B - Module.finrank ℝ V
abbrev Space := EuclideanSpace ℝ (Fin (dimension (A := A) (B := B) (V := V)))

omit [CompleteSpace A] [CompleteSpace B] [FiniteDimensional ℝ V] in
theorem index_eq : Module.finrank ℝ (WithLp 2 (A × B)) - Module.finrank ℝ V =
    dimension (A := A) (B := B) (V := V) := by
  rw [ChartedSpaceModelTransport.product_dimension]

@[reducible] def chartedSpace : ChartedSpace (Space (A := A) (B := B) (V := V)) (Incidence f g) :=
  castAtlas (index_eq (A := A) (B := B) (V := V)) (chosenAtlas f g hf hg ht)

theorem chartAt_eq (x : Incidence f g) :
    letI := chosenAtlas f g hf hg ht
    letI := chartedSpace f g hf hg ht
    chartAt (Space (A := A) (B := B) (V := V)) x =
      castChart (index_eq (A := A) (B := B) (V := V))
        (chartAt (Model (A := A) (B := B) (V := V)) x) :=
  cast_chartAt _ _ _

theorem atlas_eq :
    letI := chosenAtlas f g hf hg ht
    letI := chartedSpace f g hf hg ht
    atlas (Space (A := A) (B := B) (V := V)) (Incidence f g) =
      castChart (index_eq (A := A) (B := B) (V := V)) ''
        atlas (Model (A := A) (B := B) (V := V)) (Incidence f g) :=
  cast_atlas _ _

theorem chart_mem (x : Incidence f g) :
    letI := chartedSpace f g hf hg ht
    chartAt (Space (A := A) (B := B) (V := V)) x ∈
      atlas (Space (A := A) (B := B) (V := V)) (Incidence f g) := by
  letI := chartedSpace f g hf hg ht
  exact chart_mem_atlas _ x

theorem chart_center (x : Incidence f g) :
    letI := chartedSpace f g hf hg ht
    x ∈ (chartAt (Space (A := A) (B := B) (V := V)) x).source := by
  letI := chartedSpace f g hf hg ht
  exact mem_chart_source _ x

def derivativeAt (n : ℕ) (c : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Incidence f g))
    (x : Incidence f g) : EuclideanSpace ℝ (Fin n) →L[ℝ] (A × B) :=
  letI := c
  mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
    (Subtype.val : Incidence f g → M × N) x

def Geometry (n : ℕ) (c : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Incidence f g)) : Prop :=
  letI := c
  IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ (Incidence f g) ∧
  ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) (𝓘(ℝ,A).prod 𝓘(ℝ,B)) ∞
    (Subtype.val : Incidence f g → M × N) ∧
  (∀ x, Function.Injective (derivativeAt (A := A) (B := B) f g n c x)) ∧
  (∀ x, LinearMap.range (derivativeAt (A := A) (B := B) f g n c x).toLinearMap =
    (mfderiv (𝓘(ℝ,A).prod 𝓘(ℝ,B)) 𝓘(ℝ,V) (TransverseDifferenceRegularity.difference f g) x.val).ker) ∧
  (∀ x (v : A × B), v ∈ LinearMap.range (derivativeAt (A := A) (B := B) f g n c x).toLinearMap ↔
    mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x.val.1 v.1 = mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g x.val.2 v.2)

theorem geometry : Geometry (A := A) (B := B) f g (dimension (A := A) (B := B) (V := V)) (chartedSpace f g hf hg ht) := by
  apply cast_property (index_eq (A := A) (B := B) (V := V)) (chosenAtlas f g hf hg ht) (Geometry (A := A) (B := B) f g)
  exact ⟨chosen_isManifold f g hf hg ht, chosen_smooth_inclusion f g hf hg ht,
    TransverseIncidenceTangent.inclusion_injective f g hf hg ht,
    TransverseIncidenceTangent.inclusion_range f g hf hg ht,
    TransverseIncidenceTangent.mem_inclusion_range f g hf hg ht⟩

theorem isManifold :
    letI := chartedSpace f g hf hg ht
    IsManifold 𝓘(ℝ,Space (A := A) (B := B) (V := V)) ∞ (Incidence f g) :=
  (geometry f g hf hg ht).1

theorem smooth_inclusion :
    letI := chartedSpace f g hf hg ht
    ContMDiff 𝓘(ℝ,Space (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B)) ∞
      (Subtype.val : Incidence f g → M × N) :=
  (geometry f g hf hg ht).2.1

theorem inclusion_injective (x : Incidence f g) :
    letI := chartedSpace f g hf hg ht
    Function.Injective (mfderiv 𝓘(ℝ,Space (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (Subtype.val : Incidence f g → M × N) x) :=
  (geometry f g hf hg ht).2.2.1 x

theorem inclusion_range (x : Incidence f g) :
    LinearMap.range (derivativeAt (A := A) (B := B) f g _ (chartedSpace f g hf hg ht) x).toLinearMap =
      (mfderiv (𝓘(ℝ,A).prod 𝓘(ℝ,B)) 𝓘(ℝ,V) (TransverseDifferenceRegularity.difference f g) x.val).ker :=
  (geometry f g hf hg ht).2.2.2.1 x

theorem mem_inclusion_range (x : Incidence f g) (v : A × B) :
    v ∈ LinearMap.range (derivativeAt (A := A) (B := B) f g _ (chartedSpace f g hf hg ht) x).toLinearMap ↔
      mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x.val.1 v.1 = mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g x.val.2 v.2 :=
  (geometry f g hf hg ht).2.2.2.2 x v

theorem actual_range (x : Incidence f g) :
    letI := chartedSpace f g hf hg ht
    Set.range (mfderiv 𝓘(ℝ,Space (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (Subtype.val : Incidence f g → M × N) x) =
      {v : A × B | mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x.val.1 v.1 =
        mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g x.val.2 v.2} := by
  ext v
  exact mem_inclusion_range f g hf hg ht x v

#print axioms chartedSpace
#print axioms chartAt_eq
#print axioms atlas_eq
#print axioms chart_mem
#print axioms chart_center
#print axioms geometry
#print axioms isManifold
#print axioms smooth_inclusion
#print axioms inclusion_injective
#print axioms inclusion_range
#print axioms mem_inclusion_range
#print axioms actual_range
end ConstructionTargets.TransverseIncidenceGeometry
