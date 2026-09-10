import ConstructionTargets.CompactSurfaceTriangleCover
import ConstructionTargets.ScaledTriangleNeighborhood
noncomputable section
open Set Topology
namespace ConstructionTargets.NestedCoordinateTriangles
open StandardTriangleEmbedding ScaledTriangleNeighborhood

def shrink (z : Simplex) : Simplex := ⟨fun i => (z.1 i + 1/3)/2, by
  constructor
  · intro i; have h := z.2.1 i; positivity
  · have h := z.2.2
    rw [Fin.sum_univ_three] at h ⊢
    linarith⟩

theorem shrink_positive (z : Simplex) : shrink z ∈ interiorParameters := by
  intro i
  have h := z.2.1 i
  change 0 < (z.1 i + 1/3)/2
  linarith

theorem scaled_shrink (a : ℝ × ℝ) (r : ℝ) (z : Simplex) :
    scaled a r (shrink z) = scaled a (r/2) z := by
  apply Prod.ext <;> dsimp [scaled, parametrization, shrink] <;> ring

theorem strict_nesting (a : ℝ × ℝ) (r : ℝ) :
    Set.range (scaled a (r/2)) ⊆ scaled a r '' interiorParameters := by
  rintro _ ⟨z,rfl⟩
  exact ⟨shrink z, shrink_positive z, scaled_shrink a r z⟩

theorem geometry (a : ℝ × ℝ) (r : ℝ) (hr : 0 < r) :
    IsClosedEmbedding (scaled a r) ∧ IsCompact (Set.range (scaled a r)) ∧
    IsOpen (scaled a r '' interiorParameters) ∧ a ∈ scaled a r '' interiorParameters := by
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    (Homeomorph.smulOfNeZero r (ne_of_gt hr)).trans (Homeomorph.addLeft a)
  have he : scaled a r = H ∘ parametrization := rfl
  have hc : Continuous (scaled a r) := by rw [he]; exact H.continuous.comp continuous_parametrization
  refine ⟨hc.isClosedEmbedding (H.injective.comp injective_parametrization), isCompact_range hc, ?_, ?_⟩
  · rw [he, Set.image_comp, interior_image]
    exact H.isOpenMap _ open_interior
  · obtain ⟨z,hz,hzero⟩ := center_mem
    exact ⟨z,hz,by simp [scaled,hzero]⟩

theorem exists_nested (U : Set (ℝ × ℝ)) (hU : IsOpen U) (a : ℝ × ℝ) (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ 0 < r/2 ∧
      Set.range (scaled a r) ⊆ U ∧
      Set.range (scaled a (r/2)) ⊆ scaled a r '' interiorParameters ∧
      IsClosedEmbedding (scaled a r) ∧ IsClosedEmbedding (scaled a (r/2)) ∧
      IsCompact (Set.range (scaled a r)) ∧ IsCompact (Set.range (scaled a (r/2))) ∧
      IsOpen (scaled a r '' interiorParameters) ∧ IsOpen (scaled a (r/2) '' interiorParameters) ∧
      a ∈ scaled a (r/2) '' interiorParameters := by
  obtain ⟨r,hr,he,hc,hsub,ho,_⟩ := exists_triangle U hU a ha
  obtain ⟨hei,hci,hoi,hcenter⟩ := geometry a (r/2) (half_pos hr)
  exact ⟨r,hr,half_pos hr,hsub,strict_nesting a r,he,hei,hc,hci,ho,hoi,hcenter⟩
#print axioms shrink
#print axioms shrink_positive
#print axioms scaled_shrink
#print axioms strict_nesting
#print axioms geometry
#print axioms exists_nested
end ConstructionTargets.NestedCoordinateTriangles

namespace ConstructionTargets.SurfaceNestedTriangleCover
open StandardTriangleEmbedding ScaledTriangleNeighborhood NestedCoordinateTriangles
variable {M : Type*} [TopologicalSpace M] [T2Space M]
theorem chart_geometry (e : OpenPartialHomeomorph M (ℝ × ℝ)) (x : M)
    (hx : x ∈ e.source) (r : ℝ) (hr : 0 < r)
    (hsub : Set.range (scaled (e x) r) ⊆ e.target) :
    IsClosedEmbedding (e.symm ∘ scaled (e x) r) ∧
    IsCompact (Set.range (e.symm ∘ scaled (e x) r)) ∧
    Set.range (e.symm ∘ scaled (e x) r) ⊆ e.source ∧
    IsOpen ((e.symm ∘ scaled (e x) r) '' interiorParameters) ∧
    x ∈ (e.symm ∘ scaled (e x) r) '' interiorParameters := by
  obtain ⟨hemb,_,hopen,hcenter⟩ := geometry (e x) r hr
  have hm : MapsTo (scaled (e x) r) Set.univ e.target := fun z _ => hsub ⟨z,rfl⟩
  have hc : Continuous (e.symm ∘ scaled (e x) r) :=
    continuousOn_univ.mp (e.continuousOn_symm.comp hemb.continuous.continuousOn hm)
  have hi : Function.Injective (e.symm ∘ scaled (e x) r) := by
    intro a b h
    exact hemb.injective (e.symm.injOn (hm (Set.mem_univ a)) (hm (Set.mem_univ b)) h)
  refine ⟨hc.isClosedEmbedding hi,isCompact_range hc,?_,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    exact e.map_target (hm (Set.mem_univ z))
  · rw [Set.image_comp]
    exact e.symm.isOpen_image_of_subset_source hopen (fun y hy => hsub (Set.image_subset_range _ _ hy))
  · obtain ⟨z,hz,heq⟩ := hcenter
    refine ⟨z,hz,?_⟩
    change e.symm (scaled (e x) r z) = x
    rw [heq,e.left_inv hx]

def triangle (e : OpenPartialHomeomorph M (ℝ × ℝ)) (x : M) (r : ℝ) :=
  e.symm ∘ scaled (e x) r

def Good (e : OpenPartialHomeomorph M (ℝ × ℝ)) (x : M) (r : ℝ) : Prop :=
  0 < r ∧ Set.range (scaled (e x) r) ⊆ e.target ∧
  IsClosedEmbedding (triangle e x r) ∧ IsCompact (Set.range (triangle e x r)) ∧
  Set.range (triangle e x r) ⊆ e.source ∧
  IsOpen (triangle e x r '' interiorParameters) ∧ x ∈ triangle e x r '' interiorParameters

theorem local_nested (e : OpenPartialHomeomorph M (ℝ × ℝ)) (x : M) (hx : x ∈ e.source) :
    ∃ r : ℝ, Good e x r ∧ Good e x (r/2) ∧
      Set.range (triangle e x (r/2)) ⊆ triangle e x r '' interiorParameters := by
  obtain ⟨r,hr,_,_,hsub,_,_⟩ := exists_triangle e.target e.open_target (e x) (e.map_source hx)
  have hinner : Set.range (scaled (e x) (r/2)) ⊆ e.target :=
    (strict_nesting (e x) r).trans ((Set.image_subset_range _ _).trans hsub)
  refine ⟨r,⟨hr,hsub,chart_geometry e x hx r hr hsub⟩,
    ⟨half_pos hr,hinner,chart_geometry e x hx (r/2) (half_pos hr) hinner⟩,?_⟩
  rintro _ ⟨z,rfl⟩
  exact ⟨shrink z,shrink_positive z,congrArg e.symm (scaled_shrink (e x) r z)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [CompactSpace M]
open CompactSurfaceTriangleCover

theorem finite_nested (hd : Module.finrank ℝ E = 2) :
    ∃ (s : Finset M) (r : M → ℝ),
      (∀ x ∈ s, Good (planeChart hd x) x (r x) ∧ Good (planeChart hd x) x (r x/2) ∧
        Set.range (triangle (planeChart hd x) x (r x/2)) ⊆
          triangle (planeChart hd x) x (r x) '' interiorParameters ∧
        Set.range ((planeEquiv hd).symm ∘ scaled (planeChart hd x x) (r x)) ⊆ (chartAt E x).target) ∧
      (∀ y : M, ∃ x ∈ s, y ∈ triangle (planeChart hd x) x (r x/2) '' interiorParameters) := by
  classical
  have hx (x : M) : x ∈ (planeChart hd x).source := by
    simp [planeChart]
  choose r hr using fun x : M => local_nested (planeChart hd x) x (hx x)
  let U : M → Set M := fun x => triangle (planeChart hd x) x (r x/2) '' interiorParameters
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (hr x).2.1.2.2.2.2.2.1) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y,(hr y).2.1.2.2.2.2.2.2⟩)
  refine ⟨s,r,?_,?_⟩
  · intro x _
    exact ⟨(hr x).1,(hr x).2.1,(hr x).2.2,original_chart_target hd x (r x) (hr x).1.2.1⟩
  · intro y
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ y))
    obtain ⟨his,hiy⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,his,hiy⟩
#print axioms chart_geometry
#print axioms local_nested
#print axioms finite_nested
end ConstructionTargets.SurfaceNestedTriangleCover
