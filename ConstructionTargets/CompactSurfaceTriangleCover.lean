import Mathlib
import ConstructionTargets.ChartTriangleEmbedding
noncomputable section
open Set Topology
namespace ConstructionTargets.CompactSurfaceTriangleCover
open StandardTriangleEmbedding ScaledTriangleNeighborhood
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]

def planeEquiv (hd : Module.finrank ℝ E = 2) : E ≃L[ℝ] (ℝ × ℝ) :=
 ContinuousLinearEquiv.ofFinrankEq (by simpa using hd)

def planeChart (hd : Module.finrank ℝ E = 2) (x : M) : OpenPartialHomeomorph M (ℝ × ℝ) :=
 (chartAt E x).trans (planeEquiv hd).toHomeomorph.toOpenPartialHomeomorph

omit [T2Space M] [CompactSpace M] in
theorem original_chart_target (hd : Module.finrank ℝ E = 2) (x : M) (r : ℝ)
 (h : Set.range (scaled (planeChart hd x x) r) ⊆ (planeChart hd x).target) :
 Set.range ((planeEquiv hd).symm ∘ scaled (planeChart hd x x) r) ⊆ (chartAt E x).target := by
 rintro _ ⟨z,rfl⟩
 exact (h ⟨z,rfl⟩).2

omit [T2Space M] [CompactSpace M] in
theorem parametrization_formula (hd : Module.finrank ℝ E = 2) (x : M) (r : ℝ) (z : Simplex) :
 ((planeChart hd x).symm ∘ scaled (planeChart hd x x) r) z =
 (chartAt E x).symm ((planeEquiv hd).symm ((planeEquiv hd) ((chartAt E x) x) + r • parametrization z)) := rfl

theorem exists_finite_cover (hd : Module.finrank ℝ E = 2) :
 ∃ (s : Finset M) (r : M → ℝ),
 (∀ x ∈ s, 0 < r x ∧
   Set.range (scaled (planeChart hd x x) (r x)) ⊆ (planeChart hd x).target ∧
   IsClosedEmbedding ((planeChart hd x).symm ∘ scaled (planeChart hd x x) (r x)) ∧
   IsCompact (Set.range ((planeChart hd x).symm ∘ scaled (planeChart hd x x) (r x))) ∧
   Set.range ((planeChart hd x).symm ∘ scaled (planeChart hd x x) (r x)) ⊆ (chartAt E x).source ∧
   IsOpen (((planeChart hd x).symm ∘ scaled (planeChart hd x x) (r x)) '' interiorParameters)) ∧
 (∀ y : M, ∃ x ∈ s, y ∈ ((planeChart hd x).symm ∘ scaled (planeChart hd x x) (r x)) '' interiorParameters) := by
 classical
 have hsource (x : M) : (planeChart hd x).source = (chartAt E x).source := by
   simp [planeChart]
 have hx (x : M) : x ∈ (planeChart hd x).source := by rw [hsource]; exact mem_chart_source E x
 have h := fun x : M => ChartTriangleEmbedding.exists_chart_triangle (planeChart hd x) x (hx x)
 choose r hr using h
 let U : M → Set M := fun x => ((planeChart hd x).symm ∘ scaled (planeChart hd x x) (r x)) '' interiorParameters
 obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U (fun x => (hr x).2.2.2.2.2.1) (by
   intro y _
   exact Set.mem_iUnion.mpr ⟨y,(hr y).2.2.2.2.2.2⟩)
 refine ⟨s,r,?_,?_⟩
 · intro x _
   rcases hr x with ⟨hpos,hsub,hemb,hcomp,hsrc,hop,hcenter⟩
   exact ⟨hpos,hsub,hemb,hcomp,by rwa [hsource] at hsrc,hop⟩
 · intro y
   obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ y))
   obtain ⟨his,hiy⟩ := Set.mem_iUnion.mp hi
   exact ⟨i,his,hiy⟩

#print axioms original_chart_target
#print axioms parametrization_formula
#print axioms exists_finite_cover
end ConstructionTargets.CompactSurfaceTriangleCover
