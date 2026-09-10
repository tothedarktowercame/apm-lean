import Mathlib.Geometry.Manifold.IsManifold.Basic

open Set
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceLocalization
variable {M N P F : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace P] [NormedAddCommGroup F] [ChartedSpace F P]

def domain (f : M → P) (g : N → P) (c : P) : Set (M × N) :=
  {z | f z.1 ∈ (chartAt F c).source ∧ g z.2 ∈ (chartAt F c).source}

theorem domain_open (f : M → P) (g : N → P) (c : P)
    (hf : Continuous f) (hg : Continuous g) : IsOpen (domain (F := F) f g c) :=
  ((chartAt F c).open_source.preimage (hf.comp continuous_fst)).inter
    ((chartAt F c).open_source.preimage (hg.comp continuous_snd))

omit [TopologicalSpace M] [TopologicalSpace N] in
theorem center_mem (f : M → P) (g : N → P) (x : M) (y : N)
    (h : f x = g y) : (x,y) ∈ domain (F := F) f g (f x) := by
  constructor
  · exact mem_chart_source F (f x)
  · rw [← h]
    exact mem_chart_source F (f x)

omit [TopologicalSpace M] [TopologicalSpace N] in
theorem coordinate_zero_iff (f : M → P) (g : N → P) (c : P)
    (z : M × N) (hz : z ∈ domain (F := F) f g c) :
    (chartAt F c) (f z.1) - (chartAt F c) (g z.2) = 0 ↔ f z.1 = g z.2 := by
  rw [sub_eq_zero]
  exact ⟨fun h => (chartAt F c).injOn hz.1 hz.2 h, fun h => congrArg _ h⟩

omit [TopologicalSpace M] [TopologicalSpace N] in
theorem local_fiber_eq (f : M → P) (g : N → P) (c : P) :
    domain (F := F) f g c ∩ {z | (chartAt F c) (f z.1) - (chartAt F c) (g z.2) = 0} =
      domain (F := F) f g c ∩ {z | f z.1 = g z.2} := by
  ext z
  exact and_congr_right (fun hz => coordinate_zero_iff f g c z hz)

#print axioms domain_open
#print axioms center_mem
#print axioms coordinate_zero_iff
#print axioms local_fiber_eq
end ConstructionTargets.ManifoldTargetIncidenceLocalization
