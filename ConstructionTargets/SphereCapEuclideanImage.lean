import ConstructionTargets.SphereCapCoordinateIsometry

noncomputable section
namespace ConstructionTargets.SphereCapEuclideanImage

open Metric Set
open SphereCapL2Image SphereCapCoordinateIsometry

abbrev EA (d : ℕ) := EuclideanAmbient d

def strictUpperCap (d : ℕ) : Set (EA d) :=
  {y | y ∈ sphere 0 1 ∧ 0 < y (Fin.last d)}

def strictLowerCap (d : ℕ) : Set (EA d) :=
  {y | y ∈ sphere 0 1 ∧ y (Fin.last d) < 0}

lemma mem_sphere_zero_one_iff {d : ℕ} {y : EA d} :
    y ∈ sphere 0 1 ↔ ‖y‖ = 1 := by
  simp

lemma symm_last (d : ℕ) (y : EA d) :
    ((coordinateIsometry d).symm y).snd = y (Fin.last d) := by
  have h := coordinateIsometry_last d ((coordinateIsometry d).symm y)
  rw [(coordinateIsometry d).apply_symm_apply] at h
  exact h.symm

lemma image_upperCap (d : ℕ) :
    coordinateIsometry d '' upperCap d = strictUpperCap d := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨mem_sphere_zero_one_iff.mpr ((coordinateIsometry d).norm_map z |>.trans hz.1), ?_⟩
    rw [coordinateIsometry_last]
    exact hz.2
  · intro hy
    refine ⟨(coordinateIsometry d).symm y, ?_, (coordinateIsometry d).apply_symm_apply y⟩
    constructor
    · rw [(coordinateIsometry d).symm.norm_map, mem_sphere_zero_one_iff.mp hy.1]
    · rw [symm_last]
      exact hy.2

lemma image_lowerCap (d : ℕ) :
    coordinateIsometry d '' lowerCap d = strictLowerCap d := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨mem_sphere_zero_one_iff.mpr ((coordinateIsometry d).norm_map z |>.trans hz.1), ?_⟩
    rw [coordinateIsometry_last]
    exact hz.2
  · intro hy
    refine ⟨(coordinateIsometry d).symm y, ?_, (coordinateIsometry d).apply_symm_apply y⟩
    constructor
    · rw [(coordinateIsometry d).symm.norm_map, mem_sphere_zero_one_iff.mp hy.1]
    · rw [symm_last]
      exact hy.2

lemma image_upperGraph (d : ℕ) :
    coordinateIsometry d ''
        GraphMetricComparison.Graph d (SphereCapHeight.upper d) (SphereCapHeight.domain d) =
      strictUpperCap d := by
  rw [SphereCapL2Image.upper_graph_eq_cap, image_upperCap]

lemma image_lowerGraph (d : ℕ) :
    coordinateIsometry d ''
        GraphMetricComparison.Graph d (SphereCapHeight.lower d) (SphereCapHeight.domain d) =
      strictLowerCap d := by
  rw [SphereCapL2Image.lower_graph_eq_cap, image_lowerCap]

example : coordinateIsometry 2 '' upperCap 2 = strictUpperCap 2 := image_upperCap 2
example : coordinateIsometry 2 '' lowerCap 2 = strictLowerCap 2 := image_lowerCap 2
example : coordinateIsometry 3 '' upperCap 3 = strictUpperCap 3 := image_upperCap 3
example : coordinateIsometry 3 '' lowerCap 3 = strictLowerCap 3 := image_lowerCap 3

#print axioms mem_sphere_zero_one_iff
#print axioms symm_last
#print axioms image_upperCap
#print axioms image_lowerCap
#print axioms image_upperGraph
#print axioms image_lowerGraph

end ConstructionTargets.SphereCapEuclideanImage
