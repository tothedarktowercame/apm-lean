import ConstructionTargets.CoefficientMovingSphereCenter
noncomputable section
namespace ConstructionTargets.CoefficientCompactBoundaryMotion
open CategoryTheory PuncturedNormedSpaceRadialEquivalence
variable {K E : Type} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
theorem separation [CompactSpace K] (f : C(K,E)) (c : E) (hc : ∀ z, f z ≠ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, δ ≤ ‖f z - c‖ := by
  have ho : IsOpen (Set.range f)ᶜ := (isCompact_range f.continuous).isClosed.isOpen_compl
  have hm : c ∈ (Set.range f)ᶜ := by simpa only [Set.mem_compl_iff, Set.mem_range, not_exists] using hc
  obtain ⟨δ, hδ, hs⟩ := Metric.isOpen_iff.mp ho c hm
  refine ⟨δ,hδ,fun z => le_of_not_gt (fun hz => ?_)⟩
  have hin : f z ∈ Metric.ball c δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  exact hs hin ⟨z,rfl⟩

def boundaryMap (f : C(K,E)) (c : E) (hc : ∀ z, f z ≠ c) : C(K,PuncturedSpace E) where
  toFun z := ⟨f z - c, sub_ne_zero.mpr (hc z)⟩
  continuous_toFun := by fun_prop

theorem avoid (f : C(K,E)) (c q : E) (δ : ℝ) (hδ : ∀ z, δ ≤ ‖f z - c‖)
    (hq : ‖q-c‖ < δ) (t : unitInterval) (z : K) :
    f z - c - (t : ℝ) • (q-c) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hh : ‖(t : ℝ) • (q-c)‖ < δ := by
    rw [norm_smul, Real.norm_of_nonneg t.property.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) t.property.2) hq
  rw [← he] at hh
  exact (not_lt_of_ge (hδ z)) hh

theorem new_center (f : C(K,E)) (c q : E) (δ : ℝ) (hδ : ∀ z, δ ≤ ‖f z - c‖)
    (hq : ‖q-c‖ < δ) : ∀ z, f z ≠ q := by
  intro z he
  have hn := avoid f c q δ hδ hq 1 z
  simp [he] at hn

def boundaryHomotopy (f : C(K,E)) (c q : E) (hc : ∀ z, f z ≠ c)
    (δ : ℝ) (hδ : ∀ z, δ ≤ ‖f z - c‖) (hq : ‖q-c‖ < δ) :
    ContinuousMap.Homotopy (boundaryMap f c hc) (boundaryMap f q (new_center f c q δ hδ hq)) where
  toFun tz := ⟨f tz.2 - c - (tz.1 : ℝ) • (q-c), avoid f c q δ hδ hq tz.1 tz.2⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by apply Subtype.ext; simp [boundaryMap]
  map_one_left z := by apply Subtype.ext; simp [boundaryMap]

variable (R : Type) [CommRing R]
theorem homology_eq (f : C(K,E)) (c q : E) (hc : ∀ z, f z ≠ c)
    (δ : ℝ) (hδ : ∀ z, δ ≤ ‖f z - c‖) (hq : ‖q-c‖ < δ) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (boundaryMap f c hc)) =
      (CoefficientRadialPair.F R n).map (TopCat.ofHom (boundaryMap f q (new_center f c q δ hδ hq))) :=
  CoefficientContractiblePair.singularHomology_map_eq_of_topCatHomotopy R
    (SingularHomologyConcrete.continuousMapHomotopyCylinder (boundaryHomotopy f c q hc δ hδ hq))
    (SingularHomologyConcrete.continuousMapHomotopyCylinder_zero (boundaryHomotopy f c q hc δ hδ hq))
    (SingularHomologyConcrete.continuousMapHomotopyCylinder_one (boundaryHomotopy f c q hc δ hδ hq)) n

theorem local_homology_constancy [CompactSpace K] (f : C(K,E)) (c : E) (hc : ∀ z, f z ≠ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q, ‖q-c‖ < δ → ∃ hq : ∀ z, f z ≠ q,
      ∀ n : ℕ, (CoefficientRadialPair.F R n).map (TopCat.ofHom (boundaryMap f c hc)) =
        (CoefficientRadialPair.F R n).map (TopCat.ofHom (boundaryMap f q hq)) := by
  obtain ⟨δ,hpos,hδ⟩ := separation f c hc
  exact ⟨δ,hpos,fun q hq => ⟨new_center f c q δ hδ hq,fun n => homology_eq R f c q hc δ hδ hq n⟩⟩
def radialBoundary (f : C(K,E)) (c : E) (hc : ∀ z, f z ≠ c) :=
  (radialNormalize E).comp (boundaryMap f c hc)
theorem radial_homology_eq (f : C(K,E)) (c q : E) (hc : ∀ z, f z ≠ c)
    (δ : ℝ) (hδ : ∀ z, δ ≤ ‖f z - c‖) (hq : ‖q-c‖ < δ) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (radialBoundary f c hc)) =
      (CoefficientRadialPair.F R n).map (TopCat.ofHom (radialBoundary f q (new_center f c q δ hδ hq))) := by
  change (CoefficientRadialPair.F R n).map (TopCat.ofHom (boundaryMap f c hc) ≫ TopCat.ofHom (radialNormalize E)) =
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (boundaryMap f q (new_center f c q δ hδ hq)) ≫ TopCat.ofHom (radialNormalize E))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, homology_eq R f c q hc δ hδ hq n]

def integral_example (f : C(UnitSphere (EuclideanSpace ℝ (Fin 2)), EuclideanSpace ℝ (Fin 2)))
    (c : EuclideanSpace ℝ (Fin 2)) (hc : ∀ z, f z ≠ c) := local_homology_constancy ℤ f c hc
def rational_example (f : C(UnitSphere (EuclideanSpace ℝ (Fin 3)), EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (hc : ∀ z, f z ≠ c) := local_homology_constancy ℚ f c hc
#print axioms radial_homology_eq
#print axioms integral_example
#print axioms rational_example

#print axioms separation
#print axioms avoid
#print axioms new_center
#print axioms boundaryHomotopy
#print axioms homology_eq
#print axioms local_homology_constancy
end ConstructionTargets.CoefficientCompactBoundaryMotion
