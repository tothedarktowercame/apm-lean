import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic
noncomputable section
open Set Topology
namespace ConstructionTargets.StandardTriangleEmbedding
abbrev Simplex := stdSimplex ℝ (Fin 3)
def parametrization (z : Simplex) : ℝ × ℝ := (z.1 1 - 1/3, z.1 2 - 1/3)
def interiorParameters : Set Simplex := {z | ∀ i, 0 < z.1 i}
def triangleInterior : Set (ℝ × ℝ) := {v | -1/3 < v.1 ∧ -1/3 < v.2 ∧ v.1 + v.2 < 1/3}
theorem continuous_parametrization : Continuous parametrization := by
  unfold parametrization
  exact (((continuous_apply 1).comp continuous_subtype_val).sub continuous_const).prodMk
    (((continuous_apply 2).comp continuous_subtype_val).sub continuous_const)

theorem injective_parametrization : Function.Injective parametrization := by
  intro z w h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change z.1 1 - 1/3 = w.1 1 - 1/3 at h1
  change z.1 2 - 1/3 = w.1 2 - 1/3 at h2
  have hz := z.2.2
  have hw := w.2.2
  rw [Fin.sum_univ_three] at hz hw
  apply Subtype.ext
  funext i
  fin_cases i <;> dsimp at * <;> linarith

theorem isClosedEmbedding_parametrization : IsClosedEmbedding parametrization :=
  continuous_parametrization.isClosedEmbedding injective_parametrization

theorem compact_image : IsCompact (Set.range parametrization) :=
  isCompact_range continuous_parametrization

theorem interior_image : parametrization '' interiorParameters = triangleInterior := by
  ext v
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hs := z.2.2
    rw [Fin.sum_univ_three] at hs
    have h0 := hz 0
    have h1 := hz 1
    have h2 := hz 2
    change -1/3 < z.1 1 - 1/3 ∧ -1/3 < z.1 2 - 1/3 ∧
      (z.1 1 - 1/3) + (z.1 2 - 1/3) < 1/3
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨h1,h2,h3⟩
    let z : Simplex := ⟨![1/3-v.1-v.2, v.1+1/3, v.2+1/3], by
      constructor
      · intro i
        fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_three]; ring⟩
    refine ⟨z, ?_, ?_⟩
    · intro i
      fin_cases i <;> dsimp [z] <;> linarith
    · apply Prod.ext <;> dsimp [parametrization,z] <;> ring

theorem open_interior : IsOpen triangleInterior := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))

theorem center_mem : (0 : ℝ × ℝ) ∈ parametrization '' interiorParameters := by
  rw [interior_image]
  norm_num [triangleInterior]

#print axioms isClosedEmbedding_parametrization
#print axioms compact_image
#print axioms interior_image
#print axioms open_interior
#print axioms center_mem
end ConstructionTargets.StandardTriangleEmbedding
