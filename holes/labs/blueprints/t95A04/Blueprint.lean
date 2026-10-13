import Mathlib
import ConstructionTargets.RealProjectiveSmoothTarget
import ConstructionTargets.RealProjectiveEvenQuadraticDescent
import ConstructionTargets.RealProjectiveVeroneseFibers

/-! # Blueprint for t95A04

The quotient atlas, smooth descent, and the algebraic description of the
Veronese fibres are already available in the imported, sorry-free construction
targets.  The two remaining analytic steps are isolated below.
-/

open scoped Manifold ContDiff
open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RealProjectiveSmoothTarget
open ConstructionTargets.RealProjectiveEvenQuadraticDescent
open ConstructionTargets.RealProjectiveVeroneseFibers
noncomputable section

local instance : ChartedSpace (E 2) (Space ℝ 2) := rpSmoothAtlas.charts
local instance : IsManifold (𝓡 2) ∞ (Space ℝ 2) := rpSmoothAtlas.smooth

def T95A04SphereMap (p : Sphere 2) : E 6 :=
  WithLp.toLp 2 ![p.val 0 ^ 2, p.val 1 ^ 2, p.val 2 ^ 2,
    p.val 0 * p.val 1, p.val 0 * p.val 2, p.val 1 * p.val 2]

theorem t95A04_realProjectiveSpace_compact :
    IsCompact (Set.univ : Set (Space ℝ 2)) := by
  rw [← Set.range_eq_univ.mpr sphereProjectionQuotientAuthority.surjective]
  simpa only [Set.image_univ] using
    isCompact_univ.image continuous_sphereProjection

theorem t95A04_veroneseDescended_isEmbedding
    (hcompact : IsCompact (Set.univ : Set (Space ℝ 2)))
    (hinj : Function.Injective veroneseDescended) :
    Topology.IsEmbedding veroneseDescended := by
  letI : CompactSpace (Space ℝ 2) := ⟨hcompact⟩
  exact (veroneseDescended_contMDiff.continuous.isClosedEmbedding hinj).isEmbedding

/-- The coordinate calculation: the derivative of `x ↦ xxᵀ` has zero kernel,
transported through the local-diffeomorphism charts of `sphereProjection`. -/
theorem t95A04_veroneseDescended_mfderiv_injective
    (x : Space ℝ 2) :
    Function.Injective
      (mfderiv (𝓡 2) (𝓡 6) veroneseDescended x) := by
  sorry

/-- LIBRARY: the finite-dimensional constant-rank/inverse-function theorem
turning an everywhere-injective manifold derivative into Mathlib's local
normal-form notion of immersion.  It is specialized only to the dimensions
needed here, but takes the derivative computation as an explicit hypothesis. -/
theorem t95A04_isImmersion_of_injective_mfderiv
    (hderiv : ∀ x : Space ℝ 2,
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 6) veroneseDescended x)) :
    Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ veroneseDescended := by
  sorry

theorem apm_t95a04 :
    ∃ atlas : SmoothAtlas 2,
    letI := atlas.charts
    letI := atlas.smooth
    ∃ f : Space ℝ 2 → E 6,
      (∀ p : Sphere 2, f (sphereProjection 2 p) = T95A04SphereMap p) ∧
      ContMDiff (𝓡 2) (𝓡 6) ∞ f ∧ Topology.IsEmbedding f ∧
      Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ f := by
  refine ⟨rpSmoothAtlas, veroneseDescended, ?_,
    veroneseDescended_contMDiff, ?_, ?_⟩
  · intro p
    simpa [T95A04SphereMap, veroneseSphereMap] using
      veroneseDescended_sphereProjection p
  · exact t95A04_veroneseDescended_isEmbedding
      t95A04_realProjectiveSpace_compact veroneseDescended_injective
  · exact t95A04_isImmersion_of_injective_mfderiv
      t95A04_veroneseDescended_mfderiv_injective

#print axioms apm_t95a04
