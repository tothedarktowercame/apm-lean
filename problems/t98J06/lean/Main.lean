import Mathlib
import ConstructionTargets.ManifoldFormTargets

/-! # t98J06: graph/diagonal transversality and the local orientation number

Transversality uses the actual tangent maps of the graph and diagonal.
The local intersection sign is the determinant sign of their tangent-sum
map, ordered diagonal then graph, so the normal convention is (a,b) ↦ b-a,
as in the printed df-I sign. Both copies inherit the same orientation of X;
changing that orientation reverses both factors and leaves this sign unchanged.
Orientability is explicitly represented by existence of a smooth nowhere-zero
top form. The desired nonsingularity or local sign is not supplied as a field.
-/

open scoped Manifold ContDiff
open ConstructionTargets.ManifoldFormTargets
noncomputable section
namespace T98J06
abbrev E (n : ℕ) := Fin n → ℝ
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (E n) X]

def diagonal (x : X) : X × X := (x,x)
def graph (f : X → X) (x : X) : X × X := (x,f x)

def TransverseGraph (f : X → X) : Prop :=
  ∀ x y, graph f x = diagonal y →
    LinearMap.range (mfderiv 𝓘(ℝ,E n) (𝓘(ℝ,E n).prod 𝓘(ℝ,E n)) (graph f) x).toLinearMap ⊔
    LinearMap.range (mfderiv 𝓘(ℝ,E n) (𝓘(ℝ,E n).prod 𝓘(ℝ,E n)) diagonal y).toLinearMap = ⊤

/-- At a fixed point, both maps take values in the same product tangent space. -/
def tangentSum (f : X → X) (p : X) : (E n × E n) →L[ℝ] (E n × E n) :=
  (show E n →L[ℝ] (E n × E n) from mfderiv 𝓘(ℝ,E n) (𝓘(ℝ,E n).prod 𝓘(ℝ,E n)) diagonal p).comp
      (ContinuousLinearMap.fst ℝ (E n) (E n)) +
  (show E n →L[ℝ] (E n × E n) from mfderiv 𝓘(ℝ,E n) (𝓘(ℝ,E n).prod 𝓘(ℝ,E n)) (graph f) p).comp
      (ContinuousLinearMap.snd ℝ (E n) (E n))

def difference (f : X → X) (p : X) : E n →L[ℝ] E n :=
  (show E n →L[ℝ] E n from mfderiv 𝓘(ℝ,E n) 𝓘(ℝ,E n) f p) - ContinuousLinearMap.id ℝ (E n)

/-- Zero denotes a degenerate tangent sum; transverse points have sign ±1. -/
def localIntersectionSign (f : X → X) (p : X) : ℤ :=
  let d := (tangentSum (n := n) f p).toLinearMap.det
  if 0 < d then 1 else if d < 0 then -1 else 0

end T98J06
open T98J06

open Module in
/-- Linear-algebra core: det of (a,b) ↦ (a+b, a + A b) equals det (A - 1). -/
theorem j06_det_core (n : ℕ) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    LinearMap.det ((LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) + LinearMap.snd ℝ _ _ ).prod
      (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) + A.comp (LinearMap.snd ℝ (Fin n → ℝ) _)))
      = (A - LinearMap.id).det := by
  classical
  let b := Pi.basisFun ℝ (Fin n)
  rw [← LinearMap.det_toMatrix (b.prod b), ← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix (b.prod b) (b.prod b)
      ((LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) + LinearMap.snd ℝ _ _ ).prod
        (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) + A.comp (LinearMap.snd ℝ (Fin n → ℝ) _)))
      = Matrix.fromBlocks 1 1 1 (LinearMap.toMatrix b b A) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, b, Matrix.one_apply, Pi.single_apply]
  rw [this, Matrix.det_fromBlocks_one₁₁, Matrix.mul_one, map_sub,
    LinearMap.toMatrix_id]

theorem apm_t98j06 (n : ℕ) {X : Type*} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (E n) X] [IsManifold 𝓘(ℝ,E n) ∞ X]
    (horientable : ∃ η : Form (E n) X n, IsVolumeForm η)
    (f : X → X) (hf : ContMDiff 𝓘(ℝ,E n) 𝓘(ℝ,E n) ∞ f)
    (htrans : TransverseGraph (n := n) f) :
    ∀ p, f p = p →
      Function.Bijective (difference (n := n) f p) ∧
      (0 < (difference (n := n) f p).toLinearMap.det → localIntersectionSign (n := n) f p = 1) ∧
      (¬ 0 < (difference (n := n) f p).toLinearMap.det → localIntersectionSign (n := n) f p = -1) := by
  intro p hp
  have hfd : MDifferentiableAt 𝓘(ℝ,E n) 𝓘(ℝ,E n) f p := hf.mdifferentiableAt (by simp)
  have hdiag : ∀ y : X, mfderiv 𝓘(ℝ,E n) (𝓘(ℝ,E n).prod 𝓘(ℝ,E n)) diagonal y =
      (ContinuousLinearMap.id ℝ (E n)).prod (ContinuousLinearMap.id ℝ (E n)) := by
    intro y
    have := mfderiv_prodMk (I := 𝓘(ℝ,E n)) (x := y) (f := fun x : X => x) (g := fun x : X => x)
      mdifferentiableAt_id mdifferentiableAt_id
    refine this.trans ?_
    rw [show (fun x : X => x) = id from rfl, mfderiv_id]
    rfl
  have hgraph : mfderiv 𝓘(ℝ,E n) (𝓘(ℝ,E n).prod 𝓘(ℝ,E n)) (graph f) p =
      (ContinuousLinearMap.id ℝ (E n)).prod (mfderiv 𝓘(ℝ,E n) 𝓘(ℝ,E n) f p) := by
    have := mfderiv_prodMk (I := 𝓘(ℝ,E n)) (x := p) (f := fun x : X => x) (g := f)
      mdifferentiableAt_id hfd
    refine this.trans ?_
    rw [show (fun x : X => x) = id from rfl, mfderiv_id]
    rfl
  set A : E n →L[ℝ] E n := mfderiv 𝓘(ℝ,E n) 𝓘(ℝ,E n) f p with hA
  have hsurj : Function.Surjective (difference (n := n) f p) := by
    intro c
    have ht := htrans p p (by simp [graph, diagonal, hp])
    rw [Submodule.eq_top_iff'] at ht
    have hmem := ht ((0 : E n), c)
    rw [Submodule.mem_sup] at hmem
    obtain ⟨y, ⟨u, rfl⟩, z, ⟨w, rfl⟩, hyz⟩ := hmem
    rw [hgraph] at hyz
    rw [hdiag] at hyz
    change ((u, A u) : E n × E n) + ((w, w) : E n × E n) = ((0 : E n), c) at hyz
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hyz
    refine ⟨u, ?_⟩
    have hw : w = -u := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hyz.1
    subst hw
    change A u - (show E n from u) = c
    rw [← hyz.2]; abel
  have hbij : Function.Bijective (difference (n := n) f p) := by
    refine ⟨?_, hsurj⟩
    exact (LinearMap.injective_iff_surjective (f := (difference (n := n) f p).toLinearMap)).mpr hsurj
  have hdet : (tangentSum (n := n) f p).toLinearMap.det =
      (difference (n := n) f p).toLinearMap.det := by
    have h1 : (tangentSum (n := n) f p).toLinearMap =
        (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) + LinearMap.snd ℝ _ _ ).prod
          (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) + (A : E n →ₗ[ℝ] E n).comp
            (LinearMap.snd ℝ (Fin n → ℝ) _)) := by
      apply LinearMap.ext; rintro ⟨a, b⟩
      simp [tangentSum, hdiag, hgraph, A]
      rfl
    rw [h1, j06_det_core]
    rfl
  have hne : (difference (n := n) f p).toLinearMap.det ≠ 0 := by
    have hu : IsUnit (difference (n := n) f p).toLinearMap :=
      (Module.End.isUnit_iff _).mpr hbij
    exact ((LinearMap.isUnit_iff_isUnit_det _).mp hu).ne_zero
  refine ⟨hbij, fun hpos => ?_, fun hnpos => ?_⟩
  · simp [localIntersectionSign, hdet, hpos]
  · have hneg : (difference (n := n) f p).toLinearMap.det < 0 :=
      lt_of_le_of_ne (not_lt.mp hnpos) hne
    simp [localIntersectionSign, hdet, hnpos, hneg]
