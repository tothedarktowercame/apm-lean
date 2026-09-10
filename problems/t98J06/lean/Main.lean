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
  sorry
