import ConstructionTargets.ExteriorDerivativeSimplexCalculus

/-! # Adapter for the frozen t98A05 local calculus -/

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.FrozenSimplexIntegralAdapter

open ConstructionTargets.ExteriorDerivativeSimplexCalculus

/-- The pointwise alpha specification makes the form-valued function linear,
hence differentiable. -/
lemma differentiable_alpha (alpha : Form 1) (ha : IsAlpha alpha) :
    Differentiable ℝ alpha := by
  let L : E3 →ₗ[ℝ] (E3 [⋀^Fin 1]→L[ℝ] ℝ) :=
    { toFun := alpha
      map_add' := by
        intro x y
        apply ContinuousAlternatingMap.ext
        intro v
        change alpha (x + y) v = alpha x v + alpha y v
        rw [ha, ha, ha]
        simp
        ring
      map_smul' := by
        intro c x
        apply ContinuousAlternatingMap.ext
        intro v
        change alpha (c • x) v = c • alpha x v
        rw [ha, ha]
        simp
        ring }
  have hc : Continuous L := L.continuous_of_finiteDimensional
  exact (⟨L, hc⟩ : E3 →L[ℝ] (E3 [⋀^Fin 1]→L[ℝ] ℝ)).differentiable

lemma differentiable_beta (beta : Form 2) (hb : IsBeta beta) :
    Differentiable ℝ beta := by
  let L : E3 →ₗ[ℝ] (E3 [⋀^Fin 2]→L[ℝ] ℝ) :=
    { toFun := beta
      map_add' := by
        intro x y
        apply ContinuousAlternatingMap.ext
        intro v
        change beta (x + y) v = beta x v + beta y v
        rw [hb, hb, hb]
        simp
        ring
      map_smul' := by
        intro c x
        apply ContinuousAlternatingMap.ext
        intro v
        change beta (c • x) v = c • beta x v
        rw [hb, hb]
        simp
        ring }
  exact (⟨L, L.continuous_of_finiteDimensional⟩ :
    E3 →L[ℝ] (E3 [⋀^Fin 2]→L[ℝ] ℝ)).differentiable

lemma differentiable_gamma (gamma : Form 3) (hg : IsGamma gamma) :
    Differentiable ℝ gamma := by
  have hconst : gamma = fun _x => gamma 0 := by
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    rw [hg, hg]
  rw [hconst]
  fun_prop

/-- Exact combined exterior-derivative conclusion corresponding to the three
local frozen conjuncts. -/
theorem frozen_extDerivs
    (alpha : Form 1) (ha : IsAlpha alpha)
    (beta : Form 2) (hb : IsBeta beta)
    (gamma : Form 3) (hg : IsGamma gamma) :
    (∀ x v, extDeriv alpha x v =
      2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) ∧
    extDeriv beta = 3 • gamma ∧ extDeriv gamma = 0 := by
  refine ⟨extDeriv_alpha alpha ha (differentiable_alpha alpha ha), ?_,
    extDeriv_gamma gamma hg (differentiable_gamma gamma hg)⟩
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  rw [extDeriv_beta beta hb (differentiable_beta beta hb) x v]
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
  rw [nsmul_eq_mul]
  exact congrArg (fun z : ℝ => 3 * z) (hg x v).symm

def frozenTriangleDomain : Set E2 :=
  {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 0 + u 1 ≤ 1}

def frozenTriangleSetIntegral (f : E2 → ℝ) : ℝ :=
  ∫ u in frozenTriangleDomain, f u

/-- The precise measure-theoretic adapter still required to replace the
iterated-coordinate integral by the frozen `EuclideanSpace` set integral. -/
def FrozenTriangleMeasureAdapter : Prop :=
  frozenTriangleSetIntegral (fun _ => 2) =
    orientedTriangleIntegral (fun _ _ => 2)

theorem frozen_triangle_integral_of_adapter
    (h : FrozenTriangleMeasureAdapter) :
    frozenTriangleSetIntegral (fun _ => 2) = 1 := by
  rw [h]
  exact integral_const_two_triangle

#print axioms differentiable_alpha
#print axioms differentiable_beta
#print axioms differentiable_gamma
#print axioms frozen_extDerivs
#print axioms frozen_triangle_integral_of_adapter

end ConstructionTargets.FrozenSimplexIntegralAdapter
