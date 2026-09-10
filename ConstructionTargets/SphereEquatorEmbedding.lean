import ConstructionTargets.SphereCapCoordinateIsometry

noncomputable section
namespace ConstructionTargets.SphereEquatorEmbedding

open ConstructionTargets.SphereCapL2Image
open ConstructionTargets.SphereCapCoordinateIsometry
open scoped RealInnerProductSpace

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev EA (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

def appendZero (d : ℕ) : E d →ₗᵢ[ℝ] EA d where
  toFun x := coordinateIsometry d (WithLp.toLp 2 (x, 0))
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply WithLp.ofLp_injective
    simp
  map_smul' c x := by
    rw [← map_smul]
    congr 1
    apply WithLp.ofLp_injective
    simp
  norm_map' x := by
    change ‖coordinateIsometry d (WithLp.toLp 2 (x, 0))‖ = ‖x‖
    rw [LinearIsometryEquiv.norm_map]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp

@[simp] theorem appendZero_castSucc (d : ℕ) (x : E d) (i : Fin d) :
    appendZero d x i.castSucc = x i := by
  change coordinateIsometry d (WithLp.toLp 2 (x, 0)) i.castSucc = x i
  rw [coordinateIsometry_castSucc]
  rfl

@[simp] theorem appendZero_last (d : ℕ) (x : E d) :
    appendZero d x (Fin.last d) = 0 := by
  change coordinateIsometry d (WithLp.toLp 2 (x, 0)) (Fin.last d) = 0
  rw [coordinateIsometry_last]
  rfl

example : E 2 →ₗᵢ[ℝ] EA 2 := appendZero 2
example : E 3 →ₗᵢ[ℝ] EA 3 := appendZero 3

#print axioms appendZero_castSucc
#print axioms appendZero_last

end ConstructionTargets.SphereEquatorEmbedding
