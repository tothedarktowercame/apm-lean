import ConstructionTargets.SphereCapL2Image

noncomputable section
namespace ConstructionTargets.SphereCapCoordinateIsometry

open SphereCapHeight SphereCapL2Image
open scoped RealInnerProductSpace

abbrev EuclideanAmbient (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

def coordinateLinearEquiv (d : ℕ) : Ambient d ≃ₗ[ℝ] EuclideanAmbient d where
  toFun z := WithLp.toLp 2 (Fin.lastCases z.snd (fun i => z.fst i))
  invFun y := WithLp.toLp 2
    (WithLp.toLp 2 (fun i : Fin d => y i.castSucc), y (Fin.last d))
  map_add' x y := by
    apply WithLp.ofLp_injective
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    apply WithLp.ofLp_injective
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  left_inv z := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply WithLp.ofLp_injective
      funext i
      simp
    · simp
  right_inv y := by
    apply WithLp.ofLp_injective
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma coordinateLinearEquiv_apply (d : ℕ) (z : Ambient d) (i : Fin (d + 1)) :
    coordinateLinearEquiv d z i = Fin.lastCases z.snd (fun j => z.fst j) i := rfl

lemma coordinateLinearEquiv_castSucc (d : ℕ) (z : Ambient d) (i : Fin d) :
    coordinateLinearEquiv d z i.castSucc = z.fst i := by simp [coordinateLinearEquiv]

lemma coordinateLinearEquiv_last (d : ℕ) (z : Ambient d) :
    coordinateLinearEquiv d z (Fin.last d) = z.snd := by simp [coordinateLinearEquiv]

lemma coordinateLinearEquiv_norm (d : ℕ) (z : Ambient d) :
    ‖coordinateLinearEquiv d z‖ = ‖z‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [coordinateLinearEquiv, WithLp.prod_norm_sq_eq_of_L2,
    EuclideanSpace.norm_sq_eq]

def coordinateIsometry (d : ℕ) : Ambient d ≃ₗᵢ[ℝ] EuclideanAmbient d :=
  LinearIsometryEquiv.mk (coordinateLinearEquiv d) (coordinateLinearEquiv_norm d)

@[simp] lemma coordinateIsometry_apply (d : ℕ) (z : Ambient d) :
    coordinateIsometry d z = coordinateLinearEquiv d z := rfl

@[simp] lemma coordinateIsometry_castSucc (d : ℕ) (z : Ambient d) (i : Fin d) :
    coordinateIsometry d z i.castSucc = z.fst i := coordinateLinearEquiv_castSucc d z i

@[simp] lemma coordinateIsometry_last (d : ℕ) (z : Ambient d) :
    coordinateIsometry d z (Fin.last d) = z.snd := coordinateLinearEquiv_last d z

example : Ambient 2 ≃ₗᵢ[ℝ] EuclideanAmbient 2 := coordinateIsometry 2
example : Ambient 3 ≃ₗᵢ[ℝ] EuclideanAmbient 3 := coordinateIsometry 3

#print axioms coordinateLinearEquiv_castSucc
#print axioms coordinateLinearEquiv_last
#print axioms coordinateLinearEquiv_norm
#print axioms coordinateIsometry_castSucc
#print axioms coordinateIsometry_last

end ConstructionTargets.SphereCapCoordinateIsometry
