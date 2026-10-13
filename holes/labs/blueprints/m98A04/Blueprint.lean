import Mathlib
import ConstructionTargets.TestFunctionTranslation

/-!
# APM m98A04

## Statement repairs

The middle expression in part (a), printed as `∂ᵅ * φ`, is missing its
distribution.  It is repaired to the standard identity
`Dᵅ(T * φ) = (Dᵅ T) * φ = T * (Dᵅ φ)`, matching the surrounding
text and the informal solution.

## Encoding notes

Mathlib's genuine LF-topological `TestFunction` and `Distribution` spaces are
used on `ℝⁿ`.  A multiindex is represented by a list of coordinate indices;
repetition records repeated differentiation and every usual multiindex admits
such a list.  Bundled translated and differentiated test functions are
characterized pointwise, avoiding any replacement of distributions by regular
functions.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Interval Pointwise

abbrev apm_m98a04_TF (n : ℕ) :=
  TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤

noncomputable def apm_m98a04_partialList {n : ℕ} :
    List (Fin n) → (EuclideanSpace ℝ (Fin n) → ℝ) →
      EuclideanSpace ℝ (Fin n) → ℝ
  | [], f => f
  | i :: is, f => fun x =>
      fderiv ℝ (apm_m98a04_partialList is f) x (EuclideanSpace.single i 1)

def apm_m98a04_IsConvolution {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    ∀ ψ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤,
      (∀ y, ψ y = φ (x - y)) → h x = T ψ

def apm_m98a04_IsDistributionalPartial {n : ℕ}
    (indices : List (Fin n))
    (T DT : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) : Prop :=
  ∀ ψ dψ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤,
    (∀ x, dψ x = apm_m98a04_partialList indices (ψ : _ → ℝ) x) →
      DT ψ = (-1 : ℝ) ^ indices.length * T dψ

/-- The translated reflection `y ↦ φ (x - y)` as an actual bundled test
function.  This removes the pointwise-existence part of the convolution
definition from the remaining analytic problem. -/
noncomputable def apm_m98a04_translateReflect {n : ℕ}
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (x : EuclideanSpace ℝ (Fin n)) :
    TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤ :=
  TestFunction.mk (fun y => φ (x - y))
    (φ.contDiff.comp (contDiff_const.sub contDiff_id))
    (φ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x))
    (by simp)

@[simp] lemma apm_m98a04_translateReflect_apply {n : ℕ}
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (x y : EuclideanSpace ℝ (Fin n)) :
    apm_m98a04_translateReflect φ x y = φ (x - y) := rfl

lemma apm_m98a04_canonical_isConvolution {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) :
    apm_m98a04_IsConvolution T φ
      (fun x => T (apm_m98a04_translateReflect φ x)) := by
  intro x ψ hψ
  apply congrArg T
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext y
  exact (hψ y).symm

/-- Bundle the iterated directional derivative encoded by
`apm_m98a04_partialList` as an actual test function.  This uses Mathlib's
`TestFunction.fderivCLM` and `TestFunction.postcompCLM`. -/
noncomputable def apm_m98a04_partialListTF {n : ℕ} :
    List (Fin n) →
      TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤ →
      TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤
  | [], φ => φ
  | i :: is, φ =>
      TestFunction.postcompCLM
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))
        (TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞)
          (apm_m98a04_partialListTF is φ))

noncomputable def apm_m98a04_partialStepCLM {n : ℕ} (i : Fin n) :
    apm_m98a04_TF n →L[ℝ] apm_m98a04_TF n :=
  (TestFunction.postcompCLM
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))).comp
    (TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞))

noncomputable def apm_m98a04_partialListCLM {n : ℕ} :
    List (Fin n) → apm_m98a04_TF n →L[ℝ] apm_m98a04_TF n
  | [] => ContinuousLinearMap.id ℝ _
  | i :: is =>
      (apm_m98a04_partialStepCLM i).comp
        (apm_m98a04_partialListCLM is)

@[simp] lemma apm_m98a04_partialListCLM_apply {n : ℕ}
    (indices : List (Fin n)) (φ : apm_m98a04_TF n) :
    apm_m98a04_partialListCLM indices φ =
      apm_m98a04_partialListTF indices φ := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
      change apm_m98a04_partialStepCLM i
        (apm_m98a04_partialListCLM is φ) = _
      rw [ih]
      rfl

@[simp] lemma apm_m98a04_partialListTF_apply {n : ℕ}
    (indices : List (Fin n))
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (x : EuclideanSpace ℝ (Fin n)) :
    apm_m98a04_partialListTF indices φ x =
      apm_m98a04_partialList indices (φ : _ → ℝ) x := by
  induction indices generalizing x with
  | nil => simp [apm_m98a04_partialListTF, apm_m98a04_partialList]
  | cons i is ih =>
      change ((TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞)
        (apm_m98a04_partialListTF is φ)) x) (EuclideanSpace.single i 1) = _
      rw [TestFunction.fderivCLM_apply_of_le _ (by simp)]
      change fderiv ℝ (apm_m98a04_partialListTF is φ : _ → ℝ) x
        (EuclideanSpace.single i 1) = _
      exact congrArg (fun f : (EuclideanSpace ℝ (Fin n) → ℝ) ↦
        fderiv ℝ f x (EuclideanSpace.single i 1)) (funext ih)

/-- The empty multiindex gives the original distribution. -/
lemma apm_m98a04_isDistributionalPartial_nil {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) :
    apm_m98a04_IsDistributionalPartial [] T T := by
  intro ψ dψ hdψ
  have hψ : dψ = ψ := by
    apply TestFunction.toTestFunctionClass.coe_injective'
    funext x
    simpa [apm_m98a04_partialList] using hdψ x
  subst dψ
  simp

noncomputable def apm_m98a04_distributionalPartial {n : ℕ}
    (indices : List (Fin n))
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) :
    Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤ :=
  (-1 : ℝ) ^ indices.length • T.comp (apm_m98a04_partialListCLM indices)

lemma apm_m98a04_distributionalPartial_spec {n : ℕ}
    (indices : List (Fin n))
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) :
    apm_m98a04_IsDistributionalPartial indices T
      (apm_m98a04_distributionalPartial indices T) := by
  intro ψ dψ hdψ
  have hd : dψ = apm_m98a04_partialListCLM indices ψ := by
    apply TestFunction.toTestFunctionClass.coe_injective'
    funext x
    rw [apm_m98a04_partialListCLM_apply,
      apm_m98a04_partialListTF_apply]
    exact hdψ x
  subst dψ
  change (-1 : ℝ) ^ indices.length *
      T (apm_m98a04_partialListCLM indices ψ) = _
  rw [apm_m98a04_partialListCLM_apply]

lemma apm_m98a04_partialList_zero {n : ℕ}
    (indices : List (Fin n)) :
    apm_m98a04_partialList indices
      (0 : EuclideanSpace ℝ (Fin n) → ℝ) = 0 := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
      simp only [apm_m98a04_partialList]
      rw [ih]
      ext x
      simp

/-- Differentiating a reflected translate in its translated variable inserts
one minus sign. -/
lemma apm_m98a04_fderiv_translateReflect {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y v : EuclideanSpace ℝ (Fin n))
    (hf : DifferentiableAt ℝ f (x - y)) :
    fderiv ℝ (fun z => f (x - z)) y v = - fderiv ℝ f (x - y) v := by
  have hsub : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => x - z)
      (0 - ContinuousLinearMap.id ℝ _) y :=
    (hasFDerivAt_const (x := y) x).sub (hasFDerivAt_id y)
  have hcomp : HasFDerivAt (fun z => f (x - z))
      (fderiv ℝ f (x - y) ∘L
        (0 - ContinuousLinearMap.id ℝ _)) y := by
    convert hf.hasFDerivAt.comp y hsub using 1
  rw [hcomp.fderiv]
  simp

/-- Differentiation of a reflected translate with respect to its translation
parameter has no reflection sign. -/
lemma apm_m98a04_hasFDerivAt_translateParameter {n : ℕ}
    (φ : apm_m98a04_TF n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z => φ (z - y)) (fderiv ℝ φ (x - y)) x := by
  convert (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const y) using 1

lemma apm_m98a04_fderiv_translateParameter_apply {n : ℕ}
    (φ : apm_m98a04_TF n)
    (x y v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => φ (z - y)) x v = fderiv ℝ φ (x - y) v := by
  rw [(apm_m98a04_hasFDerivAt_translateParameter φ x y).fderiv]

/-- Reflection and translation preserve the norm of every full iterated
Fréchet derivative. -/
lemma apm_m98a04_norm_iteratedFDeriv_translateReflect {n : ℕ}
    (φ : apm_m98a04_TF n) (i : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ i (fun z => φ (x - z)) y‖ =
      ‖iteratedFDeriv ℝ i (φ : _ → ℝ) (x - y)‖ := by
  let negIso : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n) := LinearIsometryEquiv.neg ℝ
  have hfun : (fun z => φ (x - z)) =
      (fun z => φ (x + z)) ∘ negIso := by
    funext z
    simp [negIso, sub_eq_add_neg]
  rw [hfun, negIso.norm_iteratedFDeriv_comp_right]
  rw [iteratedFDeriv_comp_add_left]
  simp [negIso, sub_eq_add_neg]

/-- Every iterated derivative of a test function is globally Lipschitz.  A
bound for its derivative is supplied by the next compactly-supported
derivative. -/
lemma apm_m98a04_exists_lipschitz_iteratedFDeriv {n : ℕ}
    (φ : apm_m98a04_TF n) (i : ℕ) :
    ∃ C : NNReal, LipschitzWith C (iteratedFDeriv ℝ i (φ : _ → ℝ)) := by
  have hi1 : ((i + 1 : ℕ) : WithTop ℕ∞) ≤
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (↑(i + 1) : ℕ∞) ≤ ⊤ from le_top)
  have hi : ((i : ℕ) : WithTop ℕ∞) <
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast ENat.coe_lt_top i
  have hcont : Continuous (fun x =>
      iteratedFDeriv ℝ (i + 1) (φ : _ → ℝ) x) :=
    φ.contDiff.continuous_iteratedFDeriv hi1
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    (φ.hasCompactSupport.iteratedFDeriv (i + 1))
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_fderiv_le
    (φ.contDiff.differentiable_iteratedFDeriv hi) ?_⟩
  intro x
  apply NNReal.coe_le_coe.mp
  simpa [Real.coe_toNNReal C hC0, norm_fderiv_iteratedFDeriv] using hC x

/-- A globally Lipschitz derivative gives a uniform quadratic first-order
remainder.  The deliberately non-sharp constant is convenient for seminorm
estimates. -/
lemma apm_m98a04_quadratic_remainder_of_lipschitz_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {C : NNReal}
    (hf : Differentiable ℝ f)
    (hLip : LipschitzWith C (fderiv ℝ f)) (x y : E) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤
      (C : ℝ) * ‖y - x‖ ^ 2 := by
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤
        (C : ℝ) * ‖y - x‖ := by
    intro z hz
    exact (hLip.norm_sub_le z x).trans (mul_le_mul_of_nonneg_left
      (norm_sub_le_of_mem_segment hz) NNReal.zero_le_coe)
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf z) hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc
    ‖f y - f x - fderiv ℝ f x (y - x)‖
        ≤ ((C : ℝ) * ‖y - x‖) * ‖y - x‖ := hmv
    _ = (C : ℝ) * ‖y - x‖ ^ 2 := by ring

lemma apm_m98a04_exists_lipschitz_fderiv_iteratedFDeriv {n : ℕ}
    (φ : apm_m98a04_TF n) (i : ℕ) :
    ∃ C : NNReal, LipschitzWith C
      (fderiv ℝ (iteratedFDeriv ℝ i (φ : _ → ℝ))) := by
  obtain ⟨C, hC⟩ :=
    apm_m98a04_exists_lipschitz_iteratedFDeriv φ (i + 1)
  refine ⟨C, ?_⟩
  let e := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (i + 1) => EuclideanSpace ℝ (Fin n)) ℝ
  simpa only [fderiv_iteratedFDeriv, one_mul] using e.lipschitz.comp hC

/-- Uniform quadratic Taylor remainder for every iterated derivative of a
test function. -/
lemma apm_m98a04_iteratedFDeriv_quadratic_remainder {n : ℕ}
    (φ : apm_m98a04_TF n) (i : ℕ) :
    ∃ C : NNReal, ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ i (φ : _ → ℝ) y -
          iteratedFDeriv ℝ i (φ : _ → ℝ) x -
          fderiv ℝ (iteratedFDeriv ℝ i (φ : _ → ℝ)) x (y - x)‖ ≤
        (C : ℝ) * ‖y - x‖ ^ 2 := by
  obtain ⟨C, hC⟩ :=
    apm_m98a04_exists_lipschitz_fderiv_iteratedFDeriv φ i
  exact ⟨C, fun x y =>
    apm_m98a04_quadratic_remainder_of_lipschitz_fderiv
      (φ.contDiff.differentiable_iteratedFDeriv (by
        exact_mod_cast ENat.coe_lt_top i)) hC x y⟩

/-- Iterating the previous identity gives the exact reflection sign for the
coordinate derivatives encoded by `partialList`. -/
lemma apm_m98a04_partialList_translateReflect {n : ℕ}
    (indices : List (Fin n))
    (φ : apm_m98a04_TF n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    apm_m98a04_partialList indices (fun z => φ (x - z)) y =
      (-1 : ℝ) ^ indices.length *
        apm_m98a04_partialList indices (φ : _ → ℝ) (x - y) := by
  induction indices generalizing y with
  | nil => simp [apm_m98a04_partialList]
  | cons i is ih =>
      simp only [apm_m98a04_partialList, List.length_cons, pow_succ]
      have hsmooth : ContDiff ℝ ∞
          (apm_m98a04_partialList is (φ : _ → ℝ)) := by
        rw [← funext (apm_m98a04_partialListTF_apply is φ)]
        exact (apm_m98a04_partialListTF is φ).contDiff
      have hfun : apm_m98a04_partialList is (fun w => φ (x - w)) =
          fun z => (-1 : ℝ) ^ is.length *
            apm_m98a04_partialList is (φ : _ → ℝ) (x - z) := by
        funext z
        exact ih z
      rw [hfun]
      rw [fderiv_const_mul]
      · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [apm_m98a04_fderiv_translateReflect _ x y
          (EuclideanSpace.single i 1)
          ((hsmooth.differentiable (by simp)).differentiableAt)]
        ring
      · exact (hsmooth.comp
          (contDiff_const.sub contDiff_id)).differentiable (by simp)
            |>.differentiableAt

lemma apm_m98a04_partialListTF_translateReflect {n : ℕ}
    (indices : List (Fin n)) (φ : apm_m98a04_TF n)
    (x : EuclideanSpace ℝ (Fin n)) :
    apm_m98a04_partialListTF indices
        (apm_m98a04_translateReflect φ x) =
      (-1 : ℝ) ^ indices.length •
        apm_m98a04_translateReflect
          (apm_m98a04_partialListTF indices φ) x := by
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext y
  rw [apm_m98a04_partialListTF_apply]
  change apm_m98a04_partialList indices (fun z => φ (x - z)) y = _
  rw [apm_m98a04_partialList_translateReflect]
  simp

/-- The convolution by the distributional partial equals convolution by the
corresponding partial of the test function.  This algebraic half of the main
bridge does not require translation smoothness. -/
lemma apm_m98a04_distributionalPartial_translateReflect {n : ℕ}
    (indices : List (Fin n))
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n) (x : EuclideanSpace ℝ (Fin n)) :
    apm_m98a04_distributionalPartial indices T
        (apm_m98a04_translateReflect φ x) =
      T (apm_m98a04_translateReflect
        (apm_m98a04_partialListTF indices φ) x) := by
  rw [apm_m98a04_distributionalPartial]
  change (-1 : ℝ) ^ indices.length *
      T (apm_m98a04_partialListCLM indices
        (apm_m98a04_translateReflect φ x)) = _
  rw [apm_m98a04_partialListCLM_apply,
    apm_m98a04_partialListTF_translateReflect]
  rw [map_smul]
  change (-1 : ℝ) ^ indices.length *
      ((-1 : ℝ) ^ indices.length *
        T (apm_m98a04_translateReflect
          (apm_m98a04_partialListTF indices φ) x)) = _
  rw [← mul_assoc, ← pow_add]
  simp [two_mul]

/-- Once scalar translation smoothness and its derivative formula are known,
the remaining convolution identity follows from the compiled reflection-sign
calculation above. -/
lemma apm_m98a04_translation_bridge_of_scalar_derivatives {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n)
    (hsmooth : ContDiff ℝ ∞
      (fun x => T (apm_m98a04_translateReflect φ x)))
    (hderiv : ∀ indices : List (Fin n),
      apm_m98a04_partialList indices
          (fun x => T (apm_m98a04_translateReflect φ x)) =
        fun x => apm_m98a04_distributionalPartial indices T
          (apm_m98a04_translateReflect φ x)) :
    ContDiff ℝ ∞ (fun x => T (apm_m98a04_translateReflect φ x)) ∧
      ∀ indices : List (Fin n),
        apm_m98a04_partialList indices
            (fun x => T (apm_m98a04_translateReflect φ x)) =
          (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) ∧
        (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) =
          (fun x => T (apm_m98a04_translateReflect
            (apm_m98a04_partialListTF indices φ) x)) := by
  refine ⟨hsmooth, fun indices => ⟨hderiv indices, ?_⟩⟩
  funext x
  exact apm_m98a04_distributionalPartial_translateReflect indices T φ x

/-- It suffices analytically to prove smoothness and the one-coordinate
derivative rule for every test function; all iterated formulas then follow by
induction. -/
lemma apm_m98a04_translation_bridge_of_first_derivative {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n)
    (hsmooth : ∀ ψ : apm_m98a04_TF n,
      ContDiff ℝ ∞ (fun x => T (apm_m98a04_translateReflect ψ x)))
    (hfirst : ∀ (ψ : apm_m98a04_TF n) (i : Fin n)
        (x : EuclideanSpace ℝ (Fin n)),
      fderiv ℝ (fun z => T (apm_m98a04_translateReflect ψ z)) x
          (EuclideanSpace.single i 1) =
        T (apm_m98a04_translateReflect
          (apm_m98a04_partialListTF [i] ψ) x)) :
    ContDiff ℝ ∞ (fun x => T (apm_m98a04_translateReflect φ x)) ∧
      ∀ indices : List (Fin n),
        apm_m98a04_partialList indices
            (fun x => T (apm_m98a04_translateReflect φ x)) =
          (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) ∧
        (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) =
          (fun x => T (apm_m98a04_translateReflect
            (apm_m98a04_partialListTF indices φ) x)) := by
  apply apm_m98a04_translation_bridge_of_scalar_derivatives T φ (hsmooth φ)
  intro indices
  have hiter : apm_m98a04_partialList indices
        (fun x => T (apm_m98a04_translateReflect φ x)) =
      fun x => T (apm_m98a04_translateReflect
        (apm_m98a04_partialListTF indices φ) x) := by
    induction indices with
    | nil => rfl
    | cons i is ih =>
        simp only [apm_m98a04_partialList]
        rw [ih]
        funext x
        simpa [apm_m98a04_partialListTF] using
          hfirst (apm_m98a04_partialListTF is φ) i x
  rw [hiter]
  funext x
  exact (apm_m98a04_distributionalPartial_translateReflect indices T φ x).symm

lemma apm_m98a04_translation_analytic_zero {n : ℕ}
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) :
    ContDiff ℝ ∞ (fun x =>
      (0 : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
        (apm_m98a04_translateReflect φ x)) ∧
      ∀ indices : List (Fin n),
        apm_m98a04_partialList indices
            (fun x =>
              (0 : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
                (apm_m98a04_translateReflect φ x)) =
          (fun x => apm_m98a04_distributionalPartial indices 0
            (apm_m98a04_translateReflect φ x)) ∧
        (fun x => apm_m98a04_distributionalPartial indices 0
            (apm_m98a04_translateReflect φ x)) =
          (fun x =>
            (0 : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
              (apm_m98a04_translateReflect
                (apm_m98a04_partialListTF indices φ) x)) := by
  constructor
  · simpa using (contDiff_const : ContDiff ℝ ∞
      (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)))
  · intro indices
    constructor
    · rw [show (fun x =>
          (0 : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
            (apm_m98a04_translateReflect φ x)) = 0 by rfl,
        apm_m98a04_partialList_zero]
      funext x
      change 0 = (-1 : ℝ) ^ indices.length * (0 : ℝ)
      simp
    · funext x
      change (-1 : ℝ) ^ indices.length * (0 : ℝ) = 0
      simp

/-- A single compact set containing all reflected translates whose translation
parameter lies in the closed unit ball about `x₀`.  This is the fixed stage of
the LF space on which the remaining differentiability argument takes place. -/
noncomputable def apm_m98a04_translationCompact {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Compacts (EuclideanSpace ℝ (Fin n)) :=
  ⟨-tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ) + Metric.closedBall x₀ 1,
    φ.hasCompactSupport.isCompact.neg.add (isCompact_closedBall x₀ 1)⟩

/-- A reflected translate, bundled in one fixed compact-support stage.  The
parameter is restricted to a closed unit ball only to make that common stage
available; its underlying function is still exactly `y ↦ φ (x-y)`. -/
noncomputable def apm_m98a04_translateReflectStage {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ : EuclideanSpace ℝ (Fin n))
    (x : Metric.closedBall x₀ (1 : ℝ)) :
    ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin n)) ℝ ⊤
      (apm_m98a04_translationCompact φ x₀) :=
  ContDiffMapSupportedIn.of_support_subset
    (φ.contDiff.comp (contDiff_const.sub contDiff_id)) (by
      intro y hy
      have hxy : x.1 - y ∈ tsupport
          (φ : EuclideanSpace ℝ (Fin n) → ℝ) :=
        subset_closure (by simpa [Function.mem_support] using hy)
      change y ∈ -tsupport (φ : EuclideanSpace ℝ (Fin n) → ℝ) +
        Metric.closedBall x₀ 1
      refine ⟨-(x.1 - y), ?_, x.1, x.2, ?_⟩
      · simpa using hxy
      · abel)

@[simp] lemma apm_m98a04_translateReflectStage_apply {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ : EuclideanSpace ℝ (Fin n))
    (x : Metric.closedBall x₀ (1 : ℝ))
    (y : EuclideanSpace ℝ (Fin n)) :
    apm_m98a04_translateReflectStage φ x₀ x y = φ (x.1 - y) := rfl

/-- Inclusion of the fixed-stage translate into the LF test-function space is
the canonical reflected translate. -/
lemma apm_m98a04_ofSupportedIn_translateReflectStage {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ : EuclideanSpace ℝ (Fin n))
    (x : Metric.closedBall x₀ (1 : ℝ)) :
    TestFunction.ofSupportedIn (by simp :
        (apm_m98a04_translationCompact φ x₀ :
          Set (EuclideanSpace ℝ (Fin n))) ⊆
            (⊤ : Opens (EuclideanSpace ℝ (Fin n))))
      (apm_m98a04_translateReflectStage φ x₀ x) =
        apm_m98a04_translateReflect φ x.1 := by
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext y
  rfl

/-- On the unit neighborhood of `x₀`, evaluation by a distribution factors
through the continuous restriction of that distribution to the fixed compact
stage constructed above. -/
lemma apm_m98a04_distribution_translateReflect_factor_stage {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n) (x₀ : EuclideanSpace ℝ (Fin n))
    (x : Metric.closedBall x₀ (1 : ℝ)) :
    T (apm_m98a04_translateReflect φ x.1) =
      (T.comp (TestFunction.ofSupportedInCLM ℝ (by simp :
        (apm_m98a04_translationCompact φ x₀ :
          Set (EuclideanSpace ℝ (Fin n))) ⊆
            (⊤ : Opens (EuclideanSpace ℝ (Fin n))))))
        (apm_m98a04_translateReflectStage φ x₀ x) := by
  rw [← apm_m98a04_ofSupportedIn_translateReflectStage φ x₀ x]
  rfl

/-- The analytic bridge in dimension zero.  Here the Euclidean parameter
space is a singleton, hence every translated pairing is constant. -/
theorem apm_m98a04_translation_analytic_bridge_zero_dim
    (T : Distribution
      (⊤ : Opens (EuclideanSpace ℝ (Fin 0))) ℝ ⊤)
    (φ : apm_m98a04_TF 0) :
    ContDiff ℝ ∞ (fun x => T (apm_m98a04_translateReflect φ x)) ∧
      ∀ indices : List (Fin 0),
        apm_m98a04_partialList indices
            (fun x => T (apm_m98a04_translateReflect φ x)) =
          (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) ∧
        (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) =
          (fun x => T (apm_m98a04_translateReflect
            (apm_m98a04_partialListTF indices φ) x)) := by
  apply apm_m98a04_translation_bridge_of_first_derivative T φ
  · intro ψ
    have hconst : (fun x : EuclideanSpace ℝ (Fin 0) =>
        T (apm_m98a04_translateReflect ψ x)) =
        fun _ => T (apm_m98a04_translateReflect ψ 0) := by
      funext x
      rw [Subsingleton.elim x 0]
    rw [hconst]
    exact contDiff_const
  · intro ψ i
    exact Fin.elim0 i

/-! These are the two independent scalar consequences of the fixed-compact
stage estimates above.  They deliberately expose exactly what
`apm_m98a04_translation_bridge_of_first_derivative` consumes. -/

/-- A locally defined fixed-stage translation.  Outside the closed unit ball
we use zero; this does not affect continuity or derivatives at `x₀`. -/
noncomputable def apm_m98a04_translateReflectStageLocal {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ x : EuclideanSpace ℝ (Fin n)) :
    ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin n)) ℝ ⊤
      (apm_m98a04_translationCompact φ x₀) := by
  classical
  exact if hx : x ∈ Metric.closedBall x₀ (1 : ℝ) then
      apm_m98a04_translateReflectStage φ x₀ ⟨x, hx⟩
    else 0

/-- The test function obtained by differentiating `φ` in direction `v`. -/
noncomputable def apm_m98a04_directionalTF {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (φ : apm_m98a04_TF n) :
    apm_m98a04_TF n :=
  ∑ i : Fin n, (v i) • apm_m98a04_partialListTF [i] φ

noncomputable def apm_m98a04_translationStageToTest {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin n)) ℝ ⊤
        (apm_m98a04_translationCompact φ x₀) →L[ℝ]
      apm_m98a04_TF n :=
  TestFunction.ofSupportedInCLM ℝ (by simp :
    (apm_m98a04_translationCompact φ x₀ :
      Set (EuclideanSpace ℝ (Fin n))) ⊆
        (⊤ : Opens (EuclideanSpace ℝ (Fin n))))

/-- Shared topology fact 1: reflected translation is continuous into one
fixed compact-support stage near its base point. -/
theorem apm_m98a04_translateReflectStageLocal_continuousAt {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (apm_m98a04_translateReflectStageLocal φ x₀) x₀ := by
  let T := ContinuousLinearMap.pi
    (ContDiffMapSupportedIn.structureMapCLM ℝ (⊤ : ℕ∞) :
      ∀ i : ℕ, ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin n)) ℝ ⊤
        (apm_m98a04_translationCompact φ x₀) →L[ℝ]
          BoundedContinuousFunction (EuclideanSpace ℝ (Fin n))
            ((EuclideanSpace ℝ (Fin n)) [×i]→L[ℝ] ℝ))
  apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ).toIsUniformInducing.isInducing.continuousAt_iff.mpr
  rw [continuousAt_pi]
  intro i
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun z => φ (-z)
  let f := iteratedFDeriv ℝ i g
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    φ.contDiff.comp contDiff_neg
  have hf : Continuous f :=
    hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hgc : HasCompactSupport g := by
    exact φ.hasCompactSupport.comp_homeomorph
      (Homeomorph.neg (EuclideanSpace ℝ (Fin n)))
  have hfc : HasCompactSupport f := hgc.iteratedFDeriv i
  have hc : ContinuousAt (fun x : EuclideanSpace ℝ (Fin n) =>
      ConstructionTargets.TestFunctionTranslation.tftBCFOfCompactSupport
        (fun y => f (-x + y))
        (hf.comp (continuous_const.add continuous_id))
        (hfc.comp_homeomorph (Homeomorph.addLeft (-x)))) x₀ := by
    have ht := (ConstructionTargets.TestFunctionTranslation.tft_translate_bcf_continuous
      f hf hfc).continuousAt.comp
      (continuousAt_neg (x := x₀))
    simpa only [Function.comp_apply] using ht
  apply hc.congr_of_eventuallyEq
  filter_upwards [Metric.closedBall_mem_nhds x₀ zero_lt_one] with x hx
  apply BoundedContinuousFunction.ext
  intro y
  change (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i
      (apm_m98a04_translateReflectStageLocal φ x₀ x)) y = _
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  have heq : (apm_m98a04_translateReflectStageLocal φ x₀ x :
      EuclideanSpace ℝ (Fin n) → ℝ) = fun z => g (-x + z) := by
    funext z
    simp [apm_m98a04_translateReflectStageLocal, hx, g,
      sub_eq_add_neg, add_comm]
  rw [heq, iteratedFDeriv_comp_add_left]
  rfl

/-- Shared topology fact 2: directional difference quotients of reflected
translations converge in the same fixed compact-support stage. -/
noncomputable def apm_m98a04_translateReflectStageLocal_difference_quotient_aux_reflect
    {n : ℕ} (φ : apm_m98a04_TF n) : apm_m98a04_TF n :=
  TestFunction.mk (fun y => φ (-y))
    (φ.contDiff.comp contDiff_neg)
    (φ.hasCompactSupport.comp_homeomorph (Homeomorph.neg _))
    (by simp)

lemma apm_m98a04_translateReflectStageLocal_difference_quotient_aux_translate
    {n : ℕ} (φ : apm_m98a04_TF n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ConstructionTargets.TestFunctionTranslation.tftTranslate (-x)
        (apm_m98a04_translateReflectStageLocal_difference_quotient_aux_reflect φ) =
      apm_m98a04_translateReflect φ x := by
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext y
  simp [ConstructionTargets.TestFunctionTranslation.tftTranslate,
    apm_m98a04_translateReflectStageLocal_difference_quotient_aux_reflect]
  congr 1
  abel

lemma apm_m98a04_translateReflectStageLocal_difference_quotient_aux_local_to_test
    {n : ℕ} (φ : apm_m98a04_TF n) (x₀ x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.closedBall x₀ (1 : ℝ)) :
    apm_m98a04_translationStageToTest φ x₀
        (apm_m98a04_translateReflectStageLocal φ x₀ x) =
      apm_m98a04_translateReflect φ x := by
  simp only [apm_m98a04_translateReflectStageLocal, hx, dite_true]
  exact apm_m98a04_ofSupportedIn_translateReflectStage φ x₀ ⟨x, hx⟩

/-- The limit: differentiating the reflected function in direction `-v` and translating by
`-x₀` is the reflected translate of the directional derivative `∑ vᵢ ∂ᵢ φ`. -/
lemma apm_m98a04_translateReflectStageLocal_difference_quotient_aux_limit_eq
    {n : ℕ} (φ : apm_m98a04_TF n) (x₀ v : EuclideanSpace ℝ (Fin n)) :
    ConstructionTargets.TestFunctionTranslation.tftTranslate (-x₀)
        (ConstructionTargets.TestFunctionTranslation.tftDirectional (-v) (apm_m98a04_translateReflectStageLocal_difference_quotient_aux_reflect φ)) =
      apm_m98a04_translateReflect (apm_m98a04_directionalTF v φ) x₀ := by
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext y
  simp only [ConstructionTargets.TestFunctionTranslation.tftTranslate_apply,
    ConstructionTargets.TestFunctionTranslation.tftDirectional_apply,
    apm_m98a04_translateReflect_apply]
  have hr : ⇑(apm_m98a04_translateReflectStageLocal_difference_quotient_aux_reflect φ) = fun z => φ (-z) := rfl
  rw [hr]
  have h1 := (φ.contDiff.differentiable (by simp) (x₀ - y)).hasFDerivAt
  have h1' : HasFDerivAt (⇑φ) (fderiv ℝ (⇑φ) (x₀ - y)) (-(-x₀ + y)) := by
    rw [show -(-x₀ + y) = x₀ - y by abel]; exact h1
  have key := h1'.comp (-x₀ + y) (hasFDerivAt_id (-x₀ + y)).neg
  rw [show (fun z => φ (-z)) = (⇑φ ∘ Neg.neg) from rfl, key.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, neg_neg]
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    simp
  simp [apm_m98a04_directionalTF, apm_m98a04_partialListTF_apply, apm_m98a04_partialList]
  have hcoe : ∀ (w : EuclideanSpace ℝ (Fin n)),
      (∑ x, v x • apm_m98a04_partialListTF [x] φ : apm_m98a04_TF n) w =
        ∑ x, v x * apm_m98a04_partialListTF [x] φ w := by
    intro w
    change (TestFunction.coeFnAddMonoidHom (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤
      (∑ x, v x • apm_m98a04_partialListTF [x] φ)) w = _
    rw [map_sum, Finset.sum_apply]
    rfl
  rw [hcoe]
  simp only [apm_m98a04_partialListTF_apply, apm_m98a04_partialList]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem apm_m98a04_translateReflectStageLocal_difference_quotient {n : ℕ}
    (φ : apm_m98a04_TF n) (x₀ v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun h : ℝ => apm_m98a04_translationStageToTest φ x₀
        (h⁻¹ • (apm_m98a04_translateReflectStageLocal φ x₀ (x₀ + h • v) -
          apm_m98a04_translateReflectStageLocal φ x₀ x₀)))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (apm_m98a04_translateReflect
        (apm_m98a04_directionalTF v φ) x₀)) := by
  have hlim := ConstructionTargets.TestFunctionTranslation.tftTranslate_difference_quotient
    (apm_m98a04_translateReflectStageLocal_difference_quotient_aux_reflect φ) (-x₀) (-v)
  rw [apm_m98a04_translateReflectStageLocal_difference_quotient_aux_limit_eq] at hlim
  refine hlim.congr' ?_
  have hc : Tendsto (fun h : ℝ => x₀ + h • v) (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds x₀) := by
    have : ContinuousAt (fun h : ℝ => x₀ + h • v) 0 := by fun_prop
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hc.eventually (Metric.closedBall_mem_nhds x₀ zero_lt_one)] with h hh
  rw [map_smul, map_sub, apm_m98a04_translateReflectStageLocal_difference_quotient_aux_local_to_test φ x₀ _ hh,
    apm_m98a04_translateReflectStageLocal_difference_quotient_aux_local_to_test φ x₀ _ (Metric.mem_closedBall_self zero_le_one),
    ← apm_m98a04_translateReflectStageLocal_difference_quotient_aux_translate, ← apm_m98a04_translateReflectStageLocal_difference_quotient_aux_translate]
  congr 3
  rw [neg_add, smul_neg]

/-- Scalar derivative extraction from an explicitly supplied fixed-stage
difference-quotient theorem. -/
theorem apm_m98a04_translation_pairing_fderiv_of_stage_dq {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n)
    (hdq : ∀ (x v : EuclideanSpace ℝ (Fin n)),
      Tendsto (fun h : ℝ => apm_m98a04_translationStageToTest φ x
          (h⁻¹ • (apm_m98a04_translateReflectStageLocal φ x (x + h • v) -
            apm_m98a04_translateReflectStageLocal φ x x)))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (apm_m98a04_translateReflect
          (apm_m98a04_directionalTF v φ) x)))
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => T (apm_m98a04_translateReflect φ z)) x
        (EuclideanSpace.single i 1) =
      T (apm_m98a04_translateReflect
        (apm_m98a04_partialListTF [i] φ) x) := by
  sorry

/-- Smoothness extraction by induction on derivative order, from supplied
fixed-stage continuity and difference-quotient facts for every test function. -/
theorem apm_m98a04_translation_pairing_contDiff_of_stage_facts {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n)
    (hcont : ∀ (ψ : apm_m98a04_TF n) (x : EuclideanSpace ℝ (Fin n)),
      ContinuousAt (apm_m98a04_translateReflectStageLocal ψ x) x)
    (hdq : ∀ (ψ : apm_m98a04_TF n) (x v : EuclideanSpace ℝ (Fin n)),
      Tendsto (fun h : ℝ => apm_m98a04_translationStageToTest ψ x
          (h⁻¹ • (apm_m98a04_translateReflectStageLocal ψ x (x + h • v) -
            apm_m98a04_translateReflectStageLocal ψ x x)))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (apm_m98a04_translateReflect
          (apm_m98a04_directionalTF v ψ) x))) :
    ContDiff ℝ ∞ (fun x => T (apm_m98a04_translateReflect φ x)) := by
  sorry

theorem apm_m98a04_translation_pairing_contDiff_of_pos_dim {n : ℕ}
    (hn : 0 < n)
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n) :
    ContDiff ℝ ∞ (fun x => T (apm_m98a04_translateReflect φ x)) := by
  exact apm_m98a04_translation_pairing_contDiff_of_stage_facts T φ
    (fun ψ x => apm_m98a04_translateReflectStageLocal_continuousAt ψ x)
    (fun ψ x v =>
      apm_m98a04_translateReflectStageLocal_difference_quotient ψ x v)

theorem apm_m98a04_translation_pairing_fderiv_single_of_pos_dim {n : ℕ}
    (hn : 0 < n)
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : apm_m98a04_TF n) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => T (apm_m98a04_translateReflect φ z)) x
        (EuclideanSpace.single i 1) =
      T (apm_m98a04_translateReflect
        (apm_m98a04_partialListTF [i] φ) x) := by
  exact apm_m98a04_translation_pairing_fderiv_of_stage_dq T φ
    (fun x v =>
      apm_m98a04_translateReflectStageLocal_difference_quotient φ x v) i x

theorem apm_m98a04_translation_analytic_bridge {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) :
    ContDiff ℝ ∞ (fun x => T (apm_m98a04_translateReflect φ x)) ∧
      ∀ indices : List (Fin n),
        apm_m98a04_partialList indices
            (fun x => T (apm_m98a04_translateReflect φ x)) =
          (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) ∧
        (fun x => apm_m98a04_distributionalPartial indices T
            (apm_m98a04_translateReflect φ x)) =
          (fun x => T (apm_m98a04_translateReflect
            (apm_m98a04_partialListTF indices φ) x)) := by
  cases n with
  | zero => exact apm_m98a04_translation_analytic_bridge_zero_dim T φ
  | succ n =>
      apply apm_m98a04_translation_bridge_of_first_derivative T φ
      · intro ψ
        exact apm_m98a04_translation_pairing_contDiff_of_pos_dim
          (Nat.succ_pos n) T ψ
      · intro ψ i x
        exact apm_m98a04_translation_pairing_fderiv_single_of_pos_dim
          (Nat.succ_pos n) T ψ i x

theorem apm_m98a04_distribution_convolution_bridge :
    ∀ (n : ℕ)
      (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
      (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤),
      ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
        apm_m98a04_IsConvolution T φ h ∧ ContDiff ℝ ∞ h ∧
        ∀ indices : List (Fin n),
          ∃ (DT : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
            (dφ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
            (hDT hφ : EuclideanSpace ℝ (Fin n) → ℝ),
            apm_m98a04_IsDistributionalPartial indices T DT ∧
            (∀ x, dφ x = apm_m98a04_partialList indices (φ : _ → ℝ) x) ∧
            apm_m98a04_IsConvolution DT φ hDT ∧
            apm_m98a04_IsConvolution T dφ hφ ∧
            apm_m98a04_partialList indices h = hDT ∧ hDT = hφ := by
  intro n T φ
  let h := fun x => T (apm_m98a04_translateReflect φ x)
  obtain ⟨hsmooth, hidentities⟩ :=
    apm_m98a04_translation_analytic_bridge T φ
  refine ⟨h, apm_m98a04_canonical_isConvolution T φ, hsmooth, ?_⟩
  intro indices
  let DT := apm_m98a04_distributionalPartial indices T
  let dφ := apm_m98a04_partialListTF indices φ
  let hDT := fun x => DT (apm_m98a04_translateReflect φ x)
  let hφ := fun x => T (apm_m98a04_translateReflect dφ x)
  refine ⟨DT, dφ, hDT, hφ,
    apm_m98a04_distributionalPartial_spec indices T, ?_,
    apm_m98a04_canonical_isConvolution DT φ,
    apm_m98a04_canonical_isConvolution T dφ, ?_⟩
  · intro x
    exact apm_m98a04_partialListTF_apply indices φ x
  · simpa [h, DT, dφ, hDT, hφ] using hidentities indices

theorem apm_m98a04 :
    (∀ (n : ℕ)
      (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
      (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤),
      ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
        apm_m98a04_IsConvolution T φ h ∧ ContDiff ℝ ∞ h ∧
        ∀ indices : List (Fin n),
          ∃ (DT : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
            (dφ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
            (hDT hφ : EuclideanSpace ℝ (Fin n) → ℝ),
            apm_m98a04_IsDistributionalPartial indices T DT ∧
            (∀ x, dφ x = apm_m98a04_partialList indices (φ : _ → ℝ) x) ∧
            apm_m98a04_IsConvolution DT φ hDT ∧
            apm_m98a04_IsConvolution T dφ hφ ∧
            apm_m98a04_partialList indices h = hDT ∧ hDT = hφ) ∧
    (∀ x : ℝ,
      ∫ y in (0 : ℝ)..(2 * Real.pi),
        Real.sin y * Real.cos (x - y) = Real.pi * Real.sin x) := by
  constructor
  · exact apm_m98a04_distribution_convolution_bridge
  · intro x
    have hintegrand :
        (fun y : ℝ ↦ Real.sin y * Real.cos (x - y)) =
          fun y ↦ Real.cos x * (Real.sin y * Real.cos y) +
            Real.sin x * Real.sin y ^ 2 := by
      funext y
      rw [Real.cos_sub]
      ring
    rw [hintegrand, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      simp
      ring
    · exact (by fun_prop : Continuous fun y : ℝ ↦
        Real.cos x * (Real.sin y * Real.cos y)).intervalIntegrable 0 (2 * Real.pi)
    · exact (by fun_prop : Continuous fun y : ℝ ↦
        Real.sin x * Real.sin y ^ 2).intervalIntegrable 0 (2 * Real.pi)

#print axioms apm_m98a04
