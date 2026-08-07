import Mathlib

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

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Interval

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
  · intro n T φ
    let h := fun x => T (apm_m98a04_translateReflect φ x)
    refine ⟨h, apm_m98a04_canonical_isConvolution T φ, ?_⟩
    /-
    Boundary (closer hop 1): the translated/reflected function has now been
    constructed as the bundled test function `apm_m98a04_translateReflect`,
    using `HasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)`.  The
    canonical pairing `h x = T (translateReflect φ x)` is also proved to meet
    `apm_m98a04_IsConvolution`, so pointwise test-function existence is closed.

    Closer hop 2 additionally constructs
    `apm_m98a04_partialListTF indices φ`, a genuine bundled test function for
    every iterated directional derivative requested by the frozen statement.
    Its pointwise specification is proved by induction using
    `TestFunction.fderivCLM` and `TestFunction.postcompCLM`.  Thus the `dφ`
    existence and compact-support bookkeeping are no longer part of the
    boundary.

    The remaining goal begins precisely at LF-topological smoothness:
    `ContDiff ℝ ∞ h`, followed by constructing iterated directional derivative
    test functions and distributional derivatives. Searches of Mathlib's
    `Analysis/Distribution/TestFunction.lean` found `fderivCLM` and
    `postcompCLM`, but no theorem that the parameter map
    `x ↦ translateReflect φ x` is differentiable into the inductive-limit test
    function space. Function-level convolution lemmas in siblings `a01A03`,
    `a03J03`, and `a96J02`, and `ConstructionTargets.YoungConvolution`, concern
    integrable functions and do not apply to an arbitrary distribution `T`.
    A future closure needs a local fixed-compact reduction for this parameter
    map.  It must then compose the resulting derivative identities with `T`
    and bundle the corresponding iterated distributional derivative `DT`.

    Closer hop 3 proves the base case
    `apm_m98a04_isDistributionalPartial_nil`: the empty multiindex has `T`
    itself as its distributional partial. Source inspection also confirms that
    Mathlib's general `Distribution.lean` exposes `mapCLM` but no directional
    derivative operator; the derivative instances found are for tempered
    distributions. Thus the nonempty-index construction must be developed
    locally together with the LF-topological translation smoothness theorem.
    -/
    sorry
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
