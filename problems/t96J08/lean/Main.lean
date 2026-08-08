import Mathlib

/-!
# APM t96J08

## Statement repairs

None.

## Encoding questions

Mathlib does not currently bundle integration of differential forms over
oriented surfaces.  The specified upper hemisphere is therefore encoded by
its standard orientation-preserving parametrization over the closed unit disk.
The two-form itself, its exterior derivative, and exactness are encoded by
their concrete coordinate formulas, rather than by opaque placeholders.
-/

noncomputable section

open MeasureTheory

abbrev apm_t96j08_Point := EuclideanSpace ℝ (Fin 3)
abbrev apm_t96j08_DiskPoint := EuclideanSpace ℝ (Fin 2)

def apm_t96j08_omega
    (p u v : apm_t96j08_Point) : ℝ :=
  p 0 * (u 1 * v 2 - u 2 * v 1) +
  p 1 * (u 0 * v 2 - u 2 * v 0) +
  p 2 * (u 0 * v 1 - u 1 * v 0)

/-- The coordinate exterior derivative of the displayed two-form. -/
def apm_t96j08_domega
    (_p u v w : apm_t96j08_Point) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
  u 1 * (v 0 * w 2 - v 2 * w 0) +
  u 2 * (v 0 * w 1 - v 1 * w 0)

def apm_t96j08_IsClosed : Prop :=
  ∀ p u v w : apm_t96j08_Point, apm_t96j08_domega p u v w = 0

def apm_t96j08_dOneForm
    (η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ)
    (p u v : apm_t96j08_Point) : ℝ :=
  (fderiv ℝ (fun q => η q v) p) u -
    (fderiv ℝ (fun q => η q u) p) v

def apm_t96j08_IsExact : Prop :=
  ∃ η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ,
    ContDiff ℝ (⊤ : ℕ∞) (fun q : apm_t96j08_Point => η q) ∧
    ∀ p u v, apm_t96j08_dOneForm η p u v = apm_t96j08_omega p u v

def apm_t96j08_etaForm
    (η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ) :
    apm_t96j08_Point →
      apm_t96j08_Point [⋀^Fin 1]→L[ℝ] ℝ :=
  fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ _ (0 : Fin 1) (η p)

lemma apm_t96j08_extDeriv_etaForm_apply
    (η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (p u v : apm_t96j08_Point) :
    extDeriv (apm_t96j08_etaForm η) p ![u, v] =
      apm_t96j08_dOneForm η p u v := by
  have heta : ContDiff ℝ (⊤ : ℕ∞) (apm_t96j08_etaForm η) := by
    unfold apm_t96j08_etaForm
    exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := apm_t96j08_Point) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hη
  rw [extDeriv_apply (heta.differentiable (by simp) p)]
  simp [apm_t96j08_etaForm, apm_t96j08_dOneForm, Fin.removeNth, sub_eq_add_neg]

def apm_t96j08_upperHemisphere (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![q 0, q 1, 1 + Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

def apm_t96j08_paramTangentX (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![1, 0, -(q 0) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

def apm_t96j08_paramTangentY (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![0, 1, -(q 1) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

/-- Reflection of the parameter disk across the diagonal. -/
def apm_t96j08_swap (q : apm_t96j08_DiskPoint) : apm_t96j08_DiskPoint :=
  WithLp.toLp 2 ![q 1, q 0]

/-- The coordinate swap as a volume-preserving linear isometry. -/
def apm_t96j08_swapEquiv :
    apm_t96j08_DiskPoint ≃ₗᵢ[ℝ] apm_t96j08_DiskPoint :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

lemma apm_t96j08_swapEquiv_apply (q : apm_t96j08_DiskPoint) :
    apm_t96j08_swapEquiv q = apm_t96j08_swap q := by
  ext i
  fin_cases i <;>
    simp [apm_t96j08_swapEquiv, apm_t96j08_swap,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

@[simp] lemma apm_t96j08_swap_zero (q : apm_t96j08_DiskPoint) :
    apm_t96j08_swap q 0 = q 1 := by
  simp [apm_t96j08_swap, Matrix.cons_val_zero]

@[simp] lemma apm_t96j08_swap_one (q : apm_t96j08_DiskPoint) :
    apm_t96j08_swap q 1 = q 0 := by
  simp [apm_t96j08_swap, Matrix.cons_val_one]

lemma apm_t96j08_singularTerm_swap (q : apm_t96j08_DiskPoint) :
    ((apm_t96j08_swap q 0) ^ 2 - (apm_t96j08_swap q 1) ^ 2) /
        Real.sqrt
          (1 - (apm_t96j08_swap q 0) ^ 2 - (apm_t96j08_swap q 1) ^ 2) =
      -(((q 0) ^ 2 - (q 1) ^ 2) /
        Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)) := by
  simp
  ring_nf

def apm_t96j08_hemisphereIntegral : ℝ :=
  ∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1,
    apm_t96j08_omega (apm_t96j08_upperHemisphere q)
      (apm_t96j08_paramTangentX q) (apm_t96j08_paramTangentY q)

lemma apm_t96j08_pullback_eq (q : apm_t96j08_DiskPoint) :
    apm_t96j08_omega (apm_t96j08_upperHemisphere q)
        (apm_t96j08_paramTangentX q) (apm_t96j08_paramTangentY q) =
      1 + Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2) +
        ((q 0) ^ 2 - (q 1) ^ 2) /
          Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2) := by
  simp [apm_t96j08_omega, apm_t96j08_upperHemisphere,
    apm_t96j08_paramTangentX, apm_t96j08_paramTangentY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

lemma apm_t96j08_integral_singularTerm_eq_zero :
    (∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1,
      ((q 0) ^ 2 - (q 1) ^ 2) /
        Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)) = 0 := by
  let g : apm_t96j08_DiskPoint → ℝ := fun q ↦
    ((q 0) ^ 2 - (q 1) ^ 2) /
      Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)
  have hpre : apm_t96j08_swapEquiv ⁻¹' Metric.closedBall 0 1 =
      Metric.closedBall (0 : apm_t96j08_DiskPoint) 1 := by
    ext q
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  have h := apm_t96j08_swapEquiv.measurePreserving.setIntegral_preimage_emb
    apm_t96j08_swapEquiv.toMeasurableEquiv.measurableEmbedding g
    (Metric.closedBall (0 : apm_t96j08_DiskPoint) 1)
  rw [hpre] at h
  have hswap : ∀ q, g (apm_t96j08_swapEquiv q) = -g q := by
    intro q
    rw [apm_t96j08_swapEquiv_apply]
    exact apm_t96j08_singularTerm_swap q
  simp_rw [hswap, MeasureTheory.integral_neg] at h
  change (∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1, g q) = 0
  linarith

/-- The coordinate exterior derivative is nonzero on the standard oriented
basis. This is the direct obstruction to closedness. -/
lemma apm_t96j08_not_isClosed : ¬apm_t96j08_IsClosed := by
  intro h
  have hh := h 0 (WithLp.toLp 2 ![1, 0, 0])
    (WithLp.toLp 2 ![0, 1, 0]) (WithLp.toLp 2 ![0, 0, 1])
  norm_num [apm_t96j08_domega, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hh

/-- Why this unblocks `apm_t96j08`: after `apm_t96j08_pullback_eq` and
`apm_t96j08_integral_singularTerm_eq_zero`, this is the only nonconstant
contribution left in the hemisphere integral.  Together with the standard
area of the unit disk, it gives `π + 2π/3 = 5π/3`. -/
theorem apm_t96J08_bridge_radialDiskIntegral :
    (∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1,
      Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)) = 2 * Real.pi / 3 := by
  sorry

theorem apm_t96j08 :
    ¬apm_t96j08_IsClosed ∧
    ¬apm_t96j08_IsExact ∧
    apm_t96j08_hemisphereIntegral = 5 * Real.pi / 3 := by
  /-
  PARTIAL boundary (closer hop 1).

  `apm_t96j08_not_isClosed` now closes the first frozen conjunct by evaluating
  the concrete coordinate exterior derivative on the three standard basis
  vectors; it returns `1`, contradicting closedness.

  The exactness obstruction can in principle be routed through Mathlib's
  `extDeriv_extDeriv`: package the covector field `η` as a degree-one
  continuous alternating form, identify the custom `apm_t96j08_dOneForm`
  with `extDeriv η`, and use smoothness to obtain `d(dη)=0`, contradicting the
  same basis evaluation. That representation/identification bridge is not
  currently packaged in this encoding.

  Direct simplification of the pullback gives
  `1 + sqrt (1-x^2-y^2) + (x^2-y^2)/sqrt (1-x^2-y^2)` on the unit disk. The
  last term cancels under coordinate swap, the constant integrates to `π`,
  and the radial square-root term integrates to `2π/3`. Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets/`, sibling disk/polar artifacts
  (`a01A07`, `m99A02`, `m97A03`, `t92J09`), Mathlib's polar-coordinate and
  differential-form sources, and git history found no theorem transporting
  the `EuclideanSpace ℝ (Fin 2)` disk integral to the available complex polar
  formula or evaluating this singular boundary representative directly.
  Thus the exactness packaging and disk-integration bridges remain open; the
  frozen statement is unchanged.

  CLOSER HOP 2: the pullback simplification and the full antisymmetric
  cancellation now compile. `apm_t96j08_pullback_eq` proves the displayed
  three-term coordinate identity exactly. `apm_t96j08_swapEquiv` realizes
  coordinate exchange as a volume-preserving linear isometry of
  `EuclideanSpace ℝ (Fin 2)`, and
  `apm_t96j08_integral_singularTerm_eq_zero` uses Mathlib's
  `MeasurePreserving.setIntegral_preimage_emb` to show that the singular last
  term integrates to its own negative over the invariant closed disk, hence
  to zero. This bypasses the missing Euclidean-to-complex polar transport for
  the nonradial term.

  Renewed consultation of `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling
  `a01A07`, Mathlib's `LinearIsometryEquiv` Haar-measure API, radial integral
  sources, exterior-derivative sources, and git history leaves two independent
  bridges: evaluate the radial square-root disk integral as `2 * π / 3`, and
  package the custom exactness predicate into the `extDeriv_extDeriv`
  obstruction. The frozen statement remains unchanged.

  CLOSER HOP 3 closes the degree-one half of the exactness packaging.
  `apm_t96j08_etaForm` converts the frozen covector field to Mathlib's
  continuous alternating one-form, and
  `apm_t96j08_extDeriv_etaForm_apply` proves that its actual `extDeriv`
  evaluates exactly to `apm_t96j08_dOneForm` on every pair of vectors. This
  uses `ContinuousAlternatingMap.ofSubsingletonLIE` and the general
  `extDeriv_apply` formula, going beyond the prior representation-only
  search. The remaining exactness sub-bridge is now only to bundle the
  explicit trilinear coordinate formula `omega` as a continuous alternating
  two-form and identify its exterior derivative with `domega`; then
  `extDeriv_extDeriv` contradicts the compiled basis evaluation. The
  independent radial disk integral `2 * π / 3` remains open.
  -/
  sorry


#print axioms apm_t96j08
