import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t00J04 — extending a cotangent vector to a closed one-form

The required global form is exhibited as the manifold differential `df` of a
smooth bump-supported function.  Its value at the chosen point is pinned to
the supplied cotangent vector.  Closedness is stated using the genuine
Euclidean exterior derivative in every manifold chart: the coordinate
one-form is the Fréchet derivative of the chart expression of `f`, and its
exterior derivative vanishes.

## Statement repairs

None.

## Encoding questions

Mathlib provides `extDerivFun f` for the manifold differential of a scalar
function, but no general exterior derivative of manifold one-form sections.
The chartwise predicate below is the standard concrete meaning of `d(df)=0`
using Mathlib's existing `extDeriv` API.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t00j04_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t00j04_I (n : ℕ) := 𝓘(ℝ, apm_t00j04_E n)

abbrev T00J04OneForm {n : ℕ} (X : Type)
    [TopologicalSpace X] [ChartedSpace (apm_t00j04_E n) X] :=
  (x : X) → TangentSpace (apm_t00j04_I n) x →L[ℝ] ℝ

/-- Chartwise `d(df)=0`, expressed using the actual exterior derivative of
the coordinate one-form. -/
def t00J04DifferentialIsClosed
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (apm_t00j04_E n) X]
    (f : X → ℝ) : Prop :=
  ∀ x : X,
    extDeriv
      (fun y : apm_t00j04_E n ↦
        (ContinuousAlternatingMap.ofSubsingleton ℝ (apm_t00j04_E n) ℝ
          (0 : Fin 1))
          (fderiv ℝ (fun z : apm_t00j04_E n ↦
            f ((extChartAt (apm_t00j04_I n) x).symm z)) y))
      (extChartAt (apm_t00j04_I n) x x) = 0

/-- The chart-linear germ realizes the prescribed covector at the basepoint.
This is reused from the completed pre-repair proof at commit `625b174`. -/
lemma apm_t00j04_mfderiv_chart_linear
    {n : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (apm_t00j04_E n) X]
    [IsManifold (apm_t00j04_I n) ∞ X]
    (p : X) (omega_p : TangentSpace (apm_t00j04_I n) p →L[ℝ] ℝ) :
    mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ)
      (fun x ↦ omega_p (extChartAt (apm_t00j04_I n) p x)) p = omega_p := by
  change mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ)
    (omega_p ∘ extChartAt (apm_t00j04_I n) p) p = omega_p
  have hcomp := mfderiv_comp (I := apm_t00j04_I n)
    (I' := 𝓘(ℝ, apm_t00j04_E n)) (I'' := 𝓘(ℝ, ℝ)) p
    ((omega_p.contMDiffAt (n := (1 : ℕ∞))).mdifferentiableAt (by norm_num))
    (mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source p))
  have homega : fderiv ℝ (omega_p : apm_t00j04_E n → ℝ)
      (extChartAt (apm_t00j04_I n) p p) = omega_p :=
    omega_p.hasFDerivAt.fderiv
  rw [mfderiv_extChartAt_self] at hcomp
  apply hcomp.trans
  ext v
  rw [mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg (fun L : apm_t00j04_E n →L[ℝ] ℝ ↦ L v) homega

lemma apm_t00j04_differential_isClosed_of_contMDiff
    {n : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (apm_t00j04_E n) X]
    [IsManifold (apm_t00j04_I n) ∞ X]
    {f : X → ℝ} (hf : ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ f) :
    t00J04DifferentialIsClosed (n := n) f := by
  intro x
  let F : apm_t00j04_E n → ℝ := fun z =>
    f ((extChartAt (apm_t00j04_I n) x).symm z)
  let alpha : apm_t00j04_E n →
      apm_t00j04_E n [⋀^Fin 0]→L[ℝ] ℝ := fun y =>
    ContinuousAlternatingMap.constOfIsEmpty ℝ (apm_t00j04_E n) (Fin 0) (F y)
  have halpha :
      (fun y : apm_t00j04_E n ↦
        (ContinuousAlternatingMap.ofSubsingleton ℝ (apm_t00j04_E n) ℝ
          (0 : Fin 1)) (fderiv ℝ F y)) = extDeriv alpha := by
    funext y
    exact (extDeriv_constOfIsEmpty F y).symm
  change extDeriv
      (fun y : apm_t00j04_E n ↦
        (ContinuousAlternatingMap.ofSubsingleton ℝ (apm_t00j04_E n) ℝ
          (0 : Fin 1)) (fderiv ℝ F y))
      (extChartAt (apm_t00j04_I n) x x) = 0
  rw [halpha]
  apply extDeriv_extDeriv_apply
  · have hchart : ContDiffAt ℝ ∞ F (extChartAt (apm_t00j04_I n) x x) := by
      have h := (contMDiffAt_iff.mp (hf.contMDiffAt (x := x))).2
      simpa [F, Function.comp_def] using h
    exact ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ
      (apm_t00j04_E n) ℝ (Fin 0)).contDiff.comp_contDiffAt _ hchart)
  · rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (ENat.coe_lt_top 2).le

theorem apm_t00j04
    {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t00j04_E n) X]
    [IsManifold (apm_t00j04_I n) ∞ X]
    (p : X)
    (omega_p : TangentSpace (apm_t00j04_I n) p →L[ℝ] ℝ)
    (homega_p : omega_p ≠ 0) :
    ∃ (f : X → ℝ) (omega : T00J04OneForm (n := n) X),
      ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x : X, omega x = extDerivFun f x) ∧
      omega p = omega_p ∧
      t00J04DifferentialIsClosed (n := n) f := by
  let b : SmoothBumpFunction (apm_t00j04_I n) p := Classical.choice inferInstance
  -- Re-bundle on the explicit Euclidean model, as in the completed proof at
  -- commit `625b174`, to avoid the tangent/model module-instance diamond.
  let omegaE : apm_t00j04_E n →L[ℝ] ℝ :=
    { toFun := omega_p
      map_add' := omega_p.map_add
      map_smul' := omega_p.map_smul
      cont := omega_p.continuous }
  let g : X → ℝ := fun x ↦ omegaE (extChartAt (apm_t00j04_I n) p x)
  let f : X → ℝ := fun x ↦ b x * g x
  have hf : ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ f := by
    change ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ (fun x ↦ b x • g x)
    apply b.contMDiff_smul
    exact omegaE.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
  let omega : T00J04OneForm (n := n) X := fun x ↦ extDerivFun f x
  refine ⟨f, omega, hf, fun _ ↦ rfl, ?_,
    apm_t00j04_differential_isClosed_of_contMDiff hf⟩
  have heq : f =ᶠ[nhds p] g := by
    filter_upwards [b.eventuallyEq_one] with x hx
    simp [f, hx]
  change mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ) f p = omega_p
  rw [heq.mfderiv_eq]
  change mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ)
    (fun x ↦ omega_p (extChartAt (apm_t00j04_I n) p x)) p = omega_p
  exact apm_t00j04_mfderiv_chart_linear p omega_p
