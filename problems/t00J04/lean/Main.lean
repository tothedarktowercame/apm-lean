import Mathlib

/-!
# APM t00J04

## Statement repairs

The former conclusion used opaque predicates for smooth, closed, and exact
one-forms.  It is replaced by the stronger concrete construction from the
source proof: a global smooth real function with the prescribed derivative at
`p`.  Its manifold differential is the required smooth exact, hence closed,
one-form.  `SecondCountableTopology` makes explicit the standard countability
convention in the term “smooth manifold,” needed for global bump functions.
No source claim is changed.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t00j04_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t00j04_I (n : ℕ) := 𝓘(ℝ, apm_t00j04_E n)

/-- The chart-linear germ realizes the prescribed covector at the basepoint. -/
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

theorem apm_t00j04
    {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t00j04_E n) X]
    [IsManifold (apm_t00j04_I n) ∞ X]
    (p : X)
    (omega_p : TangentSpace (apm_t00j04_I n) p →L[ℝ] ℝ)
    (homega_p : omega_p ≠ 0) :
    ∃ f : X → ℝ,
      ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ f ∧
      mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ) f p = omega_p := by
  /-
  CLOSER HOP 2 closure. The local differential problem was closed
  by `apm_t00j04_mfderiv_chart_linear`: the germ
  `x ↦ omega_p (extChartAt I p x)` has manifold derivative exactly `omega_p`
  at `p`.  The proof uses `mfderiv_comp`, the ordinary Frechet derivative of a
  continuous linear map, and `mfderiv_extChartAt_self`.

  Mathlib's `SmoothBumpFunction` API supplies all remaining mathematical
  ingredients: a bump centered at `p`, `eventuallyEq_one`, support contained in
  the chart source, and `SmoothBumpFunction.contMDiff_smul` for globalization.
  The remaining instance diamond between the printed
  `TangentSpace (apm_t00j04_I n) p` module structure carried by `omega_p` and
  the definitionally equal Euclidean model is routed around by `omegaE`: the
  same underlying function is re-bundled with the explicit Euclidean module
  structure, reusing `omega_p`'s additivity, scalar compatibility, and
  continuity. This makes `omegaE.contMDiff` applicable. Multiplication by a
  chosen `SmoothBumpFunction` globalizes the germ, while
  `eventuallyEq_one.mfderiv_eq` and `apm_t00j04_mfderiv_chart_linear` recover
  the prescribed derivative at `p`.
  -/
  let b : SmoothBumpFunction (apm_t00j04_I n) p := Classical.choice inferInstance
  -- Re-bundle the tangent covector on the explicit Euclidean model to avoid
  -- the two definitionally equal but non-definitional module instances.
  let omegaE : apm_t00j04_E n →L[ℝ] ℝ :=
    { toFun := omega_p
      map_add' := omega_p.map_add
      map_smul' := omega_p.map_smul
      cont := omega_p.continuous }
  let g : X → ℝ := fun x ↦ omegaE (extChartAt (apm_t00j04_I n) p x)
  refine ⟨fun x ↦ b x * g x, ?_, ?_⟩
  · change ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ (fun x ↦ b x • g x)
    apply b.contMDiff_smul
    exact omegaE.contMDiff.comp_contMDiffOn contMDiffOn_extChartAt
  · have heq : (fun x ↦ b x * g x) =ᶠ[nhds p] g := by
      filter_upwards [b.eventuallyEq_one] with x hx
      simp [hx]
    rw [heq.mfderiv_eq]
    change mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ)
      (fun x ↦ omega_p (extChartAt (apm_t00j04_I n) p x)) p = omega_p
    exact apm_t00j04_mfderiv_chart_linear p omega_p
