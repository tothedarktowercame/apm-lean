import Mathlib

/-!
# APM a98J04 — symmetry of the real derivative of a holomorphic map

## Statement repairs

None.

## Encoding questions

None. Complex numbers are used directly as the real plane. The requested
matrix symmetry is encoded invariantly: the real derivative commutes with
multiplication by `I`, equivalently its real matrix has the form
`[[a, -b], [b, a]]`.
-/

noncomputable section

def apm_a98J04_HasComplexSymmetry (L : ℂ →L[ℝ] ℂ) : Prop :=
  ∀ z : ℂ, L (Complex.I * z) = Complex.I * L z

def apm_a98J04_g : ℂ → ℂ := fun z ↦ star z

def apm_a98J04_h : ℂ → ℂ := fun z ↦ z.re + (2 * z.im) * Complex.I

theorem apm_a98j04 :
    (∀ (f : ℂ → ℂ) (z : ℂ), DifferentiableAt ℂ f z →
      apm_a98J04_HasComplexSymmetry (fderiv ℝ f z)) ∧
    (∀ z : ℂ, ¬apm_a98J04_HasComplexSymmetry (fderiv ℝ apm_a98J04_g z)) ∧
    (∀ z : ℂ, ¬apm_a98J04_HasComplexSymmetry (fderiv ℝ apm_a98J04_h z)) := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    · intro f z hf
      rw [hf.fderiv_restrictScalars ℝ]
      intro w
      change (fderiv ℂ f z) (Complex.I * w) = Complex.I * (fderiv ℂ f z) w
      simpa only [smul_eq_mul] using map_smul (fderiv ℂ f z) Complex.I w
    constructor
    · intro z hs
      have hgderiv : fderiv ℝ apm_a98J04_g z = Complex.conjCLE := by
        exact Complex.conjCLE.fderiv
      rw [hgderiv] at hs
      have hi := hs 1
      simp at hi
      have him := congrArg Complex.im hi
      norm_num at him
    · intro z hs
      let Lh : ℂ →L[ℝ] ℂ :=
        Complex.ofRealCLM.comp Complex.reCLM +
          (2 * Complex.I) • (Complex.ofRealCLM.comp Complex.imCLM)
      have hhderiv : fderiv ℝ apm_a98J04_h z = Lh := by
        exact (show HasFDerivAt apm_a98J04_h Lh z by
          convert Lh.hasFDerivAt using 1
          ext w
          simp [apm_a98J04_h, Lh]
          ring).fderiv
      rw [hhderiv] at hs
      have hi := hs 1
      simp [Lh] at hi
