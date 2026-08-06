import Mathlib

/-! # APM m94J06: Fréchet differentiability of operator inversion

## Statement repairs

The source's `GL(x)` and `T ∈ (X)` are typographical errors for `GL(X)` and
`T ∈ B(X)` respectively.
-/

noncomputable section

def m94J06GL (𝕜 X : Type*)
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    Set (X →L[𝕜] X) :=
  {T | IsUnit T}

def m94J06Inverse (𝕜 X : Type*)
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] X) : X →L[𝕜] X := by
  classical
  exact if h : IsUnit T then ((h.unit)⁻¹ : (X →L[𝕜] X)ˣ) else 0

theorem apm_m94j06
    (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] :
    DifferentiableOn 𝕜 (m94J06Inverse 𝕜 X) (m94J06GL 𝕜 X) := by
  simpa [m94J06Inverse, m94J06GL, Ring.inverse] using
    (differentiableOn_inverse (𝕜 := 𝕜) (R := X →L[𝕜] X))
