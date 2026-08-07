import Mathlib

/-!
# APM t94A08 — a smooth and a degenerate conic in complex projective space

## Statement repairs

The second item reuses the name `Σ₁` in its premise but asks to prove that
`Σ₂` is not a manifold.  The second displayed locus is therefore named `Σ₂`.

## Encoding questions

Mathlib provides complex projectivization. Smoothness of each projective
hypersurface is encoded by the equivalent regular-cone criterion: the complex
derivative of its actual homogeneous quadratic is nonzero at every nonzero
point of the affine cone. This detects the crossing singularity of the
reducible second conic.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t94a08_C3 := Fin 3 → ℂ
abbrev apm_t94a08_CP2 := Projectivization ℂ apm_t94a08_C3

def apm_t94a08_quadratic1 (z : apm_t94a08_C3) : ℂ :=
  z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2

def apm_t94a08_quadratic2 (z : apm_t94a08_C3) : ℂ :=
  z 1 ^ 2 + z 2 ^ 2

def apm_t94a08_sigma1 : Set apm_t94a08_CP2 :=
  {p | apm_t94a08_quadratic1 (Projectivization.rep p) = 0}

def apm_t94a08_sigma2 : Set apm_t94a08_CP2 :=
  {p | apm_t94a08_quadratic2 (Projectivization.rep p) = 0}

def apm_t94a08_IsRealTwoManifold
    (q : apm_t94a08_C3 → ℂ) (S : Set apm_t94a08_CP2) : Prop :=
  S = {p | q (Projectivization.rep p) = 0} ∧
    ∀ z : apm_t94a08_C3, z ≠ 0 → q z = 0 → fderiv ℂ q z ≠ 0

private def apm_t94a08_dquadratic1 (z : apm_t94a08_C3) :
    apm_t94a08_C3 →L[ℂ] ℂ :=
  (2 * z 0) • ContinuousLinearMap.proj 0 +
    (2 * z 1) • ContinuousLinearMap.proj 1 +
      (2 * z 2) • ContinuousLinearMap.proj 2

set_option maxHeartbeats 800000 in
private lemma apm_t94a08_hasFDerivAt_quadratic1 (z : apm_t94a08_C3) :
    HasFDerivAt apm_t94a08_quadratic1 (apm_t94a08_dquadratic1 z) z := by
  unfold apm_t94a08_quadratic1 apm_t94a08_dquadratic1
  convert ((((ContinuousLinearMap.proj 0 : apm_t94a08_C3 →L[ℂ] ℂ)).hasFDerivAt.pow 2).add
    ((ContinuousLinearMap.proj 1 : apm_t94a08_C3 →L[ℂ] ℂ).hasFDerivAt.pow 2)).add
      ((ContinuousLinearMap.proj 2 : apm_t94a08_C3 →L[ℂ] ℂ).hasFDerivAt.pow 2) using 1 <;>
    ext x <;> simp [mul_comm]

private lemma apm_t94a08_dquadratic1_ne_zero {z : apm_t94a08_C3} (hz : z ≠ 0) :
    apm_t94a08_dquadratic1 z ≠ 0 := by
  intro hd
  apply hz
  funext i
  fin_cases i
  · have h := congrArg (fun L : apm_t94a08_C3 →L[ℂ] ℂ => L (Pi.single 0 1)) hd
    simpa [apm_t94a08_dquadratic1] using h
  · have h := congrArg (fun L : apm_t94a08_C3 →L[ℂ] ℂ => L (Pi.single 1 1)) hd
    simpa [apm_t94a08_dquadratic1] using h
  · have h := congrArg (fun L : apm_t94a08_C3 →L[ℂ] ℂ => L (Pi.single 2 1)) hd
    simpa [apm_t94a08_dquadratic1] using h

private lemma apm_t94a08_fderiv_quadratic2_at_single_zero :
    fderiv ℂ apm_t94a08_quadratic2 (Pi.single 0 1) = 0 := by
  unfold apm_t94a08_quadratic2
  have h := ((ContinuousLinearMap.proj 1 : apm_t94a08_C3 →L[ℂ] ℂ).hasFDerivAt
      (x := Pi.single 0 1) |>.pow 2).add
    ((ContinuousLinearMap.proj 2 : apm_t94a08_C3 →L[ℂ] ℂ).hasFDerivAt
      (x := Pi.single 0 1) |>.pow 2)
  convert h.fderiv using 1 <;> ext x <;> simp

theorem apm_t94a08 :
    apm_t94a08_IsRealTwoManifold apm_t94a08_quadratic1 apm_t94a08_sigma1 ∧
      ¬apm_t94a08_IsRealTwoManifold apm_t94a08_quadratic2 apm_t94a08_sigma2 := by
  constructor
  · refine ⟨rfl, ?_⟩
    intro z hz _
    rw [(apm_t94a08_hasFDerivAt_quadratic1 z).fderiv]
    exact apm_t94a08_dquadratic1_ne_zero hz
  · rintro ⟨_, hregular⟩
    have hnonzero : (Pi.single 0 1 : apm_t94a08_C3) ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simpa using h0
    have hq : apm_t94a08_quadratic2 (Pi.single 0 1) = 0 := by
      simp [apm_t94a08_quadratic2]
    exact hregular (Pi.single 0 1) hnonzero hq
      apm_t94a08_fderiv_quadratic2_at_single_zero
