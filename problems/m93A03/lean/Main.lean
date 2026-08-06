import Mathlib

/-!
# APM m93A03: weak convergence plus norm convergence

## Statement repairs

None.

## Encoding questions

The source does not specify whether the Hilbert space is real or complex, so
the statement is made uniformly over either scalar field via `IsROrC`.
-/

open Filter

theorem apm_m93a03
    (𝕜 F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (f : ℕ → F) (f₀ : F)
    (hweak : ∀ g : F,
      Tendsto (fun n => inner 𝕜 (f n) g) atTop (nhds (inner 𝕜 f₀ g)))
    (hnorm : Tendsto (fun n => ‖f n‖) atTop (nhds ‖f₀‖)) :
    Tendsto f atTop (nhds f₀) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm_sq :
      Tendsto (fun n ↦ ‖f n‖ ^ 2) atTop (nhds (‖f₀‖ ^ 2)) :=
    hnorm.pow 2
  have hinner_re :
      Tendsto (fun n ↦ RCLike.re (inner 𝕜 (f n) f₀)) atTop
        (nhds (RCLike.re (inner 𝕜 f₀ f₀))) :=
    (RCLike.continuous_re.tendsto _).comp (hweak f₀)
  have hsq : Tendsto (fun n ↦ ‖f n - f₀‖ ^ 2) atTop (nhds 0) := by
    have hconst :
        Tendsto (fun _ : ℕ ↦ ‖f₀‖ ^ 2) atTop (nhds (‖f₀‖ ^ 2)) :=
      tendsto_const_nhds
    have h := (hnorm_sq.sub (hinner_re.const_mul 2)).add hconst
    convert h using 1
    · funext n
      exact norm_sub_sq (f n) f₀
    · simp [inner_self_eq_norm_sq_to_K]
      ring
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt
