import Mathlib

/-!
# APM t91A08

## Statement repairs

None.

## Encoding questions

The torus and its integer-linear self-map are concrete: on `Circle × Circle`,
the matrix `[[5,2],[4,3]]` acts by `(z,w) ↦ (z⁵w²,z⁴w³)`. Since the form is
translation-invariant, it is represented by its full alternating two-vector
function on `ℝ²`. Pullback applies the actual linear map to both vectors, and
integration over the oriented unit fundamental cell evaluates the form on the
standard oriented basis. Homotopy is native.
-/

abbrev apm_t91A08_Torus := Circle × Circle
abbrev apm_t91A08_R2 := EuclideanSpace ℝ (Fin 2)

/-- The explicit alternating form `3 dx ∧ dy` on `ℝ²`. -/
def apm_t91A08_alpha (u v : apm_t91A08_R2) : ℝ :=
  3 * (u 0 * v 1 - u 1 * v 0)

abbrev apm_t91A08_TwoForm := apm_t91A08_R2 → apm_t91A08_R2 → ℝ

/-- A torus form descends from the indicated translation-invariant form on `ℝ²`. -/
def apm_t91A08_IsInduced
    (beta : apm_t91A08_TwoForm)
    (alpha : apm_t91A08_R2 → apm_t91A08_R2 → ℝ) : Prop :=
  beta = alpha

def apm_t91A08_linearMap (u : apm_t91A08_R2) : apm_t91A08_R2 :=
  WithLp.toLp 2 ![5 * u 0 + 2 * u 1, 4 * u 0 + 3 * u 1]

/-- Pullback by the integer-linear map inducing `apm_t91A08_g`. -/
def apm_t91A08_pullback (beta : apm_t91A08_TwoForm) : apm_t91A08_TwoForm :=
  fun u v ↦ beta (apm_t91A08_linearMap u) (apm_t91A08_linearMap v)

/-- Integral of a translation-invariant form over the oriented unit cell. -/
noncomputable def apm_t91A08_integral (beta : apm_t91A08_TwoForm) : ℝ :=
  beta (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)

/-- The torus map induced by `(x,y) ↦ (5x+2y,4x+3y)`. -/
noncomputable def apm_t91A08_g : C(apm_t91A08_Torus, apm_t91A08_Torus) :=
  ⟨fun z => (z.1 ^ 5 * z.2 ^ 2, z.1 ^ 4 * z.2 ^ 3), by fun_prop⟩

theorem apm_t91a08
    (beta : apm_t91A08_TwoForm)
    (hbeta : apm_t91A08_IsInduced beta apm_t91A08_alpha) :
    apm_t91A08_integral beta = 3 ∧
    apm_t91A08_integral (apm_t91A08_pullback beta) = 21 ∧
    ¬ContinuousMap.Homotopic apm_t91A08_g
      (ContinuousMap.id apm_t91A08_Torus) := by
  sorry
