import Mathlib

/-!
# APM t91A08

## Statement repairs

None.

## Encoding questions

The torus and its integer-linear self-map are concrete: on
`Circle × Circle`, the matrix `[[5,2],[4,3]]` acts by
`(z,w) ↦ (z⁵w²,z⁴w³)`. Mathlib does not package integration and pullback of
differential forms on this quotient manifold in one usable interface, so the
type of smooth two-forms, descent of the explicit alternating form, pullback,
and oriented integral are isolated as typed primitives. Homotopy is native.
-/

abbrev apm_t91A08_Torus := Circle × Circle
abbrev apm_t91A08_R2 := EuclideanSpace ℝ (Fin 2)

/-- The explicit alternating form `3 dx ∧ dy` on `ℝ²`. -/
def apm_t91A08_alpha (u v : apm_t91A08_R2) : ℝ :=
  3 * (u 0 * v 1 - u 1 * v 0)

/-- Smooth real two-forms on the oriented two-torus. -/
opaque apm_t91A08_TwoForm : Type

axiom apm_t91A08_twoFormNonempty : Nonempty apm_t91A08_TwoForm

noncomputable instance : Inhabited apm_t91A08_TwoForm :=
  ⟨Classical.choice apm_t91A08_twoFormNonempty⟩

/-- A torus form descends from the indicated translation-invariant form on `ℝ²`. -/
opaque apm_t91A08_IsInduced
    (beta : apm_t91A08_TwoForm)
    (alpha : apm_t91A08_R2 → apm_t91A08_R2 → ℝ) : Prop

/-- Pullback of a torus two-form by a continuous torus self-map. -/
noncomputable opaque apm_t91A08_pullback
    (g : C(apm_t91A08_Torus, apm_t91A08_Torus))
    (beta : apm_t91A08_TwoForm) : apm_t91A08_TwoForm

/-- Oriented integral of a smooth two-form over the torus. -/
opaque apm_t91A08_integral (beta : apm_t91A08_TwoForm) : ℝ

/-- The torus map induced by `(x,y) ↦ (5x+2y,4x+3y)`. -/
noncomputable def apm_t91A08_g : C(apm_t91A08_Torus, apm_t91A08_Torus) :=
  ⟨fun z => (z.1 ^ 5 * z.2 ^ 2, z.1 ^ 4 * z.2 ^ 3), by fun_prop⟩

theorem apm_t91a08
    (beta : apm_t91A08_TwoForm)
    (hbeta : apm_t91A08_IsInduced beta apm_t91A08_alpha) :
    apm_t91A08_integral beta = 3 ∧
    apm_t91A08_integral (apm_t91A08_pullback apm_t91A08_g beta) = 21 ∧
    ¬ContinuousMap.Homotopic apm_t91A08_g
      (ContinuousMap.id apm_t91A08_Torus) := by
  sorry
