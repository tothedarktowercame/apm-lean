import Mathlib

/-!
# APM t97J06 — a self-map of the two-torus

The torus is represented concretely as `Circle × Circle`.  Under the usual
covering map `x ↦ exp (2πix)`, the map below is induced by

`(x,y) ↦ (sin (2πx + 4πy), x+y)`.

The degree is recorded by the standard integral of the determinant of the
Jacobian of this lift over a fundamental square.  Non-nullhomotopy is stated
using Mathlib's actual homotopy relation on continuous maps.

## Statement repairs

The printed assertion that the lift is literally periodic is false: translating
`(x,y)` by `(m,n) ∈ ℤ²` changes its second coordinate by `m+n`.  We use the
intended lattice-equivariance statement, equivalently the descended map on
`ℝ²/ℤ²`.
-/

open scoped Real

abbrev T97J06Torus := Circle × Circle

noncomputable def t97J06Map : C(T97J06Torus, T97J06Torus) where
  toFun p :=
    (Circle.exp (2 * Real.pi * Complex.im ((p.1 : ℂ) * (p.2 : ℂ) ^ 2)),
      p.1 * p.2)
  continuous_toFun := by fun_prop

theorem apm_t97j06 :
    (∀ x y : ℝ,
      t97J06Map
          (Circle.exp (2 * Real.pi * x), Circle.exp (2 * Real.pi * y)) =
        (Circle.exp (2 * Real.pi * Real.sin (2 * Real.pi * x + 4 * Real.pi * y)),
          Circle.exp (2 * Real.pi * (x + y)))) ∧
    (∫ x in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..1,
        Matrix.det !![2 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y),
            4 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y);
          (1 : ℝ), 1]) = 0 ∧
    (∀ q : T97J06Torus,
      ¬ ContinuousMap.Homotopic t97J06Map (ContinuousMap.const T97J06Torus q)) := by
  sorry
