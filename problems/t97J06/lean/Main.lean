import Mathlib

/-! # APM t97J06: a degree-zero, non-null-homotopic torus map

## Statement repairs

The printed assertion
`hat f (x + n, y + m) = hat f (x, y)` is false as an equality in `ℝ²`:
the second coordinate changes by the integer `n + m`.  The intended and
sufficient assertion is equivariance modulo `ℤ²`, so that the displayed lift
descends to `ℝ² / ℤ²`.  The map below denotes that quotient-induced map.

## Encoding question

Mathlib does not currently package the oriented degree and null-homotopy API
for this concrete quotient torus in a form suitable for a statement-only
file.  The quotient torus, the map induced by the printed lift, its degree,
and null-homotopy predicate are retained as explicitly typed placeholders.
The theorem states both requested conclusions about that map, rather than
replacing it by its homology matrix.
-/

open CategoryTheory

def t97J06Torus : TopCat := by sorry

/-- The torus self-map induced modulo `ℤ²` by
`(x,y) ↦ (sin (2πx + 4πy), x+y)`. -/
def t97J06Map : t97J06Torus ⟶ t97J06Torus := by sorry

def t97J06Degree (f : t97J06Torus ⟶ t97J06Torus) : ℤ := by sorry

def IsT97J06NullHomotopic (f : t97J06Torus ⟶ t97J06Torus) : Prop := by sorry

theorem apm_t97j06 :
    t97J06Degree t97J06Map = 0 ∧
    ¬IsT97J06NullHomotopic t97J06Map := by
  sorry
