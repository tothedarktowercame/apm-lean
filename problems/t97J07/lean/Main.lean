import Mathlib

/-! # APM t97J07: Lefschetz data for a projective linear map

## Statement repairs

The source alternates between `g` and `hat g`.  Here `hat g` denotes the
linear map `diag(1,1,3)` on `ℂ³`, while `t97J07Map` denotes its induced map
`g` on `ℂP²`.

## Encoding question

Mathlib does not yet provide `ℂP²` as a smooth manifold together with clean
fixed-submanifold Lefschetz contributions.  The genuine projective space,
its projective line, the induced map, local Lefsche contributions, and Euler
characteristic are therefore retained as typed placeholders.  The fixed set
is nevertheless stated as an actual set equality: a fixed projective line
and one disjoint isolated point.
-/

open CategoryTheory

def t97J07ComplexProjectiveTwo : TopCat := by sorry

/-- Projectivization of `diag(1,1,3)`. -/
def t97J07Map :
    t97J07ComplexProjectiveTwo ⟶ t97J07ComplexProjectiveTwo := by sorry

/-- The projective line `{[z₀:z₁:0]}`. -/
def t97J07FixedLine : Set t97J07ComplexProjectiveTwo := by sorry

/-- The isolated projective point `[0:0:1]`. -/
def t97J07IsolatedPoint : t97J07ComplexProjectiveTwo := by sorry

def t97J07LocalLefschetzNumberOfLine : ℤ := by sorry
def t97J07LocalLefschetzNumberOfPoint : ℤ := by sorry
def t97J07EulerCharacteristic : ℤ := by sorry

theorem apm_t97j07 :
    {x : t97J07ComplexProjectiveTwo | t97J07Map x = x} =
        t97J07FixedLine ∪ {t97J07IsolatedPoint} ∧
    t97J07IsolatedPoint ∉ t97J07FixedLine ∧
    t97J07LocalLefschetzNumberOfLine = 2 ∧
    t97J07LocalLefschetzNumberOfPoint = 1 ∧
    t97J07EulerCharacteristic = 3 := by
  sorry
