import Mathlib

/-!
# APM t97J07 — Lefschetz data for a projective linear map

We use Mathlib's genuine projectivization of `ℂ³`.  The fixed component and
isolated fixed point are concrete subsets/points of that projectivization.
The affine parametrizations below pin the local representatives of the
projective map.  Thus the derivatives used for the local indices are derived
from the actual map rather than supplied as unrelated matrices.

## Statement repairs

The source alternates between `g` and `hat g`.  We reserve `t97J07Linear` for
the linear map `diag(1,1,3)` on `ℂ³` and `t97J07Map` for its projectivization.
-/

open scoped LinearAlgebra.Projectivization Matrix

abbrev T97J07CP2 := ℙ ℂ (Fin 3 → ℂ)

def t97J07Linear : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun z i := if i = 2 then 3 * z i else z i
  map_add' x y := by
    funext i
    by_cases hi : i = 2 <;> simp [hi, mul_add]
  map_smul' c x := by
    funext i
    by_cases hi : i = 2 <;> simp [hi]
    ring

noncomputable def t97J07Map : T97J07CP2 → T97J07CP2 := fun p ↦
  p.map t97J07Linear (by
    intro x y h
    funext i
    have hi := congrFun h i
    by_cases h2 : i = 2
    · subst i
      simpa [t97J07Linear] using
        (mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) hi)
    · simpa [t97J07Linear, h2] using hi)

def t97J07FixedLine : Set T97J07CP2 :=
  {p | p.rep 2 = 0}

noncomputable def t97J07IsolatedPoint : T97J07CP2 :=
  Projectivization.mk ℂ (Pi.single 2 1) (by
    intro h
    have := congrFun h 2
    simp at this)

/-- Affine coordinates normal to the fixed line, based at `[1:a:0]`. -/
noncomputable def t97J07LineChart (a u : ℂ) : T97J07CP2 :=
  Projectivization.mk ℂ ![1, a, u] (by
    intro h
    have := congrFun h 0
    simp at this)

/-- The local representative in the normal coordinate to the fixed line. -/
def t97J07LineLocal (u : ℂ) : ℂ := 3 * u

/-- Affine coordinates based at the isolated point `[0:0:1]`. -/
noncomputable def t97J07PointChart (w : Fin 2 → ℂ) : T97J07CP2 :=
  Projectivization.mk ℂ ![w 0, w 1, 1] (by
    intro h
    have := congrFun h 2
    simp at this)

/-- The local representative at `[0:0:1]`. -/
noncomputable def t97J07PointLocal (w : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i ↦ w i / 3

/-- Real determinant of `I-Dg` on the complex normal line to the fixed
projective line. -/
noncomputable def t97J07LineNormalDet : ℝ :=
  Complex.normSq (1 - fderiv ℂ t97J07LineLocal 0 1)

/-- Real determinant of `I-Dg` in the two complex affine coordinates at the
isolated fixed point. -/
noncomputable def t97J07PointDet : ℝ :=
  Complex.normSq
    ((1 - (fderiv ℂ t97J07PointLocal 0 (Pi.single 0 1)) 0) *
     (1 - (fderiv ℂ t97J07PointLocal 0 (Pi.single 1 1)) 1))

noncomputable def t97J07IndexFromDet (d : ℝ) : ℤ :=
  if 0 < d then 1 else if d < 0 then -1 else 0

/-- The fixed-line contribution is its Euler characteristic (`2`) times the
normal Lefschetz index. -/
noncomputable def t97J07LineContribution : ℤ :=
  2 * t97J07IndexFromDet t97J07LineNormalDet

theorem apm_t97j07 :
    {p : T97J07CP2 | t97J07Map p = p} =
        t97J07FixedLine ∪ {t97J07IsolatedPoint} ∧
    t97J07IsolatedPoint ∉ t97J07FixedLine ∧
    (∀ a u : ℂ,
      t97J07Map (t97J07LineChart a u) =
        t97J07LineChart a (t97J07LineLocal u)) ∧
    (∀ w : Fin 2 → ℂ,
      t97J07Map (t97J07PointChart w) =
        t97J07PointChart (t97J07PointLocal w)) ∧
    fderiv ℂ t97J07LineLocal 0 1 = 3 ∧
    (∀ i : Fin 2,
      fderiv ℂ t97J07PointLocal 0 (Pi.single i 1) =
        Pi.single i (1 / 3)) ∧
    t97J07LineNormalDet = 4 ∧
    t97J07PointDet = 16 / 81 ∧
    t97J07IndexFromDet t97J07LineNormalDet = 1 ∧
    t97J07IndexFromDet t97J07PointDet = 1 ∧
    t97J07LineContribution = 2 ∧
    t97J07LineContribution + t97J07IndexFromDet t97J07PointDet = 3 := by
  sorry
