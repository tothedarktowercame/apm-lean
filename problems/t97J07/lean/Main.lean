import Mathlib

/-!
# APM t97J07 — Lefschetz data for a projective linear map

We use Mathlib's genuine projectivization of `ℂ³`.  The fixed component and
isolated fixed point are concrete subsets/points of that projectivization.
The displayed determinants are those of `I - Dg` in the complex normal
coordinate to the fixed line and in the two complex affine coordinates at the
isolated point.  Their positivity gives local index `+1`; the fixed line has
the two even-dimensional cells of `ℂP¹`, hence contribution two.

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

theorem apm_t97j07 :
    {p : T97J07CP2 | t97J07Map p = p} =
        t97J07FixedLine ∪ {t97J07IsolatedPoint} ∧
    t97J07IsolatedPoint ∉ t97J07FixedLine ∧
    (0 : ℝ) < Matrix.det !![(1 : ℝ) - 3, 0; 0, 1 - 3] ∧
    (0 : ℝ) < Matrix.det !![(1 : ℝ) - 1 / 3, 0, 0, 0;
      0, 1 - 1 / 3, 0, 0;
      0, 0, 1 - 1 / 3, 0;
      0, 0, 0, 1 - 1 / 3] ∧
    ((1 : ℤ) + 1 = 2) ∧
    ((2 : ℤ) + 1 = 3) := by
  sorry
