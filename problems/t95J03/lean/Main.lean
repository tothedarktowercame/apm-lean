import Mathlib

/-!
# APM t95J03 — surfaces sharing a finite cover with the Klein bottle

## Statement repairs

“Surface” is read as a connected closed surface, as required by the
classification used in the source solution.

## Encoding question

Mathlib has no bundled moduli type of connected closed surfaces together with
finite-sheeted covering spaces. Surfaces are therefore represented by their
classification coordinates. Crucially, the realization theorem for cover
profiles is not hidden in a definition: the genuine cover relation is a
parameter, and both its necessary constraints and their realization are
explicit hypotheses of the theorem.
-/

open Set

inductive T95J03ClosedSurface
  | orientable (genus : ℕ)
  | nonorientable (genus : ℕ)
  deriving DecidableEq

def t95J03Torus : T95J03ClosedSurface := .orientable 1
def t95J03KleinBottle : T95J03ClosedSurface := .nonorientable 2

def T95J03ClosedSurface.euler : T95J03ClosedSurface → ℤ
  | .orientable g => 2 - 2 * g
  | .nonorientable g => 2 - g

structure T95J03CoverProfile where
  orientable : Bool
  euler : ℤ

/-- Necessary classification constraints on a connected `k`-sheeted cover.
This definition does not assert that a profile is realizable. -/
def T95J03CoverConstraints
    (k : ℕ) (F : T95J03ClosedSurface) (P : T95J03CoverProfile) : Prop :=
  P.euler = (k : ℤ) * F.euler ∧
    match F with
    | .orientable _ => P.orientable = true
    | .nonorientable _ => P.orientable = false ∨ Even k

theorem apm_t95j03 (k : ℕ) (hk : 1 < k)
    (HasConnectedKFoldCover :
      ℕ → T95J03ClosedSurface → T95J03CoverProfile → Prop)
    (hnecessary : ∀ k F P,
      HasConnectedKFoldCover k F P → T95J03CoverConstraints k F P)
    (hrealize : ∀ k F P,
      T95J03CoverConstraints k F P → HasConnectedKFoldCover k F P) :
    {F | ∃ P,
      HasConnectedKFoldCover k F P ∧
      HasConnectedKFoldCover k t95J03KleinBottle P} =
        if Even k then {t95J03Torus, t95J03KleinBottle}
        else {t95J03KleinBottle} := by
  have hcover_iff (j : ℕ) (F : T95J03ClosedSurface) (P : T95J03CoverProfile) :
      HasConnectedKFoldCover j F P ↔ T95J03CoverConstraints j F P :=
    ⟨hnecessary j F P, hrealize j F P⟩
  by_cases he : Even k
  · rw [if_pos he]
    ext F
    simp only [mem_setOf_eq]
    simp_rw [hcover_iff]
    cases F with
    | orientable g =>
        simp [T95J03CoverConstraints, T95J03ClosedSurface.euler,
          t95J03Torus, t95J03KleinBottle, he]
        constructor
        · rintro ⟨P, ⟨hP, -⟩, h0⟩
          have hk0 : (k : ℤ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hk))
          have hm : (k : ℤ) * (2 - 2 * (g : ℤ)) = 0 := hP.symm.trans h0
          have : 2 - 2 * (g : ℤ) = 0 := (mul_eq_zero.mp hm).resolve_left hk0
          omega
        · rintro rfl
          exact ⟨⟨true, 0⟩, by norm_num⟩
    | nonorientable g =>
        simp [T95J03CoverConstraints, T95J03ClosedSurface.euler,
          t95J03Torus, t95J03KleinBottle, he]
        constructor
        · rintro ⟨P, hP, h0⟩
          have hk0 : (k : ℤ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hk))
          have hm : (k : ℤ) * (2 - (g : ℤ)) = 0 := hP.symm.trans h0
          have : 2 - (g : ℤ) = 0 := (mul_eq_zero.mp hm).resolve_left hk0
          omega
        · rintro rfl
          exact ⟨⟨false, 0⟩, by norm_num⟩

  · rw [if_neg he]
    ext F
    simp only [mem_setOf_eq]
    simp_rw [hcover_iff]
    cases F with
    | orientable g =>
        simp [T95J03CoverConstraints, T95J03ClosedSurface.euler,
          t95J03KleinBottle, he]
        aesop
    | nonorientable g =>
        simp [T95J03CoverConstraints, T95J03ClosedSurface.euler,
          t95J03KleinBottle, he]
        constructor
        · rintro ⟨P, ⟨hP, -⟩, h0, -⟩
          have hk0 : (k : ℤ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hk))
          have hm : (k : ℤ) * (2 - (g : ℤ)) = 0 := hP.symm.trans h0
          have : 2 - (g : ℤ) = 0 := (mul_eq_zero.mp hm).resolve_left hk0
          omega
        · rintro rfl
          exact ⟨⟨false, 0⟩, by norm_num⟩
