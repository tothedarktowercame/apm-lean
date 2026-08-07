import Mathlib

/-! # APM t95J03: surfaces sharing a finite cover with the Klein bottle

## Statement repairs

“Surface” is read as a connected closed surface, as required for the stated
classification by Euler characteristic and as used by the supplied solution.

## Encoding question

Mathlib has no bundled moduli type of connected closed surfaces. We use the
standard classification coordinates—orientability and genus—as the surface
type. A finite cover is represented by its classification profile, with Euler
characteristic and orientability pinned by the covering equations. Thus the
common-cover witness cannot be fabricated with arbitrary invariants.
-/

open Set

/-- Classification coordinates for a connected closed surface. -/
inductive T95J03ClosedSurface
  | orientable (genus : ℕ)
  | nonorientable (genus : ℕ)
  deriving DecidableEq

def t95J03Torus : T95J03ClosedSurface := .orientable 1
def t95J03KleinBottle : T95J03ClosedSurface := .nonorientable 2

/-- Euler characteristic in the classification of closed surfaces. -/
def T95J03ClosedSurface.euler : T95J03ClosedSurface → ℤ
  | .orientable g => 2 - 2 * g
  | .nonorientable g => 2 - g

/-- The classification data of a connected finite-sheeted cover. -/
structure T95J03CoverProfile where
  orientable : Bool
  euler : ℤ

/-- The necessary and sufficient classification constraints for a connected
`k`-sheeted cover with the given profile. -/
def T95J03AdmitsKFoldCoverProfile
    (k : ℕ) (F : T95J03ClosedSurface) (P : T95J03CoverProfile) : Prop :=
  P.euler = (k : ℤ) * F.euler ∧
    match F with
    | .orientable _ => P.orientable = true
    | .nonorientable _ => P.orientable = false ∨ Even k

def T95J03ShareKFoldCover
    (k : ℕ) (F K : T95J03ClosedSurface) : Prop :=
  ∃ P : T95J03CoverProfile,
    T95J03AdmitsKFoldCoverProfile k F P ∧
    T95J03AdmitsKFoldCoverProfile k K P

def t95J03S (k : ℕ) : Set T95J03ClosedSurface :=
  {F | T95J03ShareKFoldCover k F t95J03KleinBottle}

theorem apm_t95j03 (k : ℕ) (hk : 1 < k) :
    t95J03S k =
      if Even k then {t95J03Torus, t95J03KleinBottle}
      else {t95J03KleinBottle} := by
  sorry
