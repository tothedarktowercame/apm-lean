import Mathlib
import ConstructionTargets.Surfaces

open Set

inductive T95J03ClosedSurface
  | orientable (genus : ℕ)
  | nonorientable (genus : PNat)
  deriving DecidableEq

def t95J03Torus : T95J03ClosedSurface := .orientable 1
def t95J03KleinBottle : T95J03ClosedSurface := .nonorientable 2

open ConstructionTargets.Surfaces

/-- A concrete representative of every classification coordinate.  Genus zero
in the orientable family is the two-sphere, not the zero-edge polygon (a disk).
There is no nonorientable genus-zero constructor. -/
noncomputable def T95J03SurfaceSpace : T95J03ClosedSurface → TopCat
  | .orientable 0 =>
      TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  | .orientable (g + 1) => TopCat.of (Surface true (g + 1))
  | .nonorientable g => TopCat.of (Surface false g)

def T95J03IsKFoldCover (k : ℕ) (E X : TopCat.{0}) (p : E → X) : Prop :=
  IsCoveringMap p ∧ ∀ x : X, Nat.card {e : E // p e = x} = k

def T95J03SharesKFoldCover (k : ℕ) (F G : T95J03ClosedSurface) : Prop :=
  ∃ (E K : TopCat.{0}) (p : E → T95J03SurfaceSpace F)
      (q : K → T95J03SurfaceSpace G),
    T95J03IsKFoldCover k E (T95J03SurfaceSpace F) p ∧
    T95J03IsKFoldCover k K (T95J03SurfaceSpace G) q ∧
    Nonempty (E ≃ₜ K)

theorem apm_t95j03 (k : ℕ) (hk : 1 < k) :
    {F | T95J03SharesKFoldCover k F t95J03KleinBottle} =
      if Even k then {t95J03Torus, t95J03KleinBottle}
      else {t95J03KleinBottle} := by
  sorry

