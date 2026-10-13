import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.CoveringDegree
import ConstructionTargets.RestrictPathComponent
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.SuppliedCoverAlgebra

open Set

inductive T95J03ClosedSurface
  | orientable (genus : ℕ)
  | nonorientable (genus : PNat)
  deriving DecidableEq

def t95J03Torus : T95J03ClosedSurface := .orientable 1
def t95J03KleinBottle : T95J03ClosedSurface := .nonorientable 2

open ConstructionTargets.Surfaces

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

/-- LIBRARY: multiplicativity of Euler characteristic under finite covers,
homeomorphism invariance, and the classification of connected closed surfaces. -/
theorem t95J03_shared_cover_classification (k : ℕ) (hk : 0 < k)
    (F : T95J03ClosedSurface)
    (hF : T95J03SharesKFoldCover k F t95J03KleinBottle) :
    F = t95J03Torus ∨ F = t95J03KleinBottle := by
  sorry

/-- LIBRARY: every positive degree occurs as the degree of a finite cover of
the Klein bottle (hence the same cover witnesses sharing with itself). -/
theorem t95J03_klein_self_share (k : ℕ) (hk : 0 < k) :
    T95J03SharesKFoldCover k t95J03KleinBottle t95J03KleinBottle := by
  sorry

/-- LIBRARY: the orientation double cover and the orientation character imply
that a torus and Klein bottle share degree-k covers exactly for even k. -/
theorem t95J03_torus_share_iff_even (k : ℕ) (hk : 0 < k) :
    T95J03SharesKFoldCover k t95J03Torus t95J03KleinBottle ↔ Even k := by
  sorry

theorem apm_t95j03 (k : ℕ) (hk : 1 < k) :
    {F | T95J03SharesKFoldCover k F t95J03KleinBottle} =
      if Even k then {t95J03Torus, t95J03KleinBottle}
      else {t95J03KleinBottle} := by
  have hk0 : 0 < k := by omega
  by_cases he : Even k
  · rw [if_pos he]
    ext F
    constructor
    · intro hF
      rcases t95J03_shared_cover_classification k hk0 F hF with rfl | rfl
      · simp
      · simp
    · intro hF
      simp only [mem_insert_iff, mem_singleton_iff] at hF
      rcases hF with rfl | rfl
      · exact (t95J03_torus_share_iff_even k hk0).2 he
      · exact t95J03_klein_self_share k hk0
  · rw [if_neg he]
    ext F
    constructor
    · intro hF
      rcases t95J03_shared_cover_classification k hk0 F hF with rfl | rfl
      · exact False.elim (he ((t95J03_torus_share_iff_even k hk0).1 hF))
      · simp
    · intro hF
      have : F = t95J03KleinBottle := by simpa using hF
      subst F
      exact t95J03_klein_self_share k hk0

#print axioms apm_t95j03
