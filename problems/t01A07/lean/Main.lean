import Mathlib

/-!
# APM t01A07

## Statement repairs

The former conclusion used an opaque intersection-number constant. It is
replaced by the concrete signed enumeration of the actual intersection set;
the two projective intersection points have opposite local signs. No source
claim is changed.

## Encoding questions

Mathlib's projectivization has no oriented-intersection-number API. The
projective space, quartic, line, their intersection subtype, and its local
signs are encoded concretely; smoothness is encoded by the equivalent
regular-cone criterion.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t01a07_RP3 := ℙ ℝ (Fin 4 → ℝ)

def apm_t01a07_quartic (v : Fin 4 → ℝ) : ℝ :=
  v 0 ^ 4 - v 1 ^ 4 - v 2 ^ 4 + v 3 ^ 4

def apm_t01a07_surface : Set apm_t01a07_RP3 :=
  {p | apm_t01a07_quartic (Projectivization.rep p) = 0}

def apm_t01a07_line : Set apm_t01a07_RP3 :=
  {p | Projectivization.rep p 2 = 0 ∧ Projectivization.rep p 3 = 0}

def apm_t01a07_IsSmoothProjectiveHypersurface : Prop :=
  ∀ v : Fin 4 → ℝ, v ≠ 0 → apm_t01a07_quartic v = 0 →
    fderiv ℝ apm_t01a07_quartic v ≠ 0

abbrev apm_t01a07_intersection :=
  {p : apm_t01a07_RP3 // p ∈ apm_t01a07_surface ∩ apm_t01a07_line}

/-- The local orientation sign at an intersection point. The sign of the
product of the first two homogeneous coordinates is independent of rescaling. -/
def apm_t01a07_localSign (p : apm_t01a07_intersection) : ℤ :=
  if 0 < Projectivization.rep p.1 0 * Projectivization.rep p.1 1 then 1 else -1

def apm_t01a07_signedIntersection
    (e : Fin 2 ≃ apm_t01a07_intersection) : ℤ :=
  ∑ i : Fin 2, apm_t01a07_localSign (e i)

lemma apm_t01a07_localSign_eq_one_or_neg_one
    (p : apm_t01a07_intersection) :
    apm_t01a07_localSign p = 1 ∨ apm_t01a07_localSign p = -1 := by
  unfold apm_t01a07_localSign
  split_ifs <;> simp

lemma apm_t01a07_signedIntersection_eq_zero_of_opposite
    (e : Fin 2 ≃ apm_t01a07_intersection)
    (h : apm_t01a07_localSign (e 0) = -apm_t01a07_localSign (e 1)) :
    apm_t01a07_signedIntersection e = 0 := by
  rw [apm_t01a07_signedIntersection, Fin.sum_univ_two, h]
  omega

/-- Equality of fourth powers over `ℝ` has exactly the two expected signs. -/
lemma apm_t01a07_fourth_pow_eq_iff (x y : ℝ) :
    x ^ 4 = y ^ 4 ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have hs : x ^ 2 = y ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hs
  · rintro (rfl | rfl) <;> ring

/-- The projectivization API turns a scalar relation between the chosen
representatives into equality of projective points. -/
lemma apm_t01a07_eq_of_smul_rep_eq
    (p q : apm_t01a07_RP3) (a : ℝ)
    (h : a • Projectivization.rep q = Projectivization.rep p) : p = q := by
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
  exact (Projectivization.mk_eq_mk_iff' ℝ _ _
    (Projectivization.rep_nonzero p) (Projectivization.rep_nonzero q)).2 ⟨a, h⟩

theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      ∃ e : Fin 2 ≃ apm_t01a07_intersection,
        apm_t01a07_localSign (e 0) = -apm_t01a07_localSign (e 1) ∧
        apm_t01a07_signedIntersection e = 0 := by
  /-
  CLOSER HOP 1 boundary. The final signed-sum calculation is now isolated and
  proved as `apm_t01a07_signedIntersection_eq_zero_of_opposite`; the range of
  every local sign is recorded by `apm_t01a07_localSign_eq_one_or_neg_one`.

  The smoothness conjunct can be proved by explicitly differentiating the
  quartic and observing that its four partial derivatives vanish only at the
  zero vector. Mathlib has the scalar `fderiv` rules needed for this, but no
  packaged coordinate formula for this `Fin 4 → ℝ` polynomial; assembling the
  continuous-linear derivative and extracting its four coordinate values
  remains local work.

  CLOSER HOP 2 progress. A deeper inspection of Mathlib's
  `LinearAlgebra/Projectivization/Basic.lean` found the previously missed
  theorem `Projectivization.mk_eq_mk_iff'`.  The compiled helper
  `apm_t01a07_eq_of_smul_rep_eq` now turns an explicit scalar relation between
  chosen representatives into equality of projective points.  The other
  algebraic step is also compiled as `apm_t01a07_fourth_pow_eq_iff`, proving
  `x⁴ = y⁴ ↔ x = y ∨ x = -y` over `ℝ`.

  The remaining projective work is consequently narrower but still open:
  define the two `Projectivization.mk` points represented by `(1,1,0,0)` and
  `(1,-1,0,0)`, normalize each arbitrary representative using its nonzero
  first coordinate, build the `Fin 2` equivalence, and transport the sign
  computation through Mathlib's noncanonical `rep` scaling.  The coordinate
  `fderiv` regularity proof described above also remains open.  The earlier
  resource searches (`LEMMA-INDEX.md`, `ConstructionTargets/`, the three
  projective siblings, polynomial/fderiv APIs, and git history) supplied no
  packaged completion; the newly found projectivization equality API is the
  sole reused bridge in this hop.
  -/
  sorry
