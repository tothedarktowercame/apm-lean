import Mathlib

/-!
# APM t01A07

## Statement repairs

Mathlib's projectivization currently has no tangent-orientation or oriented
intersection API from which the integer local signs can be derived.  Following
the reviewer's permitted repair, part (b) is stated as the orientation-free
mod-2 intersection number.  This is a declared weakening of the source's
integer-valued oriented intersection request.

## Encoding questions

The projective space, quartic, line, and their intersection subtype are encoded
concretely; smoothness is encoded by the equivalent regular-cone criterion.
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

noncomputable def apm_t01a07_pointPlus : apm_t01a07_RP3 :=
  Projectivization.mk ℝ ![1, 1, 0, 0] (by
    intro h
    have := congrFun h 0
    simp at this)

noncomputable def apm_t01a07_pointMinus : apm_t01a07_RP3 :=
  Projectivization.mk ℝ ![1, -1, 0, 0] (by
    intro h
    have := congrFun h 0
    simp at this)

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

lemma apm_t01a07_fderiv_apply_zero (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 0 1) = 4 * v 0 ^ 3 := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 0 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_fderiv_apply_one (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 1 1) = -(4 * v 1 ^ 3) := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 1 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_fderiv_apply_two (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 2 1) = -(4 * v 2 ^ 3) := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 2 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_fderiv_apply_three (v : Fin 4 → ℝ) :
    fderiv ℝ apm_t01a07_quartic v (Pi.single 3 1) = 4 * v 3 ^ 3 := by
  have hd := ((((hasFDerivAt_apply (𝕜 := ℝ) 0 v).pow 4).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 v).pow 4)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 2 v).pow 4)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 3 v).pow 4)
  unfold apm_t01a07_quartic
  have heq := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 3 1)) hd.fderiv
  simpa using heq

lemma apm_t01a07_smooth : apm_t01a07_IsSmoothProjectiveHypersurface := by
  intro v hv _ hzero
  have h0 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 0 1)) hzero
  have h1 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 1 1)) hzero
  have h2 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 2 1)) hzero
  have h3 := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 3 1)) hzero
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 0 1) = 0 at h0
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 1 1) = 0 at h1
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 2 1) = 0 at h2
  change fderiv ℝ apm_t01a07_quartic v (Pi.single 3 1) = 0 at h3
  rw [apm_t01a07_fderiv_apply_zero] at h0
  rw [apm_t01a07_fderiv_apply_one] at h1
  rw [apm_t01a07_fderiv_apply_two] at h2
  rw [apm_t01a07_fderiv_apply_three] at h3
  have hv0 : v 0 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h0).resolve_left (by norm_num))
  have hv1 : v 1 = 0 :=
    eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp (neg_eq_zero.mp h1)).resolve_left (by norm_num))
  have hv2 : v 2 = 0 :=
    eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp (neg_eq_zero.mp h2)).resolve_left (by norm_num))
  have hv3 : v 3 = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h3).resolve_left (by norm_num))
  apply hv
  funext i
  fin_cases i <;> assumption

theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      apm_t01a07_pointPlus ≠ apm_t01a07_pointMinus ∧
      apm_t01a07_surface ∩ apm_t01a07_line =
        {apm_t01a07_pointPlus, apm_t01a07_pointMinus} ∧
      Nonempty (Fin 2 ≃ apm_t01a07_intersection) ∧
      Nat.card apm_t01a07_intersection = 2 ∧
      Nat.card apm_t01a07_intersection % 2 = 0 := by
  refine ⟨apm_t01a07_smooth, ?_⟩
  /-
  CLOSER HOP 3 BOUNDARY (statement unchanged).

  This hop closes the entire smoothness conjunct rather than repeating the
  projectivization search. The four lemmas
  `apm_t01a07_fderiv_apply_zero/one/two/three` build the quartic's derivative
  from `hasFDerivAt_apply`, `HasFDerivAt.pow`, subtraction, and addition, then
  evaluate it on the four coordinate basis vectors. `apm_t01a07_smooth` uses
  these formulas to show a zero derivative forces all four coordinates to
  vanish, contradicting the nonzero cone representative.

  The remaining bridge is exclusively the projective two-point
  classification. For an arbitrary intersection point, the line equations
  set coordinates 2 and 3 to zero and the quartic equation, together with
  `apm_t01a07_fourth_pow_eq_iff`, gives `x₀ = x₁` or `x₀ = -x₁`.
  Formal completion must transport those raw coordinate equalities through
  the noncanonical `Projectivization.rep` of each explicit `mk`, prove both
  explicit points belong to the intersection and are distinct, and then turn
  the set equality into `Fin 2 ≃ apm_t01a07_intersection`; the two `Nat.card`
  clauses follow from that equivalence. Renewed inspection of
  `Projectivization.mk_rep`, `mk_eq_mk_iff'`, prior projective artifacts,
  `LEMMA-INDEX.md`, `ConstructionTargets`, and git history found no packaged
  normalization or two-point-subtype equivalence eliminating this assembly.
  -/
  sorry
