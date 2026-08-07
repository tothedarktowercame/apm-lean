import Mathlib

/-!
# APM m00A04: Hilbert-space minimization and a weak elliptic solution

## Statement repairs

In part (a), the strict-minimum clause prints `V ≠ u`; since `V` is the
ambient space, this is ill-typed. We replace it by the intended `v ≠ u`.

## Encoding questions

This Mathlib snapshot has no packaged `H¹₀(Ω)` space. Rather than replacing it
by a scalar shadow, `apm_m00A04_memH10WithGradient` explicitly encodes its
standard definition: an `L²` function with `L²` distributional weak gradient
that is approximable in the energy norm by smooth compactly supported tests.
-/

open MeasureTheory Set Function
open scoped ContDiff BigOperators RealInnerProductSpace

noncomputable section

def apm_m00A04_phi {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →L[ℝ] ℝ) (v : V) : ℝ :=
  (1 / 2 : ℝ) * ‖v‖ ^ 2 - f v

def apm_m00A04_testFunction {n : ℕ} (U : Set (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ IsCompact (support φ) ∧ support φ ⊆ U

def apm_m00A04_partial {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ φ x (Pi.single i 1)

def apm_m00A04_L2On {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ) : Prop :=
  IntegrableOn (fun x ↦ |u x| ^ 2) U

def apm_m00A04_weakGradient {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n) (φ : (Fin n → ℝ) → ℝ),
    apm_m00A04_testFunction U φ →
      (∫ x in U, u x * apm_m00A04_partial φ i x) =
        -∫ x in U, g i x * φ x

/-- An explicit representative-level encoding of `u ∈ H¹₀(U)` with weak
gradient `g`. -/
def apm_m00A04_memH10WithGradient {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  apm_m00A04_L2On U u ∧
  (∀ i, apm_m00A04_L2On U (g i)) ∧
  apm_m00A04_weakGradient U u g ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ φ : (Fin n → ℝ) → ℝ,
      apm_m00A04_testFunction U φ ∧
      (∫ x in U,
        |u x - φ x| ^ 2 +
          ∑ i : Fin n, |g i x - apm_m00A04_partial φ i x| ^ 2) < ε

private lemma apm_m00A04_zero_memH10WithGradient {n : ℕ}
    (U : Set (Fin n → ℝ)) :
    apm_m00A04_memH10WithGradient U 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [apm_m00A04_L2On]
  · intro i
    simp [apm_m00A04_L2On]
  · intro i φ hφ
    simp
  · intro ε hε
    refine ⟨0, ?_, ?_⟩
    · refine ⟨contDiff_const, ?_, ?_⟩
      · simp
      · simp
    · simpa [apm_m00A04_partial] using hε

theorem apm_m00a04
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V →L[ℝ] ℝ) :
    BddBelow (range (apm_m00A04_phi f)) ∧
    (∃ u : V,
      (∀ v : V, apm_m00A04_phi f u ≤ apm_m00A04_phi f v) ∧
      (∀ v : V, v ≠ u → apm_m00A04_phi f u < apm_m00A04_phi f v) ∧
      ∀ v : V, inner ℝ u v = f v) ∧
    ∀ (n : ℕ) (U : Set (Fin n → ℝ)),
      U.Nonempty → IsOpen U → Bornology.IsBounded U →
      ∀ F : (Fin n → ℝ) → ℝ, apm_m00A04_L2On U F →
        ∃ (u : (Fin n → ℝ) → ℝ)
          (g : Fin n → (Fin n → ℝ) → ℝ),
          apm_m00A04_memH10WithGradient U u g ∧
          ∀ (v : (Fin n → ℝ) → ℝ)
            (h : Fin n → (Fin n → ℝ) → ℝ),
            apm_m00A04_memH10WithGradient U v h →
              (∫ x in U,
                (∑ i : Fin n, g i x * h i x) + u x * v x) =
              ∫ x in U, F x * v x := by
  let u : V := (InnerProductSpace.toDual ℝ V).symm f
  have hu (v : V) : inner ℝ u v = f v := by
    exact InnerProductSpace.toDual_symm_apply
  have hphi (v : V) :
      apm_m00A04_phi f v =
        (1 / 2 : ℝ) * ‖v - u‖ ^ 2 - (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
    unfold apm_m00A04_phi
    rw [← hu v, norm_sub_sq_real, real_inner_comm]
    ring
  constructor
  · refine ⟨-(1 / 2 : ℝ) * ‖u‖ ^ 2, ?_⟩
    rintro _ ⟨v, rfl⟩
    rw [hphi]
    nlinarith [sq_nonneg ‖v - u‖]
  · constructor
    · refine ⟨u, ?_, ?_, hu⟩
      · intro v
        rw [hphi, hphi]
        simp only [sub_self, norm_zero, zero_pow, Nat.ofNat_pos, mul_zero]
        nlinarith [sq_nonneg ‖v - u‖]
      · intro v hv
        rw [hphi, hphi]
        have hnorm : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
        simp only [sub_self, norm_zero, zero_pow, Nat.ofNat_pos, mul_zero]
        nlinarith [sq_pos_of_pos hnorm]
    · intro n U hUne hUopen hUbounded F hF
      by_cases hn : n = 0
      · subst n
        let z : Fin 0 → ℝ := fun i ↦ Fin.elim0 i
        have hsub (x : Fin 0 → ℝ) : x = z := Subsingleton.elim _ _
        have hUtop : U = Set.univ := by
          apply eq_univ_of_forall
          intro x
          obtain ⟨y, hy⟩ := hUne
          simpa [hsub x, hsub y] using hy
        let φ : (Fin 0 → ℝ) → ℝ := fun _ ↦ F z
        have hFφ : F = φ := by
          funext x
          simp only [φ]
          rw [hsub x]
        let g : Fin 0 → (Fin 0 → ℝ) → ℝ := fun i ↦ Fin.elim0 i
        refine ⟨F, g, ?_, ?_⟩
        · refine ⟨hF, ?_, ?_, ?_⟩
          · intro i
            exact Fin.elim0 i
          · intro i
            exact Fin.elim0 i
          · intro ε hε
            refine ⟨φ, ?_, ?_⟩
            · refine ⟨contDiff_const, ?_, ?_⟩
              · exact (Set.toFinite (support φ)).isCompact
              · rw [hUtop]
                exact subset_univ _
            · simpa [hFφ] using hε
        · intro v h hv
          simp [hFφ]
      · /-
      Boundary: the Hilbert-space portion is complete above. It uses Mathlib's
      compiled Fréchet–Riesz equivalence `InnerProductSpace.toDual`; rewriting
      `φ` with `norm_sub_sq_real` gives the exact completed-square formula,
      from which boundedness, the unique strict minimizer, and representation
      follow.

      The remaining PDE conjunct is not a direct application of a packaged
      Sobolev/Lax–Milgram theorem because the frozen statement uses the custom
      representative-level predicate `apm_m00A04_memH10WithGradient`. Mathlib
      searches found no `H¹₀` completion matching this predicate. A proof must
      construct the completion of compactly supported smooth test functions in
      the encoded energy norm, prove that its elements admit representatives
      `(u,g)` satisfying the distributional identities and approximation clause,
      then descend the Riesz representative back to those functions. This is a
      full Sobolev-space construction, not supplied by solved siblings.
      Closer hop 1 additionally separates and proves the degenerate case
      `n = 0`: the Euclidean domain is a singleton, the gradient family is
      empty, and a constant test function gives exact energy approximation.
      Thus the sole remaining case has `0 < n` and requires the genuine
      Sobolev completion/representative construction described above.
      Closer hop 2 proves `apm_m00A04_zero_memH10WithGradient`, verifying from
      the frozen definitions that the zero function and zero gradient belong to
      the custom space in every dimension. Searches of
      `Analysis/FunctionalSpaces`, distribution APIs, all closed artifacts,
      `ConstructionTargets`, and `YoungL2.lean` found inequalities and abstract
      Lax--Milgram machinery, but still no completeness/representative theorem
      for this graph closure. Extending the compiled zero base case to arbitrary
      `F` therefore remains exactly the positive-dimensional completion bridge.
      -/
        sorry
