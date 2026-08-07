import Mathlib

/-!
# APM b97A01: `S₄` and groups of order 24

## Statement repairs

None.

## Encoding questions

None. The conjugacy classes are represented by explicit permutations of each
cycle type. The requested example is the literal matrix group `SL₂(ZMod 3)`.
-/

open Equiv Equiv.Perm Subgroup

noncomputable section

abbrev apm_b97A01_S4 := Equiv.Perm (Fin 4)

def apm_b97A01_transposition : apm_b97A01_S4 := swap 0 1

def apm_b97A01_doubleTransposition : apm_b97A01_S4 :=
  swap 0 1 * swap 2 3

def apm_b97A01_threeCycle : apm_b97A01_S4 :=
  swap 0 1 * swap 1 2

def apm_b97A01_fourCycle : apm_b97A01_S4 :=
  swap 0 1 * swap 1 2 * swap 2 3

/-- The Klein four subgroup, included into `S₄` from `A₄`. -/
def apm_b97A01_V4 : Subgroup apm_b97A01_S4 :=
  (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype

abbrev apm_b97A01_SL23 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

/-- The concrete special linear group in the example has order `24`. -/
lemma apm_b97A01_SL23_card : Nat.card apm_b97A01_SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- Cycle types of the four nonidentity class representatives. -/
lemma apm_b97A01_representative_cycleTypes :
    apm_b97A01_transposition.cycleType = {2} ∧
    apm_b97A01_doubleTransposition.cycleType = {2, 2} ∧
    apm_b97A01_threeCycle.cycleType = {3} ∧
    apm_b97A01_fourCycle.cycleType = {4} := by
  native_decide

theorem apm_b97a01 :
    (∀ σ : apm_b97A01_S4,
      (IsConj 1 σ ↔ σ.cycleType = {}) ∧
      (IsConj apm_b97A01_transposition σ ↔ σ.cycleType = {2}) ∧
      (IsConj apm_b97A01_doubleTransposition σ ↔
        σ.cycleType = {2, 2}) ∧
      (IsConj apm_b97A01_threeCycle σ ↔ σ.cycleType = {3}) ∧
      (IsConj apm_b97A01_fourCycle σ ↔ σ.cycleType = {4}) ∧
      (IsConj 1 σ ∨ IsConj apm_b97A01_transposition σ ∨
        IsConj apm_b97A01_doubleTransposition σ ∨
        IsConj apm_b97A01_threeCycle σ ∨
        IsConj apm_b97A01_fourCycle σ)) ∧
    Nat.card {σ : apm_b97A01_S4 // IsConj 1 σ} = 1 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_transposition σ} = 6 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_doubleTransposition σ} = 3 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_threeCycle σ} = 8 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_fourCycle σ} = 6 ∧
    (∀ N : Subgroup apm_b97A01_S4,
      N.Normal ↔
        N = ⊥ ∨ N = apm_b97A01_V4 ∨
        N = alternatingGroup (Fin 4) ∨ N = ⊤) ∧
    IsSolvable apm_b97A01_S4 ∧
    (∀ (G : Type) [Group G] [Finite G],
      Nat.card G = 24 →
      ¬Nonempty (G ≃* apm_b97A01_S4) →
      ∀ P3 : Sylow 3 G, ¬(P3 : Subgroup G).Normal →
        ∃ φ : G →* apm_b97A01_S4,
          Nat.card φ.ker = 2 ∧
          ∃ P2 : Sylow 2 G, (P2 : Subgroup G).Normal) ∧
    Nat.card apm_b97A01_SL23 = 24 ∧
    ¬Nonempty (apm_b97A01_SL23 ≃* apm_b97A01_S4) ∧
    ∃ P3 : Sylow 3 apm_b97A01_SL23,
      ¬(P3 : Subgroup apm_b97A01_SL23).Normal := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib's
  `Equiv.Perm.isConj_iff_cycleType_eq` supplies the abstract conjugacy-class
  criterion, but searches of the local Mathlib sources and solved sibling
  artifacts found no packaged bridge for the exhaustive `Fin 4` cycle-type
  enumeration and class cardinalities, the full normal-subgroup lattice of
  `Equiv.Perm (Fin 4)`, the universal order-24 action theorem, or the concrete
  cardinality and Sylow facts for `SpecialLinearGroup (Fin 2) (ZMod 3)`.
  Closer hop 1 compiles two concrete bridges that the original search left
  open. `apm_b97A01_SL23_card` rewrites `Nat.card` to the concrete `Fintype`
  cardinality and verifies that `SL₂(ZMod 3)` has order 24.
  `apm_b97A01_representative_cycleTypes` verifies the advertised cycle types
  of all four nonidentity representatives; together with
  `Equiv.Perm.isConj_iff_cycleType_eq`, this removes the representative side of
  the first five equivalences.

  I additionally tested direct finite decision for the existence of a
  nonnormal Sylow subgroup and center-cardinality separation from `S₄`.
  `Sylow` existence/normality has no computable `Decidable` instance, while
  subgroup-center `Fintype.ofFinite` is noncomputable, so neither test yields a
  kernel-compilable proof. These latter clauses are not reducible by a single finite computation: the
  theorem quantifies over arbitrary finite groups of order 24, and its
  `Nat.card`/subgroup assertions require structural group-theoretic proofs.
  Renewed searches of `LEMMA-INDEX.md`, the closed corpus,
  `ConstructionTargets/`, and the special-linear-group source found no
  structural replacement. The statement appears mathematically
  sound; the blocker is the missing formal API/bridge, not a counterexample.
  -/
  sorry
