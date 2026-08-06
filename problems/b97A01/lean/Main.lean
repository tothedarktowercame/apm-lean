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
  sorry
