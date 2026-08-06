import Mathlib

/-!
# APM b01J02: Ideals of `ℤ[x]`

## Statement repairs

None.

## Encoding questions

None. The classification in part (a) is stated as an equivalence for every
ideal of `ℤ[x]`. Reduction modulo `p` is polynomial coefficient mapping
along `Int.castRingHom (ZMod p)`.
-/

open Polynomial

noncomputable section

/-- The two-generated ideal `(p, f)` of `ℤ[x]`. -/
def apm_b01J02_twoGeneratedIdeal (p : ℕ) (f : ℤ[X]) : Ideal ℤ[X] :=
  Ideal.span {C (p : ℤ), f}

/-- The ideal `(3, x² + x + 1)` from part (b). -/
def apm_b01J02_nonprimeIdeal : Ideal ℤ[X] :=
  Ideal.span {C 3, X ^ 2 + X + 1}

/-- The ideal `(x)`, used in part (c). -/
def apm_b01J02_xIdeal : Ideal ℤ[X] :=
  Ideal.span {X}

theorem apm_b01j02 :
    (∀ I : Ideal ℤ[X],
      I.IsMaximal ↔
        ∃ (p : ℕ) (f : ℤ[X]), p.Prime ∧
          Irreducible (f.map (Int.castRingHom (ZMod p))) ∧
          I = apm_b01J02_twoGeneratedIdeal p f) ∧
    (let f : ℤ[X] := X - 1
      let g : ℤ[X] := X - 1
      f * g ∈ apm_b01J02_nonprimeIdeal ∧
        f ∉ apm_b01J02_nonprimeIdeal ∧
        g ∉ apm_b01J02_nonprimeIdeal) ∧
    apm_b01J02_xIdeal ≠ ⊥ ∧
    apm_b01J02_xIdeal.IsPrime ∧
    ¬apm_b01J02_xIdeal.IsMaximal := by
  sorry
