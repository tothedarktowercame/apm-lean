import Mathlib

/-! # APM t01A04: the fundamental group and double covers of `T² ∨ S¹`

## Statement repairs

None.

## Encoding question

Mathlib has fundamental groups but no wedge-space constructor or classification
of covering spaces by subgroups.  The pictured wedge and the two requested
covering total spaces are retained as explicitly named `TopCat` placeholders.
The presentation itself is stated by its full universal property, while the two
index-two subgroups are the kernels of the displayed parity homomorphisms.
-/

open CategoryTheory FundamentalGroupoid

def t01A04X : TopCat := by sorry
def t01A04Basepoint : t01A04X := by sorry
def t01A04FirstCover : TopCat := by sorry
def t01A04SecondCover : TopCat := by sorry

abbrev t01A04FundamentalGroup := FundamentalGroup t01A04X t01A04Basepoint
abbrev t01A04Parity := Multiplicative (ZMod 2)

theorem apm_t01a04 :
    ∃ (a b c : t01A04FundamentalGroup)
      (φc φa : t01A04FundamentalGroup →* t01A04Parity),
      a * b = b * a ∧
      Subgroup.closure {a, b, c} = ⊤ ∧
      (∀ (G : Type*) [Group G] (ga gb gc : G), ga * gb = gb * ga →
        ∃! F : t01A04FundamentalGroup →* G,
          F a = ga ∧ F b = gb ∧ F c = gc) ∧
      φc a = Multiplicative.ofAdd 0 ∧
      φc b = Multiplicative.ofAdd 0 ∧
      φc c = Multiplicative.ofAdd 1 ∧
      φa a = Multiplicative.ofAdd 1 ∧
      φa b = Multiplicative.ofAdd 0 ∧
      φa c = Multiplicative.ofAdd 0 ∧
      Function.Surjective φc ∧ Function.Surjective φa ∧
      φc.ker.index = 2 ∧ φa.ker.index = 2 ∧
      φc.ker ≠ φa.ker ∧
      ¬Nonempty (t01A04FirstCover ≅ t01A04SecondCover) := by
  sorry
