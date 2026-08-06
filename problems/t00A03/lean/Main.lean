import Mathlib

/-!
# APM t00A03 — pants decompositions

## Statement repairs

The printed `3g-g` is corrected to `3g-3`, as required by the Euler
characteristic and boundary counts and confirmed by the source solution.

## Encoding note

Each complementary orientable surface is recorded by `(genus,boundary-count)`.
The predicate `pantsAtomic` is the classification-theorem translation of
maximality: the component has boundary, contains no disk/annulus forced by an
inessential/parallel cut, and admits no further essential nonperipheral curve.
-/

def apm_t00a03_euler (s : ℕ × ℕ) : ℤ := 2 - 2 * s.1 - s.2

def apm_t00a03_pantsAtomic (s : ℕ × ℕ) : Prop :=
  0 < s.2 ∧ apm_t00a03_euler s < 0 ∧ s.1 = 0 ∧ s.2 ≤ 3

theorem apm_t00a03 :
    ∀ (g curves : ℕ) (components : List (ℕ × ℕ)), 2 ≤ g →
      (∀ s ∈ components, apm_t00a03_pantsAtomic s) →
      (components.map apm_t00a03_euler).sum = 2 - 2 * (g : ℤ) →
      (components.map Prod.snd).sum = 2 * curves →
      (∀ s ∈ components, s = (0, 3)) ∧ curves = 3 * g - 3 := by
  sorry
