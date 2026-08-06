import Mathlib

/-!
# APM t02A01 — boundary lifts in cyclic covers of a punctured torus

## Statement repairs

None.

## Encoding note

A regular cyclic cover is encoded by the translation action of `ZMod n` on
its fiber.  The punctured torus boundary word is the commutator of the two
handle monodromies.  Boundary components are the cycles of that permutation;
because this commutator is the identity, these are its `n` fixed points.
-/

def apm_t02a01_boundaryMonodromy (n : ℕ) (a b : ZMod n) : Equiv.Perm (ZMod n) :=
  Equiv.addRight a * Equiv.addRight b * (Equiv.addRight a)⁻¹ * (Equiv.addRight b)⁻¹

noncomputable def apm_t02a01_boundaryComponentCount (n : ℕ) (a b : ZMod n) : ℕ :=
  Nat.card {x : ZMod n // apm_t02a01_boundaryMonodromy n a b x = x}

theorem apm_t02a01 :
    ∀ (n : ℕ), 0 < n → ∀ a b : ZMod n,
      apm_t02a01_boundaryMonodromy n a b = 1 ∧
      apm_t02a01_boundaryComponentCount n a b = n := by
  intro n hn a b
  have hmon : apm_t02a01_boundaryMonodromy n a b = 1 := by
    ext x
    simp [apm_t02a01_boundaryMonodromy, Equiv.Perm.mul_apply]
    abel
  constructor
  · exact hmon
  · simp [apm_t02a01_boundaryComponentCount, hmon, Nat.card_zmod]
