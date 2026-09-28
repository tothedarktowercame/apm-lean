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

/-- Superseded: it defined the boundary count to be the fixed points of an
already-trivial translation commutator instead of stating the covering-space problem. -/
theorem apm_t02a01_previous_encoding :
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

/-- For a regular cyclic `n`-sheeted cover of a punctured torus, the lifted
boundary has exactly `n` connected components.  The conclusion counts the
actual connected components of the inverse image of the boundary. -/
theorem apm_t02a01
    {S Stilde : Type*} [TopologicalSpace S] [TopologicalSpace Stilde]
    (boundary : Set S) (p : Stilde → S) (n : ℕ)
    (hn : 0 < n)
    (hboundary : Nat.card (ConnectedComponents boundary) = 1)
    (hcover : IsCoveringMap p)
    (hregularCyclic : ∃ deck : ZMod n → Homeomorph Stilde Stilde,
      (∀ z x, p (deck z x) = p x) ∧
      (∀ x y, p x = p y → ∃! z, deck z x = y)) :
    Nat.card (ConnectedComponents (p ⁻¹' boundary)) = n := by
  sorry
