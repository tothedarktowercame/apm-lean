import Mathlib

/-!
# APM t02A01 — boundary lifts in cyclic covers of a punctured torus

## Statement repairs

The punctured torus and its boundary are now the concrete square-annulus quotient; the regular cyclic cover acts over that fixed base.

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

/-- A square annulus: the closed unit square with the open disk of radius
`1/4` about its centre removed. -/
abbrev apm_t02a01_squareAnnulus :=
  {x : ℝ × ℝ // x.1 ∈ Set.Icc 0 1 ∧ x.2 ∈ Set.Icc 0 1 ∧
    (1 / 4 : ℝ) ≤ ‖x - (1 / 2, 1 / 2)‖}

/-- Opposite outside edges of the square annulus are identified. -/
inductive apm_t02a01_edgeRel :
    apm_t02a01_squareAnnulus → apm_t02a01_squareAnnulus → Prop
  | horizontal (y : ℝ) (hy : y ∈ Set.Icc 0 1)
      (h₀ : (1 / 4 : ℝ) ≤ ‖((0, y) : ℝ × ℝ) - (1 / 2, 1 / 2)‖)
      (h₁ : (1 / 4 : ℝ) ≤ ‖((1, y) : ℝ × ℝ) - (1 / 2, 1 / 2)‖) :
      apm_t02a01_edgeRel ⟨(0, y), ⟨by norm_num, hy, h₀⟩⟩
        ⟨(1, y), ⟨by norm_num, hy, h₁⟩⟩
  | vertical (x : ℝ) (hx : x ∈ Set.Icc 0 1)
      (h₀ : (1 / 4 : ℝ) ≤ ‖((x, 0) : ℝ × ℝ) - (1 / 2, 1 / 2)‖)
      (h₁ : (1 / 4 : ℝ) ≤ ‖((x, 1) : ℝ × ℝ) - (1 / 2, 1 / 2)‖) :
      apm_t02a01_edgeRel ⟨(x, 0), ⟨hx, by norm_num, h₀⟩⟩
        ⟨(x, 1), ⟨hx, by norm_num, h₁⟩⟩

def apm_t02a01_puncturedTorus :=
  Quotient (Relation.EqvGen.setoid apm_t02a01_edgeRel)

noncomputable instance : TopologicalSpace apm_t02a01_puncturedTorus :=
  TopologicalSpace.coinduced
    (fun x : apm_t02a01_squareAnnulus ↦
      (Quotient.mk _ x : apm_t02a01_puncturedTorus)) inferInstance

/-- The actual inner boundary circle of the square-annulus model, after the
outside edges have been glued to make the punctured torus. -/
def apm_t02a01_boundary : Set apm_t02a01_puncturedTorus :=
  (fun x : apm_t02a01_squareAnnulus ↦
    (Quotient.mk _ x : apm_t02a01_puncturedTorus)) ''
      {x | ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)}

/-- For a regular cyclic `n`-sheeted cover of the concrete once-punctured
 torus, the inverse image of its actual boundary has exactly `n` connected
 components. -/
theorem apm_t02a01
    {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ)
    (hn : 0 < n)
    (hcover : IsCoveringMap p)
    (hp_surjective : Function.Surjective p)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y) :
    Nat.card (ConnectedComponents (p ⁻¹' apm_t02a01_boundary)) = n := by
  sorry
