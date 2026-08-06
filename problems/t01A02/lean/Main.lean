import Mathlib

/-!
# APM t01A02

## Statement repairs

None.

## Encoding questions

The torus and the four-sheeted map are concrete: `Circle × Circle` and
`(z,w) ↦ (z²,w²)`. Mathlib has covering maps but no usable general integral
singular-homology group functor in this setting, so only the `H₂` group and
its functorial map are isolated behind opaque typed helpers. The covering group
is not opaque: it is characterized by a free, fiber-transitive `(Z/2)²` action.
-/

abbrev apm_t01A02_Torus := Circle × Circle
abbrev apm_t01A02_Deck := ZMod 2 × ZMod 2

noncomputable section

/-- The double-in-each-coordinate torus covering. -/
def apm_t01A02_cover (x : apm_t01A02_Torus) : apm_t01A02_Torus :=
  (x.1 ^ 2, x.2 ^ 2)

/-- A regular covering whose deck group is `G`. -/
def apm_t01A02_hasCoveringGroup
    {S T G : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [AddGroup G] (p : S → T) : Prop :=
  IsCoveringMap p ∧
  ∃ act : G → S → S,
    (∀ x, act 0 x = x) ∧
    (∀ g h x, act (g + h) x = act g (act h x)) ∧
    (∀ g, Continuous (act g)) ∧
    (∀ g x, p (act g x) = p x) ∧
    (∀ g x, act g x = x → g = 0) ∧
    (∀ x y, p x = p y ↔ ∃ g, act g x = y)

/-- Integral second singular homology. -/
opaque apm_t01A02_H2 (X : Type*) [TopologicalSpace X] : Type

axiom apm_t01A02_H2AddCommGroupExists
    (X : Type*) [TopologicalSpace X] :
    Nonempty (AddCommGroup (apm_t01A02_H2 X))

noncomputable instance (X : Type*) [TopologicalSpace X] :
    AddCommGroup (apm_t01A02_H2 X) :=
  Classical.choice (apm_t01A02_H2AddCommGroupExists X)

/-- The map induced on integral second homology. -/
opaque apm_t01A02_H2map {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    apm_t01A02_H2 X →+ apm_t01A02_H2 Y

theorem apm_t01a02 :
    ∀ f : C(apm_t01A02_Torus, apm_t01A02_Torus),
      ¬Function.Surjective f →
      (∀ a : apm_t01A02_H2 apm_t01A02_Torus,
        apm_t01A02_H2map f a = 0) ∧
      apm_t01A02_hasCoveringGroup
        (G := apm_t01A02_Deck) apm_t01A02_cover ∧
      ((∃ g : C(apm_t01A02_Torus, apm_t01A02_Torus),
          ∀ x, f x = apm_t01A02_cover (g x)) →
        ∃ x, f x = x) := by
  sorry
