# Proof Outline: a96A07

## Problem

g is analytic in a neighborhood of the closed unit disk and one-to-one on the unit circle.
Show g maps Δ one-to-one onto the bounded domain D whose boundary is C = g(Γ).

## Proof strategy (informal)

1. g(Γ) = C is a Jordan curve (injective continuous image of a circle).
2. By the argument principle: for w ∉ C, the number of preimages of w under g in Δ
   equals the winding number of C around w.
3. Since C is a simple closed curve, winding number is 1 for interior, 0 for exterior.
4. Each interior point has exactly one preimage → g is injective and surjective onto D.

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Complete, no sorry.  Axioms: propext, Classical.choice, Quot.sound.
- **Route**: the Lean proof does not follow the strategy above.  Mathlib has no Jordan curve theorem
  or winding number, and the theorem needs only "the disk zero count of `g - w` is at most 1 off the
  curve".  That follows from local constancy, vanishing far away, a jump of one across the curve
  (factor through `dslope` and apply Rouché) and at most one bounded complementary component
  (Borsuk's logarithm criterion).  `holes/labs/blueprints/a96A07/BLUEPRINT.md` has the argument.
- **Informal solution**: its Step 2 does not follow, its sign argument should use `N >= 0`, and its
  Step 4 is unnecessary.  `holes/labs/tutor/lessons/a96A07.md` explains each.
