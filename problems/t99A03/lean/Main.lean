import Mathlib.Topology.Homotopy.Lifting

/-! # APM t99A03: fixed points on a wedge and a connected sum

## Statement repairs

The fixed-point assertion for the fourfold wedge is NOT encoded: Mathlib lacks
the projective-plane/wedge model and the Lefschetz fixed-point theorem needed to
state it without inventing a proxy.  The theorem encodes the decisive geometric
mechanism for the connected-sum counterexample: a nonidentity deck
transformation of a connected covering has no fixed point.

The identification of the particular double cover of `#³ ℝP²` with `#⁴ ℝP²`
is likewise omitted because connected sums and surface classification are not
available in Mathlib.

## Encoding questions

A deck transformation is represented by a homeomorphism `τ` over the base.
Connectedness of the covering space is the hypothesis that makes a deck
transformation fixing one point equal to the identity.
-/

theorem apm_t99a03
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] (p : E → B) (hp : IsCoveringMap p)
    (τ : E ≃ₜ E) (hdeck : p ∘ τ = p) (hne : τ ≠ Homeomorph.refl E) :
    ∀ x : E, τ x ≠ x := by
  sorry
