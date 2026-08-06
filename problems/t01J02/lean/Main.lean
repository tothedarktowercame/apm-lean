import Mathlib

/-!
# APM t01J02

## Statement repairs

The concluding display in the source has `π_n(X, x_n)`. This is repaired to
`π_n(X, x₀)`, matching the fixed basepoint used everywhere else in the problem.

## Encoding questions

Mathlib defines higher homotopy groups as `HomotopyGroup.Pi`, but currently has
no packaged map on those quotients induced by a pointed continuous map. The
typed placeholder below denotes exactly that quotient-induced map. Its source,
target, underlying covering projection, and basepoint equation are retained;
the theorem asserts that this specific induced map is bijective.
-/

noncomputable section

open scoped Topology

opaque apm_t01j02_inducedMap
    {X Xtilde : Type*} [TopologicalSpace X] [TopologicalSpace Xtilde]
    (n : ℕ) (p : Xtilde → X) (xtilde₀ : Xtilde) (x₀ : X)
    (hbase : p xtilde₀ = x₀) :
    HomotopyGroup.Pi n Xtilde xtilde₀ → HomotopyGroup.Pi n X x₀

theorem apm_t01j02
    (n : ℕ) (hn : 2 ≤ n)
    (X Xtilde : Type*) [TopologicalSpace X] [TopologicalSpace Xtilde]
    (xtilde₀ : Xtilde) (x₀ : X)
    (p : Xtilde → X) (hp : IsCoveringMap p)
    (hbase : p xtilde₀ = x₀) :
    Function.Bijective
      (apm_t01j02_inducedMap n p xtilde₀ x₀ hbase) := by
  sorry
