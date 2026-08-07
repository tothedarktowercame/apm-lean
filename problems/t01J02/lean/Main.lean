import Mathlib

/-!
# APM t01J02

## Statement repairs

The concluding display in the source has `π_n(X, x_n)`. This is repaired to
`π_n(X, x₀)`, matching the fixed basepoint used everywhere else in the problem.
The former statement's induced map was opaque; it is replaced by the actual
map on Mathlib's quotient model of the higher homotopy group.

## Encoding questions

Mathlib defines higher homotopy groups as quotients of generalized cube loops
relative to the cube boundary, but currently has no packaged functorial map.
The definitions below construct it directly by postcomposition and
`Quotient.map`.
-/

noncomputable section

open scoped Topology

def apm_t01j02_genLoopMap
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : GenLoop N X x) : GenLoop N Y (f x) :=
  ⟨f.comp a.1, fun y hy ↦ by simp only [ContinuousMap.comp_apply]; rw [a.2 y hy]⟩

def apm_t01j02_homotopyMap
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (apm_t01j02_genLoopMap f x) fun _ _ h ↦
    ContinuousMap.HomotopicRel.comp_continuousMap h f

def apm_t01j02_inducedMap
    {X Xtilde : Type*} [TopologicalSpace X] [TopologicalSpace Xtilde]
    (n : ℕ) (p : C(Xtilde, X)) (xtilde₀ : Xtilde) (x₀ : X)
    (hbase : p xtilde₀ = x₀) :
    HomotopyGroup.Pi n Xtilde xtilde₀ → HomotopyGroup.Pi n X x₀ :=
  fun a ↦ hbase ▸ apm_t01j02_homotopyMap p xtilde₀ a

theorem apm_t01j02
    (n : ℕ) (hn : 2 ≤ n)
    (X Xtilde : Type*) [TopologicalSpace X] [TopologicalSpace Xtilde]
    (xtilde₀ : Xtilde) (x₀ : X)
    (p : Xtilde → X) (hp : IsCoveringMap p)
    (hbase : p xtilde₀ = x₀) :
    Function.Bijective
      (apm_t01j02_inducedMap n ⟨p, hp.continuous⟩ xtilde₀ x₀ hbase) := by
  sorry
