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

@[simp] lemma apm_t01j02_homotopyMap_mk
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : GenLoop N X x) :
    apm_t01j02_homotopyMap f x (Quotient.mk _ a) =
      Quotient.mk _ (apm_t01j02_genLoopMap f x a) := rfl

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
  /-
  CLOSER HOP 1 boundary. The action on quotient representatives is now exposed
  by `apm_t01j02_homotopyMap_mk`.

  Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts` applies to the
  cube `I^(Fin n)`, since it is simply connected and locally path connected.
  It therefore supplies a unique lift of every representative cube map after
  fixing the value at one corner. To make that lift a `GenLoop`, however, one
  must prove it equals `xtilde₀` on the *entire cube boundary*. This follows
  because the boundary of an n-cube is path connected for `2 ≤ n`, and each
  boundary path lifts the constant base path uniquely. Searches found no
  `PathConnected (Cube.boundary (Fin n))` theorem or equivalent packaged
  boundary-path construction.

  Injectivity has the parallel missing step. `IsCoveringMap.liftHomotopy`
  lifts a homotopy between projected generalized loops, but its restriction to
  every boundary point must be identified with the constant lift throughout
  the homotopy parameter. After those relative-boundary facts are established,
  lift uniqueness gives inverse maps on quotient classes directly.

  Searches covered `LEMMA-INDEX.md`, every `ConstructionTargets/` module,
  closed homotopy/covering artifacts, Mathlib's `HomotopyGroup.lean` and
  `Topology/Homotopy/Lifting.lean`, cube-boundary and product-connectivity
  APIs, and git history. The general lifting theorems were found and are
  usable; the dimension-dependent cube-boundary connectivity assembly was
  not, so the bijectivity bridge remains open.
  -/
  sorry
