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

open scoped Topology unitInterval

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

@[simp] lemma apm_t01j02_homotopyMap_id
    {N X : Type*} [TopologicalSpace X] (x : X) (a : HomotopyGroup N X x) :
    apm_t01j02_homotopyMap (ContinuousMap.id X) x a = a := by
  induction a using Quotient.inductionOn with
  | _ a => rfl

@[simp] lemma apm_t01j02_homotopyMap_comp
    {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y)) (x : X)
    (a : HomotopyGroup N X x) :
    apm_t01j02_homotopyMap g (f x) (apm_t01j02_homotopyMap f x a) =
      apm_t01j02_homotopyMap (g.comp f) x a := by
  induction a using Quotient.inductionOn with
  | _ a => rfl

/-- Covering maps are injective on the quotient model as soon as the cube has
a boundary point.  This uses Mathlib's relative-homotopy lifting equivalence
directly and avoids any connectivity theorem for the cube boundary. -/
lemma apm_t01j02_homotopyMap_injective_of_boundary_nonempty
    {N X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PreconnectedSpace (N → Set.Icc (0 : ℝ) 1)] (p : E → X)
    (hp : IsCoveringMap p) (e : E) (y : I^N) (hy : y ∈ Cube.boundary N) :
    Function.Injective (apm_t01j02_homotopyMap (N := N) ⟨p, hp.continuous⟩ e) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ a =>
    induction b using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      change a.1.HomotopicRel b.1 (Cube.boundary N)
      apply (hp.homotopicRel_iff_comp
        ⟨y, hy, a.2 y hy |>.trans (b.2 y hy).symm⟩).mpr
      exact Quotient.exact hab

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
  CLOSER HOP 2 boundary. The action on quotient representatives is exposed by
  `apm_t01j02_homotopyMap_mk`; identity and composition laws are now compiled
  as `apm_t01j02_homotopyMap_id` and `apm_t01j02_homotopyMap_comp`.

  Going beyond the prior boundary search, injectivity no longer requires a
  separate connectivity construction for the cube boundary. Mathlib's
  `IsCoveringMap.homotopicRel_iff_comp` applies directly to two generalized
  loops on the preconnected cube: they agree at any chosen boundary point,
  and a relative homotopy of their projections therefore lifts to a relative
  homotopy upstairs. This is compiled in
  `apm_t01j02_homotopyMap_injective_of_boundary_nonempty`. For `Fin n`, the
  hypothesis `2 ≤ n` trivially supplies such a boundary point; transporting
  injectivity across `hbase` is routine equality recasting.

  Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts` applies to the
  cube `I^(Fin n)`, since it is simply connected and locally path connected.
  It therefore supplies a unique lift of every representative cube map after
  fixing the value at one corner. To make that lift a `GenLoop`, however, one
  must prove it equals `xtilde₀` on the *entire cube boundary*. This follows
  because the boundary of an n-cube is path connected for `2 ≤ n`, and each
  boundary path lifts the constant base path uniquely. Searches found no
  `PathConnected (Cube.boundary (Fin n))` theorem or equivalent packaged
  boundary-path construction.

  Thus only surjectivity retains the substantial missing step: after lifting
  a cube representative with `existsUnique_continuousMap_lifts`, show that the
  lift is constant on the entire boundary. A second source inspection found
  no boundary-connectedness theorem, sphere/cube-boundary homeomorphism, or
  alternative higher-homotopy covering theorem. The earlier searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, closed artifacts, both Mathlib
  homotopy files, cube/product connectivity, and git history likewise provide
  no packaged surjectivity bridge.
  -/
  sorry
