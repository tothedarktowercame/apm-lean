import Mathlib
import ConstructionTargets.CubeBoundaryPathConnected
import ConstructionTargets.HigherHomotopyCoveringSurjectivity
import ConstructionTargets.HigherHomotopyCoveringFrozenAdapter

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

/-- The injective half of the main theorem, specialized to the actual
`Fin n` cube and transported across the frozen basepoint equality. -/
lemma apm_t01j02_inducedMap_injective
    (n : ℕ) (hn : 2 ≤ n)
    {X Xtilde : Type*} [TopologicalSpace X] [TopologicalSpace Xtilde]
    (xtilde₀ : Xtilde) (x₀ : X) (p : Xtilde → X)
    (hp : IsCoveringMap p) (hbase : p xtilde₀ = x₀) :
    Function.Injective
      (apm_t01j02_inducedMap n ⟨p, hp.continuous⟩ xtilde₀ x₀ hbase) := by
  subst x₀
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let i : Fin n := ⟨0, hnpos⟩
  let y : I^(Fin n) := fun _ ↦ 0
  have hy : y ∈ Cube.boundary (Fin n) := ⟨i, Or.inl rfl⟩
  simpa [apm_t01j02_inducedMap] using
    (apm_t01j02_homotopyMap_injective_of_boundary_nonempty
      (N := Fin n) p hp xtilde₀ y hy)

/-- Why this unblocks `apm_t01j02`: path connectedness propagates the chosen
corner value of a covering lift across the entire cube boundary by uniqueness
of path lifting.  The lift therefore bundles as a `GenLoop`, which gives
surjectivity of the induced map on the homotopy quotient. -/
theorem apm_t01J02_bridge_pathConnectedSpace_cube_boundary
    (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace ↥(Cube.boundary (Fin n)) := by
  exact
    ConstructionTargets.CubeBoundaryPathConnected.cubeBoundary_pathConnectedSpace
      n hn

theorem apm_t01j02
    (n : ℕ) (hn : 2 ≤ n)
    (X Xtilde : Type*) [TopologicalSpace X] [TopologicalSpace Xtilde]
    (xtilde₀ : Xtilde) (x₀ : X)
    (p : Xtilde → X) (hp : IsCoveringMap p)
    (hbase : p xtilde₀ = x₀) :
    Function.Bijective
      (apm_t01j02_inducedMap n ⟨p, hp.continuous⟩ xtilde₀ x₀ hbase) := by
  /-
  `CubeBoundaryPathConnected` supplies boundary path connectedness.
  `HigherHomotopyCoveringSurjectivity` uses it to make the covering lift
  constant on the boundary and proves bijectivity on the cube quotient.
  `HigherHomotopyCoveringFrozenAdapter` transports that theorem across
  `hbase`; unfolding shows its induced map is exactly the frozen map above.
  -/
  simpa [apm_t01j02_inducedMap,
    ConstructionTargets.HigherHomotopyCoveringFrozenAdapter.inducedMap,
    apm_t01j02_homotopyMap,
    ConstructionTargets.HigherHomotopyCoveringSurjectivity.homotopyMap,
    apm_t01j02_genLoopMap,
    ConstructionTargets.HigherHomotopyCoveringSurjectivity.genLoopMap] using
    (ConstructionTargets.HigherHomotopyCoveringFrozenAdapter.inducedMap_bijective
      n hn xtilde₀ x₀ p hp hbase)
