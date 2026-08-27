import ConstructionTargets.HigherHomotopyCoveringSurjectivity

/-! # Frozen-facing adapter for higher-homotopy covering maps -/

open scoped Topology unitInterval
noncomputable section

namespace ConstructionTargets.HigherHomotopyCoveringFrozenAdapter

open HigherHomotopyCoveringSurjectivity

/-- The frozen induced-map interface: postcomposition on the `Fin n` cube
quotient, followed only by transport along the supplied basepoint equality. -/
def inducedMap
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (n : ℕ) (p : C(E, X)) (e : E) (x : X) (hbase : p e = x) :
    HomotopyGroup.Pi n E e → HomotopyGroup.Pi n X x :=
  fun q ↦ hbase ▸ homotopyMap p e q

/-- With the target basepoint written as `p e`, the frozen-facing map is
definitionally the generic quotient map. -/
@[simp] theorem inducedMap_rfl
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (n : ℕ) (p : C(E, X)) (e : E) :
    inducedMap n p e (p e) rfl = homotopyMap p e := rfl

/-- Pointwise form of the same definitional comparison. -/
@[simp] theorem inducedMap_rfl_apply
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (n : ℕ) (p : C(E, X)) (e : E) (q : HomotopyGroup.Pi n E e) :
    inducedMap n p e (p e) rfl q = homotopyMap p e q := rfl

/-- Bijectivity transports across the supplied basepoint equality.  All
mathematical content is the compiled covering-map bijection; this theorem only
performs the dependent equality cast present in the frozen statement. -/
theorem inducedMap_bijective
    (n : ℕ) (hn : 2 ≤ n)
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (e : E) (x : X) (p : E → X) (hp : IsCoveringMap p)
    (hbase : p e = x) :
    Function.Bijective
      (inducedMap n ⟨p, hp.continuous⟩ e x hbase) := by
  subst x
  simpa [inducedMap] using
    (fin_homotopyMap_bijective n hn p hp e)

/-- The surjective half is exposed separately for callers whose injectivity
proof is already part of the frozen file. -/
theorem inducedMap_surjective
    (n : ℕ) (hn : 2 ≤ n)
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (e : E) (x : X) (p : E → X) (hp : IsCoveringMap p)
    (hbase : p e = x) :
    Function.Surjective
      (inducedMap n ⟨p, hp.continuous⟩ e x hbase) :=
  (inducedMap_bijective n hn e x p hp hbase).2

#print axioms inducedMap_rfl
#print axioms inducedMap_rfl_apply
#print axioms inducedMap_bijective
#print axioms inducedMap_surjective

end ConstructionTargets.HigherHomotopyCoveringFrozenAdapter
