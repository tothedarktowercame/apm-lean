import Mathlib
import Mathlib.Topology.Constructions.SumProd
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.CoveringMonodromyCosets

/-! # APM t98A03 — blueprint

The four mathematical conclusions are isolated as library-scale contracts.
The final theorem is only their conjunction.
-/

open scoped LinearAlgebra.Projectivization
open scoped Manifold

noncomputable section

abbrev apm_t98a03_Torus := Circle × Circle
abbrev apm_t98a03_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t98a03_RP2 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℝ) inferInstance

inductive apm_t98a03_wedgeRel
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Sum apm_t98a03_Torus apm_t98a03_RP2 →
      Sum apm_t98a03_Torus apm_t98a03_RP2 → Prop
  | base : apm_t98a03_wedgeRel t₀ r₀ (.inl t₀) (.inr r₀)

def apm_t98a03_X (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :=
  Quotient (Relation.EqvGen.setoid (apm_t98a03_wedgeRel t₀ r₀))

noncomputable instance (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    TopologicalSpace (apm_t98a03_X t₀ r₀) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t98a03_Torus apm_t98a03_RP2 ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t98a03_wedgeRel t₀ r₀)) z)
    inferInstance

def apm_t98a03_basepoint
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_X t₀ r₀ :=
  Quotient.mk _ (.inl t₀)

lemma apm_t98a03_wedge_base_eq
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    apm_t98a03_basepoint t₀ r₀ = Quotient.mk _ (.inr r₀) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t98a03_wedgeRel.base (t₀ := t₀) (r₀ := r₀)))

abbrev apm_t98a03_expectedFundamentalGroup :=
  Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative (ZMod 2))

def apm_t98a03_IsTopologicalManifold
    (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty (T2Space X) ∧
    ∃ n : ℕ,
      ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) X,
        let _ := charts
        IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 0 X

structure apm_t98a03_Cover (X : Type*) [TopologicalSpace X] where
  total : Type
  topology : TopologicalSpace total
  projection : total → X

def apm_t98a03_IsConnectedThreeFoldCover
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) : Prop :=
  letI := C.topology
  IsCoveringMap C.projection ∧
    Nonempty (ConnectedSpace C.total) ∧
    ∀ x : X, Nat.card {e : C.total // C.projection e = x} = 3

def apm_t98a03_IsRegularCover
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) : Prop :=
  letI := C.topology
  IsCoveringMap C.projection ∧
    ∀ x y : C.total, C.projection x = C.projection y →
      ∃ h : C.total ≃ₜ C.total,
        (∀ z : C.total, C.projection (h z) = C.projection z) ∧ h x = y

lemma apm_t98a03_threeFoldCover_surjective
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X)
    (hC : apm_t98a03_IsConnectedThreeFoldCover C) :
    Function.Surjective C.projection := by
  letI := C.topology
  intro x
  by_contra hx
  push_neg at hx
  letI : IsEmpty {e : C.total // C.projection e = x} :=
    ⟨fun e ↦ hx e.1 e.2⟩
  have hcard := hC.2.2 x
  simp at hcard

lemma apm_t98a03_threeFoldCover_fiber_equiv_fin_three
    {X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X)
    (hC : apm_t98a03_IsConnectedThreeFoldCover C) (x : X) :
    Nonempty ({e : C.total // C.projection e = x} ≃ Fin 3) := by
  letI := C.topology
  have hcard0 : Nat.card {e : C.total // C.projection e = x} ≠ 0 := by
    rw [hC.2.2 x]
    norm_num
  letI : Finite {e : C.total // C.projection e = x} :=
    Nat.finite_of_card_ne_zero hcard0
  letI := Fintype.ofFinite {e : C.total // C.projection e = x}
  exact ⟨Fintype.equivOfCardEq (by
    simpa [Nat.card_eq_fintype_card] using hC.2.2 x)⟩

/-- LIBRARY: the wedge point separates two punctured surface neighborhoods. -/
theorem apm_t98a03_wedge_not_manifold
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ¬apm_t98a03_IsTopologicalManifold (apm_t98a03_X t₀ r₀) := by
  sorry

/-- LIBRARY: van Kampen for this literal quotient, plus the torus and RP² computations. -/
theorem apm_t98a03_fundamentalGroup
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    Nonempty
      (FundamentalGroup (apm_t98a03_X t₀ r₀) (apm_t98a03_basepoint t₀ r₀) ≃*
        apm_t98a03_expectedFundamentalGroup) := by
  sorry

/-- LIBRARY: realize the cyclic transitive action on `Fin 3` as a cover. -/
theorem apm_t98a03_regular_threeFoldCover
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ C : apm_t98a03_Cover (apm_t98a03_X t₀ r₀),
      apm_t98a03_IsConnectedThreeFoldCover C ∧ apm_t98a03_IsRegularCover C := by
  sorry

/-- LIBRARY: realize the transitive `S₃` action with nonnormal point stabilizer. -/
theorem apm_t98a03_irregular_threeFoldCover
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    ∃ C : apm_t98a03_Cover (apm_t98a03_X t₀ r₀),
      apm_t98a03_IsConnectedThreeFoldCover C ∧ ¬apm_t98a03_IsRegularCover C := by
  sorry

theorem apm_t98a03
    (t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) :
    let X := apm_t98a03_X t₀ r₀
    let x₀ := apm_t98a03_basepoint t₀ r₀
    (¬apm_t98a03_IsTopologicalManifold X) ∧
    Nonempty
      (FundamentalGroup X x₀ ≃* apm_t98a03_expectedFundamentalGroup) ∧
    (∃ C : apm_t98a03_Cover X,
      apm_t98a03_IsConnectedThreeFoldCover C ∧
        apm_t98a03_IsRegularCover C) ∧
    (∃ C : apm_t98a03_Cover X,
      apm_t98a03_IsConnectedThreeFoldCover C ∧
        ¬apm_t98a03_IsRegularCover C) := by
  exact ⟨apm_t98a03_wedge_not_manifold t₀ r₀,
    apm_t98a03_fundamentalGroup t₀ r₀,
    apm_t98a03_regular_threeFoldCover t₀ r₀,
    apm_t98a03_irregular_threeFoldCover t₀ r₀⟩

#print axioms apm_t98a03
