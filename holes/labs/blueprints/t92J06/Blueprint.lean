import Mathlib

/-!
# Blueprint for APM t92J06

The quotient-wedge infrastructure is copied from the registered statement.
The two remaining declarations are the independent large construction
contracts identified by the topology audit.
-/

open Set

noncomputable section

abbrev apm_t92J06_S1 := Metric.sphere (0 : ℂ) 1

def apm_t92J06_circleBase : apm_t92J06_S1 :=
  ⟨1, by simp⟩

inductive apm_t92J06_wedgeRel :
    Sum apm_t92J06_S1 apm_t92J06_S1 →
      Sum apm_t92J06_S1 apm_t92J06_S1 → Prop
  | base : apm_t92J06_wedgeRel
      (Sum.inl apm_t92J06_circleBase) (Sum.inr apm_t92J06_circleBase)

def apm_t92J06_X :=
  Quotient (Relation.EqvGen.setoid apm_t92J06_wedgeRel)

noncomputable instance : TopologicalSpace apm_t92J06_X :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t92J06_S1 apm_t92J06_S1 ↦
      Quotient.mk (Relation.EqvGen.setoid apm_t92J06_wedgeRel) z)
    inferInstance

def apm_t92J06_inl (z : apm_t92J06_S1) : apm_t92J06_X :=
  Quotient.mk _ (.inl z)

def apm_t92J06_inr (z : apm_t92J06_S1) : apm_t92J06_X :=
  Quotient.mk _ (.inr z)

lemma apm_t92J06_continuous_inl : Continuous apm_t92J06_inl := by
  exact continuous_coinduced_rng.comp continuous_inl

lemma apm_t92J06_continuous_inr : Continuous apm_t92J06_inr := by
  exact continuous_coinduced_rng.comp continuous_inr

lemma apm_t92J06_inl_base_eq_inr_base :
    apm_t92J06_inl apm_t92J06_circleBase =
      apm_t92J06_inr apm_t92J06_circleBase := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ apm_t92J06_wedgeRel.base

lemma apm_t92J06_wedgeDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    {x y} (hxy : Relation.EqvGen apm_t92J06_wedgeRel x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
      cases hab
      exact hbase
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t92J06_wedgeDesc
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase) :
    C(apm_t92J06_X, Y) := by
  let raw : Sum apm_t92J06_S1 apm_t92J06_S1 → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw
      (fun _ _ hxy ↦ apm_t92J06_wedgeDesc_respects f g hbase hxy),
    hraw.quotient_lift
      (fun _ _ hxy ↦ apm_t92J06_wedgeDesc_respects f g hbase hxy)⟩

@[simp] lemma apm_t92J06_wedgeDesc_inl
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    (z : apm_t92J06_S1) :
    apm_t92J06_wedgeDesc f g hbase (apm_t92J06_inl z) = f z := rfl

@[simp] lemma apm_t92J06_wedgeDesc_inr
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    (z : apm_t92J06_S1) :
    apm_t92J06_wedgeDesc f g hbase (apm_t92J06_inr z) = g z := rfl

lemma apm_t92J06_wedgeDesc_unique
    {Y : Type*} [TopologicalSpace Y]
    (f g : C(apm_t92J06_S1, Y))
    (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase)
    (u : C(apm_t92J06_X, Y))
    (hul : ∀ z, u (apm_t92J06_inl z) = f z)
    (hur : ∀ z, u (apm_t92J06_inr z) = g z) :
    u = apm_t92J06_wedgeDesc f g hbase := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (z | z)
  · exact hul z
  · exact hur z

structure apm_t92J06_Covering (n : ℕ) where
  E : Type
  topology : TopologicalSpace E
  p : E → apm_t92J06_X
  covering : @IsCoveringMap E apm_t92J06_X topology _ p
  fiberCard : ∀ x : apm_t92J06_X, Nat.card {e : E // p e = x} = n

/-- LIBRARY: realize the Cayley four-regular tree as an actual simply connected
covering of the concrete quotient wedge. -/
theorem apm_t92J06_exists_simplyConnected_cover :
    ∃ (E : Type*) (_ : TopologicalSpace E) (p : E → apm_t92J06_X),
      IsCoveringMap p ∧ SimplyConnectedSpace E := by
  sorry

/-- LIBRARY: realize four explicit three-sheeted labeled graph covers and
separate the homeomorphism types of their total spaces. -/
theorem apm_t92J06_exists_four_threeSheeted_covers :
    ∃ C : Fin 4 → apm_t92J06_Covering 3,
      Pairwise fun i j ↦
        ¬ Nonempty
          (@Homeomorph (C i).E (C j).E (C i).topology (C j).topology) := by
  sorry

theorem apm_t92j06 :
    (∃ (E : Type*) (_ : TopologicalSpace E) (p : E → apm_t92J06_X),
      IsCoveringMap p ∧ SimplyConnectedSpace E) ∧
    ∃ C : Fin 4 → apm_t92J06_Covering 3,
      Pairwise fun i j ↦
        ¬ Nonempty
          (@Homeomorph (C i).E (C j).E (C i).topology (C j).topology) := by
  exact ⟨apm_t92J06_exists_simplyConnected_cover,
    apm_t92J06_exists_four_threeSheeted_covers⟩

#print axioms apm_t92j06
