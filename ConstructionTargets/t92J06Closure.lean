import Mathlib

/-!
# Reusable quotient-wedge API for t92J06

This module isolates the sorry-free target-space layer from the reviewed
closure blueprint.  Later graph-realization milestones can import this model
without depending on the registered problem file.
-/

open Set

noncomputable section

namespace ConstructionTargets.t92J06Closure

abbrev S1 := Metric.sphere (0 : ℂ) 1

def circleBase : S1 := ⟨1, by simp⟩

inductive WedgeRel : Sum S1 S1 → Sum S1 S1 → Prop
  | base : WedgeRel (.inl circleBase) (.inr circleBase)

def X := Quotient (Relation.EqvGen.setoid WedgeRel)

noncomputable instance : TopologicalSpace X :=
  TopologicalSpace.coinduced
    (fun z : Sum S1 S1 => Quotient.mk (Relation.EqvGen.setoid WedgeRel) z)
    inferInstance

def inl (z : S1) : X := Quotient.mk _ (.inl z)

def inr (z : S1) : X := Quotient.mk _ (.inr z)

theorem continuous_leftLeg : Continuous inl :=
  continuous_coinduced_rng.comp continuous_inl

theorem continuous_rightLeg : Continuous inr :=
  continuous_coinduced_rng.comp continuous_inr

theorem inl_base_eq_inr_base : inl circleBase = inr circleBase := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ WedgeRel.base

private def leftCoordinate : Sum S1 S1 → S1
  | .inl z => z
  | .inr _ => circleBase

private def rightCoordinate : Sum S1 S1 → S1
  | .inl _ => circleBase
  | .inr z => z

private theorem leftCoordinate_eq_of_eqvGen {a b : Sum S1 S1}
    (h : Relation.EqvGen WedgeRel a b) : leftCoordinate a = leftCoordinate b := by
  induction h with
  | rel _ _ hab => cases hab; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem rightCoordinate_eq_of_eqvGen {a b : Sum S1 S1}
    (h : Relation.EqvGen WedgeRel a b) : rightCoordinate a = rightCoordinate b := by
  induction h with
  | rel _ _ hab => cases hab; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The left circle embeds in the quotient wedge. -/
theorem inl_injective : Function.Injective inl := by
  intro z w h
  exact leftCoordinate_eq_of_eqvGen (Quotient.exact h)

/-- The right circle embeds in the quotient wedge. -/
theorem inr_injective : Function.Injective inr := by
  intro z w h
  exact rightCoordinate_eq_of_eqvGen (Quotient.exact h)

/-- The two embedded circle legs meet exactly at their common basepoint. -/
theorem inl_eq_inr_iff (z w : S1) :
    inl z = inr w ↔ z = circleBase ∧ w = circleBase := by
  constructor
  · intro h
    exact ⟨leftCoordinate_eq_of_eqvGen (Quotient.exact h),
      (rightCoordinate_eq_of_eqvGen (Quotient.exact h)).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact inl_base_eq_inr_base

theorem wedgeDesc_respects {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase)
    {x y} (hxy : Relation.EqvGen WedgeRel x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel _ _ hab => cases hab; exact hbase
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def wedgeDesc {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase) : C(X, Y) := by
  let raw : Sum S1 S1 → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy => wedgeDesc_respects f g hbase hxy),
    hraw.quotient_lift (fun _ _ hxy => wedgeDesc_respects f g hbase hxy)⟩

@[simp] theorem wedgeDesc_inl {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase) (z : S1) :
    wedgeDesc f g hbase (inl z) = f z := rfl

@[simp] theorem wedgeDesc_inr {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase) (z : S1) :
    wedgeDesc f g hbase (inr z) = g z := rfl

theorem wedgeDesc_unique {Y : Type*} [TopologicalSpace Y]
    (f g : C(S1, Y)) (hbase : f circleBase = g circleBase)
    (u : C(X, Y)) (hul : ∀ z, u (inl z) = f z)
    (hur : ∀ z, u (inr z) = g z) : u = wedgeDesc f g hbase := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (z | z)
  · exact hul z
  · exact hur z

/-- A finite-sheeted covering of the reusable wedge model with exact fibers. -/
structure Covering (n : ℕ) where
  E : Type
  topology : TopologicalSpace E
  p : E → X
  covering : @IsCoveringMap E X topology _ p
  fiberCard : ∀ x : X, Nat.card {e : E // p e = x} = n

/-! ## Combinatorial graph-cover data -/

/-- A labeled directed graph over the two-loop rose.  Invertibility of each
transition is the combinatorial local-covering condition. -/
structure TwoLoopGraphCoverData (V : Type*) where
  step : Fin 2 → Equiv.Perm V

namespace TwoLoopGraphCoverData

variable {V : Type*} (D : TwoLoopGraphCoverData V)

abbrev Edge (V : Type*) := Fin 2 × V

def source (e : Edge V) : V := e.2

def target (e : Edge V) : V := D.step e.1 e.2

/-- The outgoing labeled star at every vertex is exactly the two labels. -/
def outgoingStarEquiv (v : V) : {e : Edge V // source e = v} ≃ Fin 2 where
  toFun e := e.1.1
  invFun i := ⟨(i, v), rfl⟩
  left_inv e := by
    rcases e with ⟨⟨i, w⟩, hw⟩
    simp only [source] at hw
    subst w
    rfl
  right_inv _ := rfl

/-- Invertibility of the transitions makes the incoming labeled star exactly
the two labels as well. -/
def incomingStarEquiv (v : V) : {e : Edge V // D.target e = v} ≃ Fin 2 where
  toFun e := e.1.1
  invFun i := ⟨(i, (D.step i).symm v), (D.step i).apply_symm_apply v⟩
  left_inv e := by
    rcases e with ⟨⟨i, w⟩, hw⟩
    simp only [target] at hw
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (D.step i).injective ((D.step i).apply_symm_apply _ |>.trans hw.symm)
  right_inv _ := rfl

/-- The Cayley graph transition datum for the free group on two generators. -/
def cayleyData : TwoLoopGraphCoverData (FreeGroup (Fin 2)) where
  step i := Equiv.mulRight (FreeGroup.of i)

private def finThreeSwap : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private def finThreeCycle : Equiv.Perm (Fin 3) := Equiv.addRight 1

/-- The four permutation pairs from the reviewed blueprint. -/
def threeSheetData : Fin 4 → TwoLoopGraphCoverData (Fin 3) := ![
  ⟨fun _ ↦ Equiv.refl (Fin 3)⟩,
  ⟨fun _ ↦ finThreeSwap⟩,
  ⟨fun i ↦ if i = 0 then finThreeCycle else Equiv.refl (Fin 3)⟩,
  ⟨fun _ ↦ finThreeCycle⟩]

/-! ## Topological realization carrier -/

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- Vertices together with one closed interval for every labeled directed
edge. -/
abbrev RealizationRaw (V : Type*) := V ⊕ (Fin 2 × V × UnitInterval)

def intervalZero : UnitInterval := ⟨0, by simp⟩

def intervalOne : UnitInterval := ⟨1, by simp⟩

/-- Endpoint identifications for the graph realization.  The initial endpoint
is glued to the source vertex and the terminal endpoint to the vertex selected
by the corresponding transition permutation. -/
inductive RealizationRel : RealizationRaw V → RealizationRaw V → Prop
  | source (i : Fin 2) (v : V) :
      RealizationRel (.inr (i, v, intervalZero)) (.inl v)
  | target (i : Fin 2) (v : V) :
      RealizationRel (.inr (i, v, intervalOne)) (.inl (D.step i v))

abbrev Realization := Quotient (Relation.EqvGen.setoid D.RealizationRel)

noncomputable instance realizationRawTopology : TopologicalSpace (RealizationRaw V) :=
  letI : TopologicalSpace V := ⊥
  inferInstance

noncomputable instance realizationTopology : TopologicalSpace D.Realization :=
  TopologicalSpace.coinduced
    (fun z : RealizationRaw V => Quotient.mk (Relation.EqvGen.setoid D.RealizationRel) z)
    inferInstance

/-- The raw graph realization map is the quotient authority for the topology
on the realized graph.  Openness of covering charts can therefore be checked
on their saturated raw preimages. -/
theorem realizationQuotientMap_isQuotientMap :
    Topology.IsQuotientMap
      (fun z : RealizationRaw V =>
        Quotient.mk (Relation.EqvGen.setoid D.RealizationRel) z) :=
  isQuotientMap_quotient_mk'

/-- The raw open interval belonging to one labeled lifted edge. -/
def rawEdgeInterior (i : Fin 2) (v : V) : Set (RealizationRaw V) :=
  Sum.inr '' ({i} ×ˢ ({v} ×ˢ
    {t : UnitInterval | t.1 ∈ Set.Ioo (0 : ℝ) 1}))

/-- A single lifted edge interior is open before taking the endpoint
quotient. -/
theorem rawEdgeInterior_isOpen (i : Fin 2) (v : V) :
    IsOpen (rawEdgeInterior i v) := by
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  change @IsOpen (V ⊕ (Fin 2 × V × UnitInterval))
    inferInstance (rawEdgeInterior i v)
  apply isOpenMap_inr
  exact (isOpen_discrete ({i} : Set (Fin 2))).prod
    ((isOpen_discrete ({v} : Set V)).prod
      (isOpen_Ioo.preimage continuous_subtype_val))

/-- The full raw chart above one open base edge, obtained by taking all
vertex-labelled lifted edge interiors. -/
def rawEdgeChart (V : Type*) (i : Fin 2) : Set (RealizationRaw V) :=
  ⋃ v : V, rawEdgeInterior i v

/-- The full raw edge chart is open. -/
theorem rawEdgeChart_isOpen (i : Fin 2) : IsOpen (rawEdgeChart V i) := by
  unfold rawEdgeChart
  exact isOpen_iUnion (fun v => rawEdgeInterior_isOpen (V := V) i v)

def vertex (v : V) : D.Realization := Quotient.mk _ (.inl v)

def edgePoint (i : Fin 2) (v : V) (t : UnitInterval) : D.Realization :=
  Quotient.mk _ (.inr (i, v, t))

theorem edgePoint_zero (i : Fin 2) (v : V) :
    D.edgePoint i v intervalZero = D.vertex v := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (RealizationRel.source i v)

theorem edgePoint_one (i : Fin 2) (v : V) :
    D.edgePoint i v intervalOne = D.vertex (D.step i v) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (RealizationRel.target i v)

/-! ## Projection to the two-loop wedge -/

/-- Traverse the unit circle once while the interval parameter runs from zero
to one. -/
def intervalCircle : C(UnitInterval, S1) :=
  ⟨fun t => Circle.exp (2 * Real.pi * t.1),
    Circle.exp.continuous.comp
      (continuous_const.mul continuous_subtype_val)⟩

@[simp] theorem intervalCircle_zero : intervalCircle intervalZero = circleBase := by
  change Circle.exp (2 * Real.pi * 0) = 1
  simp

@[simp] theorem intervalCircle_one : intervalCircle intervalOne = circleBase := by
  change Circle.exp (2 * Real.pi * 1) = 1
  rw [mul_one]
  exact Circle.exp_two_pi

/-- Every circle point has a representative in the closed unit interval. -/
theorem intervalCircle_surjective : Function.Surjective intervalCircle := by
  intro z
  by_cases hz : 0 ≤ Complex.arg (z : ℂ)
  · let t : UnitInterval :=
      ⟨Complex.arg (z : ℂ) / (2 * Real.pi), by
        constructor
        · positivity
        · have hp := Real.pi_pos
          have ha := Complex.arg_le_pi (z : ℂ)
          apply (div_le_one (by positivity)).2
          linarith⟩
    refine ⟨t, ?_⟩
    change Circle.exp (2 * Real.pi *
      (Complex.arg (z : ℂ) / (2 * Real.pi))) = z
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0)]
    exact Circle.exp_arg z
  · let t : UnitInterval :=
      ⟨(Complex.arg (z : ℂ) + 2 * Real.pi) / (2 * Real.pi), by
        constructor
        · have hp := Real.pi_pos
          have ha := Complex.neg_pi_lt_arg (z : ℂ)
          exact le_of_lt (div_pos (by linarith) (by positivity))
        · have hp := Real.pi_pos
          have ha : Complex.arg (z : ℂ) < 0 := lt_of_not_ge hz
          apply (div_le_one (by positivity)).2
          linarith⟩
    refine ⟨t, ?_⟩
    change Circle.exp (2 * Real.pi *
      ((Complex.arg (z : ℂ) + 2 * Real.pi) / (2 * Real.pi))) = z
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0)]
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
    exact Circle.exp_arg z

/-- Equality along the closed interval parametrization is literal except for
the two endpoint representatives of the circle basepoint. -/
theorem intervalCircle_eq_imp_coordinate_cases (t u : UnitInterval)
    (h : intervalCircle t = intervalCircle u) :
    t = u ∨ (t = intervalZero ∧ u = intervalOne) ∨
      (t = intervalOne ∧ u = intervalZero) := by
  change Circle.exp (2 * Real.pi * t.1) =
    Circle.exp (2 * Real.pi * u.1) at h
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h
  have hp : 0 < Real.pi := Real.pi_pos
  have htu : (t : ℝ) = u + k := by
    nlinarith
  have hkloR : (-1 : ℝ) ≤ k := by nlinarith [t.2.1, u.2.2]
  have hkhiR : (k : ℝ) ≤ 1 := by nlinarith [t.2.2, u.2.1]
  have hklo : (-1 : ℤ) ≤ k := by exact_mod_cast hkloR
  have hkhi : k ≤ (1 : ℤ) := by exact_mod_cast hkhiR
  rcases (show k = -1 ∨ k = 0 ∨ k = 1 by omega) with rfl | rfl | rfl
  · right; left
    norm_num at htu
    constructor
    · apply Subtype.ext
      dsimp [intervalZero]
      nlinarith [t.2.1, u.2.2]
    · apply Subtype.ext
      dsimp [intervalOne]
      nlinarith [t.2.1, u.2.2]
  · left
    norm_num at htu
    exact Subtype.ext htu
  · right; right
    norm_num at htu
    constructor
    · apply Subtype.ext
      dsimp [intervalOne]
      nlinarith [t.2.2, u.2.1]
    · apply Subtype.ext
      dsimp [intervalZero]
      nlinarith [t.2.2, u.2.1]

/-- The edge parametrization is injective away from the glued endpoints. -/
theorem intervalCircle_injective_on_interior :
    Set.InjOn intervalCircle {t : UnitInterval | t.1 ∈ Set.Ioo (0 : ℝ) 1} := by
  intro t ht u hu h
  rcases intervalCircle_eq_imp_coordinate_cases t u h with htu | hends | hends
  · exact htu
  · rcases hends with ⟨rfl, rfl⟩
    exact False.elim (lt_irrefl (0 : ℝ) ht.1)
  · rcases hends with ⟨rfl, rfl⟩
    exact False.elim (lt_irrefl (1 : ℝ) ht.2)

/-- An interior interval parameter never represents the circle basepoint. -/
theorem intervalCircle_ne_base {t : UnitInterval}
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1) : intervalCircle t ≠ circleBase := by
  intro h
  have h0 : intervalCircle t = intervalCircle intervalZero := by simpa using h
  rcases intervalCircle_eq_imp_coordinate_cases t intervalZero h0 with htz | hends | hends
  · subst t
    exact (lt_irrefl (0 : ℝ)) ht.1
  · have hz : intervalZero ≠ intervalOne := by
      intro hz
      have := congrArg Subtype.val hz
      norm_num [intervalZero, intervalOne] at this
    exact hz hends.2
  · rw [hends.1] at ht
    exact (lt_irrefl (1 : ℝ)) ht.2

/-- The open interval parametrizes precisely the circle with its basepoint
removed.  This is the base-space input for the open edge charts used by the
covering trivializations. -/
theorem intervalCircle_image_interior :
    intervalCircle '' {t : UnitInterval | t.1 ∈ Set.Ioo (0 : ℝ) 1} =
      {z : S1 | z ≠ circleBase} := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact intervalCircle_ne_base ht
  · intro hz
    obtain ⟨t, rfl⟩ := intervalCircle_surjective z
    refine ⟨t, ?_, rfl⟩
    constructor
    · apply lt_of_le_of_ne t.2.1
      intro h
      apply hz
      have : t = intervalZero := by
        apply Subtype.ext
        simpa [intervalZero] using h.symm
      simpa [this]
    · apply lt_of_le_of_ne t.2.2
      intro h
      apply hz
      have : t = intervalOne := by
        apply Subtype.ext
        simpa [intervalOne] using h
      simpa [this]

/-- The two interval labels map to the two circle legs of the rose. -/
def edgeProjection (i : Fin 2) : C(UnitInterval, X) :=
  Fin.cases
    ⟨fun t => inl (intervalCircle t),
      continuous_leftLeg.comp intervalCircle.continuous⟩
    (fun _ =>
      ⟨fun t => inr (intervalCircle t),
        continuous_rightLeg.comp intervalCircle.continuous⟩) i

@[simp] theorem edgeProjection_zero (i : Fin 2) :
    edgeProjection i intervalZero = inl circleBase := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [edgeProjection]
  exact inl_base_eq_inr_base.symm

@[simp] theorem edgeProjection_one (i : Fin 2) :
    edgeProjection i intervalOne = inl circleBase := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [edgeProjection]
  exact inl_base_eq_inr_base.symm

/-- Away from the wedge vertex, the projection remembers both the edge label
and its interval coordinate. -/
theorem edgeProjection_eq_of_interior (i j : Fin 2) (t u : UnitInterval)
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1) (hu : u.1 ∈ Set.Ioo (0 : ℝ) 1)
    (h : edgeProjection i t = edgeProjection j u) : i = j ∧ t = u := by
  fin_cases i <;> fin_cases j
  · refine ⟨rfl, intervalCircle_injective_on_interior ht hu ?_⟩
    exact inl_injective h
  · exfalso
    have hb := (inl_eq_inr_iff (intervalCircle t) (intervalCircle u)).mp h
    exact intervalCircle_ne_base ht hb.1
  · exfalso
    have hb := (inl_eq_inr_iff (intervalCircle u) (intervalCircle t)).mp h.symm
    exact intervalCircle_ne_base hu hb.1
  · refine ⟨rfl, intervalCircle_injective_on_interior ht hu ?_⟩
    exact inr_injective h

/-- An interior point of either labeled base edge is distinct from the wedge
vertex. -/
theorem edgeProjection_ne_wedgePoint (i : Fin 2) (t : UnitInterval)
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1) :
    edgeProjection i t ≠ inl circleBase := by
  fin_cases i
  · intro h
    exact intervalCircle_ne_base ht (inl_injective h)
  · intro h
    have hb := (inl_eq_inr_iff circleBase (intervalCircle t)).mp h.symm
    exact intervalCircle_ne_base ht hb.2

/-- The map before imposing the graph endpoint identifications. -/
def realizationRawProjection (D : TwoLoopGraphCoverData V) : RealizationRaw V → X
  | .inl _ => inl circleBase
  | .inr (i, _, t) => edgeProjection i t

theorem realizationRawProjection_respects {a b : RealizationRaw V}
    (h : Relation.EqvGen D.RealizationRel a b) :
    D.realizationRawProjection a = D.realizationRawProjection b := by
  induction h with
  | rel _ _ hab =>
      cases hab <;> simp [realizationRawProjection]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem continuous_realizationRawProjection :
    Continuous (D.realizationRawProjection : RealizationRaw V → X) := by
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  change Continuous (D.realizationRawProjection : RealizationRaw V → X)
  rw [continuous_sum_dom]
  constructor
  · exact continuous_const
  · rw [continuous_prod_of_discrete_left]
    intro i
    rw [continuous_prod_of_discrete_left]
    intro v
    exact (edgeProjection i).continuous

/-- The continuous realization map sends each graph edge homeomorphically
around the circle selected by its label. -/
def projection : C(D.Realization, X) :=
  ⟨Quotient.lift D.realizationRawProjection
      (fun _ _ h => D.realizationRawProjection_respects h),
    D.continuous_realizationRawProjection.quotient_lift
      (fun _ _ h => D.realizationRawProjection_respects h)⟩

@[simp] theorem projection_vertex (v : V) :
    D.projection (D.vertex v) = inl circleBase := rfl

@[simp] theorem projection_edgePoint (i : Fin 2) (v : V) (t : UnitInterval) :
    D.projection (D.edgePoint i v t) = edgeProjection i t := rfl

/-- A nonempty graph realization projects onto the entire two-loop wedge. -/
theorem projection_surjective [Nonempty V] : Function.Surjective D.projection := by
  intro x
  induction x using Quotient.inductionOn with
  | _ raw =>
      obtain ⟨v⟩ := (inferInstance : Nonempty V)
      cases raw with
      | inl z =>
          obtain ⟨t, ht⟩ := intervalCircle_surjective z
          exact ⟨D.edgePoint 0 v t, by
            change edgeProjection 0 t = inl z
            simp [edgeProjection, ht]⟩
      | inr z =>
          obtain ⟨t, ht⟩ := intervalCircle_surjective z
          exact ⟨D.edgePoint 1 v t, by
            change edgeProjection 1 t = inr z
            change inr (intervalCircle t) = inr z
            rw [ht]⟩

/-- Over an interior point of either circle, equality in the base already
determines the edge label and interval coordinate.  Thus the only remaining
freedom in an interior fiber is the graph vertex indexing the lifted edge. -/
theorem projection_edgePoint_eq_of_interior (i j : Fin 2) (v w : V)
    (t u : UnitInterval) (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hu : u.1 ∈ Set.Ioo (0 : ℝ) 1)
    (h : D.projection (D.edgePoint i v t) =
      D.projection (D.edgePoint j w u)) : i = j ∧ t = u := by
  apply edgeProjection_eq_of_interior i j t u ht hu
  simpa only [projection_edgePoint] using h

/-- A lifted interior edge point never coincides with a lifted graph vertex.
This is the vertex/interior separation needed for the exact local fibers. -/
theorem edgePoint_ne_vertex_of_interior (i : Fin 2) (v w : V)
    (t : UnitInterval) (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1) :
    D.edgePoint i v t ≠ D.vertex w := by
  intro h
  have hp := congrArg D.projection h
  exact edgeProjection_ne_wedgePoint i t ht (by
    simpa only [projection_edgePoint, projection_vertex] using hp)

/-- A raw realization coordinate which records precisely the points away from
the glued endpoints.  It is constant on the endpoint-generated relation. -/
noncomputable def interiorCoordinate : RealizationRaw V →
    Option (Fin 2 × V × UnitInterval)
  | .inl _ => none
  | .inr (i, v, t) =>
      if t = intervalZero ∨ t = intervalOne then none else some (i, v, t)

theorem interiorCoordinate_eq_of_eqvGen {a b : RealizationRaw V}
    (h : Relation.EqvGen D.RealizationRel a b) :
    interiorCoordinate a = interiorCoordinate b := by
  induction h with
  | rel _ _ hab =>
      cases hab <;> simp [interiorCoordinate]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Membership in a raw edge chart is exactly the presence of an interior
coordinate with the prescribed edge label. -/
theorem mem_rawEdgeChart_iff_interiorCoordinate (i : Fin 2)
    (a : RealizationRaw V) :
    a ∈ rawEdgeChart V i ↔
      ∃ v : V, ∃ t : UnitInterval,
        interiorCoordinate a = some (i, v, t) := by
  cases a with
  | inl v => simp [rawEdgeChart, rawEdgeInterior, interiorCoordinate]
  | inr ivt =>
      rcases ivt with ⟨j, v, t⟩
      simp [rawEdgeChart, rawEdgeInterior, interiorCoordinate]
      constructor
      · rintro ⟨hji, ht0, ht1⟩
        refine ⟨⟨?_, ?_⟩, hji⟩
        · intro h
          subst t
          exact (lt_irrefl (0 : ℝ)) ht0
        · intro h
          subst t
          exact (lt_irrefl (1 : ℝ)) ht1
      · rintro ⟨⟨ht0, ht1⟩, hji⟩
        refine ⟨hji, ?_, ?_⟩
        · apply lt_of_le_of_ne t.2.1
          intro h
          apply ht0
          apply Subtype.ext
          simpa [intervalZero] using h.symm
        · apply lt_of_le_of_ne t.2.2
          intro h
          apply ht1
          apply Subtype.ext
          simpa [intervalOne] using h

/-- Endpoint identifications preserve membership in a raw open-edge chart.
Thus each raw edge chart is saturated for the realization quotient. -/
theorem rawEdgeChart_mem_iff_of_eqvGen (i : Fin 2)
    {a b : RealizationRaw V} (h : Relation.EqvGen D.RealizationRel a b) :
    a ∈ rawEdgeChart V i ↔ b ∈ rawEdgeChart V i := by
  rw [mem_rawEdgeChart_iff_interiorCoordinate,
    mem_rawEdgeChart_iff_interiorCoordinate,
    D.interiorCoordinate_eq_of_eqvGen h]

/-- The open-edge chart descended to the endpoint quotient realization. -/
def edgeChart (i : Fin 2) : Set D.Realization :=
  Quotient.mk (Relation.EqvGen.setoid D.RealizationRel) '' rawEdgeChart V i

/-- The raw preimage of a descended edge chart is exactly the saturated raw
chart from which it was defined. -/
theorem realization_preimage_edgeChart (i : Fin 2) :
    (fun z : RealizationRaw V ↦
      Quotient.mk (Relation.EqvGen.setoid D.RealizationRel) z) ⁻¹'
        D.edgeChart i = rawEdgeChart V i := by
  ext a
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (D.rawEdgeChart_mem_iff_of_eqvGen i (Quotient.exact hba)).mp hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Each edge chart is open in the realized graph quotient. -/
theorem edgeChart_isOpen (i : Fin 2) : IsOpen (D.edgeChart i) := by
  rw [← D.realizationQuotientMap_isQuotientMap.isOpen_preimage,
    D.realization_preimage_edgeChart]
  exact rawEdgeChart_isOpen i

/-- Points of a descended edge chart are exactly realized interior points of
lifted edges with the prescribed base-edge label. -/
theorem mem_edgeChart_iff (i : Fin 2) (e : D.Realization) :
    e ∈ D.edgeChart i ↔
      ∃ v : V, ∃ t : UnitInterval,
        t.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ e = D.edgePoint i v t := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    change a ∈ ⋃ v, rawEdgeInterior i v at ha
    simp only [Set.mem_iUnion] at ha
    rcases ha with ⟨v, p, hp, rfl⟩
    rcases p with ⟨j, w, t⟩
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq] at hp
    rcases hp with ⟨rfl, rfl, ht⟩
    exact ⟨w, t, ht, rfl⟩
  · rintro ⟨v, t, ht, rfl⟩
    refine ⟨.inr (i, v, t), ?_, rfl⟩
    change .inr (i, v, t) ∈ ⋃ w, rawEdgeInterior i w
    simp only [Set.mem_iUnion]
    exact ⟨v, ⟨(i, v, t), by
      simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq,
        true_and]
      exact ht, rfl⟩⟩

/-- The open part of one labeled loop in the base wedge, parametrized away
from the two interval endpoints. -/
def baseEdgeChart (i : Fin 2) : Set X :=
  edgeProjection i '' {t : UnitInterval | t.1 ∈ Set.Ioo (0 : ℝ) 1}

/-- The raw preimage of a base open-edge chart is the corresponding open
circle summand with its wedge endpoint removed. -/
theorem wedge_preimage_baseEdgeChart (i : Fin 2) :
    (fun z : Sum S1 S1 =>
      (Quotient.mk (Relation.EqvGen.setoid WedgeRel) z : X)) ⁻¹'
        baseEdgeChart i =
      Fin.cases
        (Sum.inl '' {z : S1 | z ≠ circleBase})
        (fun _ => Sum.inr '' {z : S1 | z ≠ circleBase}) i := by
  have hleft : baseEdgeChart 0 = inl '' {z : S1 | z ≠ circleBase} := by
    rw [baseEdgeChart, show edgeProjection 0 = inl ∘ intervalCircle by rfl,
      Set.image_comp, intervalCircle_image_interior]
  have hright : baseEdgeChart 1 = inr '' {z : S1 | z ≠ circleBase} := by
    rw [baseEdgeChart, show edgeProjection 1 = inr ∘ intervalCircle by rfl,
      Set.image_comp, intervalCircle_image_interior]
  fin_cases i
  · change
      (fun z : Sum S1 S1 =>
        (Quotient.mk (Relation.EqvGen.setoid WedgeRel) z : X)) ⁻¹'
          baseEdgeChart 0 = Sum.inl '' {z : S1 | z ≠ circleBase}
    rw [hleft]
    ext z
    cases z with
    | inl z =>
        change (inl z ∈ inl '' {w : S1 | w ≠ circleBase}) ↔
          (Sum.inl z ∈ Sum.inl '' {w : S1 | w ≠ circleBase})
        constructor
        · rintro ⟨w, hw, h⟩
          exact ⟨z, (inl_injective h).symm ▸ hw, rfl⟩
        · rintro ⟨w, hw, h⟩
          exact ⟨z, (Sum.inl.inj h).symm ▸ hw, rfl⟩
    | inr z =>
        change (inr z ∈ inl '' {w : S1 | w ≠ circleBase}) ↔
          (Sum.inr z ∈ Sum.inl '' {w : S1 | w ≠ circleBase})
        constructor
        · rintro ⟨w, hw, h⟩
          exact False.elim (hw ((inl_eq_inr_iff w z).mp h |>.1))
        · rintro ⟨w, _, h⟩
          exfalso
          exact Sum.inl_ne_inr h
  · change
      (fun z : Sum S1 S1 =>
        (Quotient.mk (Relation.EqvGen.setoid WedgeRel) z : X)) ⁻¹'
          baseEdgeChart 1 = Sum.inr '' {z : S1 | z ≠ circleBase}
    rw [hright]
    ext z
    cases z with
    | inl z =>
        change (inl z ∈ inr '' {w : S1 | w ≠ circleBase}) ↔
          (Sum.inl z ∈ Sum.inr '' {w : S1 | w ≠ circleBase})
        constructor
        · rintro ⟨w, hw, h⟩
          exact False.elim (hw ((inl_eq_inr_iff z w).mp h.symm |>.2))
        · rintro ⟨w, _, h⟩
          exfalso
          exact Sum.inr_ne_inl h
    | inr z =>
        change (inr z ∈ inr '' {w : S1 | w ≠ circleBase}) ↔
          (Sum.inr z ∈ Sum.inr '' {w : S1 | w ≠ circleBase})
        constructor
        · rintro ⟨w, hw, h⟩
          exact ⟨z, (inr_injective h).symm ▸ hw, rfl⟩
        · rintro ⟨w, hw, h⟩
          exact ⟨z, (Sum.inr.inj h).symm ▸ hw, rfl⟩

theorem wedgeQuotientMap_isQuotientMap :
    @Topology.IsQuotientMap (Sum S1 S1) X inferInstance instTopologicalSpaceX
      (fun z : Sum S1 S1 =>
        (Quotient.mk (Relation.EqvGen.setoid WedgeRel) z : X)) :=
  ⟨Quotient.mk_surjective, rfl⟩

/-- Each base loop minus the wedge vertex is open in the quotient rose. -/
theorem baseEdgeChart_isOpen (i : Fin 2) : IsOpen (baseEdgeChart i) := by
  apply wedgeQuotientMap_isQuotientMap.isOpen_preimage.mp
  change IsOpen
    ((fun z : Sum S1 S1 =>
      (Quotient.mk (Relation.EqvGen.setoid WedgeRel) z : X)) ⁻¹'
        baseEdgeChart i)
  rw [wedge_preimage_baseEdgeChart]
  fin_cases i
  · apply isOpenMap_inl
    exact isOpen_compl_singleton
  · apply isOpenMap_inr
    exact isOpen_compl_singleton

/-- A raw endpoint remembers the graph vertex to which it is glued.  Open
edge points have no vertex coordinate. -/
noncomputable def vertexCoordinate : RealizationRaw V → Option V
  | .inl v => some v
  | .inr (i, v, t) =>
      if t = intervalZero then some v
      else if t = intervalOne then some (D.step i v)
      else none

theorem vertexCoordinate_eq_of_eqvGen {a b : RealizationRaw V}
    (h : Relation.EqvGen D.RealizationRel a b) :
    D.vertexCoordinate a = D.vertexCoordinate b := by
  induction h with
  | rel _ _ hab =>
      cases hab <;> norm_num [vertexCoordinate, intervalZero, intervalOne]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Distinct graph vertices remain distinct in the endpoint quotient. -/
theorem vertex_injective : Function.Injective D.vertex := by
  intro v w hvw
  have hc := D.vertexCoordinate_eq_of_eqvGen (Quotient.exact hvw)
  simpa [vertexCoordinate] using hc

theorem intervalCircle_eq_base_cases (t : UnitInterval)
    (h : intervalCircle t = circleBase) :
    t = intervalZero ∨ t = intervalOne := by
  have h0 : intervalCircle t = intervalCircle intervalZero := by simpa using h
  rcases intervalCircle_eq_imp_coordinate_cases t intervalZero h0 with
    htz | hends | hends
  · exact Or.inl htz
  · exact Or.inl hends.1
  · exact Or.inr hends.1

/-- Every point over the wedge vertex is represented by exactly one graph
vertex. -/
theorem existsUnique_vertex_of_projection_eq_wedgePoint
    (e : D.Realization) (he : D.projection e = inl circleBase) :
    ∃! v : V, e = D.vertex v := by
  induction e using Quotient.inductionOn with
  | _ raw =>
      cases raw with
      | inl v =>
          refine ⟨v, rfl, ?_⟩
          intro w hw
          exact D.vertex_injective hw.symm
      | inr itu =>
          rcases itu with ⟨i, v, t⟩
          have hc : intervalCircle t = circleBase := by
            fin_cases i
            · exact inl_injective (by
                simpa [projection, realizationRawProjection, edgeProjection] using he)
            · exact (inl_eq_inr_iff circleBase (intervalCircle t)).mp (by
                simpa [projection, realizationRawProjection, edgeProjection] using he.symm) |>.2
          rcases intervalCircle_eq_base_cases t hc with rfl | rfl
          · refine ⟨v, D.edgePoint_zero i v, ?_⟩
            intro w hw
            exact D.vertex_injective (hw.symm.trans (D.edgePoint_zero i v))
          · refine ⟨D.step i v, D.edgePoint_one i v, ?_⟩
            intro w hw
            exact D.vertex_injective (hw.symm.trans (D.edgePoint_one i v))

/-- The fiber over the wedge point is canonically the graph vertex type. -/
noncomputable def vertexFiberEquiv :
    {e : D.Realization // D.projection e = inl circleBase} ≃ V where
  toFun e := (D.existsUnique_vertex_of_projection_eq_wedgePoint e e.2).choose
  invFun v := ⟨D.vertex v, by simp⟩
  left_inv e := by
    apply Subtype.ext
    exact (D.existsUnique_vertex_of_projection_eq_wedgePoint e e.2).choose_spec.1.symm
  right_inv v := by
    have h := D.existsUnique_vertex_of_projection_eq_wedgePoint
      (D.vertex v) (by simp)
    exact h.unique h.choose_spec.1 rfl

/-- The complete preimage of the wedge vertex is the discrete set of graph
vertices.  This is the central fiber in a vertex covering chart. -/
theorem projection_preimage_wedgePoint :
    D.projection ⁻¹' ({inl circleBase} : Set X) = Set.range D.vertex := by
  ext e
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · intro he
    obtain ⟨v, hv, _⟩ := D.existsUnique_vertex_of_projection_eq_wedgePoint e he
    exact ⟨v, hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact D.projection_vertex v

/-- Distinct graph-edge labels cannot be identified at an interior parameter
by the endpoint quotient.  In particular, the vertex coordinate is retained
throughout each open edge. -/
theorem edgePoint_injective_of_interior (i : Fin 2) (t : UnitInterval)
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1) :
    Function.Injective (fun v : V => D.edgePoint i v t) := by
  intro v w hvw
  have ht0 : t ≠ intervalZero := by
    intro h
    rw [h] at ht
    exact (lt_irrefl (0 : ℝ)) ht.1
  have ht1 : t ≠ intervalOne := by
    intro h
    rw [h] at ht
    exact (lt_irrefl (1 : ℝ)) ht.2
  have hc := interiorCoordinate_eq_of_eqvGen D (Quotient.exact hvw)
  simp only [interiorCoordinate, ht0, ht1, false_or, if_false,
    Option.some.injEq, Prod.mk.injEq] at hc
  exact hc.2.1

/-- On an open lifted edge, the realization remembers both the sheet label
and the interval parameter.  This is the coordinate uniqueness needed to
turn an edge chart into a product trivialization. -/
theorem edgePoint_eq_iff_of_interior (i : Fin 2) (v w : V)
    (t u : UnitInterval) (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hu : u.1 ∈ Set.Ioo (0 : ℝ) 1) :
    D.edgePoint i v t = D.edgePoint i w u ↔ v = w ∧ t = u := by
  constructor
  · intro h
    have htu := (D.projection_edgePoint_eq_of_interior i i v w t u ht hu
      (congrArg D.projection h)).2
    subst u
    exact ⟨D.edgePoint_injective_of_interior i t ht h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every point above an interior base-edge point has a unique graph-vertex
coordinate.  This is the exact interior-fiber classification used by the
edge charts of the realization. -/
theorem existsUnique_edgePoint_of_projection_eq_interior
    (i : Fin 2) (t : UnitInterval) (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1)
    (e : D.Realization) (he : D.projection e = edgeProjection i t) :
    ∃! v : V, e = D.edgePoint i v t := by
  induction e using Quotient.inductionOn with
  | _ raw =>
      cases raw with
      | inl v =>
          exfalso
          exact edgeProjection_ne_wedgePoint i t ht (by
            simpa only [projection_vertex] using he.symm)
      | inr itu =>
          rcases itu with ⟨j, w, u⟩
          have hu0 : u ≠ intervalZero := by
            intro h
            subst u
            exact edgeProjection_ne_wedgePoint i t ht (by
              simpa [projection, realizationRawProjection] using he.symm)
          have hu1 : u ≠ intervalOne := by
            intro h
            subst u
            exact edgeProjection_ne_wedgePoint i t ht (by
              simpa [projection, realizationRawProjection] using he.symm)
          have hu : u.1 ∈ Set.Ioo (0 : ℝ) 1 := by
            constructor
            · apply lt_of_le_of_ne u.2.1
              intro h
              apply hu0
              apply Subtype.ext
              simpa [intervalZero] using h.symm
            · apply lt_of_le_of_ne u.2.2
              intro h
              apply hu1
              apply Subtype.ext
              simpa [intervalOne] using h
          have hij := edgeProjection_eq_of_interior j i u t hu ht (by
            simpa only [projection_edgePoint] using he)
          rcases hij with ⟨hji, hut⟩
          subst j
          subst u
          refine ⟨w, rfl, ?_⟩
          intro v hv
          exact edgePoint_injective_of_interior D i t ht hv.symm

/-- The descended lifted-edge chart is exactly the full preimage of its
corresponding open base edge. -/
theorem projection_preimage_baseEdgeChart (i : Fin 2) :
    D.projection ⁻¹' baseEdgeChart i = D.edgeChart i := by
  ext e
  rw [Set.mem_preimage, D.mem_edgeChart_iff]
  constructor
  · rintro ⟨t, ht, he⟩
    obtain ⟨v, hv, _⟩ :=
      D.existsUnique_edgePoint_of_projection_eq_interior i t ht e he.symm
    exact ⟨v, t, ht, hv⟩
  · rintro ⟨v, t, ht, rfl⟩
    exact ⟨t, ht, D.projection_edgePoint i v t⟩

/-- The fiber over every open-edge point is canonically the graph vertex
type. -/
noncomputable def interiorFiberEquiv (i : Fin 2) (t : UnitInterval)
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1) :
    {e : D.Realization // D.projection e = edgeProjection i t} ≃ V where
  toFun e := (existsUnique_edgePoint_of_projection_eq_interior D i t ht e e.2).choose
  invFun v := ⟨D.edgePoint i v t, by simp⟩
  left_inv e := by
    apply Subtype.ext
    exact (existsUnique_edgePoint_of_projection_eq_interior D i t ht e e.2).choose_spec.1.symm
  right_inv v := by
    let e : {e : D.Realization // D.projection e = edgeProjection i t} :=
      ⟨D.edgePoint i v t, by simp⟩
    have h := existsUnique_edgePoint_of_projection_eq_interior D i t ht e e.2
    exact h.unique h.choose_spec.1 rfl

/-- The complete preimage of an open-edge point is its labeled family of
lifted edge points.  This is the central fiber in every edge chart. -/
theorem projection_preimage_edgePoint (i : Fin 2) (t : UnitInterval)
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1) :
    D.projection ⁻¹' ({edgeProjection i t} : Set X) =
      Set.range (fun v : V => D.edgePoint i v t) := by
  ext e
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · intro he
    obtain ⟨v, hv, _⟩ :=
      D.existsUnique_edgePoint_of_projection_eq_interior i t ht e he
    exact ⟨v, hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact D.projection_edgePoint i v t

/-- Every fiber of the graph realization projection has the cardinality of
the graph vertex type. -/
theorem projection_fiberCard [Finite V] (x : X) :
    Nat.card {e : D.Realization // D.projection e = x} = Nat.card V := by
  induction x using Quotient.inductionOn with
  | _ raw =>
      cases raw with
      | inl z =>
          change Nat.card {e : D.Realization // D.projection e = inl z} = Nat.card V
          by_cases hz : z = circleBase
          · subst z
            exact Nat.card_congr D.vertexFiberEquiv
          · obtain ⟨t, ht⟩ := intervalCircle_surjective z
            have ht0 : t ≠ intervalZero := by
              intro h
              apply hz
              rw [← ht]
              simp [h]
            have ht1 : t ≠ intervalOne := by
              intro h
              apply hz
              rw [← ht]
              simp [h]
            have hti : t.1 ∈ Set.Ioo (0 : ℝ) 1 := by
              constructor
              · exact lt_of_le_of_ne t.2.1 (by
                  intro h
                  apply ht0
                  apply Subtype.ext
                  simpa [intervalZero] using h.symm)
              · exact lt_of_le_of_ne t.2.2 (by
                  intro h
                  apply ht1
                  apply Subtype.ext
                  simpa [intervalOne] using h)
            have hx : inl z = edgeProjection 0 t := by
              simp [edgeProjection, ht]
            rw [hx]
            exact Nat.card_congr (D.interiorFiberEquiv 0 t hti)
      | inr z =>
          change Nat.card {e : D.Realization // D.projection e = inr z} = Nat.card V
          by_cases hz : z = circleBase
          · subst z
            rw [← inl_base_eq_inr_base]
            exact Nat.card_congr D.vertexFiberEquiv
          · obtain ⟨t, ht⟩ := intervalCircle_surjective z
            have ht0 : t ≠ intervalZero := by
              intro h
              apply hz
              rw [← ht]
              simp [h]
            have ht1 : t ≠ intervalOne := by
              intro h
              apply hz
              rw [← ht]
              simp [h]
            have hti : t.1 ∈ Set.Ioo (0 : ℝ) 1 := by
              constructor
              · exact lt_of_le_of_ne t.2.1 (by
                  intro h
                  apply ht0
                  apply Subtype.ext
                  simpa [intervalZero] using h.symm)
              · exact lt_of_le_of_ne t.2.2 (by
                  intro h
                  apply ht1
                  apply Subtype.ext
                  simpa [intervalOne] using h)
            have hx : inr z = edgeProjection 1 t := by
              change inr z = inr (intervalCircle t)
              rw [ht]
            rw [hx]
            exact Nat.card_congr (D.interiorFiberEquiv 1 t hti)

#print axioms vertex_injective
#print axioms realizationQuotientMap_isQuotientMap
#print axioms rawEdgeInterior_isOpen
#print axioms rawEdgeChart_isOpen
#print axioms rawEdgeChart_mem_iff_of_eqvGen
#print axioms realization_preimage_edgeChart
#print axioms edgeChart_isOpen
#print axioms mem_edgeChart_iff
#print axioms wedge_preimage_baseEdgeChart
#print axioms baseEdgeChart_isOpen
#print axioms projection_preimage_baseEdgeChart
#print axioms edgePoint_eq_iff_of_interior
#print axioms existsUnique_vertex_of_projection_eq_wedgePoint
#print axioms vertexFiberEquiv
#print axioms intervalCircle_surjective
#print axioms projection_surjective
#print axioms projection_preimage_wedgePoint
#print axioms projection_preimage_edgePoint
#print axioms projection_fiberCard

end TwoLoopGraphCoverData

end ConstructionTargets.t92J06Closure
