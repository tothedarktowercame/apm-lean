import Mathlib
import ConstructionTargets.WedgePermutationCover
import ConstructionTargets.CoveringSubgroupCorrespondence

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

/-! ### Simply connected cover (split 2026-10-19)

`ConstructionTargets.CoveringSubgroupCorrespondence.exists_connected_subgroup_cover_of_small`
at the trivial subgroup gives a path-connected cover with trivial fundamental
group.  Its hypothesis `SemilocallySimplyConnected` is proved point by point:
near each point a homotopy `I × X → X` that fixes the point, starts at the
identity and ends constant on a neighbourhood contracts every loop in that
neighbourhood.  The homotopy squeezes a small arc of each circle onto its
centre (`apm_t92J06_squeeze`) and fixes everything outside twice the arc. -/

/-- Angle of `w` measured from `z`, in `(-π, π]`. -/
def apm_t92J06_relArg (z w : apm_t92J06_S1) : ℝ :=
  Complex.arg ((w : ℂ) * star (z : ℂ))

/-- `a` clamped to `[-δ, δ]`. -/
def apm_t92J06_clamp (δ a : ℝ) : ℝ := max (-δ) (min δ a)

/-- Tent profile: `a` on `[-δ, δ]`, falling linearly to `0` at `±2δ`, `0` beyond. -/
def apm_t92J06_tent (δ a : ℝ) : ℝ :=
  apm_t92J06_clamp δ a - apm_t92J06_clamp δ (a - apm_t92J06_clamp δ a)

/-- Rotate `w` towards `z` by `s` times the tent of its angle from `z`.  At
`s = 1` the arc of half-width `δ` around `z` lands on `z`; points at angle at
least `2δ` from `z` never move. -/
def apm_t92J06_squeeze (z : apm_t92J06_S1) (δ : ℝ) (s : unitInterval)
    (w : apm_t92J06_S1) : apm_t92J06_S1 :=
  ⟨(w : ℂ) * Complex.exp (-(((s : ℝ) * apm_t92J06_tent δ (apm_t92J06_relArg z w) : ℝ) : ℂ)
      * Complex.I), by
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
    simp [hw, Complex.norm_exp]⟩

/-- The squeeze is jointly continuous for `0 < δ < π / 2`: the tent vanishes
near angle `±π`, where `Complex.arg` jumps. -/
lemma apm_t92J06_squeeze_continuous {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi / 2)
    (z : apm_t92J06_S1) :
    Continuous fun q : unitInterval × apm_t92J06_S1 ↦ apm_t92J06_squeeze z δ q.1 q.2 := by
  sorry

/-- Values of the squeeze: identity at time `0`, fixes the centre, collapses
the `δ`-arc at time `1`, fixes points at angle at least `2δ`. -/
lemma apm_t92J06_squeeze_values {δ : ℝ} (hδ : 0 < δ) (z : apm_t92J06_S1) :
    (∀ w, apm_t92J06_squeeze z δ 0 w = w) ∧
    (∀ s, apm_t92J06_squeeze z δ s z = z) ∧
    (∀ w, |apm_t92J06_relArg z w| < δ → apm_t92J06_squeeze z δ 1 w = z) ∧
    (∀ s w, 2 * δ ≤ |apm_t92J06_relArg z w| → apm_t92J06_squeeze z δ s w = w) := by
  sorry

/-- Homotopies on the two legs agreeing at the base glue to a homotopy on the
wedge (`unitInterval` is locally compact, so `id × quotient` is a quotient map). -/
lemma apm_t92J06_wedgeHomotopy {Y : Type*} [TopologicalSpace Y]
    (f g : C(unitInterval × apm_t92J06_S1, Y))
    (hbase : ∀ s, f (s, apm_t92J06_circleBase) = g (s, apm_t92J06_circleBase)) :
    ∃ Φ : C(unitInterval × apm_t92J06_X, Y),
      (∀ s z, Φ (s, apm_t92J06_inl z) = f (s, z)) ∧
      (∀ s z, Φ (s, apm_t92J06_inr z) = g (s, z)) := by
  let q : Sum apm_t92J06_S1 apm_t92J06_S1 → apm_t92J06_X :=
    fun z ↦ Quotient.mk _ z
  have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
  have hrespect : ∀ (s : unitInterval) {x y},
      Relation.EqvGen apm_t92J06_wedgeRel x y →
        Sum.elim (fun z ↦ f (s, z)) (fun z ↦ g (s, z)) x =
          Sum.elim (fun z ↦ f (s, z)) (fun z ↦ g (s, z)) y := by
    intro s x y hxy
    induction hxy with
    | rel a b hab =>
        cases hab
        exact hbase s
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let Φ : C(unitInterval × apm_t92J06_X, Y) :=
    ⟨fun p ↦ Quotient.lift
        (fun z ↦ Sum.elim (fun w ↦ f (p.1, w)) (fun w ↦ g (p.1, w)) z)
        (fun _ _ hxy ↦ hrespect p.1 hxy) p.2,
      by
        apply hq.continuous_lift_prod_right
        have hfg : Continuous
            (Sum.elim f g : Sum (unitInterval × apm_t92J06_S1)
              (unitInterval × apm_t92J06_S1) → Y) :=
          continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
        have hc := hfg.comp
          (Homeomorph.prodSumDistrib :
            unitInterval × Sum apm_t92J06_S1 apm_t92J06_S1 ≃ₜ
              Sum (unitInterval × apm_t92J06_S1)
                (unitInterval × apm_t92J06_S1)).continuous
        simpa only [q, Quotient.lift_mk] using hc.congr (by
          rintro ⟨s, z⟩
          cases z <;> rfl)⟩
  refine ⟨Φ, ?_, ?_⟩
  · intro s z
    rfl
  · intro s z
    rfl

/-- A homotopy from the identity that fixes `y` and ends at `y` on `U`
contracts every loop at `y` inside `U`. -/
lemma apm_t92J06_loop_trivial_of_contraction {Y : Type*} [TopologicalSpace Y]
    {y : Y} {U : Set Y} (Φ : C(unitInterval × Y, Y))
    (h0 : ∀ u, Φ (0, u) = u) (hfix : ∀ s, Φ (s, y) = y)
    (h1 : ∀ u ∈ U, Φ (1, u) = y) (γ : Path y y) (hγ : range γ ⊆ U) :
    Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl y) := by
  apply Path.Homotopic.Quotient.eq.mpr
  refine ⟨{
    toFun := fun q ↦ Φ (q.1, γ q.2)
    continuous_toFun := Φ.continuous.comp (by fun_prop)
    map_zero_left := fun t ↦ by
      change Φ (0, γ t) = γ t
      exact h0 _
    map_one_left := fun t ↦ by
      rw [h1 (γ t) (hγ ⟨t, rfl⟩)]
      rfl
    prop' := fun s t ht ↦ by
      rcases ht with (rfl | rfl)
      · simpa using hfix s
      · simpa using hfix s }⟩

/-- Semilocal simple connectivity at the wedge point: squeeze both legs. -/
lemma apm_t92J06_slsc_aux_base :
    ∃ U ∈ nhds (apm_t92J06_inl apm_t92J06_circleBase),
      ∀ γ : Path (apm_t92J06_inl apm_t92J06_circleBase)
          (apm_t92J06_inl apm_t92J06_circleBase), range γ ⊆ U →
        Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl _) := by
  sorry

/-- Semilocal simple connectivity at a non-base point of the left leg: squeeze
the left leg around `z` with `2δ` less than the angle to the base, fix the
right leg. -/
lemma apm_t92J06_slsc_aux_inl (z : apm_t92J06_S1) (hz : z ≠ apm_t92J06_circleBase) :
    ∃ U ∈ nhds (apm_t92J06_inl z),
      ∀ γ : Path (apm_t92J06_inl z) (apm_t92J06_inl z), range γ ⊆ U →
        Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl _) := by
  sorry

/-- Semilocal simple connectivity at a non-base point of the right leg. -/
lemma apm_t92J06_slsc_aux_inr (z : apm_t92J06_S1) (hz : z ≠ apm_t92J06_circleBase) :
    ∃ U ∈ nhds (apm_t92J06_inr z),
      ∀ γ : Path (apm_t92J06_inr z) (apm_t92J06_inr z), range γ ⊆ U →
        Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl _) := by
  sorry

/-- Assembly: every point is a left-leg point, a right-leg point or the base. -/
lemma apm_t92J06_slsc :
    ConstructionTargets.CoveringSubgroupCorrespondence.SemilocallySimplyConnected
      apm_t92J06_X := by
  intro x
  induction x using Quotient.inductionOn with
  | h q =>
    rcases q with z | z
    · by_cases hz : z = apm_t92J06_circleBase
      · subst hz; exact apm_t92J06_slsc_aux_base
      · exact apm_t92J06_slsc_aux_inl z hz
    · by_cases hz : z = apm_t92J06_circleBase
      · subst hz
        have h := apm_t92J06_slsc_aux_base
        rw [apm_t92J06_inl_base_eq_inr_base] at h
        exact h
      · exact apm_t92J06_slsc_aux_inr z hz

/-- The wedge is path-connected: each leg is, and they share the base. -/
lemma apm_t92J06_pathConnected : PathConnectedSpace apm_t92J06_X := by
  sorry

/-- The unit circle is locally path-connected (for example via `Circle`, or
the squeeze arcs, which are path-connected and form a neighbourhood basis). -/
lemma apm_t92J06_S1_locPathConnected : LocPathConnectedSpace apm_t92J06_S1 := by
  sorry

lemma apm_t92J06_locPathConnected : LocPathConnectedSpace apm_t92J06_X := by
  haveI := apm_t92J06_S1_locPathConnected
  show LocPathConnectedSpace (Quotient (Relation.EqvGen.setoid apm_t92J06_wedgeRel))
  infer_instance

/-- A path-connected space whose fundamental group at one point is trivial is
simply connected. -/
-- BEGIN SEAT AREA
lemma apm_t92J06_simplyConnected_of_pi_one_bot {E : Type*} [TopologicalSpace E]
    [PathConnectedSpace E] (e : E) {G : Type*} [Group G]
    (h : Nonempty (FundamentalGroup E e ≃* (⊥ : Subgroup G))) :
    SimplyConnectedSpace E := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x γ
  apply Path.Homotopic.Quotient.eq.mp
  let φ : FundamentalGroup E x ≃* (⊥ : Subgroup G) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x e).trans h.some
  exact φ.injective (Subsingleton.elim _ _)
-- END SEAT AREA

/-- Assembly: the based-path cover at the trivial subgroup. -/
theorem apm_t92J06_exists_simplyConnected_cover :
    ∃ (E : Type*) (_ : TopologicalSpace E) (p : E → apm_t92J06_X),
      IsCoveringMap p ∧ SimplyConnectedSpace E := by
  haveI := apm_t92J06_pathConnected
  haveI := apm_t92J06_locPathConnected
  obtain ⟨E, t, p, e, hp, hE, -, -, hpi, -⟩ :=
    ConstructionTargets.CoveringSubgroupCorrespondence.exists_connected_subgroup_cover_of_small.{0, u_1}
      apm_t92J06_slsc (apm_t92J06_inl apm_t92J06_circleBase) ⊥
  exact ⟨E, t, p, hp, apm_t92J06_simplyConnected_of_pi_one_bot e hpi⟩

/-- Transport a family of shared circle-wedge covers to this file's wedge. -/
lemma apm_t92J06_shared_cover_adapter_aux_forward_respects {x y}
    (h : Relation.EqvGen
      (ConstructionTargets.WedgePermutationCover.WedgeRel
        apm_t92J06_circleBase apm_t92J06_circleBase) x y) :
    (Quotient.mk (Relation.EqvGen.setoid apm_t92J06_wedgeRel) x :
      apm_t92J06_X) = Quotient.mk _ y := by
  induction h with
  | rel x y h =>
      cases h
      exact Quotient.sound (Relation.EqvGen.rel _ _ apm_t92J06_wedgeRel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t92J06_shared_cover_adapter_aux_backward_respects {x y}
    (h : Relation.EqvGen apm_t92J06_wedgeRel x y) :
    (Quotient.mk (Relation.EqvGen.setoid
      (ConstructionTargets.WedgePermutationCover.WedgeRel
        apm_t92J06_circleBase apm_t92J06_circleBase)) x :
      ConstructionTargets.WedgePermutationCover.CircleWedge) =
        Quotient.mk _ y := by
  induction h with
  | rel x y h =>
      cases h
      exact Quotient.sound (Relation.EqvGen.rel _ _
        ConstructionTargets.WedgePermutationCover.WedgeRel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

noncomputable def apm_t92J06_shared_cover_adapter_aux_homeomorph :
    ConstructionTargets.WedgePermutationCover.CircleWedge ≃ₜ apm_t92J06_X where
  toFun := Quotient.lift (fun x => Quotient.mk _ x)
    (fun _ _ h => apm_t92J06_shared_cover_adapter_aux_forward_respects h)
  invFun := Quotient.lift (fun x => Quotient.mk _ x)
    (fun _ _ h => apm_t92J06_shared_cover_adapter_aux_backward_respects h)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn
    rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn
    rfl
  continuous_toFun := by
    exact continuous_coinduced_rng.quotient_lift
      (fun _ _ h => apm_t92J06_shared_cover_adapter_aux_forward_respects h)
  continuous_invFun := by
    exact continuous_coinduced_rng.quotient_lift
      (fun _ _ h => apm_t92J06_shared_cover_adapter_aux_backward_respects h)

theorem apm_t92J06_shared_cover_adapter
    (C : Fin 4 → ConstructionTargets.WedgePermutationCover.ThreeCover)
    (hC : Pairwise fun i j ↦ ¬ Nonempty
      (@Homeomorph (C i).E (C j).E (C i).topology (C j).topology)) :
    ∃ D : Fin 4 → apm_t92J06_Covering 3,
      Pairwise fun i j ↦ ¬ Nonempty
        (@Homeomorph (D i).E (D j).E (D i).topology (D j).topology) := by
  let h := apm_t92J06_shared_cover_adapter_aux_homeomorph
  let D : Fin 4 → apm_t92J06_Covering 3 := fun i => by
    letI : TopologicalSpace (C i).E := (C i).topology
    exact
      { E := (C i).E
        topology := (C i).topology
        p := h ∘ (C i).p
        covering := (C i).covering.1.homeomorph_comp h
        fiberCard := by
          intro x
          change Nat.card {z : (C i).E // h ((C i).p z) = x} = 3
          let e : {z : (C i).E // h ((C i).p z) = x} ≃
              {z : (C i).E // (C i).p z = h.symm x} :=
            Equiv.subtypeEquiv (Equiv.refl _) (by
              intro z
              constructor
              · intro hz
                simpa using congrArg h.symm hz
              · intro hz
                simpa using congrArg h hz)
          rw [Nat.card_congr e]
          exact (C i).covering.2 (h.symm x) }
  exact ⟨D, hC⟩

/-- Assembly: the shared four pairwise nonhomeomorphic covers, transported. -/
theorem apm_t92J06_exists_four_threeSheeted_covers :
    ∃ C : Fin 4 → apm_t92J06_Covering 3,
      Pairwise fun i j ↦
        ¬ Nonempty
          (@Homeomorph (C i).E (C j).E (C i).topology (C j).topology) := by
  obtain ⟨C, hC⟩ :=
    ConstructionTargets.WedgePermutationCover.circleWedge_four_pairwise_nonhomeomorphic
  exact apm_t92J06_shared_cover_adapter C hC

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
