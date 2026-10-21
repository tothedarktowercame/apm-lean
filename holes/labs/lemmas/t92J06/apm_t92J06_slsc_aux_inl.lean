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
lemma apm_t92J06_squeeze_continuous_aux_tent_zero {δ a : ℝ} (hδ : 0 < δ)
    (ha : 2 * δ ≤ |a|) : apm_t92J06_tent δ a = 0 := by
  rcases le_total 0 a with ha0 | ha0
  · rw [abs_of_nonneg ha0] at ha
    have hδa : δ ≤ a := by linarith
    have hδsub : δ ≤ a - δ := by linarith
    simp [apm_t92J06_tent, apm_t92J06_clamp, min_eq_left hδa,
      max_eq_right (by linarith : -δ ≤ δ), min_eq_left hδsub]
  · rw [abs_of_nonpos ha0] at ha
    have haδ : a ≤ -δ := by linarith
    have hsub : a - -δ ≤ -δ := by linarith
    have hca : apm_t92J06_clamp δ a = -δ := by
      unfold apm_t92J06_clamp
      rw [min_eq_right (by linarith : a ≤ δ), max_eq_left haδ]
    have hcb : apm_t92J06_clamp δ (a - -δ) = -δ := by
      unfold apm_t92J06_clamp
      rw [min_eq_right (by linarith : a - -δ ≤ δ), max_eq_left hsub]
    rw [apm_t92J06_tent, hca]
    simp only [hca, hcb, sub_self]

lemma apm_t92J06_squeeze_continuous_aux_tent :
    Continuous fun a : ℝ ↦ apm_t92J06_tent δ a := by
  unfold apm_t92J06_tent apm_t92J06_clamp
  fun_prop

lemma apm_t92J06_squeeze_continuous {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi / 2)
    (z : apm_t92J06_S1) :
    Continuous fun q : unitInterval × apm_t92J06_S1 ↦ apm_t92J06_squeeze z δ q.1 q.2 := by
  rw [continuous_induced_rng]
  rw [continuous_iff_continuousAt]
  rintro ⟨s, w⟩
  let r : ℂ := (w : ℂ) * star (z : ℂ)
  have hz : (z : ℂ) ≠ 0 := by
    intro hz0
    have := congrArg norm hz0
    simpa [mem_sphere_zero_iff_norm.mp z.2] using this
  have hw : (w : ℂ) ≠ 0 := by
    intro hw0
    have := congrArg norm hw0
    simpa [mem_sphere_zero_iff_norm.mp w.2] using this
  have hr : r ≠ 0 := mul_ne_zero hw (star_ne_zero.mpr hz)
  have hwcont : ContinuousAt (fun q : unitInterval × apm_t92J06_S1 ↦ (q.2 : ℂ)) (s, w) :=
    continuous_subtype_val.continuousAt.comp continuousAt_snd
  have hrcont : ContinuousAt
      (fun q : unitInterval × apm_t92J06_S1 ↦ (q.2 : ℂ) * star (z : ℂ)) (s, w) :=
    hwcont.mul continuousAt_const
  by_cases hslit : r ∈ Complex.slitPlane
  · have harg : ContinuousAt
        (fun q : unitInterval × apm_t92J06_S1 ↦ apm_t92J06_relArg z q.2) (s, w) := by
      change ContinuousAt (fun q : unitInterval × apm_t92J06_S1 ↦
        Complex.arg ((q.2 : ℂ) * star (z : ℂ))) (s, w)
      have hslit' : (w : ℂ) * star (z : ℂ) ∈ Complex.slitPlane := by simpa [r] using hslit
      simpa only [Function.comp_apply] using
        ContinuousAt.comp (f := fun q : unitInterval × apm_t92J06_S1 ↦
          (q.2 : ℂ) * star (z : ℂ)) (Complex.continuousAt_arg hslit') hrcont
    unfold apm_t92J06_squeeze
    exact hwcont.mul (Complex.continuous_exp.continuousAt.comp
      (((Complex.continuous_ofReal.continuousAt.comp
        ((continuous_subtype_val.continuousAt.comp continuousAt_fst).mul
          (apm_t92J06_squeeze_continuous_aux_tent.continuousAt.comp harg))).neg).mul
            continuousAt_const))
  · have hrneg : r.re < 0 ∧ r.im = 0 := by
      apply Complex.arg_eq_pi_iff.mp
      have hn : ¬(Complex.arg r ≠ Real.pi ∧ r ≠ 0) := by
        rwa [← Complex.mem_slitPlane_iff_arg]
      by_contra harg
      exact hn ⟨harg, hr⟩
    have hargval : |Complex.arg r| = Real.pi := by
      rw [Complex.arg_eq_pi_iff.2 hrneg, abs_of_pos Real.pi_pos]
    have htwo : 2 * δ < Real.pi := by linarith
    have hang : ContinuousAt
        (fun q : unitInterval × apm_t92J06_S1 ↦
          InnerProductGeometry.angle (1 : ℂ) ((q.2 : ℂ) * star (z : ℂ))) (s, w) := by
      simpa only [Function.comp_apply, r] using
        ContinuousAt.comp
          (f := fun q : unitInterval × apm_t92J06_S1 ↦
            ((1 : ℂ), (q.2 : ℂ) * star (z : ℂ)))
          (InnerProductGeometry.continuousAt_angle (x := ((1 : ℂ), r)) one_ne_zero hr)
          (ContinuousAt.prodMk
            (f := fun _ : unitInterval × apm_t92J06_S1 ↦ (1 : ℂ))
            (g := fun q ↦ (q.2 : ℂ) * star (z : ℂ)) continuousAt_const hrcont)
    have hevent : ∀ᶠ q in nhds (s, w), 2 * δ ≤ |apm_t92J06_relArg z q.2| := by
      have hevent' : ∀ᶠ q in nhds (s, w), 2 * δ <
          InnerProductGeometry.angle (1 : ℂ) ((q.2 : ℂ) * star (z : ℂ)) :=
        (hang.eventually_const_lt (by
          change 2 * δ < InnerProductGeometry.angle (1 : ℂ) r
          rw [Complex.angle_one_left hr, hargval]
          exact htwo))
      filter_upwards [hevent'] with q hq
      have hqne : (q.2 : ℂ) * star (z : ℂ) ≠ 0 := by
        exact mul_ne_zero (by
          intro h
          have := congrArg norm h
          simpa [mem_sphere_zero_iff_norm.mp q.2.2] using this) (star_ne_zero.mpr hz)
      rw [Complex.angle_one_left hqne] at hq
      simpa [apm_t92J06_relArg] using hq.le
    apply (hwcont.mul continuousAt_const).congr_of_eventuallyEq
    filter_upwards [hevent] with q hq
    change ((q.2 : ℂ) * Complex.exp _ = (q.2 : ℂ) * 1)
    simp [apm_t92J06_squeeze_continuous_aux_tent_zero hδ hq]

/-- Values of the squeeze: identity at time `0`, fixes the centre, collapses
the `δ`-arc at time `1`, fixes points at angle at least `2δ`. -/
lemma apm_t92J06_squeeze_values_aux_clamp_of_abs_lt {δ a : ℝ}
    (hδ : 0 < δ) (ha : |a| < δ) : apm_t92J06_clamp δ a = a := by
  rw [abs_lt] at ha
  simp [apm_t92J06_clamp, ha.1.le, ha.2.le]

lemma apm_t92J06_squeeze_values_aux_clamp_zero (δ : ℝ) (hδ : 0 < δ) :
    apm_t92J06_clamp δ 0 = 0 := by
  simp [apm_t92J06_clamp, hδ.le]

lemma apm_t92J06_squeeze_values_aux_tent_of_abs_lt {δ a : ℝ}
    (hδ : 0 < δ) (ha : |a| < δ) : apm_t92J06_tent δ a = a := by
  rw [apm_t92J06_tent, apm_t92J06_squeeze_values_aux_clamp_of_abs_lt hδ ha]
  simp [apm_t92J06_squeeze_values_aux_clamp_zero δ hδ]

lemma apm_t92J06_squeeze_values_aux_tent_zero (δ : ℝ) (hδ : 0 < δ) :
    apm_t92J06_tent δ 0 = 0 := by
  simp [apm_t92J06_tent, apm_t92J06_squeeze_values_aux_clamp_zero δ hδ]

lemma apm_t92J06_squeeze_values_aux_tent_of_two_mul_le_abs {δ a : ℝ}
    (hδ : 0 < δ) (ha : 2 * δ ≤ |a|) : apm_t92J06_tent δ a = 0 := by
  rcases le_total 0 a with ha0 | ha0
  · have hδa : δ ≤ a := by rw [abs_of_nonneg ha0] at ha; linarith
    have h2δa : 2 * δ ≤ a := by simpa [abs_of_nonneg ha0] using ha
    have hsub : δ ≤ a - δ := by linarith
    simp [apm_t92J06_tent, apm_t92J06_clamp, hδ.le, hδa, hsub]
  · have haδ : a ≤ -δ := by rw [abs_of_nonpos ha0] at ha; linarith
    have ha2δ : a ≤ -(2 * δ) := by rw [abs_of_nonpos ha0] at ha; linarith
    have hadd : a + δ ≤ -δ := by linarith
    simp [apm_t92J06_tent, apm_t92J06_clamp, haδ, hadd]

lemma apm_t92J06_squeeze_values {δ : ℝ} (hδ : 0 < δ) (z : apm_t92J06_S1) :
    (∀ w, apm_t92J06_squeeze z δ 0 w = w) ∧
    (∀ s, apm_t92J06_squeeze z δ s z = z) ∧
    (∀ w, |apm_t92J06_relArg z w| < δ → apm_t92J06_squeeze z δ 1 w = z) ∧
    (∀ s w, 2 * δ ≤ |apm_t92J06_relArg z w| → apm_t92J06_squeeze z δ s w = w) := by
  have hz_norm : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hz_ne : (z : ℂ) ≠ 0 := by intro hz; simpa [hz] using hz_norm
  have hrel_self : apm_t92J06_relArg z z = 0 := by
    simp [apm_t92J06_relArg, Complex.mul_conj, hz_norm]
  constructor
  · intro w
    apply Subtype.ext
    simp [apm_t92J06_squeeze]
  constructor
  · intro s
    apply Subtype.ext
    simp [apm_t92J06_squeeze, hrel_self,
      apm_t92J06_squeeze_values_aux_tent_zero δ hδ]
  constructor
  · intro w hw
    apply Subtype.ext
    change (w : ℂ) * Complex.exp (-(((1 : unitInterval) : ℝ) *
      apm_t92J06_tent δ (apm_t92J06_relArg z w) : ℝ) * Complex.I) = z
    rw [apm_t92J06_squeeze_values_aux_tent_of_abs_lt hδ hw]
    norm_num
    let x : ℂ := (w : ℂ) * star (z : ℂ)
    have hw_norm : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
    have hx_norm : ‖x‖ = 1 := by simp [x, hw_norm, hz_norm]
    have hexp : Complex.exp (Complex.arg x * Complex.I) = x := by
      simpa [hx_norm] using Complex.norm_mul_exp_arg_mul_I x
    have hinv : Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) * x = 1 := by
      calc
        Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) * x =
            Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) *
              Complex.exp (Complex.arg x * Complex.I) := by rw [hexp]
        _ = 1 := by rw [← Complex.exp_add]; simp
    rw [show apm_t92J06_relArg z w = Complex.arg x by rfl]
    have hzz : star (z : ℂ) * (z : ℂ) = 1 := by
      calc
        star (z : ℂ) * (z : ℂ) = (Complex.normSq (z : ℂ) : ℂ) :=
          Complex.normSq_eq_conj_mul_self.symm
        _ = 1 := by rw [← Complex.norm_mul_self_eq_normSq, hz_norm, one_mul]; norm_num
    calc
      (w : ℂ) * Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) =
          Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) * (w : ℂ) := mul_comm _ _
      _ = Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) *
          ((w : ℂ) * (star (z : ℂ) * (z : ℂ))) := by rw [hzz, mul_one]
      _ =
          (Complex.exp (-((Complex.arg x : ℂ) * Complex.I)) * x) * (z : ℂ) := by
            simp only [x]
            ring
      _ = z := by rw [hinv, one_mul]
  · intro s w hw
    apply Subtype.ext
    simp [apm_t92J06_squeeze,
      apm_t92J06_squeeze_values_aux_tent_of_two_mul_le_abs hδ hw]

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
-- BEGIN SEAT AREA
lemma apm_t92J06_slsc_aux_inl (z : apm_t92J06_S1) (hz : z ≠ apm_t92J06_circleBase) :
    ∃ U ∈ nhds (apm_t92J06_inl z),
      ∀ γ : Path (apm_t92J06_inl z) (apm_t92J06_inl z), range γ ⊆ U →
        Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl _) := by
  have hz_norm : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hb_norm : ‖(apm_t92J06_circleBase : ℂ)‖ = 1 := by simp
  let r : ℂ := (apm_t92J06_circleBase : ℂ) * star (z : ℂ)
  have hr_norm : ‖r‖ = 1 := by simp [r, hz_norm]
  have hr_ne : r ≠ 0 := by simpa [norm_ne_zero_iff] using (show ‖r‖ ≠ 0 by simp [hr_norm])
  let a := InnerProductGeometry.angle (1 : ℂ) r
  have ha : 0 < a := by
    have ha0 : 0 ≤ a := InnerProductGeometry.angle_nonneg _ _
    refine lt_of_le_of_ne ha0 ?_
    intro hae
    have heq : (1 : ℂ) = r :=
      InnerProductGeometry.eq_of_angle_eq_zero_of_norm_eq hae.symm (by simp [hr_norm])
    have hzval : (z : ℂ) = 1 := by
      have hzz : star (z : ℂ) * (z : ℂ) = 1 := by
        calc
          star (z : ℂ) * (z : ℂ) = (Complex.normSq (z : ℂ) : ℂ) :=
            Complex.normSq_eq_conj_mul_self.symm
          _ = 1 := by rw [← Complex.norm_mul_self_eq_normSq, hz_norm]; norm_num
      calc
        (z : ℂ) = 1 * (z : ℂ) := by simp
        _ = r * (z : ℂ) := congrArg (fun u : ℂ ↦ u * (z : ℂ)) heq
        _ = (apm_t92J06_circleBase : ℂ) * (star (z : ℂ) * (z : ℂ)) := by
          simp [r, mul_assoc]
        _ = (apm_t92J06_circleBase : ℂ) := by rw [hzz, mul_one]
        _ = 1 := rfl
    apply hz
    apply Subtype.ext
    simpa [apm_t92J06_circleBase] using hzval
  let δ : ℝ := min (a / 4) (Real.pi / 4)
  have hδ : 0 < δ := by
    exact lt_min (div_pos ha (by norm_num)) (div_pos Real.pi_pos (by norm_num))
  have hδπ : δ < Real.pi / 2 := by
    have : δ ≤ Real.pi / 4 := min_le_right _ _
    linarith [Real.pi_pos]
  have hbase_far : 2 * δ ≤ |apm_t92J06_relArg z apm_t92J06_circleBase| := by
    have hδa : δ ≤ a / 4 := min_le_left _ _
    have hargeq : |apm_t92J06_relArg z apm_t92J06_circleBase| = a := by
      simp only [apm_t92J06_relArg, r, a]
      exact (Complex.angle_one_left hr_ne).symm
    rw [hargeq]
    linarith
  let A : Set apm_t92J06_S1 := {w | InnerProductGeometry.angle (1 : ℂ)
    ((w : ℂ) * star (z : ℂ)) < δ}
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    have hwne : (w : ℂ) * star (z : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · intro h
        have := congrArg norm h
        simpa [mem_sphere_zero_iff_norm.mp w.2] using this
      · exact star_ne_zero.mpr (by
          intro h
          have := congrArg norm h
          simpa [hz_norm] using this)
    have hc : ContinuousAt (fun w : apm_t92J06_S1 ↦
        InnerProductGeometry.angle (1 : ℂ) ((w : ℂ) * star (z : ℂ))) w :=
      ContinuousAt.comp
        (f := fun w : apm_t92J06_S1 ↦ ((1 : ℂ), (w : ℂ) * star (z : ℂ)))
        (InnerProductGeometry.continuousAt_angle
          (x := ((1 : ℂ), (w : ℂ) * star (z : ℂ))) one_ne_zero hwne)
        (ContinuousAt.prodMk continuousAt_const
          (continuous_subtype_val.continuousAt.mul continuousAt_const))
    exact hc.eventually_lt continuousAt_const hw
  have hzA : z ∈ A := by
    change InnerProductGeometry.angle (1 : ℂ) ((z : ℂ) * star (z : ℂ)) < δ
    have hzz : (z : ℂ) * star (z : ℂ) = 1 := by
      rw [mul_comm]
      calc
        star (z : ℂ) * (z : ℂ) = (Complex.normSq (z : ℂ) : ℂ) :=
          Complex.normSq_eq_conj_mul_self.symm
        _ = 1 := by rw [← Complex.norm_mul_self_eq_normSq, hz_norm]; norm_num
    rw [hzz]
    simpa using hδ
  have hbA : apm_t92J06_circleBase ∉ A := by
    intro hb
    change a < δ at hb
    have := min_le_left (a / 4) (Real.pi / 4)
    dsimp [δ] at hb ⊢
    linarith
  let pred0 : Sum apm_t92J06_S1 apm_t92J06_S1 → Prop :=
    Sum.elim (fun w ↦ w ∈ A) (fun _ ↦ False)
  have hrespect : ∀ {x y}, Relation.EqvGen apm_t92J06_wedgeRel x y → pred0 x = pred0 y := by
    intro x y hxy
    induction hxy with
    | rel x y h => cases h; exact propext ⟨fun h ↦ (hbA h).elim, False.elim⟩
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let pred : apm_t92J06_X → Prop := Quotient.lift pred0 (fun _ _ h ↦ hrespect h)
  let U : Set apm_t92J06_X := {x | pred x}
  have hUopen : IsOpen U := by
    let q : Sum apm_t92J06_S1 apm_t92J06_S1 → apm_t92J06_X := fun x ↦ Quotient.mk _ x
    have hq : Topology.IsQuotientMap q := ⟨Quotient.mk_surjective, rfl⟩
    rw [← hq.isOpen_preimage]
    rw [isOpen_sum_iff]
    simpa only [q, U, pred, pred0, Quotient.lift_mk, Sum.elim_inl, Sum.elim_inr,
      Set.mem_setOf_eq, preimage_setOf_eq] using And.intro hAopen isOpen_empty
  have hzU : apm_t92J06_inl z ∈ U := by simpa [U, pred, pred0] using hzA
  have hUnhds : U ∈ nhds (apm_t92J06_inl z) := hUopen.mem_nhds hzU
  let f : C(unitInterval × apm_t92J06_S1, apm_t92J06_X) :=
    ⟨fun q ↦ apm_t92J06_inl (apm_t92J06_squeeze z δ q.1 q.2),
      apm_t92J06_continuous_inl.comp (apm_t92J06_squeeze_continuous hδ hδπ z)⟩
  let g : C(unitInterval × apm_t92J06_S1, apm_t92J06_X) :=
    ⟨fun q ↦ apm_t92J06_inr q.2, apm_t92J06_continuous_inr.comp continuous_snd⟩
  have hfg : ∀ s, f (s, apm_t92J06_circleBase) = g (s, apm_t92J06_circleBase) := by
    intro s
    change apm_t92J06_inl (apm_t92J06_squeeze z δ s apm_t92J06_circleBase) =
      apm_t92J06_inr apm_t92J06_circleBase
    rw [(apm_t92J06_squeeze_values hδ z).2.2.2 s _ hbase_far]
    exact apm_t92J06_inl_base_eq_inr_base
  obtain ⟨Φ, hΦl, hΦr⟩ := apm_t92J06_wedgeHomotopy f g hfg
  refine ⟨U, hUnhds, ?_⟩
  intro γ hγ
  apply apm_t92J06_loop_trivial_of_contraction Φ
  · intro u
    induction u using Quotient.inductionOn with
    | h q =>
      rcases q with w | w
      · change Φ (0, apm_t92J06_inl w) = apm_t92J06_inl w
        rw [hΦl]
        exact congrArg apm_t92J06_inl ((apm_t92J06_squeeze_values hδ z).1 w)
      · change Φ (0, apm_t92J06_inr w) = apm_t92J06_inr w
        rw [hΦr]
        rfl
  · intro s
    rw [hΦl]
    exact congrArg apm_t92J06_inl ((apm_t92J06_squeeze_values hδ z).2.1 s)
  · intro u hu
    induction u using Quotient.inductionOn with
    | h q =>
      rcases q with w | w
      · change apm_t92J06_inl w ∈ U at hu
        have hwA : w ∈ A := by simpa [U, pred, pred0] using hu
        have hwarg : |apm_t92J06_relArg z w| < δ := by
          have hwne : (w : ℂ) * star (z : ℂ) ≠ 0 := by
            apply mul_ne_zero
            · simpa [norm_ne_zero_iff] using
                (show ‖(w : ℂ)‖ ≠ 0 by simp [mem_sphere_zero_iff_norm.mp w.2])
            · exact star_ne_zero.mpr (by simpa [norm_ne_zero_iff] using
                (show ‖(z : ℂ)‖ ≠ 0 by simp [hz_norm]))
          change InnerProductGeometry.angle (1 : ℂ) ((w : ℂ) * star (z : ℂ)) < δ at hwA
          rw [Complex.angle_one_left hwne] at hwA
          simpa [apm_t92J06_relArg] using hwA
        change Φ (1, apm_t92J06_inl w) = apm_t92J06_inl z
        rw [hΦl]
        exact congrArg apm_t92J06_inl ((apm_t92J06_squeeze_values hδ z).2.2.1 w hwarg)
      · change apm_t92J06_inr w ∈ U at hu
        exact False.elim (by simpa [U, pred, pred0] using hu)
  · exact hγ
-- END SEAT AREA

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
  have h_rank : 1 < Module.rank ℝ ℂ := by
    rw [show Module.rank ℝ ℂ = 2 from Complex.rank_real_complex]
    norm_num
  letI : PathConnectedSpace apm_t92J06_S1 :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere h_rank 0 (by norm_num))
  let b := apm_t92J06_inl apm_t92J06_circleBase
  have toBase : ∀ x : apm_t92J06_X, Joined x b := by
    intro x
    induction x using Quotient.inductionOn with
    | h q =>
      rcases q with z | z
      · exact ⟨(PathConnectedSpace.joined z apm_t92J06_circleBase).somePath.map
          apm_t92J06_continuous_inl⟩
      · have h : Joined (apm_t92J06_inr z)
            (apm_t92J06_inr apm_t92J06_circleBase) :=
          ⟨(PathConnectedSpace.joined z apm_t92J06_circleBase).somePath.map
            apm_t92J06_continuous_inr⟩
        simpa [b, apm_t92J06_inl_base_eq_inr_base] using h
  exact ⟨⟨b⟩, fun x y ↦ (toBase x).trans (toBase y).symm⟩

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
