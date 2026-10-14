import Mathlib
import ConstructionTargets.TorusFormTargets

/-! # t93A06: descent, primitive and periods of the printed torus form

The large quotient-atlas construction is isolated from the coordinate
calculations.  Downstream lemmas receive the conclusions they need as explicit
hypotheses, so their seats can be worked independently.
-/
open scoped Manifold ContDiff
open ConstructionTargets.ManifoldFormTargets ConstructionTargets.TorusFormTargets
noncomputable section

lemma t93A06_torusAtlas_aux_quotient_charts_aux_fibers (x y : Plane) :
    projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ) := by
  constructor
  · intro h
    have hcoord (i : Fin 2) : (x i : AddCircle (1 : ℝ)) =
        (y i : AddCircle (1 : ℝ)) := congrFun h i
    choose n hn using fun i =>
      (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := x i - y i)).mp (by
        rw [AddCircle.coe_sub, hcoord i, sub_self])
    refine ⟨fun i => -n i, fun i => ?_⟩
    have hd : (n i : ℝ) = x i - y i := by simpa using hn i
    rw [Int.cast_neg]
    linarith
  · rintro ⟨k, hk⟩
    funext i
    change (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
    rw [hk i, AddCircle.coe_add]
    simp

lemma t93A06_torusAtlas_aux_quotient_charts_aux_box_inj (a : Plane) :
    Set.InjOn projection
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioo (a i - (1 / 4 : ℝ))
        (a i + 1 / 4))) := by
  intro x hx y hy hxy
  obtain ⟨k, hk⟩ :=
    (t93A06_torusAtlas_aux_quotient_charts_aux_fibers x y).mp hxy
  funext i
  have hxi := hx i (Set.mem_univ i)
  have hyi := hy i (Set.mem_univ i)
  change a i - 1 / 4 < x i ∧ x i < a i + 1 / 4 at hxi
  change a i - 1 / 4 < y i ∧ y i < a i + 1 / 4 at hyi
  have hlt : ((k i : ℤ) : ℝ) < 1 := by
    rw [hk i] at hyi
    linarith
  have hgt : (-1 : ℝ) < ((k i : ℤ) : ℝ) := by
    rw [hk i] at hyi
    linarith
  have hk0 : k i = 0 := by
    have hlo : (-1 : ℤ) < k i := by exact_mod_cast hgt
    have hhi : k i < 1 := by exact_mod_cast hlt
    omega
  symm
  simpa [hk0] using hk i

def t93A06_torusAtlas_aux_quotient_charts_aux_box (a : Plane) : Set Plane :=
  Set.pi Set.univ (fun i : Fin 2 => Set.Ioo (a i - (1 / 4 : ℝ)) (a i + 1 / 4))

lemma t93A06_torusAtlas_aux_quotient_charts_aux_box_open (a : Plane) :
    IsOpen (t93A06_torusAtlas_aux_quotient_charts_aux_box a) := by
  exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_Ioo

lemma t93A06_torusAtlas_aux_quotient_charts_aux_mem_box (a : Plane) :
    a ∈ t93A06_torusAtlas_aux_quotient_charts_aux_box a := by
  intro i _
  constructor <;> linarith

lemma t93A06_torusAtlas_aux_quotient_charts_aux_open_projection :
    IsOpenMap projection := by
  unfold projection
  exact IsOpenMap.piMap
    (fun _ : Fin 2 => (QuotientAddGroup.isOpenMap_coe :
      IsOpenMap (fun x : ℝ => (x : AddCircle (1 : ℝ)))))
    (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)

noncomputable def t93A06_torusAtlas_aux_quotient_charts_aux_chart (a : Plane) :
    OpenPartialHomeomorph Torus Plane :=
  (OpenPartialHomeomorph.ofContinuousOpen
    ((t93A06_torusAtlas_aux_quotient_charts_aux_box_inj a).toPartialEquiv
      projection (t93A06_torusAtlas_aux_quotient_charts_aux_box a))
    (show Continuous projection from by
      unfold projection
      fun_prop).continuousOn
    t93A06_torusAtlas_aux_quotient_charts_aux_open_projection
    (t93A06_torusAtlas_aux_quotient_charts_aux_box_open a)).symm

lemma t93A06_torusAtlas_aux_quotient_charts_aux_chart_source (a : Plane) :
    (t93A06_torusAtlas_aux_quotient_charts_aux_chart a).source =
      projection '' t93A06_torusAtlas_aux_quotient_charts_aux_box a := by
  simp [t93A06_torusAtlas_aux_quotient_charts_aux_chart]

lemma t93A06_torusAtlas_aux_quotient_charts_aux_chart_target (a : Plane) :
    (t93A06_torusAtlas_aux_quotient_charts_aux_chart a).target =
      t93A06_torusAtlas_aux_quotient_charts_aux_box a := by
  simp [t93A06_torusAtlas_aux_quotient_charts_aux_chart]

lemma t93A06_torusAtlas_aux_quotient_charts_aux_chart_proj
    (a x : Plane) (hx : x ∈ t93A06_torusAtlas_aux_quotient_charts_aux_box a) :
    t93A06_torusAtlas_aux_quotient_charts_aux_chart a (projection x) = x := by
  apply OpenPartialHomeomorph.left_inv
  simpa [t93A06_torusAtlas_aux_quotient_charts_aux_chart] using hx

noncomputable def t93A06_torusAtlas_aux_quotient_charts_aux_lift (z : Torus) : Plane :=
  Classical.choose (show ∃ x, projection x = z by
    choose x hx using fun i => QuotientAddGroup.mk_surjective (z i)
    exact ⟨x, funext fun i => hx i⟩)

lemma t93A06_torusAtlas_aux_quotient_charts_aux_lift_spec (z : Torus) :
    projection (t93A06_torusAtlas_aux_quotient_charts_aux_lift z) = z := by
  exact Classical.choose_spec (show ∃ x, projection x = z by
    choose x hx using fun i => QuotientAddGroup.mk_surjective (z i)
    exact ⟨x, funext fun i => hx i⟩)

noncomputable def t93A06_torusAtlas_aux_quotient_charts_aux_charts :
    ChartedSpace Plane Torus :=
  { atlas := Set.range (fun z =>
      t93A06_torusAtlas_aux_quotient_charts_aux_chart
        (t93A06_torusAtlas_aux_quotient_charts_aux_lift z))
    chartAt := fun z => t93A06_torusAtlas_aux_quotient_charts_aux_chart
        (t93A06_torusAtlas_aux_quotient_charts_aux_lift z)
    mem_chart_source := fun z => by
      rw [t93A06_torusAtlas_aux_quotient_charts_aux_chart_source]
      refine ⟨t93A06_torusAtlas_aux_quotient_charts_aux_lift z,
        t93A06_torusAtlas_aux_quotient_charts_aux_mem_box _, ?_⟩
      exact t93A06_torusAtlas_aux_quotient_charts_aux_lift_spec z
    chart_mem_atlas := fun z => ⟨z, rfl⟩ }

lemma t93A06_torusAtlas_aux_quotient_charts_aux_transition
    (x y : Torus) (z : Plane)
    (hz : z ∈ ((t93A06_torusAtlas_aux_quotient_charts_aux_chart
      (t93A06_torusAtlas_aux_quotient_charts_aux_lift x)).symm.trans
        (t93A06_torusAtlas_aux_quotient_charts_aux_chart
          (t93A06_torusAtlas_aux_quotient_charts_aux_lift y))).source) :
    ∃ k : Fin 2 → ℤ, ∀ i,
      ((t93A06_torusAtlas_aux_quotient_charts_aux_chart
        (t93A06_torusAtlas_aux_quotient_charts_aux_lift x)).symm.trans
          (t93A06_torusAtlas_aux_quotient_charts_aux_chart
            (t93A06_torusAtlas_aux_quotient_charts_aux_lift y))) z i =
        z i + (k i : ℝ) := by
  apply (t93A06_torusAtlas_aux_quotient_charts_aux_fibers z _).mp
  simpa [t93A06_torusAtlas_aux_quotient_charts_aux_chart] using
    (((t93A06_torusAtlas_aux_quotient_charts_aux_chart
      (t93A06_torusAtlas_aux_quotient_charts_aux_lift y))).left_inv hz.2).symm

lemma t93A06_torusAtlas_aux_quotient_charts_aux_projection_smooth :
    letI := t93A06_torusAtlas_aux_quotient_charts_aux_charts
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection := by
  letI := t93A06_torusAtlas_aux_quotient_charts_aux_charts
  intro x
  rw [contMDiffAt_iff]
  constructor
  · exact (show Continuous projection from by unfold projection; fun_prop).continuousAt
  · simp only [mfld_simps]
    let a := t93A06_torusAtlas_aux_quotient_charts_aux_lift (projection x)
    obtain ⟨k, hk⟩ :=
      (t93A06_torusAtlas_aux_quotient_charts_aux_fibers x a).mp
        (t93A06_torusAtlas_aux_quotient_charts_aux_lift_spec (projection x)).symm
    let c : Plane := fun i => (k i : ℝ)
    have hac : x + c = a := by
      funext i
      exact (hk i).symm
    have hg : ContDiff ℝ ∞ (fun w : Plane => w + c) :=
      contDiff_id.add contDiff_const
    have hevN : ∀ᶠ w in nhds x,
        w + c ∈ t93A06_torusAtlas_aux_quotient_charts_aux_box a := by
      apply hg.continuous.continuousAt
      change t93A06_torusAtlas_aux_quotient_charts_aux_box a ∈ nhds (x + c)
      rw [hac]
      exact (t93A06_torusAtlas_aux_quotient_charts_aux_box_open a).mem_nhds
        (t93A06_torusAtlas_aux_quotient_charts_aux_mem_box a)
    have hev : ∀ᶠ w in nhdsWithin x Set.univ,
        w + c ∈ t93A06_torusAtlas_aux_quotient_charts_aux_box a :=
      Filter.Eventually.filter_mono inf_le_left hevN
    apply hg.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [hev] with w hw
      have hp : projection w = projection (w + c) := by
        apply (t93A06_torusAtlas_aux_quotient_charts_aux_fibers w (w + c)).mpr
        exact ⟨k, fun i => rfl⟩
      change
        t93A06_torusAtlas_aux_quotient_charts_aux_chart a (projection w) = w + c
      rw [hp]
      exact t93A06_torusAtlas_aux_quotient_charts_aux_chart_proj a (w + c) hw
    · change
        t93A06_torusAtlas_aux_quotient_charts_aux_chart a (projection x) = x + c
      rw [hac]
      have hpa : projection x = projection a :=
        (t93A06_torusAtlas_aux_quotient_charts_aux_lift_spec (projection x)).symm
      rw [hpa]
      exact t93A06_torusAtlas_aux_quotient_charts_aux_chart_proj a a
        (t93A06_torusAtlas_aux_quotient_charts_aux_mem_box a)

lemma t93A06_torusAtlas_aux_quotient_charts_aux_inverse_smooth (x : Plane) :
    letI := t93A06_torusAtlas_aux_quotient_charts_aux_charts
    let e := OpenPartialHomeomorph.ofContinuousOpen
      ((t93A06_torusAtlas_aux_quotient_charts_aux_box_inj x).toPartialEquiv
        projection (t93A06_torusAtlas_aux_quotient_charts_aux_box x))
      (show Continuous projection from by unfold projection; fun_prop).continuousOn
      t93A06_torusAtlas_aux_quotient_charts_aux_open_projection
      (t93A06_torusAtlas_aux_quotient_charts_aux_box_open x)
    ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ e.symm e.target := by
  letI := t93A06_torusAtlas_aux_quotient_charts_aux_charts
  dsimp only
  let e := OpenPartialHomeomorph.ofContinuousOpen
    ((t93A06_torusAtlas_aux_quotient_charts_aux_box_inj x).toPartialEquiv
      projection (t93A06_torusAtlas_aux_quotient_charts_aux_box x))
    (show Continuous projection from by unfold projection; fun_prop).continuousOn
    t93A06_torusAtlas_aux_quotient_charts_aux_open_projection
    (t93A06_torusAtlas_aux_quotient_charts_aux_box_open x)
  change ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ e.symm e.target
  intro z hz
  rw [contMDiffWithinAt_iff]
  constructor
  · exact e.symm.continuousOn.continuousWithinAt hz
  · let a := t93A06_torusAtlas_aux_quotient_charts_aux_lift z
    let c := t93A06_torusAtlas_aux_quotient_charts_aux_chart a
    have hza : projection a = z :=
      t93A06_torusAtlas_aux_quotient_charts_aux_lift_spec z
    have hzc : z ∈ c.source := by
      rw [t93A06_torusAtlas_aux_quotient_charts_aux_chart_source]
      exact ⟨a, t93A06_torusAtlas_aux_quotient_charts_aux_mem_box a, hza⟩
    have hc_eq : chartAt Plane z = c := rfl
    let t := c.symm.trans e.symm
    have ha : a ∈ t.source := by
      constructor
      · simpa [c, t93A06_torusAtlas_aux_quotient_charts_aux_chart] using
          t93A06_torusAtlas_aux_quotient_charts_aux_mem_box a
      · simpa [t, c, t93A06_torusAtlas_aux_quotient_charts_aux_chart, hza] using hz
    have hta : t a = e.symm z := by
      simp [t, c, t93A06_torusAtlas_aux_quotient_charts_aux_chart, hza]
    have hcont : ContinuousWithinAt (fun w ↦ t w - w) t.source a :=
      (t.continuousOn.continuousWithinAt ha).sub continuousWithinAt_id
    have hev : ∀ᶠ w in nhdsWithin a t.source,
        dist (t w - w) (t a - a) < 1 :=
      (Metric.tendsto_nhds.mp hcont) 1 zero_lt_one
    have heq : ∀ᶠ w in nhdsWithin (extChartAt 𝓘(ℝ, Plane) z z)
        ((extChartAt 𝓘(ℝ, Plane) z).symm ⁻¹' e.target ∩ Set.range (𝓘(ℝ, Plane))),
        (extChartAt 𝓘(ℝ, Plane) (e.symm z) ∘ e.symm ∘
          (extChartAt 𝓘(ℝ, Plane) z).symm) w =
          w + (e.symm z - a) := by
      have hcenter : extChartAt 𝓘(ℝ, Plane) z z = a := by
        change c z = a
        rw [← hza]
        exact t93A06_torusAtlas_aux_quotient_charts_aux_chart_proj a a
          (t93A06_torusAtlas_aux_quotient_charts_aux_mem_box a)
      rw [hcenter]
      rw [eventually_nhdsWithin_iff] at hev ⊢
      filter_upwards [hev, c.open_target.eventually_mem
        (by simpa [c, t93A06_torusAtlas_aux_quotient_charts_aux_chart] using
          t93A06_torusAtlas_aux_quotient_charts_aux_mem_box a)] with w hw hwc hwd
      have hproj : (extChartAt 𝓘(ℝ, Plane) z).symm w = projection w := by
        simp [extChartAt, hc_eq, c,
          t93A06_torusAtlas_aux_quotient_charts_aux_chart]
      have hwe : projection w ∈ e.target := by
        simpa [hproj] using hwd.1
      have hwt : w ∈ t.source := ⟨hwc, by simpa [t, hproj] using hwe⟩
      have hw := hw hwt
      have hfib : projection (e.symm (projection w)) = projection w := by
        exact e.right_inv hwe
      obtain ⟨k, hk⟩ :=
        (t93A06_torusAtlas_aux_quotient_charts_aux_fibers w
          (e.symm (projection w))).mp hfib.symm
      have hfibz : projection a = projection (e.symm z) := by
        rw [hza]
        simpa [e] using (e.right_inv hz).symm
      obtain ⟨q, hq⟩ :=
        (t93A06_torusAtlas_aux_quotient_charts_aux_fibers a (e.symm z)).mp hfibz
      have hkz : k = q := by
        funext i
        have hcproj : c.symm w = projection w := by
          simp [c, t93A06_torusAtlas_aux_quotient_charts_aux_chart]
        have htw : t w = e.symm (projection w) := by
          simp [t, hcproj]
        have hcoord : |((k i - q i : ℤ) : ℝ)| < 1 := by
          calc
            |((k i - q i : ℤ) : ℝ)| = |(t w - w) i - (t a - a) i| := by
              rw [Int.cast_sub]
              simp only [Pi.sub_apply, hta, htw, hk i, hq i]
              ring
            _ ≤ ‖(t w - w) - (t a - a)‖ :=
              norm_le_pi_norm ((t w - w) - (t a - a)) i
            _ = dist (t w - w) (t a - a) := by rw [dist_eq_norm]
            _ < 1 := hw
        have hlo : (-1 : ℤ) < k i - q i := by exact_mod_cast (abs_lt.mp hcoord).1
        have hhi : k i - q i < 1 := by exact_mod_cast (abs_lt.mp hcoord).2
        omega
      funext i
      change e.symm (projection w) i = w i + (e.symm z i - a i)
      rw [hk i]
      rw [hkz, hq i]
      ring
    apply (contDiff_id.add (contDiff_const : ContDiff ℝ ∞
      (fun _ : Plane ↦ e.symm z - a))).contDiffWithinAt.congr_of_eventuallyEq heq
    have : (chartAt Plane z) z = a := by
      rw [hc_eq, ← hza]
      exact t93A06_torusAtlas_aux_quotient_charts_aux_chart_proj a a
        (t93A06_torusAtlas_aux_quotient_charts_aux_mem_box a)
    change e.symm ((chartAt Plane z).symm ((chartAt Plane z) z)) =
      (chartAt Plane z) z + (e.symm z - a)
    rw [(chartAt Plane z).left_inv hzc, this]
    ring
theorem t93A06_torusAtlas_aux_quotient_charts :
    ∃ charts : ChartedSpace Plane Torus,
      letI := charts
      (∀ e ∈ atlas Plane Torus, ∃ x : Torus, e = chartAt Plane x) ∧
      (∀ x y : Torus, ∀ z ∈ ((chartAt Plane x).symm.trans (chartAt Plane y)).source,
        ∃ k : Fin 2 → ℤ, ∀ i,
          ((chartAt Plane x).symm.trans (chartAt Plane y)) z i =
            z i + (k i : ℝ)) ∧
      IsLocalDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection := by
  let charts := t93A06_torusAtlas_aux_quotient_charts_aux_charts
  refine ⟨charts, ?_, ?_, ?_⟩
  · rintro e ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · exact t93A06_torusAtlas_aux_quotient_charts_aux_transition
  · letI := charts
    have hsmooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection :=
      t93A06_torusAtlas_aux_quotient_charts_aux_projection_smooth
    intro x
    let e := OpenPartialHomeomorph.ofContinuousOpen
      ((t93A06_torusAtlas_aux_quotient_charts_aux_box_inj x).toPartialEquiv
        projection (t93A06_torusAtlas_aux_quotient_charts_aux_box x))
      (show Continuous projection from by unfold projection; fun_prop).continuousOn
      t93A06_torusAtlas_aux_quotient_charts_aux_open_projection
      (t93A06_torusAtlas_aux_quotient_charts_aux_box_open x)
    let de : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane Torus ∞ :=
      { toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := by
          intro y hy
          exact (hsmooth y).contMDiffWithinAt
        contMDiffOn_invFun := by
          exact t93A06_torusAtlas_aux_quotient_charts_aux_inverse_smooth x }
    refine ⟨de, ?_, ?_⟩
    · exact t93A06_torusAtlas_aux_quotient_charts_aux_mem_box x
    · intro y hy
      rfl

/-- LIBRARY (atlas coverage): a charted structure on the quotient for which
the surjective projection from the plane is locally a diffeomorphism is a
smooth two-manifold.  Its input is explicit, so this seat does not depend on
the sorry proving `t93A06_torusAtlas_aux_quotient_charts`. -/
theorem t93A06_torusAtlas_aux_manifold_of_localDiffeomorph
    (charts : ChartedSpace Plane Torus)
    (hatlas : letI := charts
      (∀ e ∈ atlas Plane Torus, ∃ x : Torus, e = chartAt Plane x))
    (htrans : letI := charts
      (∀ x y : Torus, ∀ z ∈ ((chartAt Plane x).symm.trans (chartAt Plane y)).source, ∃ k : Fin 2 → ℤ, ∀ i, ((chartAt Plane x).symm.trans (chartAt Plane y)) z i = z i + (k i : ℝ))) :
    letI := charts
    IsManifold 𝓘(ℝ,Plane) ∞ Torus := by
  letI := charts
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := hatlas e he
  obtain ⟨y, rfl⟩ := hatlas e' he'
  let t := (chartAt Plane x).symm.trans (chartAt Plane y)
  have ht : ContDiffOn ℝ ∞ (↑t) t.source := by
    intro z hz
    obtain ⟨k, hk⟩ := htrans x y z hz
    have hc : ContinuousWithinAt (fun w ↦ t w - w) t.source z :=
      (t.continuousOn.continuousWithinAt hz).sub continuousWithinAt_id
    have hev : ∀ᶠ w in nhdsWithin z t.source,
        dist (t w - w) (t z - z) < 1 :=
      (Metric.tendsto_nhds.mp hc) 1 zero_lt_one
    have heq : ∀ᶠ w in nhdsWithin z t.source, t w = w + fun i ↦ (k i : ℝ) := by
      filter_upwards [hev, self_mem_nhdsWithin] with w hw hws
      obtain ⟨l, hl⟩ := htrans x y w hws
      change ∀ i, t w i = w i + (l i : ℝ) at hl
      change ∀ i, t z i = z i + (k i : ℝ) at hk
      have hlk : l = k := by
        funext i
        have hcoord : |((l i - k i : ℤ) : ℝ)| < 1 := by
          calc
            |((l i - k i : ℤ) : ℝ)| = |(t w - w) i - (t z - z) i| := by
              rw [Int.cast_sub]
              simp only [Pi.sub_apply]
              rw [hl i, hk i]
              ring
            _ ≤ ‖(t w - w) - (t z - z)‖ :=
              norm_le_pi_norm ((t w - w) - (t z - z)) i
            _ = dist (t w - w) (t z - z) := by rw [dist_eq_norm]
            _ < 1 := hw
        have hlo : (-1 : ℤ) < l i - k i := by
          exact_mod_cast (abs_lt.mp hcoord).1
        have hhi : l i - k i < 1 := by
          exact_mod_cast (abs_lt.mp hcoord).2
        omega
      simpa [hlk] using funext hl
    apply (contDiff_id.add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : Plane ↦ (fun i ↦ (k i : ℝ))))).contDiffWithinAt.congr_of_eventuallyEq
      heq
    exact funext hk
  simpa using ht

/-- The two independent quotient-chart conclusions assemble into the target
atlas structure. -/
theorem t93A06_torusAtlas : Nonempty SmoothAtlas := by
  obtain ⟨charts, hatlas, htrans, hlocal⟩ := t93A06_torusAtlas_aux_quotient_charts
  letI := charts
  exact ⟨⟨charts,
    t93A06_torusAtlas_aux_manifold_of_localDiffeomorph charts hatlas htrans,
    hlocal⟩⟩

/-- The fibres of the printed quotient projection are precisely integer
translates. -/
theorem t93A06_projection_fibers (x y : Plane) :
    projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ) := by
  constructor
  · intro h
    have hcoord (i : Fin 2) : (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ)) :=
      congrFun h i
    choose n hn using fun i =>
      (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := x i - y i)).mp (by
        rw [AddCircle.coe_sub, hcoord i, sub_self])
    refine ⟨fun i => -n i, fun i => ?_⟩
    have hd : (n i : ℝ) = x i - y i := by
      simpa using hn i
    rw [Int.cast_neg]
    linarith
  · rintro ⟨k, hk⟩
    funext i
    change (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
    rw [hk i, AddCircle.coe_add]
    simp

lemma t93A06_periodic_form_descent_aux_source_periodic
    (x : Plane) (k : Fin 2 → ℤ) :
    sourceForm (fun i ↦ x i + (k i : ℝ)) = sourceForm x := by
  unfold sourceForm
  have hs : Real.sin (2 * Real.pi * (x 0 + (k 0 : ℝ))) =
      Real.sin (2 * Real.pi * x 0) := by
    rw [show 2 * Real.pi * (x 0 + (k 0 : ℝ)) =
      2 * Real.pi * x 0 + (k 0 : ℝ) * (2 * Real.pi) by ring]
    exact Real.sin_add_int_mul_two_pi _ _
  have hc : Real.cos (2 * Real.pi * (x 1 + (k 1 : ℝ))) =
      Real.cos (2 * Real.pi * x 1) := by
    rw [show 2 * Real.pi * (x 1 + (k 1 : ℝ)) =
      2 * Real.pi * x 1 + (k 1 : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_int_mul_two_pi _ _
  rw [hs, hc]

lemma t93A06_periodic_form_descent_aux_projection_surjective :
    Function.Surjective projection := by
  intro z
  choose x hx using fun i ↦ QuotientAddGroup.mk_surjective (z i)
  refine ⟨x, funext fun i ↦ ?_⟩
  exact hx i

lemma t93A06_periodic_form_descent_aux_pullback_injective
    (atlas : SmoothAtlas) :
    letI := atlas.charts
    Function.Injective
      (pullback (k := 2) projection : Form Plane Torus 2 → Form Plane Plane 2) := by
  letI := atlas.charts
  intro a b hab
  funext z
  obtain ⟨x, rfl⟩ := t93A06_periodic_form_descent_aux_projection_surjective z
  let L : Plane ≃L[ℝ] Plane :=
    atlas.quotient_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x
  apply ContinuousAlternatingMap.ext
  intro v
  have hpoint := congr_fun hab x
  have happ := congrArg (fun q ↦ q (fun i ↦ L.symm (v i))) hpoint
  change a (projection x) (fun i ↦ L (L.symm (v i))) =
    b (projection x) (fun i ↦ L (L.symm (v i))) at happ
  have hv : (fun i ↦ L (L.symm (v i))) = v := by
    funext i
    exact L.apply_symm_apply (v i)
  simpa [hv] using happ

lemma t93A06_periodic_form_descent_aux_source_smooth :
    ContDiff ℝ ∞ sourceForm := by
  unfold sourceForm areaForm
  fun_prop

/-- Set-level descent of the periodic covector field.  Periodicity is an
explicit input so this leaf can be proved independently of the trigonometric
calculation above. -/
theorem t93A06_periodic_form_descent_aux_set_descent
    (atlas : SmoothAtlas)
    (hfib : ∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ))
    (hperiodic : ∀ (x : Plane) (k : Fin 2 → ℤ),
      sourceForm (fun i ↦ x i + (k i : ℝ)) = sourceForm x) :
    letI := atlas.charts
    ∃ form : Form Plane Torus 2,
      pullback projection form = sourceForm := by
  letI := atlas.charts
  classical
  let lift : Torus → Plane := fun z ↦
    Classical.choose (t93A06_periodic_form_descent_aux_projection_surjective z)
  have hlift (z : Torus) : projection (lift z) = z :=
    Classical.choose_spec (t93A06_periodic_form_descent_aux_projection_surjective z)
  let D (x : Plane) : Plane ≃L[ℝ] Plane :=
    atlas.quotient_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x
  let form : Form Plane Torus 2 := fun z ↦
    (sourceForm (lift z)).compContinuousLinearMap (D (lift z)).symm
  refine ⟨form, funext fun x ↦ ?_⟩
  obtain ⟨k, hk⟩ :=
    (hfib x (lift (projection x))).mp (hlift (projection x)).symm
  have hproj : (fun y : Plane ↦ projection (fun i ↦ y i + (k i : ℝ))) =
      projection := by
    funext y
    exact ((hfib y (fun i ↦ y i + (k i : ℝ))).mpr
      ⟨k, fun i ↦ rfl⟩).symm
  have htrans : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane)
      (fun y : Plane ↦ fun i ↦ y i + (k i : ℝ)) x =
      ContinuousLinearMap.id ℝ Plane := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id x).add_const (fun i ↦ (k i : ℝ))).fderiv
  have hlift_eq : lift (projection x) = (fun i ↦ x i + (k i : ℝ)) := by
    funext i
    exact hk i
  have hd : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection
      (lift (projection x)) =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection x := by
    rw [hlift_eq]
    have hc := mfderiv_comp x
      ((atlas.quotient_localDiffeomorph
        (fun i ↦ x i + (k i : ℝ))).mdifferentiableAt (by simp))
      (show MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane)
        (fun y : Plane ↦ fun i ↦ y i + (k i : ℝ)) x by
          rw [mdifferentiableAt_iff_differentiableAt]
          exact ((hasFDerivAt_id x).add_const
            (fun i ↦ (k i : ℝ))).differentiableAt)
    rw [show (projection ∘ (fun y : Plane ↦ fun i ↦ y i + (k i : ℝ))) =
      projection by funext y; exact congrFun hproj y,
      htrans] at hc
    simpa using hc.symm
  apply ContinuousAlternatingMap.ext
  intro v
  change sourceForm (lift (projection x))
      (fun i ↦ (D (lift (projection x))).symm
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection x (v i))) =
    sourceForm x v
  rw [show sourceForm (lift (projection x)) = sourceForm x by
    rw [hlift_eq, hperiodic x k]]
  have hD : (D (lift (projection x)) : Plane →L[ℝ] Plane) =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection x := by
    change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection (lift (projection x)) = _
    exact hd
  rw [← hD]
  congr 1
  funext i
  exact (D (lift (projection x))).symm_apply_apply (v i)

lemma t93A06_periodic_form_descent_aux_smooth_of_pullback_aux_euclidean
    (g : Plane → Plane) (y : Plane) (hg : ContDiffAt ℝ ∞ g y)
    (hsource : ContDiff ℝ ∞ sourceForm) :
    ContDiffAt ℝ ∞ (fun u ↦ (sourceForm (g u)).compContinuousLinearMap
      (fderiv ℝ g u)) y := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g) y :=
    hg.fderiv_right (by norm_cast)
  clear hsource
  have heq : (fun u ↦ (sourceForm (g u)).compContinuousLinearMap
      (fderiv ℝ g u)) = fun u ↦
      ((Real.sin (2 * Real.pi * g u 0) ^ 2 *
          Real.cos (2 * Real.pi * g u 1) ^ 2) *
        areaForm (⇑(fderiv ℝ g u) ∘ ⇑(Pi.basisFun ℝ (Fin 2)))) • areaForm := by
    funext u
    apply ContinuousAlternatingMap.ext
    intro v
    have h := congrArg (fun q ↦ q v) (AlternatingMap.eq_smul_basis_det
      (Pi.basisFun ℝ (Fin 2))
      ((sourceForm (g u)).compContinuousLinearMap
        (fderiv ℝ g u)).toAlternatingMap)
    simpa [sourceForm, areaForm] using h
  rw [heq]
  have hv : ContDiffAt ℝ ∞
      (fun u ↦ ⇑(fderiv ℝ g u) ∘ ⇑(Pi.basisFun ℝ (Fin 2))) y := by
    rw [contDiffAt_pi]
    intro i
    exact hd.clm_apply contDiffAt_const
  have ha : ContDiffAt ℝ ∞
      (fun u ↦ areaForm
        (⇑(fderiv ℝ g u) ∘ ⇑(Pi.basisFun ℝ (Fin 2)))) y :=
    areaForm.toContinuousMultilinearMap.contDiff.contDiffAt.comp y hv
  fun_prop

theorem t93A06_periodic_form_descent_aux_smooth_of_pullback
    (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hsource : ContDiff ℝ ∞ sourceForm)
    (hpull : letI := atlas.charts
      pullback projection form = sourceForm) :
    letI := atlas.charts
    IsSmooth form := by
  letI := atlas.charts
  letI : IsManifold 𝓘(ℝ, Plane) ∞ Torus := atlas.smooth
  intro e he
  intro y hy
  have hz : e.symm y ∈ e.source := e.map_target hy
  obtain ⟨x, hx⟩ := t93A06_periodic_form_descent_aux_projection_surjective (e.symm y)
  let hloc := atlas.quotient_localDiffeomorph x
  let s := hloc.localInverse
  let g : Plane → Plane := fun u ↦ s (e.symm u)
  have hsz : e.symm y ∈ s.source := by
    rw [← hx]
    exact hloc.localInverse_mem_source
  have hg : ContDiffWithinAt ℝ ∞ g e.target y := by
    change ContDiffWithinAt ℝ ∞ (fun u ↦ s (e.symm u)) e.target y
    have hsmooth_s : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ s (e.symm y) :=
      hloc.localInverse_contMDiffOn.contMDiffAt (s.open_source.mem_nhds hsz)
    have hsmooth_e : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ e.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
    have hcomp := (hsmooth_s.comp y hsmooth_e).contMDiffWithinAt (s := e.target)
    rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp
    exact hcomp
  have hrhs : ContDiffWithinAt ℝ ∞
      (fun u ↦ (sourceForm (g u)).compContinuousLinearMap
        (fderiv ℝ g u)) e.target y := by
    have hga : ContDiffAt ℝ ∞ g y := hg.contDiffAt (e.open_target.mem_nhds hy)
    exact (t93A06_periodic_form_descent_aux_smooth_of_pullback_aux_euclidean
      g y hga hsource).contDiffWithinAt
  apply hrhs.congr_of_eventuallyEq
  filter_upwards [self_mem_nhdsWithin,
    (e.continuousOn_symm y hy).preimage_mem_nhdsWithin
      (s.open_source.mem_nhds hsz)] with u hu hus
  · unfold inChart
    have hpu : projection (g u) = e.symm u := hloc.localInverse_right_inv hus
    rw [← hpu, ← congrFun hpull (g u)]
    unfold pullback
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_apply]
    have he_smooth : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ e.symm u :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hu
    have hs_smooth : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ s (e.symm u) :=
      hloc.localInverse_contMDiffOn.contMDiffAt (s.open_source.mem_nhds hus)
    have hg_smooth : ContDiffAt ℝ ∞ g u := by
      have hh := hs_smooth.comp u he_smooth
      rw [contMDiffAt_iff_contDiffAt] at hh
      exact hh
    have hp_smooth := (atlas.quotient_localDiffeomorph (g u)).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp u hp_smooth
      (mdifferentiableAt_iff_differentiableAt.mpr (hg_smooth.differentiableAt (by simp)))
    have hev : (projection ∘ g) =ᶠ[nhds u] e.symm := by
      filter_upwards [(e.continuousAt_symm hu).preimage_mem_nhds
        (s.open_source.mem_nhds hus)] with v hv
      exact hloc.localInverse_right_inv hv
    rw [← hev.mfderiv_eq, hchain]
    congr 1
    funext i
    simp only [mfderiv_eq_fderiv]
    change ((mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection (g u)).comp
      (fderiv ℝ g u)) (v i) = _
    rw [ContinuousLinearMap.comp_apply]
    rfl
  · unfold inChart
    have hpy : projection (g y) = e.symm y := hloc.localInverse_right_inv hsz
    rw [← hpy, ← congrFun hpull (g y)]
    unfold pullback
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_apply]
    have hga : ContDiffAt ℝ ∞ g y := hg.contDiffAt (e.open_target.mem_nhds hy)
    have hp_smooth := (atlas.quotient_localDiffeomorph (g y)).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp y hp_smooth
      (mdifferentiableAt_iff_differentiableAt.mpr (hga.differentiableAt (by simp)))
    have hev : (projection ∘ g) =ᶠ[nhds y] e.symm := by
      filter_upwards [(e.continuousAt_symm hy).preimage_mem_nhds
        (s.open_source.mem_nhds hsz)] with v hv
      exact hloc.localInverse_right_inv hv
    rw [← hev.mfderiv_eq, hchain]
    congr 1
    funext i
    simp only [mfderiv_eq_fderiv]
    change ((mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection (g y)).comp
      (fderiv ℝ g y)) (v i) = _
    rw [ContinuousLinearMap.comp_apply]
    rfl

/-- A smooth invariant form descends uniquely through the quotient atlas.
The fibre characterization is supplied as a hypothesis to keep this seat
independent of the atlas and fibre seats. -/
theorem t93A06_periodic_form_descent (atlas : SmoothAtlas)
    (hfib : ∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ)) :
    letI := atlas.charts
    ∃ form : Form Plane Torus 2,
      IsSmooth form ∧ pullback projection form = sourceForm ∧
      (∀ other : Form Plane Torus 2, IsSmooth other →
        pullback projection other = sourceForm → other = form) := by
  letI := atlas.charts
  obtain ⟨form, hpull⟩ :=
    t93A06_periodic_form_descent_aux_set_descent atlas hfib
      t93A06_periodic_form_descent_aux_source_periodic
  have hsmooth : IsSmooth form :=
    t93A06_periodic_form_descent_aux_smooth_of_pullback atlas form
      t93A06_periodic_form_descent_aux_source_smooth hpull
  refine ⟨form, hsmooth, hpull, ?_⟩
  intro other _ hother
  exact t93A06_periodic_form_descent_aux_pullback_injective atlas
    (hother.trans hpull.symm)

/-- The fundamental-square integral is `1/4` for any form whose pullback is
the printed periodic form. -/
lemma t93A06_torusIntegral_quarter_aux_sin :
    (∫ x : ℝ in 0..1, Real.sin (2 * Real.pi * x) ^ 2) = 1 / 2 := by
  have hd : deriv (fun x : ℝ => x / 2 - Real.sin (4 * Real.pi * x) / (8 * Real.pi)) =
      fun x => Real.sin (2 * Real.pi * x) ^ 2 := by
    funext x
    have h := ((hasDerivAt_id x).div_const 2 |>.sub
      (((Real.hasDerivAt_sin (4 * Real.pi * x)).comp x
        (((hasDerivAt_const x (4 * Real.pi)).mul (hasDerivAt_id x)))).div_const
          (8 * Real.pi)))
    rw [show deriv (fun x : ℝ => x / 2 - Real.sin (4 * Real.pi * x) /
      (8 * Real.pi)) x = _ by simpa only [Function.comp_apply, id_eq] using h.deriv]
    rw [Real.sin_sq_eq_half_sub]
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => x / 2 - Real.sin (4 * Real.pi * x) / (8 * Real.pi)) hd]
  · norm_num
    rw [show 4 * Real.pi = (4 : ℕ) * Real.pi by norm_num,
      Real.sin_nat_mul_pi]
  · intro x hx
    fun_prop
  · fun_prop

lemma t93A06_torusIntegral_quarter_aux_cos :
    (∫ x : ℝ in 0..1, Real.cos (2 * Real.pi * x) ^ 2) = 1 / 2 := by
  have hd : deriv (fun x : ℝ => x / 2 + Real.sin (4 * Real.pi * x) / (8 * Real.pi)) =
      fun x => Real.cos (2 * Real.pi * x) ^ 2 := by
    funext x
    have h := ((hasDerivAt_id x).div_const 2 |>.add
      (((Real.hasDerivAt_sin (4 * Real.pi * x)).comp x
        (((hasDerivAt_const x (4 * Real.pi)).mul (hasDerivAt_id x)))).div_const
          (8 * Real.pi)))
    rw [show deriv (fun x : ℝ => x / 2 + Real.sin (4 * Real.pi * x) /
      (8 * Real.pi)) x = _ by simpa only [Function.comp_apply, id_eq] using h.deriv]
    rw [Real.cos_sq]
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => x / 2 + Real.sin (4 * Real.pi * x) / (8 * Real.pi)) hd]
  · norm_num
    rw [show 4 * Real.pi = (4 : ℕ) * Real.pi by norm_num,
      Real.sin_nat_mul_pi]
  · intro x hx
    fun_prop
  · fun_prop

theorem t93A06_torusIntegral_quarter (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hpull : letI := atlas.charts
      pullback projection form = sourceForm) :
    letI := atlas.charts
    torusIntegral form = 1 / 4 := by
  letI := atlas.charts
  unfold ConstructionTargets.TorusFormTargets.torusIntegral
  rw [hpull]
  simp [sourceForm, pullback, areaForm]
  rw [t93A06_torusIntegral_quarter_aux_sin,
    t93A06_torusIntegral_quarter_aux_cos]
  norm_num
  change Matrix.det ![Pi.single 0 (1 : ℝ), Pi.single 1 (1 : ℝ)] = 1
  norm_num [Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The two coordinate coefficients of the pullback of a torus one-form. -/
def t93A06_pulledCoeff (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1) (i : Fin 2) (x : Plane) : ℝ := by
  letI := atlas.charts
  exact (pullback projection η x) (fun _ : Fin 1 ↦ (Pi.single i (1 : ℝ) : Plane))

/-- Naturality of `exteriorDerivative` for the quotient local diffeomorphism.
This is isolated from the subsequent coordinate integration. -/
theorem t93A06_exact_integral_aux_pullback_d (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) :
    letI := atlas.charts
    pullback projection (exteriorDerivative η) =
      exteriorDerivative (E := Plane) (M := Plane) (pullback projection η) := by
  letI := atlas.charts
  letI := atlas.smooth
  funext x
  let e := chartAt Plane (projection x)
  let g : Plane → Plane := fun y ↦ e (projection y)
  have hxsrc : projection x ∈ e.source := mem_chart_source Plane (projection x)
  have hxtgt : e (projection x) ∈ e.target := e.map_source hxsrc
  have hω : DifferentiableAt ℝ (inChart η e) (e (projection x)) := by
    have hs := hη e (chart_mem_atlas _ _)
    exact (hs.differentiableOn (by simp)).differentiableAt
      (e.open_target.mem_nhds hxtgt)
  have hg : ContDiffAt ℝ ∞ g x := by
    have hp : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ projection x :=
      (atlas.quotient_localDiffeomorph x).contMDiffAt
    have he : ContMDiffAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ e (projection x) :=
      (contMDiffOn_chart (x := projection x)).contMDiffAt
        ((e.open_source.mem_nhds hxsrc))
    simpa [g, contMDiffAt_iff_contDiffAt] using he.comp x hp
  have hlocal : pullback projection η =ᶠ[nhds x]
      fun y ↦ ((inChart η e) (g y)).compContinuousLinearMap (fderiv ℝ g y) := by
    filter_upwards [(atlas.quotient_localDiffeomorph x).contMDiffAt.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hxsrc)] with y hy
    unfold pullback inChart
    rw [e.left_inv hy]
    rw [show fderiv ℝ g y =
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e (projection y)).comp
          (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection y) by
      rw [← mfderiv_comp y
        (((contMDiffOn_chart (x := projection x)).contMDiffAt
          (e.open_source.mem_nhds hy)).mdifferentiableAt
            (show (∞ : WithTop ℕ∞) ≠ 0 by simp))
        ((atlas.quotient_localDiffeomorph y).mdifferentiableAt
          (show (∞ : WithTop ℕ∞) ≠ 0 by simp))]
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ g y = fderiv ℝ g y
      rfl]
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      Function.comp_apply]
    have hc := (mdifferentiable_chart (I := 𝓘(ℝ, Plane))
      (projection x)).symm_comp_deriv hy
    congr 1
    funext i
    change (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection y) (v i) =
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e.symm (e (projection y)))
        ((mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e (projection y))
          ((mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection y) (v i)))
    rw [← ContinuousLinearMap.comp_apply, hc]
    rfl
  have hdg : fderiv ℝ g x =
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e (projection x)).comp
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection x) := by
    rw [← mfderiv_comp x
      (((contMDiffOn_chart (x := projection x)).contMDiffAt
        (e.open_source.mem_nhds hxsrc)).mdifferentiableAt
          (show (∞ : WithTop ℕ∞) ≠ 0 by simp))
      ((atlas.quotient_localDiffeomorph x).mdifferentiableAt
        (show (∞ : WithTop ℕ∞) ≠ 0 by simp))]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ g x = fderiv ℝ g x
    rfl
  have hself : inChart (pullback projection η) (OpenPartialHomeomorph.refl Plane) =
      pullback projection η := by
    funext y
    apply ContinuousAlternatingMap.ext
    intro v
    have hr : mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
        (OpenPartialHomeomorph.refl Plane).symm y = ContinuousLinearMap.id ℝ Plane := by
      simpa only [OpenPartialHomeomorph.refl_symm] using
        (mfderiv_id (I := 𝓘(ℝ, Plane)) (x := y))
    unfold inChart
    rw [hr]
    congr 1
  unfold exteriorDerivative
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, hself, mfderiv_id]
  change ((extDeriv (inChart η e) (g x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e (projection x))).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection x) =
      (extDeriv (pullback projection η) x).compContinuousLinearMap
        (ContinuousLinearMap.id ℝ Plane)
  apply ContinuousAlternatingMap.ext
  intro v
  change extDeriv (inChart η e) (g x)
      (fun i ↦ (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e (projection x))
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection x (v i))) =
    extDeriv (pullback projection η) x v
  rw [show (fun i ↦ (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e (projection x))
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) projection x (v i))) =
      fun i ↦ fderiv ℝ g x (v i) by
    funext i
    rw [hdg]
    rfl]
  rw [hlocal.extDeriv_eq]
  have hn : extDeriv (fun y ↦ ((inChart η e) (g y)).compContinuousLinearMap
        (fderiv ℝ g y)) x =
      (extDeriv (inChart η e) (g x)).compContinuousLinearMap (fderiv ℝ g x) :=
    extDeriv_pullback hω hg (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  exact congrArg (fun q ↦ q v) hn.symm

lemma t93A06_exact_integral_aux_coeff_smooth_aux_global
    (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) (i : Fin 2) :
    ContDiff ℝ 1 (t93A06_pulledCoeff atlas η i) := by
  letI := atlas.charts
  letI : IsManifold 𝓘(ℝ,Plane) ∞ Torus := atlas.smooth
  rw [contDiff_iff_contDiffAt]
  intro x
  let e := chartAt Plane (projection x)
  let g : Plane → Plane := fun y ↦ e (projection y)
  have hp : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection x :=
    atlas.quotient_localDiffeomorph.contMDiff x
  have he : ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ e (projection x) :=
    (contMDiffOn_chart (I := 𝓘(ℝ,Plane)) (n := ∞)).contMDiffAt
      (e.open_source.mem_nhds (mem_chart_source Plane (projection x)))
  have hg : ContDiffAt ℝ ∞ g x :=
    (he.comp x hp).contDiffAt
  have hform : ContDiffAt ℝ ∞ (inChart η e) (g x) := by
    apply (hη e (chart_mem_atlas Plane (projection x))).contDiffAt
    exact e.open_target.mem_nhds (mem_chart_target Plane (projection x))
  have hcomp : ContDiffAt ℝ ∞ (fun y ↦ inChart η e (g y)) x :=
    hform.comp x hg
  have hdg : ContDiffAt ℝ 1 (fun y ↦ fderiv ℝ g y
      (Pi.single i (1 : ℝ) : Plane)) x := by
    have hle : (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    exact (hg.fderiv_right hle).clm_apply contDiffAt_const
  have hsmooth : ContDiffAt ℝ 1 (fun y ↦
      (inChart η e (g y))
        (fun _ : Fin 1 ↦ fderiv ℝ g y (Pi.single i (1 : ℝ) : Plane))) x := by
    let ev : (Plane [⋀^Fin 1]→L[ℝ] ℝ) →ₗ[ℝ] (Plane →L[ℝ] ℝ) :=
      { toFun := fun A ↦ LinearMap.toContinuousLinearMap
          { toFun := fun v ↦ A (fun _ ↦ v)
            map_add' := by
              intro u v
              simpa [Function.update_eq_const_of_subsingleton] using
                A.map_update_add (fun _ ↦ u) 0 u v
            map_smul' := by
              intro m v
              simpa [Function.update_eq_const_of_subsingleton] using
                A.map_update_smul (fun _ ↦ v) 0 m v }
        map_add' := by intro A B; ext v; simp
        map_smul' := by intro c A; ext v; simp }
    let evc : (Plane [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (Plane →L[ℝ] ℝ) :=
      ev.mkContinuous 1 (fun A ↦ by
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro v
        simpa using A.le_opNorm (fun _ : Fin 1 ↦ v))
    have hev : ContDiffAt ℝ 1 (fun y ↦ evc (inChart η e (g y))) x := by
      have hle : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
      exact evc.contDiff.contDiffAt.comp x (hcomp.of_le hle)
    simpa [evc, ev] using hev.clm_apply hdg
  apply hsmooth.congr_of_eventuallyEq
  have hnhds : projection ⁻¹' e.source ∈ nhds x :=
    hp.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (mem_chart_source Plane (projection x)))
  filter_upwards [hnhds] with y hy
  unfold t93A06_pulledCoeff pullback inChart
  simp only [g, e]
  rw [e.left_inv hy]
  change η (projection y) (fun _ ↦
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection y (Pi.single i 1)) =
    (η (projection y)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) e.symm (e (projection y)))
      (fun _ ↦ fderiv ℝ (e ∘ projection) y (Pi.single i 1))
  rw [← mfderiv_eq_fderiv]
  rw [mfderiv_comp y
    (((contMDiffOn_chart (I := 𝓘(ℝ,Plane)) (n := ∞)).contMDiffAt
      (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
    (atlas.quotient_localDiffeomorph.mdifferentiable (by simp) y)]
  simp only [e]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]
  congr 1
  funext j
  have hder := congrArg (fun L : Plane →L[ℝ] Plane ↦
      L (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection y (Pi.single i 1)))
    ((mdifferentiable_chart (I := 𝓘(ℝ,Plane)) (projection x)).symm_comp_deriv hy)
  simpa using hder.symm

theorem t93A06_exact_integral_aux_coeff_smooth (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) :
    (∀ y : ℝ, ContDiff ℝ 1
      (fun x ↦ t93A06_pulledCoeff atlas η 1 ![x, y])) ∧
    (∀ x : ℝ, ContDiff ℝ 1
      (fun y ↦ t93A06_pulledCoeff atlas η 0 ![x, y])) := by
  have h0 := t93A06_exact_integral_aux_coeff_smooth_aux_global atlas η hη 0
  have h1 := t93A06_exact_integral_aux_coeff_smooth_aux_global atlas η hη 1
  constructor
  · intro y
    apply h1.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  · intro x
    apply h0.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop

/-- Unfold the fundamental-square integral and use the supplied naturality
identity.  This leaf contains no coordinate differentiation or integration
linearity. -/
theorem t93A06_exact_integral_aux_square_formula_unfold (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hnat : letI := atlas.charts
      pullback projection (exteriorDerivative η) =
        exteriorDerivative (E := Plane) (M := Plane) (pullback projection η)) :
    letI := atlas.charts
    torusIntegral (exteriorDerivative η) =
      ∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
        exteriorDerivative (E := Plane) (M := Plane) (pullback projection η)
          ![x, y] ![Pi.single 0 1, Pi.single 1 1] := by
  sorry

/-- The Euclidean exterior derivative of the pulled-back one-form, on the
positive coordinate basis, is `∂x Q - ∂y P`.  Global `C¹` regularity is
an explicit input, so this leaf is independent of both naturality and the
integral manipulation below. -/
theorem t93A06_exact_integral_aux_square_formula_pointwise (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hC1 : ∀ i : Fin 2, ContDiff ℝ 1 (t93A06_pulledCoeff atlas η i)) :
    letI := atlas.charts
    ∀ x y : ℝ,
      exteriorDerivative (E := Plane) (M := Plane) (pullback projection η)
          ![x, y] ![Pi.single 0 1, Pi.single 1 1] =
        deriv (fun s ↦ t93A06_pulledCoeff atlas η 1 ![s, y]) x -
        deriv (fun t ↦ t93A06_pulledCoeff atlas η 0 ![x, t]) y := by
  sorry

/-- Move the pointwise coordinate identity through the two interval integrals
and split the integral of a difference.  The identity is passed explicitly,
so this seat can be proved before the coordinate-calculus seat lands. -/
theorem t93A06_exact_integral_aux_square_formula_integral_split
    (F : ℝ → ℝ → ℝ) (P Q : Plane → ℝ)
    (hC1P : ContDiff ℝ 1 P) (hC1Q : ContDiff ℝ 1 Q)
    (hcoord : ∀ x y : ℝ, F x y =
      deriv (fun s ↦ Q ![s, y]) x - deriv (fun t ↦ P ![x, t]) y) :
    (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1, F x y) =
      (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
        deriv (fun s ↦ Q ![s, y]) x) -
      (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
        deriv (fun t ↦ P ![x, t]) y) := by
  sorry

/-- Coordinate formula for the integral of an exterior derivative.  This is
only the assembly of the three independent leaves above. -/
theorem t93A06_exact_integral_aux_square_formula (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hnat : letI := atlas.charts
      pullback projection (exteriorDerivative η) =
        exteriorDerivative (E := Plane) (M := Plane) (pullback projection η))
    (hC1 : ∀ i : Fin 2, ContDiff ℝ 1 (t93A06_pulledCoeff atlas η i)) :
    letI := atlas.charts
    torusIntegral (exteriorDerivative η) =
      (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
        deriv (fun s ↦ t93A06_pulledCoeff atlas η 1 ![s, y]) x) -
      (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
        deriv (fun t ↦ t93A06_pulledCoeff atlas η 0 ![x, t]) y) := by
  letI := atlas.charts
  rw [t93A06_exact_integral_aux_square_formula_unfold atlas η hnat]
  exact t93A06_exact_integral_aux_square_formula_integral_split
    (fun x y ↦ exteriorDerivative (E := Plane) (M := Plane)
      (pullback projection η) ![x, y] ![Pi.single 0 1, Pi.single 1 1])
    (t93A06_pulledCoeff atlas η 0) (t93A06_pulledCoeff atlas η 1)
    (hC1 0) (hC1 1)
    (t93A06_exact_integral_aux_square_formula_pointwise atlas η hC1)

/-- One-variable FTC for the `x` derivative, already integrated in `y`. -/
theorem t93A06_exact_integral_aux_ftc_x
    (Q : ℝ → ℝ → ℝ) (hQ : ∀ y, ContDiff ℝ 1 (fun x ↦ Q x y)) :
    (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1, deriv (fun s ↦ Q s y) x) =
      ∫ y : ℝ in 0..1, (Q 1 y - Q 0 y) := by
  apply intervalIntegral.integral_congr
  intro y _
  change (∫ x : ℝ in 0..1, deriv (fun s ↦ Q s y) x) = Q 1 y - Q 0 y
  rw [intervalIntegral.integral_deriv_eq_sub' (fun x ↦ Q x y) rfl]
  · intro x _
    exact (hQ y).differentiable (by norm_num) x
  · fun_prop

/-- Seat: the pulled-back coefficients are jointly `C¹` in `(x, y)`
(compose `t93A06_exact_integral_aux_coeff_smooth_aux_global` with the
continuous linear map `(x, y) ↦ ![x, y]`). -/
theorem t93A06_exact_integral_aux_joint_C1 (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) (i : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ t93A06_pulledCoeff atlas η i ![p.1, p.2]) := by
  apply (t93A06_exact_integral_aux_coeff_smooth_aux_global atlas η hη i).comp
  rw [contDiff_pi]
  intro j
  fin_cases j <;> simp <;> fun_prop

/-- One-variable FTC for the `y` derivative, already integrated in `x`. -/
theorem t93A06_exact_integral_aux_ftc_y
    (P : ℝ → ℝ → ℝ) (hP : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ P p.1 p.2)) :
    (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1, deriv (fun t ↦ P x t) y) =
      ∫ x : ℝ in 0..1, (P x 1 - P x 0) := by
  let f : ℝ × ℝ → ℝ := fun p ↦ deriv (fun t ↦ P p.1 t) p.2
  have hf_eq (p : ℝ × ℝ) :
      f p = fderiv ℝ (fun q : ℝ × ℝ ↦ P q.1 q.2) p (0, 1) := by
    have hp := (hP.differentiable one_ne_zero) p
    have hg : HasDerivAt (fun t : ℝ ↦ (p.1, t)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hs : HasDerivAt (fun t ↦ P p.1 t)
        (fderiv ℝ (fun q : ℝ × ℝ ↦ P q.1 q.2) p (0, 1)) p.2 := by
      simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
        (hp.hasFDerivAt.comp p.2 hg.hasFDerivAt).hasDerivAt
    exact hs.deriv
  have hf : Continuous f := by
    rw [show f = fun p ↦ fderiv ℝ (fun q : ℝ × ℝ ↦ P q.1 q.2) p (0, 1) from
      funext hf_eq]
    fun_prop
  have hint : MeasureTheory.Integrable (Function.uncurry fun y x ↦ f (x, y))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    simp only [Set.uIoc_of_le zero_le_one]
    exact ((hf.comp continuous_swap).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  rw [show (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
      deriv (fun t ↦ P x t) y) =
      ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, deriv (fun t ↦ P x t) y by
    simpa [f, intervalIntegral.integral_of_le zero_le_one] using
      (MeasureTheory.integral_integral_swap hint)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact intervalIntegral.integral_deriv_of_contDiffOn_Icc
    ((hP.comp (by fun_prop : ContDiff ℝ 1 (fun t : ℝ ↦ (x, t)))).contDiffOn) zero_le_one

/-- Pullback coefficients agree on opposite sides of the unit square. -/
lemma t93A06_exact_integral_aux_periodic_aux_shift (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1) (i : Fin 2)
    (x : Plane) (k : Fin 2 → ℤ) :
    t93A06_pulledCoeff atlas η i (fun j ↦ x j + (k j : ℝ)) =
      t93A06_pulledCoeff atlas η i x := by
  letI := atlas.charts
  let c : Plane := fun j ↦ (k j : ℝ)
  let τ : Plane → Plane := fun y ↦ y + c
  have hproj : projection ∘ τ = projection := by
    funext y j
    change ((y j + (k j : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (y j : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add]
    simp
  have hτ : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) τ x = ContinuousLinearMap.id ℝ Plane := by
    rw [mfderiv_eq_fderiv]
    dsimp [τ]
    exact ((hasFDerivAt_id (𝕜 := ℝ) x).add_const c).fderiv
  have hd := mfderiv_comp x
    ((atlas.quotient_localDiffeomorph (τ x)).mdifferentiableAt (by simp))
    (show MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) τ x by
      rw [mdifferentiableAt_iff_differentiableAt]
      dsimp [τ]
      exact (((contDiff_id : ContDiff ℝ ∞ (id : Plane → Plane)).add
        (contDiff_const : ContDiff ℝ ∞ (fun _ : Plane ↦ c))).differentiable
          (by simp)).differentiableAt)
  rw [hproj] at hd
  rw [hτ] at hd
  have hd' : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection (τ x) =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection x := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun L : Plane →L[ℝ] Plane ↦ L v) hd
    simpa using hv.symm
  unfold t93A06_pulledCoeff ConstructionTargets.ManifoldFormTargets.pullback
  change (η (projection (τ x))).compContinuousLinearMap
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection (τ x)) _ = _
  rw [show projection (τ x) = projection x by
    exact congrFun hproj x, hd']
  rfl

theorem t93A06_exact_integral_aux_periodic (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1) :
    (∀ y : ℝ, t93A06_pulledCoeff atlas η 1 ![1, y] =
      t93A06_pulledCoeff atlas η 1 ![0, y]) ∧
    (∀ x : ℝ, t93A06_pulledCoeff atlas η 0 ![x, 1] =
      t93A06_pulledCoeff atlas η 0 ![x, 0]) := by
  constructor
  · intro y
    convert t93A06_exact_integral_aux_periodic_aux_shift atlas η 1
      (![0, y] : Plane) (![1, 0] : Fin 2 → ℤ) using 1 <;>
      congr 1 <;> funext j <;> fin_cases j <;> simp
  · intro x
    convert t93A06_exact_integral_aux_periodic_aux_shift atlas η 0
      (![x, 0] : Plane) (![0, 1] : Fin 2 → ℤ) using 1 <;>
      congr 1 <;> funext j <;> fin_cases j <;> simp

/-- The two FTC boundary terms vanish under opposite-edge periodicity. -/
theorem t93A06_exact_integral_aux_boundary_cancel
    (P Q : ℝ → ℝ → ℝ)
    (hQ : ∀ y, Q 1 y = Q 0 y) (hP : ∀ x, P x 1 = P x 0) :
    (∫ y : ℝ in 0..1, (Q 1 y - Q 0 y)) -
      (∫ x : ℝ in 0..1, (P x 1 - P x 0)) = 0 := by
  simp_rw [hQ, hP, sub_self]

/-- On this closed quotient torus, a smooth exact top form has zero
fundamental-square integral.  The proof is now only assembly of naturality,
coordinate FTC, and periodic cancellation. -/
theorem t93A06_not_exact_of_integral_quarter (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hsmooth : letI := atlas.charts; IsSmooth form)
    (hint : letI := atlas.charts; torusIntegral form = 1 / 4) :
    letI := atlas.charts
    ¬ IsExact form := by
  letI := atlas.charts
  rintro ⟨η, hη, rfl⟩
  have hnat := t93A06_exact_integral_aux_pullback_d atlas η hη
  have hsquare := t93A06_exact_integral_aux_square_formula atlas η hnat
    (fun i ↦ t93A06_exact_integral_aux_coeff_smooth_aux_global atlas η hη i)
  let P : ℝ → ℝ → ℝ := fun x y ↦ t93A06_pulledCoeff atlas η 0 ![x, y]
  let Q : ℝ → ℝ → ℝ := fun x y ↦ t93A06_pulledCoeff atlas η 1 ![x, y]
  obtain ⟨hQy, hPx⟩ := t93A06_exact_integral_aux_coeff_smooth atlas η hη
  have hftcx := t93A06_exact_integral_aux_ftc_x Q hQy
  have hftcy := t93A06_exact_integral_aux_ftc_y P
    (t93A06_exact_integral_aux_joint_C1 atlas η hη 0)
  obtain ⟨hQper, hPper⟩ := t93A06_exact_integral_aux_periodic atlas η
  have hcancel := t93A06_exact_integral_aux_boundary_cancel P Q hQper hPper
  have hz : torusIntegral (exteriorDerivative η) = 0 := by
    rw [hsquare]
    rw [hftcx, hftcy]
    exact hcancel
  linarith

/-- Coordinate calculus for the explicit primitive: it is smooth and its
exterior derivative is the source form. -/
lemma t93A06_primitive_calculus_aux_fderiv (w : Fin 1 → Plane) (x u : Plane) :
    fderiv ℝ (fun y ↦ primitive y w) x u =
      (Real.sin (2 * Real.pi * x 0) ^ 2 * u 0 * Real.cos (2 * Real.pi * x 1) ^ 2 -
       (x 0 / 2 - Real.sin (4 * Real.pi * x 0) / (8 * Real.pi)) *
         (4 * Real.pi * Real.cos (2 * Real.pi * x 1) *
           Real.sin (2 * Real.pi * x 1) * u 1)) * (w 0 1) := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have hA := (h0.mul_const (1 / 2)).sub
    (((h0.const_mul (4 * Real.pi)).sin).mul_const (1 / (8 * Real.pi)))
  have hC := ((h1.const_mul (2 * Real.pi)).cos).pow 2
  have h := (hA.mul hC).mul_const (w 0 1)
  have hf := congrArg (fun L : Plane →L[ℝ] ℝ ↦ L u) h.fderiv
  calc
    fderiv ℝ (fun y ↦ primitive y w) x u =
        fderiv ℝ (fun y ↦
          (y 0 * (1 / 2) - Real.sin (4 * Real.pi * y 0) * (1 / (8 * Real.pi))) *
            Real.cos (2 * Real.pi * y 1) ^ 2 * (w 0 1)) x u := by
      apply congrArg (fun f : Plane → ℝ ↦ fderiv ℝ f x u)
      funext y
      simp [primitive, div_eq_mul_inv]
    _ = _ := hf
    _ = _ := by
      simp [ContinuousLinearMap.proj_apply]
      have hs : Real.sin (2 * Real.pi * x 0) ^ 2 =
          1 - Real.cos (2 * Real.pi * x 0) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * x 0)]
      rw [hs]
      field_simp [Real.pi_ne_zero]
      rw [show x 0 * 4 * Real.pi = 2 * (x 0 * 2 * Real.pi) by ring,
        Real.cos_two_mul]
      ring

theorem t93A06_primitive_calculus :
    IsSmooth primitive ∧ exteriorDerivative primitive = sourceForm := by
  constructor
  · intro e he
    rw [chartedSpaceSelf_atlas] at he
    subst e
    unfold inChart primitive
    simp
    convert (show ContDiffOn ℝ ∞ primitive Set.univ by
      unfold primitive
      fun_prop) using 1
  · unfold exteriorDerivative
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply]
    have hin : inChart primitive (OpenPartialHomeomorph.refl Plane) = primitive := by
      funext y
      apply ContinuousAlternatingMap.ext
      intro w
      unfold inChart
      simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
        mfderiv_id]
      congr 1
    rw [hin]
    simp
    change extDeriv primitive x v = sourceForm x v
    have hd : Differentiable ℝ primitive := by
      unfold primitive
      fun_prop
    rw [extDeriv_apply (hd x)]
    simp only [Nat.reduceAdd, Int.reduceNeg, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      pow_zero, Fin.removeNth_zero, one_mul, Nat.mod_succ, pow_one, neg_mul]
    rw [t93A06_primitive_calculus_aux_fderiv,
      t93A06_primitive_calculus_aux_fderiv]
    simp [sourceForm, Fin.tail, Fin.removeNth]
    change _ = _ * Matrix.det v
    rw [Matrix.det_fin_two]
    ring

/-- Direct evaluation of the explicit primitive on the four oriented edges of
the parallelogram. -/
theorem t93A06_primitive_parallelogramIntegral :
    parallelogramIntegral primitive = 1 / 4 := by
  simp [parallelogramIntegral, segmentIntegral, primitive]
  let f : ℝ → ℝ := fun x ↦
    (x / 2 - Real.sin (4 * Real.pi * x) / (8 * Real.pi)) *
      Real.cos (2 * Real.pi * x) ^ 2
  have hf : Continuous f := by
    unfold f
    fun_prop
  have hreflect : (∫ x : ℝ in 0..1, f (1 - x)) = ∫ x : ℝ in 0..1, f x := by
    simpa using (intervalIntegral.integral_comp_sub_left f (a := (0 : ℝ)) (b := 1) 1)
  have hshift (x : ℝ) :
      ((1 - x + x * 2) / 2 -
          Real.sin (4 * Real.pi * (1 - x + x * 2)) / (8 * Real.pi)) *
          Real.cos (2 * Real.pi * x) ^ 2 =
        f x + (1 / 2 : ℝ) * Real.cos (2 * Real.pi * x) ^ 2 := by
    have hs : Real.sin (4 * Real.pi * (1 - x + x * 2)) =
        Real.sin (4 * Real.pi * x) := by
      rw [show 4 * Real.pi * (1 - x + x * 2) =
        4 * Real.pi * x + (2 : ℤ) * (2 * Real.pi) by push_cast; ring]
      exact Real.sin_add_int_mul_two_pi _ _
    rw [hs]
    unfold f
    ring
  rw [intervalIntegral.integral_congr (fun x _ ↦ hshift x)]
  change (∫ x : ℝ in 0..1, (f x + (1 / 2 : ℝ) * Real.cos (2 * Real.pi * x) ^ 2)) -
      (∫ x : ℝ in 0..1, f (1 - x)) = 4⁻¹
  have hg : Continuous (fun x : ℝ ↦
      (1 / 2 : ℝ) * Real.cos (2 * Real.pi * x) ^ 2) := by fun_prop
  rw [hreflect, intervalIntegral.integral_add (hf.intervalIntegrable 0 1)
    (hg.intervalIntegrable 0 1)]
  ring_nf
  have hder (x : ℝ) : HasDerivAt
      (fun y : ℝ ↦ y / 4 + Real.sin (4 * Real.pi * y) / (16 * Real.pi))
      (Real.cos (Real.pi * x * 2) ^ 2 * (1 / 2)) x := by
    have h := (hasDerivAt_id x).div_const 4 |>.add
      ((((hasDerivAt_const x (4 * Real.pi)).mul (hasDerivAt_id x)).sin).div_const
        (16 * Real.pi))
    convert h using 1
    · simp only [Pi.mul_apply, id_eq, zero_mul, zero_add, one_mul]
      rw [show Real.pi * x * 2 = 2 * Real.pi * x by ring, Real.cos_sq]
      rw [show 4 * Real.pi * x = 2 * (2 * Real.pi * x) by ring,
        Real.cos_two_mul]
      field_simp [Real.pi_ne_zero]
      ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hder x)
    ((by fun_prop : Continuous (fun x : ℝ ↦
      Real.cos (Real.pi * x * 2) ^ 2 * (1 / 2))).intervalIntegrable 0 1)]
  have hs : Real.sin (4 * Real.pi) = 0 := by
    rw [show 4 * Real.pi = 0 + (2 : ℤ) * (2 * Real.pi) by push_cast; ring,
      Real.sin_add_int_mul_two_pi, Real.sin_zero]
  simp [hs]

theorem apm_t93a06 : ∃ atlas : SmoothAtlas,
    letI := atlas.charts
    (∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ)) ∧
    (∃ form : Form Plane Torus 2,
      IsSmooth form ∧ pullback projection form = sourceForm ∧
      (∀ other : Form Plane Torus 2, IsSmooth other →
        pullback projection other = sourceForm → other = form) ∧
      torusIntegral form = 1 / 4 ∧ ¬ IsExact form) ∧
    IsSmooth primitive ∧ exteriorDerivative primitive = sourceForm ∧
    parallelogramIntegral primitive = 1 / 4 := by
  obtain ⟨atlas⟩ := t93A06_torusAtlas
  refine ⟨atlas, ?_⟩
  letI := atlas.charts
  have hfib : ∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ) :=
    t93A06_projection_fibers
  refine ⟨hfib, ?_, t93A06_primitive_calculus.1,
    t93A06_primitive_calculus.2,
    t93A06_primitive_parallelogramIntegral⟩
  obtain ⟨form, hsmooth, hpull, hunique⟩ :=
    t93A06_periodic_form_descent atlas hfib
  have hint : torusIntegral form = 1 / 4 :=
    t93A06_torusIntegral_quarter atlas form hpull
  exact ⟨form, hsmooth, hpull, hunique, hint,
    t93A06_not_exact_of_integral_quarter atlas form hsmooth hint⟩

#print axioms apm_t93a06
