import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.StandardSurfaceFiniteCover
import ConstructionTargets.LiteralPullbackCover
import ConstructionTargets.CirclePowerFiberCard

/-!
# APM t91J05 — finite covers of the genus-three orientable surface

The two remaining obligations are deliberately stated as independent library
boundaries: recognition of an arbitrary connected finite cover, and an
explicit connected finite cover of every positive degree.
-/

open Set Topology ConstructionTargets.Surfaces

noncomputable section

abbrev apm_t91J05_Surface (g : ℕ) := Surface true g

def apm_t91J05_IsFiniteCover
    (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ p : X → apm_t91J05_Surface 3,
    IsCoveringMap p ∧ Function.Surjective p ∧
    ∀ s : apm_t91J05_Surface 3, (p ⁻¹' ({s} : Set _)).Finite

/-- The finite-cover predicate is invariant under replacing its source by a
homeomorphic space. -/
lemma apm_t91J05_isFiniteCover_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hY : apm_t91J05_IsFiniteCover Y) :
    apm_t91J05_IsFiniteCover X := by
  obtain ⟨p, hpcover, hpsurj, hpfinite⟩ := hY
  refine ⟨p ∘ e, hpcover.comp_homeomorph e, hpsurj.comp e.surjective, ?_⟩
  intro s
  rw [show (p ∘ e) ⁻¹' ({s} : Set _) = e ⁻¹' (p ⁻¹' ({s} : Set _)) by
    ext x
    rfl]
  exact (hpfinite s).preimage e.injective.injOn

/-- The Euler-characteristic arithmetic behind the odd-genus formula. -/
lemma apm_t91J05_eulerCharacteristic_odd_genus (n : ℕ) :
    eulerCharacteristic true (2 * n + 1) =
      (n : ℤ) * eulerCharacteristic true 3 := by
  simp [eulerCharacteristic]
  omega

/-- The total space of a local homeomorphism onto a locally path-connected
space is locally path-connected. -/
theorem apm_t91J05_connected_finite_cover_classification_aux_locPath
    {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [LocPathConnectedSpace B] {p : X → B} (hp : IsLocalHomeomorph p) :
    LocPathConnectedSpace X := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x F hFo hxF
  have hF : F ∈ 𝓝 x := hFo.mem_nhds hxF
  obtain ⟨e, hxe, rfl⟩ := hp x
  have hV : e.source ∩ F ∈ 𝓝 x :=
    Filter.inter_mem (e.open_source.mem_nhds hxe) hF
  have hT : e.target ∩ e.symm ⁻¹' (e.source ∩ F) ∈ 𝓝 (e x) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hxe)) ?_
    apply e.continuousAt_symm (e.map_source hxe)
    rwa [e.left_inv hxe]
  set N := pathComponentIn (e.target ∩ e.symm ⁻¹' (e.source ∩ F)) (e x)
  have hN : N ∈ 𝓝 (e x) := pathComponentIn_mem_nhds hT
  have hNsub : N ⊆ e.target ∩ e.symm ⁻¹' (e.source ∩ F) := pathComponentIn_subset
  have hxN : e x ∈ N := mem_pathComponentIn_self (mem_of_mem_nhds hT)
  have himg : IsPathConnected (e.symm '' N) :=
    (isPathConnected_pathComponentIn (mem_of_mem_nhds hT)).image'
      (e.continuousOn_symm.mono fun y hy => (hNsub hy).1)
  have hximg : x ∈ e.symm '' N := ⟨e x, hxN, e.left_inv hxe⟩
  have himgF : e.symm '' N ⊆ F := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hNsub hy).2.2
  have hsub : e.symm '' N ⊆ pathComponentIn F x :=
    himg.subset_pathComponentIn hximg himgF
  refine Filter.mem_of_superset ?_ hsub
  have hpre : e.source ∩ e ⁻¹' N ∈ 𝓝 x :=
    Filter.inter_mem (e.open_source.mem_nhds hxe)
      (e.continuousAt hxe |>.preimage_mem_nhds hN)
  refine Filter.mem_of_superset hpre ?_
  rintro y ⟨hys, hyN⟩
  exact ⟨e y, hyN, e.left_inv hys⟩

/-- Over a connected base, a covering map has a locally constant, hence
constant, fibre cardinality. -/
theorem apm_t91J05_connected_finite_cover_classification_aux_sheets
    {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [PreconnectedSpace B]
    {p : X → B} (hp : IsCoveringMap p) (b₀ b : B) :
    Nat.card {e : X // p e = b} = Nat.card {e : X // p e = b₀} := by
  have hloc : IsLocallyConstant (fun b : B => Nat.card {e : X // p e = b}) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨_, U, hxU, hU, _, H, hH⟩ := hp x
    filter_upwards [hU.mem_nhds hxU] with y hy
    have key : ∀ z (hz : z ∈ U),
        Nat.card {e : X // p e = z} = Nat.card (p ⁻¹' {x}) := by
      intro z hz
      refine Nat.card_congr
        { toFun := fun e => (H ⟨e.1, by simp [mem_preimage, e.2, hz]⟩).2
          invFun := fun i => ⟨H.symm (⟨z, hz⟩, i), by
            have := hH (H.symm (⟨z, hz⟩, i))
            simp only [Homeomorph.apply_symm_apply] at this
            exact this.symm⟩
          left_inv := ?_
          right_inv := ?_ }
      · rintro ⟨e, he⟩
        apply Subtype.ext
        have h1 : (H ⟨e, by simp [mem_preimage, he, hz]⟩).1 = ⟨z, hz⟩ :=
          Subtype.ext ((hH _).trans he)
        change ((H.symm (⟨z, hz⟩, _) : p ⁻¹' U) : X) = e
        rw [← h1, Prod.mk.eta, Homeomorph.symm_apply_apply]
      · intro i
        simp
    rw [key y hy, key x hxU]
  exact hloc.apply_eq_of_preconnectedSpace b b₀

/-- LIBRARY: recognition and Euler-characteristic multiplication for a
connected finite cover of the concrete genus-three polygon surface. -/
theorem apm_t91J05_connected_finite_cover_classification
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X]
    (hX : apm_t91J05_IsFiniteCover X) :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (X ≃ₜ apm_t91J05_Surface (2 * n + 1)) := by
  obtain ⟨p, hp, hsurj, hfin⟩ := hX
  haveI : LocPathConnectedSpace Disk := (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace
  haveI : LocPathConnectedSpace (apm_t91J05_Surface 3) :=
    LocPathConnectedSpace.coinduced (fun x : Disk ↦ Quotient.mk _ x)
  haveI : LocPathConnectedSpace X :=
    apm_t91J05_connected_finite_cover_classification_aux_locPath hp.isLocalHomeomorph
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locPathConnectedSpace
  haveI : ConnectedSpace (apm_t91J05_Surface 3) := hsurj.connectedSpace hp.continuous
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set b₀ := p x₀
  set n := Nat.card {e : X // p e = b₀}
  have hn : 0 < n := by
    haveI : Finite {e : X // p e = b₀} := (hfin b₀).to_subtype
    exact Nat.card_pos_iff.mpr ⟨⟨⟨x₀, rfl⟩⟩, inferInstance⟩
  have hsheets : ∀ b, Nat.card {e : X // p e = b} = n := fun b =>
    apm_t91J05_connected_finite_cover_classification_aux_sheets hp b₀ b
  obtain ⟨h⟩ :=
    ConstructionTargets.StandardSurfaceFiniteCover.connectedFiniteCover_homeomorph_standardSurface
      3 n (by norm_num) hn X p hp hsheets
  have harith : n * (3 - 1) + 1 = 2 * n + 1 := by omega
  rw [harith] at h
  exact ⟨n, hn, ⟨h⟩⟩


/-! ## The cyclic cover (split of `apm_t91J05_cyclic_surface_cover`)

`φ` on the 12-gon rises from `0` to `1` along side `0` (the first `a`), is `1`
on side `1`, falls back to `0` along side `2` (the paired `a⁻¹`), and is `0`
on sides `3, …, 11`.  Paired sides then carry values differing by an integer,
so `exp (2πiφ)` descends to `f : Surface true 3 → Circle`, winding once along
the loop of side `0`.  The pullback of `z ↦ zⁿ` along `f` is an `n`-sheeted
cover; it is path-connected because the side-`0` loop lifts to a path from `w`
to `w·e^{2πi/n}` in the fibre over the vertex.  The module theorem then
identifies it as `Surface true (n·2 + 1)`. -/

/-- The piecewise-linear profile in the angle: `0` up to angle `0`, slope `6/π`
up to `π/6`, `1` up to `π/3`, slope `-6/π` down to `0` at `π/2`, then `0`. -/
def apm_t91J05_profile (θ : ℝ) : ℝ :=
  max 0 (min (min (θ / (Real.pi / 6)) 1) ((Real.pi / 2 - θ) / (Real.pi / 6)))

/-- The disk function: radius times the profile of the argument. -/
def apm_t91J05_phi (z : Disk) : ℝ :=
  ‖(z : ℂ)‖ * apm_t91J05_profile (Complex.arg (z : ℂ))

/-- The cyclic `n`-sheeted cover attached to a circle map `f`. -/
abbrev apm_t91J05_CyclicCover (n : ℕ) (f : apm_t91J05_Surface 3 → Circle) :=
  ConstructionTargets.LiteralPullbackCover.Pullback (fun z : Circle => z ^ n) f

/-- Leaf: `φ` is continuous.  Away from `0` and the closed negative real axis,
`arg` is continuous (`Complex.continuousAt_arg` on the slit plane).  Near a
point of the negative real axis the argument is near `±π`, where the profile
vanishes, so `φ` is `0` nearby.  At `0`, `|φ z| ≤ ‖z‖` since the profile lies in
`[0, 1]`. -/
lemma apm_t91J05_cyclic_surface_cover_aux_phi_continuous_aux_profile :
    Continuous apm_t91J05_profile := by
  unfold apm_t91J05_profile
  fun_prop

lemma apm_t91J05_cyclic_surface_cover_aux_phi_continuous_aux_bounds (t : ℝ) :
    0 ≤ apm_t91J05_profile t ∧ apm_t91J05_profile t ≤ 1 := by
  unfold apm_t91J05_profile
  constructor
  · exact le_max_left _ _
  · apply max_le (by norm_num)
    exact (min_le_left _ _).trans (min_le_right _ _)

lemma apm_t91J05_cyclic_surface_cover_aux_phi_continuous_aux_left
    (z : ℂ) (hz : z.re < 0) :
    apm_t91J05_profile z.arg = 0 := by
  have hpi : 0 < Real.pi / 6 := div_pos Real.pi_pos (by norm_num)
  unfold apm_t91J05_profile
  by_cases hi : z.im < 0
  · have ha : z.arg < 0 := Complex.arg_neg_iff.mpr hi
    rw [max_eq_left]
    exact (min_le_left _ _).trans
      ((min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg ha.le hpi.le))
  · have hi' : 0 ≤ z.im := le_of_not_gt hi
    have ha : Real.pi / 2 < z.arg := by
      rw [lt_iff_not_ge, Complex.arg_le_pi_div_two_iff]
      exact not_or_intro (not_le_of_gt hz) hi
    rw [max_eq_left]
    exact (min_le_right _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha.le) hpi.le)

theorem apm_t91J05_cyclic_surface_cover_aux_phi_continuous :
    Continuous apm_t91J05_phi := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne (z : ℂ) 0 with hz | hz
  · have hz' : z = 0 := Subtype.ext hz
    subst z
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro w hw
    have hb :=
      apm_t91J05_cyclic_surface_cover_aux_phi_continuous_aux_bounds
        (Complex.arg (w : ℂ))
    have hnonneg : 0 ≤ apm_t91J05_phi w :=
      mul_nonneg (norm_nonneg _) hb.1
    have hle : apm_t91J05_phi w ≤ ‖(w : ℂ)‖ := by
      unfold apm_t91J05_phi
      nlinarith [norm_nonneg (w : ℂ)]
    rw [show apm_t91J05_phi (0 : Disk) = 0 by simp [apm_t91J05_phi]]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact lt_of_le_of_lt hle (by
      change dist (w : ℂ) 0 < ε at hw
      simpa [dist_zero_right] using hw)
  · by_cases hr : (z : ℂ).re < 0
    · have hev : ∀ᶠ w : Disk in 𝓝 z, (w : ℂ).re < 0 :=
        (Complex.continuous_re.continuousAt.comp
          continuous_subtype_val.continuousAt).eventually (Iio_mem_nhds hr)
      refine (continuousAt_const : ContinuousAt (fun _ : Disk => (0 : ℝ)) z).congr_of_eventuallyEq ?_
      filter_upwards [hev] with w hw
      symm
      simp [apm_t91J05_phi,
        apm_t91J05_cyclic_surface_cover_aux_phi_continuous_aux_left _ hw]
    · have hr' : 0 ≤ (z : ℂ).re := le_of_not_gt hr
      have hs : (z : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff_arg]
        refine ⟨?_, hz⟩
        intro ha
        have hn := (Complex.arg_eq_pi_iff.mp ha).1
        exact (not_lt_of_ge hr') hn
      have hn : ContinuousAt (fun w : Disk => ‖(w : ℂ)‖) z :=
        continuous_norm.continuousAt.comp continuous_subtype_val.continuousAt
      have ha : ContinuousAt (fun w : Disk => Complex.arg (w : ℂ)) z :=
        (Complex.continuousAt_arg hs).comp continuous_subtype_val.continuousAt
      change ContinuousAt
        (fun w : Disk => ‖(w : ℂ)‖ * apm_t91J05_profile (Complex.arg (w : ℂ))) z
      exact hn.mul
        (apm_t91J05_cyclic_surface_cover_aux_phi_continuous_aux_profile.continuousAt.comp ha)

/-- Leaf: boundary values on the first three sides.  `edgePoint 12 k t` is
`exp (i·π(k+t)/6)`, with argument `π(k+t)/6 ∈ [0, π/2]` for `k ≤ 2`
(`Complex.arg_exp_mul_I` or `Complex.arg_cos_add_sin_mul_I`), and norm `1`. -/
lemma apm_t91J05_cyclic_surface_cover_aux_phi_edge_low_aux_arg
    (k : ℕ) (hk : k ≤ 2) (t : Set.Icc (0 : ℝ) 1) :
    Complex.arg ((edgePoint 12 k t : Disk) : ℂ) =
      Real.pi * ((k : ℝ) + t.1) / 6 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  rw [show ((edgePoint 12 k t : Disk) : ℂ) =
      Complex.exp ((Real.pi * ((k : ℝ) + t.1) / 6) * Complex.I) by
    simp only [edgePoint]
    congr 1
    push_cast
    ring]
  have hrange : Real.pi * ((k : ℝ) + t.1) / 6 ∈
      Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    constructor <;> dsimp <;> nlinarith
  have ha := Complex.arg_exp_mul_I (Real.pi * ((k : ℝ) + t.1) / 6)
  rw [(toIocMod_eq_self Real.two_pi_pos).2 hrange] at ha
  convert ha using 1 <;> push_cast <;> ring

theorem apm_t91J05_cyclic_surface_cover_aux_phi_edge_low (t : Set.Icc (0 : ℝ) 1) :
    apm_t91J05_phi (edgePoint 12 0 t) = t ∧
      apm_t91J05_phi (edgePoint 12 1 t) = 1 ∧
      apm_t91J05_phi (edgePoint 12 2 t) = 1 - t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  simp only [apm_t91J05_phi, apm_t91J05_profile]
  rw [apm_t91J05_cyclic_surface_cover_aux_phi_edge_low_aux_arg 0 (by omega),
    apm_t91J05_cyclic_surface_cover_aux_phi_edge_low_aux_arg 1 (by omega),
    apm_t91J05_cyclic_surface_cover_aux_phi_edge_low_aux_arg 2 (by omega)]
  have hnorm (k : ℕ) : ‖((edgePoint 12 k t : Disk) : ℂ)‖ = 1 := by
    simp [edgePoint, Complex.norm_exp]
  have hdiv (k : ℕ) :
      (Real.pi * ((k : ℝ) + t.1) / 6) / (Real.pi / 6) = (k : ℝ) + t.1 := by
    field_simp
  have hfall (k : ℕ) :
      (Real.pi / 2 - Real.pi * ((k : ℝ) + t.1) / 6) / (Real.pi / 6) =
        3 - ((k : ℝ) + t.1) := by
    field_simp
    ring
  simp only [hnorm, one_mul, hdiv, hfall]
  constructor
  · norm_num
    rw [min_eq_left ht1, min_eq_left (by linarith), max_eq_right ht0]
  constructor
  · norm_num
    have hi : min (1 + t.1) 1 = 1 := min_eq_right (by linarith)
    rw [hi, min_eq_left (by linarith), max_eq_right (by norm_num)]
  · norm_num
    have hi : min (2 + t.1) 1 = 1 := min_eq_right (by linarith)
    rw [hi, min_eq_right (by linarith), max_eq_right (by linarith)]
    ring

/-- Leaf: `φ` vanishes on sides `3, …, 11`.  The angle `π(k+t)/6` lies in
`[π/2, 2π]`; its argument is either that angle (when `≤ π`) or that angle
minus `2π` (in `(-π, 0]`), and the profile is `0` on both ranges. -/
theorem apm_t91J05_cyclic_surface_cover_aux_phi_edge_high
    (k : ℕ) (hk3 : 3 ≤ k) (hk : k < 12) (t : Set.Icc (0 : ℝ) 1) :
    apm_t91J05_phi (edgePoint 12 k t) = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hk12' : (k : ℝ) ≤ 11 := by exact_mod_cast (Nat.le_pred_of_lt hk)
  let θ : ℝ := Real.pi * ((k : ℝ) + t.1) / 6
  have hθlo : Real.pi / 2 ≤ θ := by
    dsimp [θ]
    nlinarith
  have hθhi : θ ≤ 2 * Real.pi := by
    dsimp [θ]
    nlinarith
  have hedge : ((edgePoint 12 k t : Disk) : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [edgePoint]
    congr 1
    dsimp [θ]
    push_cast
    ring
  have harg : Complex.arg (((edgePoint 12 k t : Disk) : ℂ)) = θ ∨
      Complex.arg (((edgePoint 12 k t : Disk) : ℂ)) = θ - 2 * Real.pi := by
    rw [hedge, Complex.arg_exp_mul_I]
    by_cases hθ : θ ≤ Real.pi
    · left
      exact (toIocMod_eq_self Real.two_pi_pos).2 ⟨by nlinarith, by nlinarith⟩
    · right
      apply (toIocMod_eq_iff Real.two_pi_pos).2
      constructor
      · constructor <;> dsimp <;> nlinarith
      · refine ⟨1, ?_⟩
        norm_num
  unfold apm_t91J05_phi apm_t91J05_profile
  rcases harg with harg | harg
  · rw [harg]
    have hfall : (Real.pi / 2 - θ) / (Real.pi / 6) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθlo) (by positivity)
    have hrise0 : 0 ≤ θ / (Real.pi / 6) := by positivity
    have hinner0 : 0 ≤ min (θ / (Real.pi / 6)) 1 :=
      le_min hrise0 (by norm_num)
    rw [min_eq_right (le_trans hfall hinner0), max_eq_left hfall]
    ring
  · rw [harg]
    have hnonpos : θ - 2 * Real.pi ≤ 0 := by linarith
    have hrise : (θ - 2 * Real.pi) / (Real.pi / 6) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hnonpos (by positivity)
    rw [max_eq_left (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hrise))]
    ring

/-- Leaf: any `ψ` with these boundary values changes by an integer across a
generating identification of `Surface true 3`.  Unfold `SurfaceRel true 3`
(`4 * 3 = 12`): `j = 0` pairs side `0` at `t` with side `2` at `1 - t` (both
`t`) and side `1` with side `3` (`1` and `0`); `j = 1, 2` pair sides `≥ 4`
(both `0`). -/
theorem apm_t91J05_cyclic_surface_cover_aux_phi_rel (ψ : Disk → ℝ)
    (h0 : ∀ t : Set.Icc (0 : ℝ) 1, ψ (edgePoint 12 0 t) = t)
    (h1 : ∀ t : Set.Icc (0 : ℝ) 1, ψ (edgePoint 12 1 t) = 1)
    (h2 : ∀ t : Set.Icc (0 : ℝ) 1, ψ (edgePoint 12 2 t) = 1 - t)
    (hhigh : ∀ k, 3 ≤ k → k < 12 → ∀ t : Set.Icc (0 : ℝ) 1,
      ψ (edgePoint 12 k t) = 0)
    (x y : Disk) (hxy : SurfaceRel true 3 x y) :
    ∃ m : ℤ, ψ y = ψ x + m := by
  simp only [SurfaceRel, if_true] at hxy
  rcases hxy with ⟨j, hj, t, hxy | hxy⟩
  · rcases hxy with ⟨rfl, rfl⟩
    interval_cases j
    · refine ⟨0, ?_⟩
      rw [h0, h2]
      simp
    · refine ⟨0, ?_⟩
      rw [hhigh 6 (by omega) (by omega), hhigh 4 (by omega) (by omega)]
      norm_num
    · refine ⟨0, ?_⟩
      rw [hhigh 10 (by omega) (by omega), hhigh 8 (by omega) (by omega)]
      norm_num
  · rcases hxy with ⟨rfl, rfl⟩
    interval_cases j
    · refine ⟨-1, ?_⟩
      rw [hhigh 3 (by omega) (by omega), h1]
      norm_num
    · refine ⟨0, ?_⟩
      rw [hhigh 7 (by omega) (by omega), hhigh 5 (by omega) (by omega)]
      norm_num
    · refine ⟨0, ?_⟩
      rw [hhigh 11 (by omega) (by omega), hhigh 9 (by omega) (by omega)]
      norm_num

/-- Leaf: a continuous `ψ` that changes by integers across the identifications
descends to a continuous circle map.  `Circle.exp (2π(ψ + m)) = Circle.exp (2πψ)`
(`Circle.exp_two_pi_mul_int` style periodicity), so the map respects
`EqvGen (SurfaceRel true 3)` by induction; continuity is
`continuous_coinduced_dom`. -/
theorem apm_t91J05_cyclic_surface_cover_aux_circleMap (ψ : Disk → ℝ)
    (hψ : Continuous ψ)
    (hrel : ∀ x y, SurfaceRel true 3 x y → ∃ m : ℤ, ψ y = ψ x + m) :
    ∃ f : C(apm_t91J05_Surface 3, Circle),
      ∀ x, f (surfaceQuotient true 3 x) = Circle.exp (2 * Real.pi * ψ x) := by
  let g : Disk → Circle := fun x ↦ Circle.exp (2 * Real.pi * ψ x)
  have hgrel : ∀ x y, SurfaceRel true 3 x y → g x = g y := by
    intro x y hxy
    obtain ⟨m, hm⟩ := hrel x y hxy
    symm
    change Circle.exp (2 * Real.pi * ψ y) = Circle.exp (2 * Real.pi * ψ x)
    rw [hm, mul_add, Circle.exp_add, Circle.exp_two_pi_mul_int, mul_one]
  have hgeqv : ∀ x y, Relation.EqvGen (SurfaceRel true 3) x y → g x = g y := by
    intro x y hxy
    induction hxy with
    | rel x y h => exact hgrel x y h
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  let f : apm_t91J05_Surface 3 → Circle := Quotient.lift g hgeqv
  have hg : Continuous g := by
    exact Circle.exp.continuous.comp (continuous_const.mul hψ)
  have hf : Continuous f := by
    apply continuous_coinduced_dom.mpr
    simpa [f, g, Function.comp_def] using hg
  refine ⟨⟨f, hf⟩, ?_⟩
  intro x
  rfl

/-- Leaf: both ends of side `0` are the vertex.  `edgePoint 12 0 1 =
edgePoint 12 1 0` (same exponential), and the chain
`(side 0, t=1) ~ (side 2, t=0)`, `edgePoint 12 2 0 = edgePoint 12 1 1`,
`(side 1, t=1) ~ (side 3, t=0)`, `edgePoint 12 3 0 = edgePoint 12 2 1`,
`(side 2, t=1) ~ (side 0, t=0)` consists of `SurfaceRel true 3` steps with
`j = 0` and equalities of disk points. -/
theorem apm_t91J05_cyclic_surface_cover_aux_vertex :
    surfaceQuotient true 3 (edgePoint 12 0 ⟨0, by norm_num, by norm_num⟩) =
      surfaceQuotient true 3 (edgePoint 12 0 ⟨1, by norm_num, by norm_num⟩) := by
  let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num, by norm_num⟩
  let t1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num, by norm_num⟩
  have corner (k : ℕ) : edgePoint 12 k t1 = edgePoint 12 (k + 1) t0 := by
    apply Subtype.ext
    simp only [edgePoint, t0, t1]
    congr 1
    push_cast
    ring
  have pair0 (t : Set.Icc (0 : ℝ) 1) :
      surfaceQuotient true 3 (edgePoint 12 0 t) =
        surfaceQuotient true 3 (edgePoint 12 2
          (ConstructionTargets.PolygonSurfacePiOne.reverseIcc t)) := by
    apply Quotient.sound
    apply Relation.EqvGen.rel
    rw [SurfaceRel, if_pos rfl]
    exact ⟨0, by omega, t, Or.inl ⟨rfl, rfl⟩⟩
  have pair1 (t : Set.Icc (0 : ℝ) 1) :
      surfaceQuotient true 3 (edgePoint 12 1 t) =
        surfaceQuotient true 3 (edgePoint 12 3
          (ConstructionTargets.PolygonSurfacePiOne.reverseIcc t)) := by
    apply Quotient.sound
    apply Relation.EqvGen.rel
    rw [SurfaceRel, if_pos rfl]
    exact ⟨0, by omega, t, Or.inr ⟨rfl, rfl⟩⟩
  change surfaceQuotient true 3 (edgePoint 12 0 t0) =
    surfaceQuotient true 3 (edgePoint 12 0 t1)
  calc
    surfaceQuotient true 3 (edgePoint 12 0 t0) =
        surfaceQuotient true 3 (edgePoint 12 2 t1) := by
          simpa [t0, t1, ConstructionTargets.PolygonSurfacePiOne.reverseIcc] using pair0 t0
    _ = surfaceQuotient true 3 (edgePoint 12 3 t0) :=
      congrArg (surfaceQuotient true 3) (corner 2)
    _ = surfaceQuotient true 3 (edgePoint 12 1 t1) := by
      simpa [t0, t1, ConstructionTargets.PolygonSurfacePiOne.reverseIcc] using (pair1 t1).symm
    _ = surfaceQuotient true 3 (edgePoint 12 2 t0) :=
      congrArg (surfaceQuotient true 3) (corner 1)
    _ = surfaceQuotient true 3 (edgePoint 12 0 t1) := by
      simpa [t0, t1, ConstructionTargets.PolygonSurfacePiOne.reverseIcc] using (pair0 t1).symm

/-- Leaf: the fibre over the vertex is joined.  The vertex `s₀` is
`surfaceQuotient true 3 (edgePoint 12 0 0)`, and `f s₀ = 1` by `hf` at `0`, so
the fibre is `{w | wⁿ = 1}`.  For such `w`, the path
`t ↦ (surfaceQuotient (edgePoint 12 0 t), w · Circle.exp (2πt/n))` lies in the
pullback (by `hf`) and joins `(s₀, w)` to `(s₀, w · ζ)`, `ζ = Circle.exp (2π/n)`,
using `hv` at the end.  Every `n`-th root of unity in `Circle` is a power of
`ζ` (write `w = Circle.exp θ`; `nθ ∈ 2πℤ`), so all of them are joined to `1`. -/
theorem apm_t91J05_cyclic_surface_cover_aux_vertexFibre_joined
    (n : ℕ) (hn : 0 < n) (f : C(apm_t91J05_Surface 3, Circle))
    (hf : ∀ t : Set.Icc (0 : ℝ) 1,
      f (surfaceQuotient true 3 (edgePoint 12 0 t)) = Circle.exp (2 * Real.pi * t))
    (hv : surfaceQuotient true 3 (edgePoint 12 0 ⟨0, by norm_num, by norm_num⟩) =
      surfaceQuotient true 3 (edgePoint 12 0 ⟨1, by norm_num, by norm_num⟩))
    (q q' : apm_t91J05_CyclicCover n f)
    (hq : q.1.1 = surfaceQuotient true 3 (edgePoint 12 0 ⟨0, by norm_num, by norm_num⟩))
    (hq' : q'.1.1 = surfaceQuotient true 3 (edgePoint 12 0 ⟨0, by norm_num, by norm_num⟩)) :
    Joined q q' := by
  sorry

/-- Leaf: if one fibre is joined, the cyclic cover is path-connected.  It is
nonempty (`Circle` has `n`-th roots, `n > 0`).  The base is path-connected,
being the image of the disk under `surfaceQuotient`.  For any point `q`, lift a
base path from `q.1.1` to `s₀` starting at `q` (`IsCoveringMap.liftPath`; the
projection is a covering by `LiteralPullbackCover.isCoveringMap` and
`Circle.isQuotientCoveringMap_npow`); its end lies over `s₀`, so `hjoin`
joins it to any other point over `s₀`. -/
theorem apm_t91J05_cyclic_surface_cover_aux_pathConnected
    (n : ℕ) (hn : 0 < n) (f : C(apm_t91J05_Surface 3, Circle))
    (s₀ : apm_t91J05_Surface 3)
    (hjoin : ∀ q q' : apm_t91J05_CyclicCover n f, q.1.1 = s₀ → q'.1.1 = s₀ → Joined q q') :
    PathConnectedSpace (apm_t91J05_CyclicCover n f) := by
  haveI : NeZero n := ⟨by omega⟩
  let p := ConstructionTargets.LiteralPullbackCover.projection
    (fun z : Circle => z ^ n) f
  have hp : IsCoveringMap p :=
    ConstructionTargets.LiteralPullbackCover.isCoveringMap
      (Circle.isQuotientCoveringMap_npow n).isCoveringMap f.continuous
  haveI : PathConnectedSpace Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : ℂ) 1).isPathConnected
        ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  haveI : PathConnectedSpace (apm_t91J05_Surface 3) :=
    (surjective_surfaceQuotient true 3).pathConnectedSpace
      (continuous_surfaceQuotient true 3)
  have hcard : Nat.card {q : apm_t91J05_CyclicCover n f // p q = s₀} = n :=
    ConstructionTargets.LiteralPullbackCover.sheet_card _ f s₀ n
      (ConstructionTargets.CirclePowerFiberCard.circlePower_fiber_card n (f s₀))
  have hne : Nat.card {q : apm_t91J05_CyclicCover n f // p q = s₀} ≠ 0 := by
    rw [hcard]
    omega
  obtain ⟨⟨q₀, hq₀⟩⟩ := (Nat.card_ne_zero.mp hne).1
  refine ⟨⟨q₀⟩, ?_⟩
  intro q q'
  let γ := PathConnectedSpace.somePath (p q) s₀
  let γ' := PathConnectedSpace.somePath (p q') s₀
  let Γ := hp.liftPath γ q (by simp [γ])
  let Γ' := hp.liftPath γ' q' (by simp [γ'])
  have hΓ0 : Γ 0 = q := hp.liftPath_zero _ _ _
  have hΓ'0 : Γ' 0 = q' := hp.liftPath_zero _ _ _
  have hΓ1 : p (Γ 1) = s₀ :=
    (congr_fun (hp.liftPath_lifts γ q (by simp [γ])) 1).trans γ.target
  have hΓ'1 : p (Γ' 1) = s₀ :=
    (congr_fun (hp.liftPath_lifts γ' q' (by simp [γ'])) 1).trans γ'.target
  have hqΓ : Joined q (Γ 1) := ⟨⟨Γ, hΓ0, rfl⟩⟩
  have hq'Γ' : Joined q' (Γ' 1) := ⟨⟨Γ', hΓ'0, rfl⟩⟩
  exact hqΓ.trans ((hjoin (Γ 1) (Γ' 1) hΓ1 hΓ'1).trans hq'Γ'.symm)

/-- The explicit connected cyclic cover of every positive degree. -/
theorem apm_t91J05_cyclic_surface_cover
    (n : ℕ) (hn : 0 < n) :
    apm_t91J05_IsFiniteCover (apm_t91J05_Surface (2 * n + 1)) := by
  haveI : NeZero n := ⟨by omega⟩
  have hlow := apm_t91J05_cyclic_surface_cover_aux_phi_edge_low
  obtain ⟨f, hf⟩ := apm_t91J05_cyclic_surface_cover_aux_circleMap apm_t91J05_phi
    apm_t91J05_cyclic_surface_cover_aux_phi_continuous
    (apm_t91J05_cyclic_surface_cover_aux_phi_rel apm_t91J05_phi
      (fun t => (hlow t).1) (fun t => (hlow t).2.1) (fun t => (hlow t).2.2)
      apm_t91J05_cyclic_surface_cover_aux_phi_edge_high)
  have hf0 : ∀ t : Set.Icc (0 : ℝ) 1,
      f (surfaceQuotient true 3 (edgePoint 12 0 t)) = Circle.exp (2 * Real.pi * t) := by
    intro t
    rw [hf, (hlow t).1]
  haveI := apm_t91J05_cyclic_surface_cover_aux_pathConnected n hn f _
    (apm_t91J05_cyclic_surface_cover_aux_vertexFibre_joined n hn f hf0
      apm_t91J05_cyclic_surface_cover_aux_vertex)
  let p := ConstructionTargets.LiteralPullbackCover.projection
    (fun z : Circle => z ^ n) f
  have hp : IsCoveringMap p :=
    ConstructionTargets.LiteralPullbackCover.isCoveringMap
      (Circle.isQuotientCoveringMap_npow n).isCoveringMap f.continuous
  have hsheets : ∀ b, Nat.card {e : apm_t91J05_CyclicCover n f // p e = b} = n :=
    fun b => ConstructionTargets.LiteralPullbackCover.sheet_card _ f b n
      (ConstructionTargets.CirclePowerFiberCard.circlePower_fiber_card n (f b))
  obtain ⟨h⟩ :=
    ConstructionTargets.StandardSurfaceFiniteCover.connectedFiniteCover_homeomorph_standardSurface
      3 n (by norm_num) hn _ p hp hsheets
  have harith : n * (3 - 1) + 1 = 2 * n + 1 := by omega
  rw [harith] at h
  refine apm_t91J05_isFiniteCover_of_homeomorph h.symm ⟨p, hp, fun b => ?_, fun b => ?_⟩
  · have hne : Nat.card {e : apm_t91J05_CyclicCover n f // p e = b} ≠ 0 := by
      rw [hsheets b]; omega
    obtain ⟨⟨e, he⟩⟩ := (Nat.card_ne_zero.mp hne).1
    exact ⟨e, he⟩
  · have hne : Nat.card {e : apm_t91J05_CyclicCover n f // p e = b} ≠ 0 := by
      rw [hsheets b]; omega
    exact Set.finite_coe_iff.mp (Nat.card_ne_zero.mp hne).2

theorem apm_t91j05
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] :
    apm_t91J05_IsFiniteCover X ↔
      ∃ n : ℕ, 0 < n ∧
        Nonempty (X ≃ₜ apm_t91J05_Surface (2 * n + 1)) := by
  constructor
  · exact apm_t91J05_connected_finite_cover_classification X
  · rintro ⟨n, hn, ⟨e⟩⟩
    exact apm_t91J05_isFiniteCover_of_homeomorph e
      (apm_t91J05_cyclic_surface_cover n hn)

#print axioms apm_t91j05
