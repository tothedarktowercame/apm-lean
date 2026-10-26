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
theorem apm_t91J05_cyclic_surface_cover_aux_phi_continuous :
    Continuous apm_t91J05_phi := by
  sorry

/-- Leaf: boundary values on the first three sides.  `edgePoint 12 k t` is
`exp (i·π(k+t)/6)`, with argument `π(k+t)/6 ∈ [0, π/2]` for `k ≤ 2`
(`Complex.arg_exp_mul_I` or `Complex.arg_cos_add_sin_mul_I`), and norm `1`. -/
theorem apm_t91J05_cyclic_surface_cover_aux_phi_edge_low (t : Set.Icc (0 : ℝ) 1) :
    apm_t91J05_phi (edgePoint 12 0 t) = t ∧
      apm_t91J05_phi (edgePoint 12 1 t) = 1 ∧
      apm_t91J05_phi (edgePoint 12 2 t) = 1 - t := by
  sorry

/-- Leaf: `φ` vanishes on sides `3, …, 11`.  The angle `π(k+t)/6` lies in
`[π/2, 2π]`; its argument is either that angle (when `≤ π`) or that angle
minus `2π` (in `(-π, 0]`), and the profile is `0` on both ranges. -/
theorem apm_t91J05_cyclic_surface_cover_aux_phi_edge_high
    (k : ℕ) (hk3 : 3 ≤ k) (hk : k < 12) (t : Set.Icc (0 : ℝ) 1) :
    apm_t91J05_phi (edgePoint 12 k t) = 0 := by
  sorry

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
  sorry

/-- Leaf: a continuous `ψ` that changes by integers across the identifications
descends to a continuous circle map.  `Circle.exp (2π(ψ + m)) = Circle.exp (2πψ)`
(`Circle.exp_two_pi_mul_int` style periodicity), so the map respects
`EqvGen (SurfaceRel true 3)` by induction; continuity is
`continuous_coinduced_dom`. -/
-- BEGIN SEAT AREA
theorem apm_t91J05_cyclic_surface_cover_aux_circleMap (ψ : Disk → ℝ)
    (hψ : Continuous ψ)
    (hrel : ∀ x y, SurfaceRel true 3 x y → ∃ m : ℤ, ψ y = ψ x + m) :
    ∃ f : C(apm_t91J05_Surface 3, Circle),
      ∀ x, f (surfaceQuotient true 3 x) = Circle.exp (2 * Real.pi * ψ x) := by
  sorry
-- END SEAT AREA

/-- Leaf: both ends of side `0` are the vertex.  `edgePoint 12 0 1 =
edgePoint 12 1 0` (same exponential), and the chain
`(side 0, t=1) ~ (side 2, t=0)`, `edgePoint 12 2 0 = edgePoint 12 1 1`,
`(side 1, t=1) ~ (side 3, t=0)`, `edgePoint 12 3 0 = edgePoint 12 2 1`,
`(side 2, t=1) ~ (side 0, t=0)` consists of `SurfaceRel true 3` steps with
`j = 0` and equalities of disk points. -/
theorem apm_t91J05_cyclic_surface_cover_aux_vertex :
    surfaceQuotient true 3 (edgePoint 12 0 ⟨0, by norm_num, by norm_num⟩) =
      surfaceQuotient true 3 (edgePoint 12 0 ⟨1, by norm_num, by norm_num⟩) := by
  sorry

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
  sorry

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
