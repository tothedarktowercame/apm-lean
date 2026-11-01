import Mathlib
import ConstructionTargets.ComplexProjectiveChartTargets
import ConstructionTargets.CP2RationalHomology
import ConstructionTargets.SphereHomology

open scoped LinearAlgebra.Projectivization
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t98a04_C2 := EuclideanSpace ℂ (Fin 2)
abbrev apm_t98a04_R3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t98a04_R2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t98a04_S3 := Metric.sphere (0 : apm_t98a04_C2) 1
abbrev apm_t98a04_CP1 := Projectivization ℂ apm_t98a04_C2

local instance : Fact (Module.finrank ℝ apm_t98a04_C2 = 3 + 1) := ⟨by
  rw [← Module.finrank_mul_finrank ℝ ℂ apm_t98a04_C2,
    Complex.finrank_real_complex]
  simp [apm_t98a04_C2]⟩

noncomputable instance : TopologicalSpace apm_t98a04_CP1 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance

lemma apm_t98a04_sphere_ne_zero (z : apm_t98a04_S3) : z.1 ≠ 0 := by
  intro hz
  have hdist : dist (z.1 : apm_t98a04_C2) 0 = 1 := by
    simpa [dist_comm] using z.2
  simp [hz] at hdist

def apm_t98a04_hopf (z : apm_t98a04_S3) : apm_t98a04_CP1 :=
  Projectivization.mk ℂ z.1 (apm_t98a04_sphere_ne_zero z)

def apm_t98a04_e0 : {z : apm_t98a04_C2 // z ≠ 0} :=
  ⟨WithLp.toLp 2 ![(1 : ℂ), 0], by
    intro h
    have h0 := congrArg (fun z : apm_t98a04_C2 ↦ z 0) h
    simpa using h0⟩

def apm_t98a04_p10 : apm_t98a04_CP1 :=
  Projectivization.mk' ℂ apm_t98a04_e0

def apm_t98a04_fiber (p : apm_t98a04_CP1) : Set apm_t98a04_S3 :=
  {z | apm_t98a04_hopf z = p}

def apm_t98a04_circleOrbit (z : apm_t98a04_S3) : Set apm_t98a04_S3 :=
  {w | ∃ u : Circle, w.1 = (u : ℂ) • z.1}

def apm_t98a04_IsSubmersion
    (f : apm_t98a04_S3 → apm_t98a04_CP1) : Prop :=
  ∃ targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1,
    let _ := targetCharts
    IsManifold (𝓘(ℝ, apm_t98a04_R2)) (⊤ : ℕ∞) apm_t98a04_CP1 ∧
    ContMDiff (𝓘(ℝ, apm_t98a04_R3)) (𝓘(ℝ, apm_t98a04_R2))
      (⊤ : ℕ∞) f ∧
    ∀ z : apm_t98a04_S3,
      Function.Surjective
        (mfderiv (𝓘(ℝ, apm_t98a04_R3)) (𝓘(ℝ, apm_t98a04_R2)) f z)

def apm_t98a04_affineCoordinate
    (i : Fin 2) (p : apm_t98a04_CP1) : apm_t98a04_R2 :=
  let w := if i = 0 then
      Projectivization.rep p 1 / Projectivization.rep p 0
    else Projectivization.rep p 0 / Projectivization.rep p 1
  WithLp.toLp 2 ![w.re, w.im]

def apm_t98a04_affineVector
    (i : Fin 2) (x : apm_t98a04_R2) : apm_t98a04_C2 :=
  let w : ℂ := x 0 + x 1 * Complex.I
  if i = 0 then WithLp.toLp 2 ![(1 : ℂ), w]
  else WithLp.toLp 2 ![w, (1 : ℂ)]

lemma apm_t98a04_affineVector_ne_zero
    (i : Fin 2) (x : apm_t98a04_R2) :
    apm_t98a04_affineVector i x ≠ 0 := by
  intro h
  by_cases hi : i = 0
  · have h0 := congrArg (fun z : apm_t98a04_C2 ↦ z 0) h
    simp [apm_t98a04_affineVector, hi] at h0
  · have h1 := congrArg (fun z : apm_t98a04_C2 ↦ z 1) h
    simp [apm_t98a04_affineVector, hi] at h1

def apm_t98a04_affineInverse
    (i : Fin 2) (x : apm_t98a04_R2) : apm_t98a04_CP1 :=
  Projectivization.mk ℂ (apm_t98a04_affineVector i x)
    (apm_t98a04_affineVector_ne_zero i x)

/-- The two standard ratio charts, on the already-fixed coinduced topology.
This records their exact coordinate and inverse maps, so later smoothness
leaves cannot choose an unrelated atlas. -/
def apm_t98a04_IsStandardAffineAtlas
    (targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1) : Prop :=
  let _ := targetCharts
  ∃ e : Fin 2 → OpenPartialHomeomorph apm_t98a04_CP1 apm_t98a04_R2,
    atlas apm_t98a04_R2 apm_t98a04_CP1 = Set.range e ∧
    ∀ i,
      (e i).source = {p : apm_t98a04_CP1 | Projectivization.rep p i ≠ 0} ∧
      (e i).target = Set.univ ∧
      (∀ p ∈ (e i).source, e i p = apm_t98a04_affineCoordinate i p) ∧
      (∀ x, (e i).symm x = apm_t98a04_affineInverse i x)

lemma apm_t98a04_continuous_hopf : Continuous apm_t98a04_hopf := by
  change Continuous
    (Projectivization.mk' ℂ ∘
      fun z : apm_t98a04_S3 ↦
        (⟨z.1, apm_t98a04_sphere_ne_zero z⟩ :
          {w : apm_t98a04_C2 // w ≠ 0}))
  exact continuous_coinduced_rng.comp
    (continuous_subtype_val.subtype_mk fun z ↦ apm_t98a04_sphere_ne_zero z)

/-- Build the two ratio charts from `affineSource_isOpen`, quotient descent,
and the explicit inverse `[1:w]`/`[w:1]`.  At `[1:0]`, chart zero is
`w = z₁/z₀` and sends the point to `0`. -/
theorem apm_t98a04_submersion_aux_affine_atlas :
    ∃ targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1,
      apm_t98a04_IsStandardAffineAtlas targetCharts := by
  sorry

/-- Prove smooth compatibility of the two affine charts.  On their overlap
the transition is complex inversion; use `contDiffOn_inv₀`, real/complex
coordinate smoothness, and `IsManifold.of_compatible`. -/
lemma apm_t98a04_submersion_aux_affine_isManifold_aux_transition01
    (targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1)
    (e : Fin 2 → OpenPartialHomeomorph apm_t98a04_CP1 apm_t98a04_R2)
    (he : let _ := targetCharts
      ∀ i,
        (e i).source = {p : apm_t98a04_CP1 |
          Projectivization.rep p i ≠ 0} ∧
        (e i).target = Set.univ ∧
        (∀ p ∈ (e i).source,
          e i p = apm_t98a04_affineCoordinate i p) ∧
        (∀ x, (e i).symm x = apm_t98a04_affineInverse i x)) :
    let _ := targetCharts
    ContDiffOn ℝ (⊤ : ℕ∞) ((e 0).symm ≫ₕ e 1)
      ((e 0).symm ≫ₕ e 1).source := by
  sorry

lemma apm_t98a04_submersion_aux_affine_isManifold_aux_transition10
    (targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1)
    (e : Fin 2 → OpenPartialHomeomorph apm_t98a04_CP1 apm_t98a04_R2)
    (he : let _ := targetCharts
      ∀ i,
        (e i).source = {p : apm_t98a04_CP1 |
          Projectivization.rep p i ≠ 0} ∧
        (e i).target = Set.univ ∧
        (∀ p ∈ (e i).source,
          e i p = apm_t98a04_affineCoordinate i p) ∧
        (∀ x, (e i).symm x = apm_t98a04_affineInverse i x)) :
    let _ := targetCharts
    ContDiffOn ℝ (⊤ : ℕ∞) ((e 1).symm ≫ₕ e 0)
      ((e 1).symm ≫ₕ e 0).source := by
  sorry

theorem apm_t98a04_submersion_aux_affine_isManifold
    (targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1)
    (haffine : apm_t98a04_IsStandardAffineAtlas targetCharts) :
    let _ := targetCharts
    IsManifold (𝓘(ℝ, apm_t98a04_R2)) (⊤ : ℕ∞) apm_t98a04_CP1 := by
  let _ := targetCharts
  obtain ⟨e, he_atlas, he⟩ := haffine
  dsimp only
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ apm_t98a04_R2)
    (⊤ : ℕ∞) apm_t98a04_CP1
  intro c d hc hd
  rw [he_atlas] at hc hd
  obtain ⟨i, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := hd
  fin_cases i <;> fin_cases j
  all_goals simp only [mfld_simps]
  case «0».«0» =>
    refine contDiffOn_id.congr ?_
    intro x hx
    exact (e 0).right_inv hx.1
  case «1».«1» =>
    refine contDiffOn_id.congr ?_
    intro x hx
    exact (e 1).right_inv hx.1
  case «0».«1» =>
    exact apm_t98a04_submersion_aux_affine_isManifold_aux_transition01
      targetCharts e he
  case «1».«0» =>
    exact apm_t98a04_submersion_aux_affine_isManifold_aux_transition10
      targetCharts e he

/-- In either ratio chart the Hopf map is the corresponding homogeneous
coordinate quotient.  Combine the standard sphere charts with smooth
division on the nonzero-coordinate patch.  At `(1,0)` the local map is
`z ↦ z₁/z₀`. -/
-- BEGIN SEAT AREA
theorem apm_t98a04_submersion_aux_hopf_smooth
    (targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1)
    (haffine : apm_t98a04_IsStandardAffineAtlas targetCharts)
    (hmanifold : let _ := targetCharts
      IsManifold (𝓘(ℝ, apm_t98a04_R2)) (⊤ : ℕ∞) apm_t98a04_CP1) :
    let _ := targetCharts
    ContMDiff (𝓘(ℝ, apm_t98a04_R3)) (𝓘(ℝ, apm_t98a04_R2))
      (⊤ : ℕ∞) apm_t98a04_hopf := by
  sorry
-- END SEAT AREA

/-- Differentiate the ratio formula and use
`range_mfderiv_coe_sphere`/`mfderiv_coe_sphere_injective` to identify the
source tangent space with the real orthogonal complement of `z`.  Varying
the unused complex coordinate gives both target directions; at `(1,0)` the
vectors `(0,1)` and `(0,I)` map to the standard real basis. -/
theorem apm_t98a04_submersion_aux_mfderiv_surjective
    (targetCharts : ChartedSpace apm_t98a04_R2 apm_t98a04_CP1)
    (haffine : apm_t98a04_IsStandardAffineAtlas targetCharts)
    (hmanifold : let _ := targetCharts
      IsManifold (𝓘(ℝ, apm_t98a04_R2)) (⊤ : ℕ∞) apm_t98a04_CP1)
    (hsmooth : let _ := targetCharts
      ContMDiff (𝓘(ℝ, apm_t98a04_R3)) (𝓘(ℝ, apm_t98a04_R2))
        (⊤ : ℕ∞) apm_t98a04_hopf) :
    let _ := targetCharts
    ∀ z : apm_t98a04_S3,
      Function.Surjective
        (mfderiv (𝓘(ℝ, apm_t98a04_R3)) (𝓘(ℝ, apm_t98a04_R2))
          apm_t98a04_hopf z) := by
  sorry

/-- Assemble the affine atlas, its compatibility, smoothness, and the
pointwise derivative calculation. -/
theorem apm_t98a04_submersion_bridge :
    apm_t98a04_IsSubmersion apm_t98a04_hopf := by
  obtain ⟨targetCharts, haffine⟩ :=
    apm_t98a04_submersion_aux_affine_atlas
  let _ := targetCharts
  have hmanifold :=
    apm_t98a04_submersion_aux_affine_isManifold targetCharts haffine
  have hsmooth :=
    apm_t98a04_submersion_aux_hopf_smooth targetCharts haffine hmanifold
  have hsurj :=
    apm_t98a04_submersion_aux_mfderiv_surjective targetCharts haffine
      hmanifold hsmooth
  exact ⟨targetCharts, hmanifold, hsmooth, hsurj⟩

/-- Two unit representatives of one projective point differ by a unit scalar. -/
theorem apm_t98a04_fiber_eq_circleOrbit
    (p : apm_t98a04_CP1) (z : apm_t98a04_S3)
    (hz : z ∈ apm_t98a04_fiber p) :
    apm_t98a04_fiber p = apm_t98a04_circleOrbit z := by
  ext w
  constructor
  · intro hw
    have hp : apm_t98a04_hopf w = apm_t98a04_hopf z := by
      exact hw.trans hz.symm
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℂ w.1 z.1
        (apm_t98a04_sphere_ne_zero w) (apm_t98a04_sphere_ne_zero z)).mp hp
    have hw_norm : ‖(w.1 : apm_t98a04_C2)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using w.2
    have hz_norm : ‖(z.1 : apm_t98a04_C2)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using z.2
    have ha_norm : ‖a‖ = 1 := by
      rw [← ha, norm_smul, hz_norm, mul_one] at hw_norm
      exact hw_norm
    let u : Circle := ⟨a, by
      exact mem_sphere_zero_iff_norm.mpr ha_norm⟩
    exact ⟨u, ha.symm⟩
  · rintro ⟨u, hu⟩
    have hp : apm_t98a04_hopf w = apm_t98a04_hopf z := by
      apply (Projectivization.mk_eq_mk_iff' ℂ w.1 z.1
        (apm_t98a04_sphere_ne_zero w) (apm_t98a04_sphere_ne_zero z)).mpr
      exact ⟨(u : ℂ), hu.symm⟩
    exact hp.trans hz

/-- The fiber over [1:0] is exactly the coordinate circle. -/
theorem apm_t98a04_fiber_p10 :
    apm_t98a04_fiber apm_t98a04_p10 = {z | z.1 1 = 0} := by
  ext z
  change apm_t98a04_hopf z = apm_t98a04_p10 ↔ z.1 1 = 0
  rw [apm_t98a04_hopf, apm_t98a04_p10,
    Projectivization.mk'_eq_mk]
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have h := congrFun (congrArg WithLp.ofLp ha) 1
    simpa [apm_t98a04_e0] using h.symm
  · intro hz
    refine ⟨z.1 0, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [apm_t98a04_e0]
    · simpa [apm_t98a04_e0] using hz.symm

/-- Every Hopf fiber is homeomorphic to the unit circle. -/
private noncomputable def apm_t98a04_fiber_homeomorph_circle_aux_z
    (p : apm_t98a04_CP1) : apm_t98a04_C2 :=
  (‖Projectivization.rep p‖ : ℂ)⁻¹ • Projectivization.rep p

private lemma apm_t98a04_fiber_homeomorph_circle_aux_norm
    (p : apm_t98a04_CP1) :
    ‖apm_t98a04_fiber_homeomorph_circle_aux_z p‖ = 1 := by
  simp [apm_t98a04_fiber_homeomorph_circle_aux_z, norm_smul,
    Projectivization.rep_nonzero]

private noncomputable def apm_t98a04_fiber_homeomorph_circle_aux_point
    (p : apm_t98a04_CP1) : apm_t98a04_S3 :=
  ⟨apm_t98a04_fiber_homeomorph_circle_aux_z p, by
    rw [Metric.mem_sphere, dist_zero_right,
      apm_t98a04_fiber_homeomorph_circle_aux_norm]⟩

private lemma apm_t98a04_fiber_homeomorph_circle_aux_hopf
    (p : apm_t98a04_CP1) :
    apm_t98a04_hopf (apm_t98a04_fiber_homeomorph_circle_aux_point p) = p := by
  unfold apm_t98a04_hopf apm_t98a04_fiber_homeomorph_circle_aux_point
  change Projectivization.mk ℂ _ _ = p
  calc
    _ = Projectivization.mk ℂ (Projectivization.rep p)
        (Projectivization.rep_nonzero p) :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
        ⟨(‖Projectivization.rep p‖ : ℂ)⁻¹, rfl⟩
    _ = p := Projectivization.mk_rep p

private noncomputable def apm_t98a04_fiber_homeomorph_circle_aux_map
    (p : apm_t98a04_CP1) (u : Circle) : apm_t98a04_fiber p :=
  ⟨⟨(u : ℂ) • apm_t98a04_fiber_homeomorph_circle_aux_z p, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul,
        apm_t98a04_fiber_homeomorph_circle_aux_norm]
      simp⟩, by
    change Projectivization.mk ℂ
      ((u : ℂ) • apm_t98a04_fiber_homeomorph_circle_aux_z p) _ = p
    calc
      _ = Projectivization.mk ℂ
          (apm_t98a04_fiber_homeomorph_circle_aux_z p) _ :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨(u : ℂ), rfl⟩
      _ = p := by
        simpa [apm_t98a04_hopf,
          apm_t98a04_fiber_homeomorph_circle_aux_point] using
          apm_t98a04_fiber_homeomorph_circle_aux_hopf p⟩

private lemma apm_t98a04_fiber_homeomorph_circle_aux_continuous
    (p : apm_t98a04_CP1) :
    Continuous (apm_t98a04_fiber_homeomorph_circle_aux_map p) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_subtype_val.smul continuous_const

private lemma apm_t98a04_fiber_homeomorph_circle_aux_bijective
    (p : apm_t98a04_CP1) :
    Function.Bijective (apm_t98a04_fiber_homeomorph_circle_aux_map p) := by
  let z := apm_t98a04_fiber_homeomorph_circle_aux_z p
  have hz : ‖z‖ = 1 := apm_t98a04_fiber_homeomorph_circle_aux_norm p
  constructor
  · intro u v huv
    have hvec : (u : ℂ) • z = (v : ℂ) • z := congrArg (fun x => x.1.1) huv
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
    apply Subtype.ext
    have hzero : ((u : ℂ) - (v : ℂ)) • z = 0 := by
      rw [sub_smul, sub_eq_zero, hvec]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hz0)
  · rintro ⟨w, hw⟩
    have hproj : Projectivization.mk ℂ w.1 (apm_t98a04_sphere_ne_zero w) = p := hw
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
    have hpz : Projectivization.mk ℂ z hz0 = p := by
      simpa [z] using apm_t98a04_fiber_homeomorph_circle_aux_hopf p
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ w.1 z
      (apm_t98a04_sphere_ne_zero w) hz0).1 (hproj.trans hpz.symm)
    have hw_norm : ‖(w.1 : apm_t98a04_C2)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using w.2
    have ha_norm : ‖a‖ = 1 := by
      calc
        ‖a‖ = ‖a‖ * ‖z‖ := by rw [hz, mul_one]
        _ = ‖a • z‖ := (norm_smul a z).symm
        _ = ‖w.1‖ := by rw [ha]
        _ = 1 := hw_norm
    let u : Circle := ⟨a, by
      simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using ha_norm⟩
    refine ⟨u, Subtype.ext (Subtype.ext ?_)⟩
    change a • z = w.1
    exact ha

theorem apm_t98a04_fiber_homeomorph_circle
    (p : apm_t98a04_CP1) :
    Nonempty (apm_t98a04_fiber p ≃ₜ Circle) := by
  let f := apm_t98a04_fiber_homeomorph_circle_aux_map p
  have hf := apm_t98a04_fiber_homeomorph_circle_aux_bijective p
  let e : Circle ≃ apm_t98a04_fiber p := Equiv.ofBijective f hf
  have hec : Continuous e := by
    simpa [e, f] using apm_t98a04_fiber_homeomorph_circle_aux_continuous p
  have heh : IsHomeomorph e :=
    (isHomeomorph_iff_continuous_bijective).2 ⟨hec, e.bijective⟩
  exact ⟨(e.toHomeomorphOfContinuousClosed hec heh.isClosedMap).symm⟩

abbrev apm_t98a04_HQ (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

/-- Identify this file's `WithLp`-carrier quotient with the literal `CP 1`
model in `CP2RationalHomology`, then with its explicit two-sphere.  Transport
`CoefficientSphereEndpoints.rationalS2H2` across the resulting homotopy
equivalence to show that rational `H₂` is not zero. -/
noncomputable def apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv :
    apm_t98a04_C2 ≃L[ℂ] (Fin 2 → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 ↦ ℂ)

noncomputable def apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_forward :
    apm_t98a04_CP1 → RP3Homology.cpU_homology_aux_CP1 :=
  Projectivization.map
    (apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.toLinearMap :
      apm_t98a04_C2 →ₗ[ℂ] (Fin 2 → ℂ))
    apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.injective

noncomputable def apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_backward :
    RP3Homology.cpU_homology_aux_CP1 → apm_t98a04_CP1 :=
  Projectivization.map
    (apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.symm.toLinearMap :
      (Fin 2 → ℂ) →ₗ[ℂ] apm_t98a04_C2)
    apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.symm.injective

noncomputable def apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_equiv :
    apm_t98a04_CP1 ≃
      RP3Homology.cpU_homology_aux_CP1 where
  toFun := apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_forward
  invFun := apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_backward
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_forward,
        apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_backward, Projectivization.map_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      exact ⟨1, by simp⟩
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      simp only [apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_forward,
        apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_backward, Projectivization.map_mk]
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
      exact ⟨1, by simp⟩

lemma apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_continuous :
    Continuous apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_equiv := by
  apply continuous_coinduced_dom.mpr
  change Continuous
    (ConstructionTargets.ProjectiveSpaceTopology.quotientMap ℂ 1 ∘
      fun v : {v : apm_t98a04_C2 // v ≠ 0} ↦
      ⟨apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv v.1, by
        exact apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.injective.ne v.2⟩)
  exact continuous_coinduced_rng.comp
    ((apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.continuous.comp
      continuous_subtype_val).subtype_mk _)

lemma apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_continuous_symm :
    Continuous apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_equiv.symm := by
  apply continuous_coinduced_dom.mpr
  change Continuous
    (Projectivization.mk' ℂ ∘
      fun v : {v : Fin 2 → ℂ // v ≠ 0} ↦
      ⟨apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.symm v.1, by
        exact apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.symm.injective.ne v.2⟩)
  exact continuous_coinduced_rng.comp
    ((apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_linearEquiv.symm.continuous.comp
      continuous_subtype_val).subtype_mk _)

noncomputable def apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_homeomorph :
    apm_t98a04_CP1 ≃ₜ RP3Homology.cpU_homology_aux_CP1 :=
  { apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_equiv with
    continuous_toFun :=
      apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_continuous
    continuous_invFun :=
      apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_continuous_symm }

theorem apm_t98a04_no_section_aux_cp1_h2_nonzero :
    ¬ CategoryTheory.Limits.IsZero
      (apm_t98a04_HQ 2 apm_t98a04_CP1) := by
  intro hzero
  obtain ⟨eS⟩ := RP3Homology.cpU_homology_aux_CP1_hequiv_S2
  let e : ContinuousMap.HomotopyEquiv apm_t98a04_CP1
      RP3Homology.cpU_homology_aux_S2 :=
    apm_t98a04_no_section_aux_cp1_h2_nonzero_aux_homeomorph.toHomotopyEquiv.trans eS
  let hiso : apm_t98a04_HQ 2 apm_t98a04_CP1 ≅ ModuleCat.of ℚ ℚ :=
    ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
      ℚ e 2 ≪≫
    ConstructionTargets.CoefficientFirstReflection.topIso ℚ 1
  have hQzero : CategoryTheory.Limits.IsZero (ModuleCat.of ℚ ℚ) :=
    hzero.of_iso hiso.symm
  have hsub : Subsingleton ℚ :=
    ModuleCat.isZero_iff_subsingleton.mp hQzero
  exact zero_ne_one (hsub.elim 0 1)

/-- Regard `ℂ²` as `ℝ⁴` by the canonical real-linear isometry, restrict it to
the unit spheres, and transport `SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top`
for `H₂(S³;ℚ)` (or its coefficient-change counterpart). -/
noncomputable def apm_t98a04_no_section_aux_s3_h2_zero_aux_isometry :
    apm_t98a04_C2 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) := by
  have hdim : Module.finrank ℝ apm_t98a04_C2 = 4 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ apm_t98a04_C2,
      Complex.finrank_real_complex]
    simp [apm_t98a04_C2]
  exact ((stdOrthonormalBasis ℝ apm_t98a04_C2).reindex (finCongr hdim)).repr

noncomputable def apm_t98a04_no_section_aux_s3_h2_zero_aux_homeomorph :
    apm_t98a04_S3 ≃ₜ T02A06.euclideanUnitSphere 4 where
  toFun z := ⟨apm_t98a04_no_section_aux_s3_h2_zero_aux_isometry z.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using z.2⟩
  invFun z := ⟨apm_t98a04_no_section_aux_s3_h2_zero_aux_isometry.symm z.1, by
    simpa [Metric.mem_sphere, dist_zero_right] using z.2⟩
  left_inv z := Subtype.ext (by simp)
  right_inv z := Subtype.ext (by simp)
  continuous_toFun :=
    Continuous.subtype_mk
      (apm_t98a04_no_section_aux_s3_h2_zero_aux_isometry.continuous.comp
        continuous_subtype_val) (fun z ↦ by
          simpa [Metric.mem_sphere, dist_zero_right] using z.2)
  continuous_invFun :=
    Continuous.subtype_mk
      (apm_t98a04_no_section_aux_s3_h2_zero_aux_isometry.symm.continuous.comp
        continuous_subtype_val) (fun z ↦ by
          simpa [Metric.mem_sphere, dist_zero_right] using z.2)

theorem apm_t98a04_no_section_aux_s3_h2_zero :
    CategoryTheory.Limits.IsZero
      (apm_t98a04_HQ 2 apm_t98a04_S3) := by
  have hreal := RP3Homology.sphere_isZero 2 (by omega) (by omega)
  exact hreal.of_iso
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 2).obj
      (ModuleCat.of ℚ ℚ)).mapIso
        (TopCat.isoOfHomeo apm_t98a04_no_section_aux_s3_h2_zero_aux_homeomorph))

/-- Apply rational singular homology to `hopf ∘ i = id`.  Functoriality makes
the identity of `H₂(CP¹)` factor through the zero object `H₂(S³)`, contradicting
the supplied nonvanishing.  Tools: `Functor.map_comp`, `Functor.map_id`, and
`IsZero.eq_of_src`/`IsZero.iff_id_eq_zero`. -/
theorem apm_t98a04_no_section_aux_homology_factor
    (hbase : ¬ CategoryTheory.Limits.IsZero
      (apm_t98a04_HQ 2 apm_t98a04_CP1))
    (htotal : CategoryTheory.Limits.IsZero
      (apm_t98a04_HQ 2 apm_t98a04_S3)) :
    ¬∃ i : apm_t98a04_CP1 → apm_t98a04_S3,
      Continuous i ∧ ∀ p, apm_t98a04_hopf (i p) = p := by
  open CategoryTheory in
    rintro ⟨i, hi, hsection⟩
    apply hbase
    rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 2).obj
      (ModuleCat.of ℚ ℚ)
    let fi : TopCat.of apm_t98a04_CP1 ⟶ TopCat.of apm_t98a04_S3 :=
      TopCat.ofHom ⟨i, hi⟩
    let fh : TopCat.of apm_t98a04_S3 ⟶ TopCat.of apm_t98a04_CP1 :=
      TopCat.ofHom ⟨apm_t98a04_hopf, apm_t98a04_continuous_hopf⟩
    have hcomp : fi ≫ fh = 𝟙 (TopCat.of apm_t98a04_CP1) := by
      ext p
      exact hsection p
    calc
      𝟙 (apm_t98a04_HQ 2 apm_t98a04_CP1) = F.map (𝟙 _) :=
        (F.map_id _).symm
      _ = F.map (fi ≫ fh) := by rw [hcomp]
      _ = F.map fi ≫ F.map fh := F.map_comp fi fh
      _ = F.map fi ≫ 0 := by rw [htotal.eq_of_src (F.map fh)]
      _ = 0 := by simp

/-- Assemble the rational-homology obstruction to a section. -/
theorem apm_t98a04_no_section_bridge :
    ¬∃ i : apm_t98a04_CP1 → apm_t98a04_S3,
      Continuous i ∧ ∀ p, apm_t98a04_hopf (i p) = p := by
  exact apm_t98a04_no_section_aux_homology_factor
    apm_t98a04_no_section_aux_cp1_h2_nonzero
    apm_t98a04_no_section_aux_s3_h2_zero

#check RP3Homology.cpU_homology_aux_CP1_hequiv_S2
#check ConstructionTargets.CoefficientSphereEndpoints.rationalS2H2
#check ConstructionTargets.SphereHomology.sphereModuleHomology_isZero_of_ne_zero_top
#check range_mfderiv_coe_sphere
#check mfderiv_coe_sphere_injective

theorem apm_t98a04 :
    Continuous apm_t98a04_hopf ∧
    apm_t98a04_IsSubmersion apm_t98a04_hopf ∧
    apm_t98a04_fiber apm_t98a04_p10 = {z | z.1 1 = 0} ∧
    (∀ p : apm_t98a04_CP1,
      Nonempty (apm_t98a04_fiber p ≃ₜ Circle) ∧
      ∀ z ∈ apm_t98a04_fiber p,
        apm_t98a04_fiber p = apm_t98a04_circleOrbit z) ∧
    ¬∃ i : apm_t98a04_CP1 → apm_t98a04_S3,
      Continuous i ∧ ∀ p, apm_t98a04_hopf (i p) = p := by
  refine ⟨apm_t98a04_continuous_hopf, apm_t98a04_submersion_bridge,
    apm_t98a04_fiber_p10, ?_, apm_t98a04_no_section_bridge⟩
  intro p
  exact ⟨apm_t98a04_fiber_homeomorph_circle p,
    fun z hz ↦ apm_t98a04_fiber_eq_circleOrbit p z hz⟩

#print axioms apm_t98a04
