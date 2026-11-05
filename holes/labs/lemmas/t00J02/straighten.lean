import Mathlib
import ConstructionTargets.t00J02Closure

open Set Filter
open scoped Topology ContDiff
open ConstructionTargets.T00J02Closure

noncomputable section

/-- An open parameter neighborhood in a compact embedded curve can be isolated
by an ambient open neighborhood. Its intersection with the whole curve is
exactly the chosen arc, so no other part of the curve enters it. -/
lemma straightening_isolate_arc
    {S : Type} [TopologicalSpace S] [T2Space S]
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    {V : Set Circle} (hV : IsOpen V) {z : Circle} (hz : z ∈ V) :
    ∃ O : Set S, IsOpen O ∧ c z ∈ O ∧
      (∀ t, c t ∈ O ↔ t ∈ V) ∧ O ∩ Set.range c = c '' V := by
  let O : Set S := (c '' Vᶜ)ᶜ
  have hO : IsOpen O := ((hV.isClosed_compl.isCompact).image c.continuous).isClosed.isOpen_compl
  have he : ∀ t, c t ∈ O ↔ t ∈ V := by
    intro t
    change c t ∉ c '' Vᶜ ↔ t ∈ V
    constructor
    · intro h
      by_contra ht
      exact h ⟨t, ht, rfl⟩
    · rintro ht ⟨u, hu, heq⟩
      exact hu ((hc.injective heq).symm ▸ ht)
  refine ⟨O, hO, (he z).mpr hz, he, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, t, rfl⟩
    exact ⟨t, (he t).mp hx, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(he t).mpr ht, ⟨t, rfl⟩⟩

/-- The derivative of the transverse thickening `(r,s) ↦ w(r) + s • n`
is the linear map with columns `w'(0)` and `n`. -/
lemma straightening_thickening_derivative
    (w : ℝ → SurfaceModel) (v n : SurfaceModel)
    (hw : HasDerivAt w v 0) :
    HasFDerivAt (fun x : ℝ × ℝ => w x.1 + x.2 • n)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight n) (0, 0) := by
  have hf : HasFDerivAt (fun x : ℝ × ℝ => x.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) := hasFDerivAt_fst
  have hg : HasFDerivAt (fun x : ℝ × ℝ => x.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := hasFDerivAt_snd
  have h := hw.hasFDerivAt.comp (0 : ℝ × ℝ) hf
  convert h.add (hg.smul_const n) using 1

/-- A nonzero planar tangent has the explicit transverse vector obtained by
quarter-turn rotation. Together they define an invertible continuous linear
map from the parameter plane. -/
lemma straightening_transverse_basis (v : SurfaceModel) (hv : v ≠ 0) :
    ∃ n : SurfaceModel, ∃ L : (ℝ × ℝ) ≃L[ℝ] SurfaceModel,
      (L : (ℝ × ℝ) →L[ℝ] SurfaceModel) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight n := by
  let n : SurfaceModel := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let T : (ℝ × ℝ) →L[ℝ] SurfaceModel :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight n
  have hd : v 0 ^ 2 + v 1 ^ 2 ≠ 0 := by
    intro h
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0)]
    apply hv
    ext i
    fin_cases i <;> simp [h0, h1]
  have hT : ∀ x : ℝ × ℝ, T x 0 = x.1 * v 0 - x.2 * v 1 ∧
      T x 1 = x.1 * v 1 + x.2 * v 0 := by
    intro x
    simp [T, n, sub_eq_add_neg]
  have hi : Function.Injective T := by
    intro x y he
    have h0 := congrArg (fun u : SurfaceModel => u 0) he
    have h1 := congrArg (fun u : SurfaceModel => u 1) he
    dsimp only at h0 h1
    erw [(hT x).1, (hT y).1] at h0
    erw [(hT x).2, (hT y).2] at h1
    have hx : (x.1 - y.1) * (v 0 ^ 2 + v 1 ^ 2) = 0 := by
      nlinarith [congrArg (fun t : ℝ => t * v 0) h0,
        congrArg (fun t : ℝ => t * v 1) h1]
    have hy : (x.2 - y.2) * (v 0 ^ 2 + v 1 ^ 2) = 0 := by
      nlinarith [congrArg (fun t : ℝ => t * v 1) h0,
        congrArg (fun t : ℝ => t * v 0) h1]
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hd))
      (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right hd))
  have hs : Function.Surjective T := by
    intro y
    refine ⟨((y 0 * v 0 + y 1 * v 1) / (v 0 ^ 2 + v 1 ^ 2),
      (y 1 * v 0 - y 0 * v 1) / (v 0 ^ 2 + v 1 ^ 2)), ?_⟩
    ext i
    fin_cases i
    · erw [(hT _).1]
      dsimp
      field_simp [hd]
      ring
    · erw [(hT _).2]
      dsimp
      field_simp [hd]
      ring
  exact ⟨n, (LinearEquiv.ofBijective T.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

/-- Once the transverse derivative columns form a basis, the explicit
thickening has a local inverse. The inverse straightens the original curve
with its prescribed parameter, and both maps are smooth at the base point. -/
lemma straightening_thickening_inverse
    (w : ℝ → SurfaceModel) (v n : SurfaceModel)
    (hw : HasDerivAt w v 0) (hs : ContDiffAt ℝ ∞ w 0)
    (L : (ℝ × ℝ) ≃L[ℝ] SurfaceModel)
    (hL : (L : (ℝ × ℝ) →L[ℝ] SurfaceModel) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight n) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) SurfaceModel,
      (0, 0) ∈ e.source ∧ w 0 ∈ e.target ∧ e.symm (w 0) = (0, 0) ∧
      (∀ x, e x = w x.1 + x.2 • n) ∧
      ContDiffAt ℝ ∞ e (0, 0) ∧ ContDiffAt ℝ ∞ e.symm (w 0) ∧
      ∀ r, (r, 0) ∈ e.source → e.symm (w r) = (r, 0) := by
  let f : ℝ × ℝ → SurfaceModel := fun x => w x.1 + x.2 • n
  have hf : ContDiffAt ℝ ∞ f (0, 0) :=
    (hs.comp (0 : ℝ × ℝ) contDiff_fst.contDiffAt).add
      (contDiff_snd.contDiffAt.smul contDiff_const.contDiffAt)
  have hd : HasFDerivAt f (L : (ℝ × ℝ) →L[ℝ] SurfaceModel) (0, 0) := by
    rw [hL]
    exact straightening_thickening_derivative w v n hw
  let e := hf.toOpenPartialHomeomorph f hd (by simp)
  have h0 : (0, 0) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  have he0 : e (0, 0) = w 0 := by change w 0 + (0 : ℝ) • n = w 0; simp
  have ht : w 0 ∈ e.target := he0 ▸ e.map_source h0
  refine ⟨e, h0, ht, ?_, (fun _ => rfl), hf, ?_, ?_⟩
  · rw [← he0]
    exact e.left_inv h0
  · have hi := hf.to_localInverse hd (by simp)
    simpa only [f, zero_smul, add_zero] using hi
  · intro r hr
    have he : e (r, 0) = w r := by change w r + (0 : ℝ) • n = w r; simp
    rw [← he]
    exact e.left_inv hr

/-- A smooth regular parametrized planar curve has local inverse coordinates
which send `w r` to exactly `(r,0)` on a whole interval about zero. This
assembles the explicit transverse basis and the inverse-function step. -/
lemma straightening_regular_planar_curve
    (w : ℝ → SurfaceModel) (v : SurfaceModel)
    (hw : HasDerivAt w v 0) (hv : v ≠ 0) (hs : ContDiffAt ℝ ∞ w 0) :
    ∃ β : OpenPartialHomeomorph SurfaceModel (ℝ × ℝ), ∃ δ : ℝ,
      0 < δ ∧ w 0 ∈ β.source ∧ β (w 0) = (0, 0) ∧
      ContDiffAt ℝ ∞ β (w 0) ∧ ContDiffAt ℝ ∞ β.symm (0, 0) ∧
      ∀ r ∈ Set.Ioo (-δ) δ, w r ∈ β.source ∧ β (w r) = (r, 0) := by
  obtain ⟨n, L, hL⟩ := straightening_transverse_basis v hv
  obtain ⟨e, h0, ht, he0, he, hf, hi, ha⟩ :=
    straightening_thickening_inverse w v n hw hs L hL
  have hO : IsOpen {r : ℝ | (r, (0 : ℝ)) ∈ e.source} :=
    e.open_source.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp hO 0 h0
  refine ⟨e.symm, δ, hδ, ht, he0, hi, hf, ?_⟩
  intro r hr
  have hrO : (r, (0 : ℝ)) ∈ e.source := by
    apply hδO
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using hr
  have her : e (r, 0) = w r := by simpa only [zero_smul, add_zero] using he (r, 0)
  exact ⟨her ▸ e.map_source hrO, ha r hrO⟩

#print axioms straightening_isolate_arc
#print axioms straightening_thickening_inverse

#print axioms straightening_transverse_basis
#print axioms straightening_regular_planar_curve

open scoped Manifold

/-- Circle exponential, followed by translation, is open because it is the
quotient map onto the angle circle followed by two homeomorphisms. -/
lemma straightening_circle_param_open (z : Circle) :
    IsOpenMap (fun r : ℝ => z * Circle.exp r) := by
  exact (Homeomorph.mulLeft z).isOpenMap.comp
    (AddCircle.homeomorphCircle'.isOpenMap.comp QuotientAddGroup.isOpenMap_coe)

/-- The curve written in the extended chart is smooth at parameter zero. -/
lemma straightening_coordinate_smooth
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (c : C(Circle, S))
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c) (z : Circle) :
    ContDiffAt ℝ ∞
      (fun r : ℝ => extChartAt SurfaceModelWithCorners (c z) (c (z * Circle.exp r))) 0 := by
  have hg : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun r : ℝ => z * Circle.exp r) :=
    contMDiff_const.mul contMDiff_circleExp
  have h := contMDiffAt_extChartAt (I := SurfaceModelWithCorners) (x := c z) (n := ∞)
  have hg0 : z * Circle.exp 0 = z := by simp
  apply ContMDiffAt.contDiffAt
  have h' : ContMDiffAt SurfaceModelWithCorners 𝓘(ℝ, SurfaceModel) ∞
      (extChartAt SurfaceModelWithCorners (c z)) (c (z * Circle.exp 0)) := by
    simpa only [hg0] using h
  exact h'.comp 0 (hc.comp hg).contMDiffAt

/-- The translated exponential parameter has surjective manifold derivative:
its composite with the complex inclusion has derivative `z * I`, which is
nonzero, and the circle tangent space is one-dimensional. -/
lemma straightening_circle_param_deriv_surjective (z : Circle) :
    Function.Surjective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1)
      (fun r : ℝ => z * Circle.exp r) 0) := by
  let g : ℝ → Circle := fun r => z * Circle.exp r
  have hg : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ g :=
    contMDiff_const.mul contMDiff_circleExp
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ)
      (fun q : Circle => (q : ℂ)) (g 0) :=
    (contMDiff_coe_sphere (m := ∞) (n := 1) (g 0)).mdifferentiableAt (by simp)
  have hd : HasDerivAt (fun r : ℝ => (g r : ℂ)) ((z : ℂ) * Complex.I) 0 := by
    have h := ((((hasDerivAt_id (0 : ℂ)).mul_const Complex.I).cexp).const_mul (z : ℂ)).comp_ofReal
    simpa [g, Circle.coe_mul, Circle.coe_exp] using h
  have hchain := mfderiv_comp 0 hcoe (hg.contMDiffAt.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  change fderiv ℝ (fun r : ℝ => (g r : ℂ)) 0 = _ at hchain
  rw [hd.hasFDerivAt.fderiv] at hchain
  have hne : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) g 0 ≠ 0 := by
    intro he
    rw [he, ContinuousLinearMap.comp_zero] at hchain
    have heval := congrArg (fun T : ℝ →L[ℝ] ℂ => T 1) hchain
    have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
    have heval' : (z : ℂ) * Complex.I = 0 := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul,
        ContinuousLinearMap.zero_apply] using heval
    exact mul_ne_zero hz Complex.I_ne_zero heval'
  apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ)
    (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 by simp)
    (f := (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) g 0).toLinearMap)
  intro he
  apply hne
  apply DFunLike.ext
  intro r
  exact LinearMap.congr_fun he r

/-- Regularity survives the circle exponential parameter and the target chart.
The exponential parameter has invertible derivative at zero; the extended
chart has identity derivative at its centre. The chain rule therefore makes
this derivative nonzero whenever `mfderiv c z` is nonzero.
This is the derivative bridge from the manifold hypotheses to the planar
inverse-function construction. -/
lemma straightening_coordinate_deriv_ne_zero
    {S : Type} [TopologicalSpace S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (c : C(Circle, S))
    (hc : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c) (z : Circle)
    (hz : mfderiv (𝓡 1) SurfaceModelWithCorners c z ≠ 0) :
    deriv (fun r : ℝ => extChartAt SurfaceModelWithCorners (c z)
      (c (z * Circle.exp r))) 0 ≠ 0 := by
  let g : ℝ → Circle := fun r => z * Circle.exp r
  let φ := extChartAt SurfaceModelWithCorners (c z)
  let w : ℝ → SurfaceModel := fun r => φ (c (g r))
  have hg0 : g 0 = z := by simp [g]
  have hg : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ g :=
    contMDiff_const.mul contMDiff_circleExp
  have hcg := (hc.comp hg).contMDiffAt.mdifferentiableAt (x := 0) (by simp)
  have hφ : MDifferentiableAt SurfaceModelWithCorners SurfaceModelWithCorners φ (c (g 0)) := by
    rw [hg0]
    exact (contMDiffAt_extChartAt (I := SurfaceModelWithCorners) (x := c z)
      (n := ∞)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp 0 hφ hcg
  rw [mfderiv_eq_fderiv] at hchain
  have hcgchain := mfderiv_comp 0 (hc.contMDiffAt.mdifferentiableAt (x := g 0) (by simp))
    (hg.contMDiffAt.mdifferentiableAt (x := 0) (by simp))
  rw [hcgchain] at hchain
  simp only [Function.comp_apply] at hchain
  erw [hg0] at hchain
  change fderiv ℝ w 0 = (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners
    (extChartAt SurfaceModelWithCorners (c z)) (c z)).comp
      ((mfderiv (𝓡 1) SurfaceModelWithCorners c z).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) g 0)) at hchain
  rw [mfderiv_extChartAt_self] at hchain
  erw [ContinuousLinearMap.id_comp] at hchain
  intro he
  have hs := straightening_coordinate_smooth c hc z
  have hd := (hs.differentiableAt (by simp)).hasDerivAt.hasFDerivAt.fderiv
  rw [he] at hd
  have hwzero : fderiv ℝ w 0 = 0 := by simpa [w, φ, g] using hd
  rw [hwzero] at hchain
  apply hz
  ext v
  obtain ⟨r, hr⟩ := straightening_circle_param_deriv_surjective z v
  have hh := congrArg (fun T : ℝ →L[ℝ] SurfaceModel => T r) hchain
  change 0 = (mfderiv (𝓡 1) SurfaceModelWithCorners c z)
    ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) g 0) r) at hh
  change (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) g 0) r = v at hr
  rw [hr] at hh
  exact hh.symm

/-- Fixed Cartesian coordinates on the surface model. -/
def straightening_plane_coordinates : (ℝ × ℝ) ≃L[ℝ] SurfaceModel :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

@[simp] lemma straightening_plane_coordinates_axis (r : ℝ) :
    straightening_plane_coordinates (r, 0) =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0] := rfl

/-- A local straightening chart with the original exponential parameter and
no other portion of the embedded circle in its source. -/
theorem exists_straightening_chart
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (c : C(Circle, S)) (hc : Topology.IsEmbedding c)
    (hcsmooth : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c) (z : Circle)
    (hz : mfderiv (𝓡 1) SurfaceModelWithCorners c z ≠ 0) :
    ∃ (β : OpenPartialHomeomorph S SurfaceModel) (δ : ℝ), 0 < δ ∧
      c z ∈ β.source ∧ β (c z) = 0 ∧
      ContMDiffAt SurfaceModelWithCorners SurfaceModelWithCorners ∞ β (c z) ∧
      (∀ r ∈ Set.Ioo (-δ) δ, c (z * Circle.exp r) ∈ β.source ∧
        β (c (z * Circle.exp r)) = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0]) ∧
      (∀ p ∈ β.source, p ∈ Set.range c →
        ∃ r ∈ Set.Ioo (-δ) δ, p = c (z * Circle.exp r)) := by
  let φ := chartAt SurfaceModel (c z)
  let g : ℝ → Circle := fun r => z * Circle.exp r
  let w : ℝ → SurfaceModel := fun r => extChartAt SurfaceModelWithCorners (c z) (c (g r))
  have hg0 : g 0 = z := by simp [g]
  have hw0 : w 0 = φ (c z) := by simp [w, hg0, φ, extChartAt, SurfaceModelWithCorners]
  have hs : ContDiffAt ℝ ∞ w 0 := straightening_coordinate_smooth c hcsmooth z
  have hd : HasDerivAt w (deriv w 0) 0 := (hs.differentiableAt (by simp)).hasDerivAt
  obtain ⟨a, ε, hε, ha0, hav, has, _, har⟩ :=
    straightening_regular_planar_curve w (deriv w 0) hd
      (straightening_coordinate_deriv_ne_zero c hcsmooth z hz) hs
  let b := (φ.trans a).trans straightening_plane_coordinates.toHomeomorph.toOpenPartialHomeomorph
  have hbsource : b.source = {p | p ∈ φ.source ∧ φ p ∈ a.source} := by
    ext p
    simp [b]
  have hbval : ∀ p, b p = straightening_plane_coordinates (a (φ p)) := fun _ => rfl
  have hbc : c z ∈ b.source := by
    rw [hbsource]
    exact ⟨mem_chart_source _ _, hw0 ▸ ha0⟩
  have hbzero : b (c z) = 0 := by
    rw [hbval, ← hw0, hav]
    exact map_zero _
  have hbsm : ContMDiffAt SurfaceModelWithCorners SurfaceModelWithCorners ∞ b (c z) := by
    have hφ : ContMDiffAt SurfaceModelWithCorners SurfaceModelWithCorners ∞ φ (c z) := by
      simpa [φ, extChartAt, SurfaceModelWithCorners] using
        (contMDiffAt_extChartAt (I := SurfaceModelWithCorners) (x := c z))
    have hcomp := (hw0 ▸ has).contMDiffAt.comp (c z) hφ
    exact straightening_plane_coordinates.contDiff.contMDiff.contMDiffAt.comp (c z) hcomp
  have hpre : IsOpen {r : ℝ | c (g r) ∈ φ.source} :=
    φ.open_source.preimage (c.continuous.comp (continuous_const.mul Circle.exp.continuous))
  obtain ⟨η, hη, hηφ⟩ := Metric.isOpen_iff.mp hpre 0 (by
    change c (g 0) ∈ φ.source
    rw [hg0]
    exact mem_chart_source SurfaceModel (c z))
  let δ := min ε η
  have hδ : 0 < δ := lt_min hε hη
  have hδε : δ ≤ ε := min_le_left _ _
  have hδη : δ ≤ η := min_le_right _ _
  have hδr : ∀ r ∈ Set.Ioo (-δ) δ, c (g r) ∈ b.source ∧
      b (c (g r)) = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0] := by
    intro r hr
    have hrε : r ∈ Set.Ioo (-ε) ε := ⟨lt_of_le_of_lt (neg_le_neg hδε) hr.1, hr.2.trans_le hδε⟩
    have hrη : r ∈ Metric.ball (0 : ℝ) η := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨lt_of_le_of_lt (neg_le_neg hδη) hr.1, hr.2.trans_le hδη⟩
    have hwr : w r = φ (c (g r)) := rfl
    refine ⟨?_, ?_⟩
    · rw [hbsource]
      exact ⟨hηφ hrη, hwr ▸ (har r hrε).1⟩
    · rw [hbval, ← hwr, (har r hrε).2, straightening_plane_coordinates_axis]
  let V : Set Circle := g '' Set.Ioo (-δ) δ
  have hV : IsOpen V := straightening_circle_param_open z _ isOpen_Ioo
  have hzV : z ∈ V := ⟨0, ⟨neg_neg_of_pos hδ, hδ⟩, hg0⟩
  obtain ⟨O, hO, hzO, hOV, _⟩ := straightening_isolate_arc c hc hV hzV
  refine ⟨b.restrOpen O hO, δ, hδ, ⟨hbc, hzO⟩, hbzero, hbsm, ?_, ?_⟩
  · intro r hr
    exact ⟨⟨(hδr r hr).1, (hOV (g r)).mpr ⟨r, hr, rfl⟩⟩, (hδr r hr).2⟩
  · rintro p hp ⟨t, rfl⟩
    obtain ⟨r, hr, he⟩ := (hOV t).mp hp.2
    exact ⟨r, hr, congrArg c he.symm⟩

#print axioms exists_straightening_chart

#print axioms straightening_circle_param_deriv_surjective
#print axioms straightening_coordinate_deriv_ne_zero
