import Mathlib
import ConstructionTargets.t00J02Closure

open Set
open scoped Manifold Topology ContDiff

noncomputable section
set_option autoImplicit false

namespace ConstructionTargets.T00J02Closure

/-- Linear core of the transverse normal-form argument.  If the source
derivative together with the curve derivative spans the target, the
straightening derivative sends the curve into the kernel of the normal
coordinate, and that normal coordinate is nonzero somewhere after
straightening, then its composite with the source derivative is nonzero. -/
theorem transverse_normal_component_ne_zero
    {R E F G H K : Type}
    [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    [AddCommGroup H] [Module R H]
    [AddCommGroup K] [Module R K]
    (A : E →ₗ[R] G) (C : F →ₗ[R] G)
    (B : G →ₗ[R] H) (q : H →ₗ[R] K)
    (hspan : LinearMap.range A ⊔ LinearMap.range C = ⊤)
    (hcurve : ∀ v, q (B (C v)) = 0)
    (hnormal : ∃ y, q (B y) ≠ 0) :
    q.comp (B.comp A) ≠ 0 := by
  rintro hzero
  obtain ⟨y, hy⟩ := hnormal
  have hyspan : y ∈ LinearMap.range A ⊔ LinearMap.range C := by
    rw [hspan]
    trivial
  rw [Submodule.mem_sup] at hyspan
  obtain ⟨a, ha, c, hc, rfl⟩ := hyspan
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hc
  apply hy
  rw [map_add, map_add, hcurve, add_zero]
  have hz := LinearMap.congr_fun hzero u
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz

/-- An injective endomorphism of a finite-dimensional space cannot send the
whole space into the kernel of a nonzero linear functional. -/
theorem exists_normal_value_of_ker_eq_bot
    {K V W : Type}
    [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (B : V →ₗ[K] V) (q : V →ₗ[K] W)
    (hB : LinearMap.ker B = ⊥) (hq : q ≠ 0) :
    ∃ y, q (B y) ≠ 0 := by
  have hBinj : Function.Injective B := LinearMap.ker_eq_bot.mp hB
  have hBsurj : Function.Surjective B :=
    LinearMap.injective_iff_surjective.mp hBinj
  have hqvalue : ∃ w, q w ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hq
    ext w
    exact hall w
  obtain ⟨w, hw⟩ := hqvalue
  obtain ⟨y, rfl⟩ := hBsurj w
  exact ⟨y, hw⟩

/-- Transversality forces a nonzero normal component after an injective
finite-dimensional straightening derivative.  This packages the two linear
steps needed before applying the strict inverse-function theorem. -/
theorem transverse_normal_component_ne_zero_of_ker_eq_bot
    {K E F V W : Type}
    [DivisionRing K]
    [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (A : E →ₗ[K] V) (C : F →ₗ[K] V)
    (B : V →ₗ[K] V) (q : V →ₗ[K] W)
    (hspan : LinearMap.range A ⊔ LinearMap.range C = ⊤)
    (hcurve : ∀ v, q (B (C v)) = 0)
    (hB : LinearMap.ker B = ⊥) (hq : q ≠ 0) :
    q.comp (B.comp A) ≠ 0 :=
  transverse_normal_component_ne_zero (R := K) (E := E) (F := F)
    (G := V) (H := V) (K := W) A C B q hspan hcurve
    (exists_normal_value_of_ker_eq_bot B q hB hq)

#print axioms transverse_normal_component_ne_zero
#print axioms exists_normal_value_of_ker_eq_bot
#print axioms transverse_normal_component_ne_zero_of_ker_eq_bot


/-- Stage A of the normal form: in the chart at a fibre point, `β ∘ f` is smooth and its normal
(second) coordinate has nonzero derivative. -/
theorem normal_derivative_ne_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : C(S, S)) (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (c : C(Circle, S)) (hcsmooth : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c) (z : Circle)
    (β : OpenPartialHomeomorph S SurfaceModel)
    (hβsmooth : ContMDiffAt SurfaceModelWithCorners SurfaceModelWithCorners ∞ β (c z))
    (hβinv : LinearMap.ker
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners β (c z)).toLinearMap = ⊥)
    (hβc : ∀ᶠ w in 𝓝 z, β (c w) 1 = 0)
    (x : S) (hx : f x = c z)
    (htrans : LinearMap.range
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ContDiffAt ℝ ∞ (fun p => β (f ((chartAt SurfaceModel x).symm p))) (chartAt SurfaceModel x x) ∧
      (EuclideanSpace.proj (1 : Fin 2) : SurfaceModel →L[ℝ] ℝ).comp
        (fderiv ℝ (fun p => β (f ((chartAt SurfaceModel x).symm p)))
          (chartAt SurfaceModel x x)) ≠ 0 := by
  set I := SurfaceModelWithCorners
  set φ := chartAt SurfaceModel x
  set q : SurfaceModel →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 2)
  have hβ' : ContMDiffAt I I ∞ β (f x) := by rw [hx]; exact hβsmooth
  have hh : ContMDiffAt I I ∞ (fun p => β (f p)) x := hβ'.comp x (hf x)
  have hφs : ContMDiffAt I I ∞ φ.symm (φ x) :=
    (contMDiffOn_chart_symm (x := x)).contMDiffAt
      (φ.open_target.mem_nhds (φ.map_source (mem_chart_source _ x)))
  have hG : ContMDiffAt I I ∞ (fun p => β (f (φ.symm p))) (φ x) :=
    hh.comp_of_eq hφs (φ.left_inv (mem_chart_source _ x))
  refine ⟨contMDiffAt_iff_contDiffAt.mp hG, ?_⟩
  -- derivatives
  have hdβ : MDifferentiableAt I I β (c z) := hβsmooth.mdifferentiableAt (by simp)
  have hdf : MDifferentiableAt I I f x := (hf x).mdifferentiableAt (by simp)
  have hdc : MDifferentiableAt (𝓡 1) I c z := (hcsmooth z).mdifferentiableAt (by simp)
  have hdφ : MDifferentiableAt I I φ.symm (φ x) := hφs.mdifferentiableAt (by simp)
  have hcurve : ∀ v, q (mfderiv I I β (c z) (mfderiv (𝓡 1) I c z v)) = 0 := by
    have h0 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun w => q (β (c w))) z = 0 := by
      have : (fun w => q (β (c w))) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [hβc] with w hw
        simpa [q] using hw
      rw [this.mfderiv_eq]
      exact mfderiv_const
    have hchain : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun w => q (β (c w))) z =
        q.comp ((mfderiv I I β (c z)).comp (mfderiv (𝓡 1) I c z)) := by
      have h1 := mfderiv_comp z hdβ hdc
      have h2 := mfderiv_comp z (q.mdifferentiableAt (x := β (c z))) (hdβ.comp z hdc)
      rw [show (fun w => q (β (c w))) = q ∘ (β ∘ c) from rfl, h2, q.mfderiv_eq]
      erw [h1]
      rfl
    intro v
    have := congrArg (fun L => L v) (hchain.symm.trans h0)
    simpa using this
  haveI : FiniteDimensional ℝ (TangentSpace I (c z)) :=
    inferInstanceAs (FiniteDimensional ℝ SurfaceModel)
  haveI : FiniteDimensional ℝ (TangentSpace I (f x)) :=
    inferInstanceAs (FiniteDimensional ℝ SurfaceModel)
  have hq' : q ≠ 0 := by
    intro h
    have := congrArg (fun L : SurfaceModel →L[ℝ] ℝ => L (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) h
    simp [q] at this
  have hcore := transverse_normal_component_ne_zero_of_ker_eq_bot (K := ℝ)
    (mfderiv I I f x).toLinearMap (mfderiv (𝓡 1) I c z).toLinearMap
    (mfderiv I I β (c z)).toLinearMap q.toLinearMap
    (by rw [hx] at htrans; exact htrans) hcurve hβinv
    (fun h => hq' (ContinuousLinearMap.coe_injective (by rw [h, ContinuousLinearMap.coe_zero]; rfl)))
  -- fderiv of the chart expression is the manifold derivative of β ∘ f at x
  have hdH : MDifferentiableAt I I (fun p => β (f p)) x := hh.mdifferentiableAt (by simp)
  have hfd : fderiv ℝ (fun p => β (f (φ.symm p))) (φ x) = mfderiv I I (fun p => β (f p)) x := by
    rw [hdH.mfderiv]
    simp [writtenInExtChartAt, I, φ, Function.comp_def]
  rw [← hx] at hcore hdβ
  have hHd : mfderiv I I (fun p => β (f p)) x = (mfderiv I I β (f x)).comp (mfderiv I I f x) :=
    mfderiv_comp x hdβ hdf
  rw [hfd, hHd]
  intro h0
  apply hcore
  ext v
  have := congrArg (fun L => L v) h0
  simpa using this

/-- Stage B of the normal form (planar): if the second coordinate of `G` has nonzero derivative
at `x₀` and vanishes there, a local diffeomorphism `Ψ` with `Ψ x₀ = 0` makes it the second
coordinate. -/
theorem planar_normal_coordinate
    (G : SurfaceModel → SurfaceModel) (x₀ : SurfaceModel)
    (hG : ContDiffAt ℝ ∞ G x₀) (hG0 : G x₀ 1 = 0)
    (hℓ : (EuclideanSpace.proj (1 : Fin 2) : SurfaceModel →L[ℝ] ℝ).comp (fderiv ℝ G x₀) ≠ 0) :
    ∃ Ψ : OpenPartialHomeomorph SurfaceModel SurfaceModel,
      x₀ ∈ Ψ.source ∧ Ψ x₀ = 0 ∧ ∀ p ∈ Ψ.target, G (Ψ.symm p) 1 = p 1 := by
  set q : SurfaceModel →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 2)
  set q0 : SurfaceModel →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 2)
  set ℓ := q.comp (fderiv ℝ G x₀)
  set e0 : SurfaceModel := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set e1 : SurfaceModel := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  set a := ℓ e0
  set b := ℓ e1
  set Λ : SurfaceModel →L[ℝ] ℝ := (-b) • q0 + a • q
  have hdecomp : ∀ v : SurfaceModel, v = v 0 • e0 + v 1 • e1 := by
    intro v; ext i; fin_cases i <;> simp [e0, e1]
  have hℓv : ∀ v : SurfaceModel, ℓ v = a * v 0 + b * v 1 := by
    intro v
    conv_lhs => rw [hdecomp v]
    simp [a, b, map_add, map_smul, mul_comm]
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    apply hℓ
    ext v
    rw [hℓv, ha, hb]; simp
  let Φ : SurfaceModel → SurfaceModel := fun p => Λ (p - x₀) • e0 + q (G p) • e1
  let M : SurfaceModel →L[ℝ] SurfaceModel := Λ.smulRight e0 + ℓ.smulRight e1
  have hGs : HasStrictFDerivAt G (fderiv ℝ G x₀) x₀ := hG.hasStrictFDerivAt (by simp)
  have hΦ : HasStrictFDerivAt Φ M x₀ := by
    have h1 : HasStrictFDerivAt (fun p => Λ (p - x₀)) Λ x₀ := by
      simpa using (Λ.hasStrictFDerivAt.comp x₀ ((hasStrictFDerivAt_id x₀).sub_const x₀))
    have h2 : HasStrictFDerivAt (fun p => q (G p)) ℓ x₀ := q.hasStrictFDerivAt.comp x₀ hGs
    exact (h1.smul_const e0).add (h2.smul_const e1)
  have hMinj : Function.Injective (M : SurfaceModel →ₗ[ℝ] SurfaceModel) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 := congrArg (fun w : SurfaceModel => w 0) hv
    have h1 := congrArg (fun w : SurfaceModel => w 1) hv
    simp [M, e0, e1] at h0 h1
    rw [hℓv] at h1
    simp [Λ, q0, q] at h0
    have hv0 : v 0 = 0 := by
      have : (a ^ 2 + b ^ 2) * v 0 = 0 := by linear_combination a * h1 - b * h0
      exact (mul_eq_zero.mp this).resolve_left hab
    have hv1 : v 1 = 0 := by
      have : (a ^ 2 + b ^ 2) * v 1 = 0 := by linear_combination b * h1 + a * h0
      exact (mul_eq_zero.mp this).resolve_left hab
    rw [hdecomp v, hv0, hv1]; simp
  let Me : SurfaceModel ≃L[ℝ] SurfaceModel :=
    (LinearEquiv.ofInjectiveEndo (M : SurfaceModel →ₗ[ℝ] SurfaceModel) hMinj).toContinuousLinearEquiv
  have hMe : (Me : SurfaceModel →L[ℝ] SurfaceModel) = M := by ext v; rfl
  have hΦe : HasStrictFDerivAt Φ (Me : SurfaceModel →L[ℝ] SurfaceModel) x₀ := hMe ▸ hΦ
  refine ⟨hΦe.toOpenPartialHomeomorph Φ, hΦe.mem_toOpenPartialHomeomorph_source, ?_, ?_⟩
  · rw [hΦe.toOpenPartialHomeomorph_coe]
    simp [Φ, hG0, q]
  · intro p hp
    have hinv := (hΦe.toOpenPartialHomeomorph Φ).right_inv hp
    rw [hΦe.toOpenPartialHomeomorph_coe] at hinv
    have := congrArg (fun w : SurfaceModel => w 1) hinv
    simpa [Φ, e0, e1, q] using this


/-- **C2: transverse normal form at a fibre point.**  In a chart `α` at `x` and the straightening
chart `β` at `c z`, the map is `(u, v) ↦ (g(u, v), v)`, the shape `productMap g` of the model
product lemma. -/
theorem exists_transverse_normal_form
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : C(S, S)) (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (c : C(Circle, S)) (hcsmooth : ContMDiff (𝓡 1) SurfaceModelWithCorners ∞ c) (z : Circle)
    (β : OpenPartialHomeomorph S SurfaceModel)
    (hβz : c z ∈ β.source)
    (hβsmooth : ContMDiffAt SurfaceModelWithCorners SurfaceModelWithCorners ∞ β (c z))
    (hβinv : LinearMap.ker
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners β (c z)).toLinearMap = ⊥)
    (hβc : ∀ᶠ w in 𝓝 z, β (c w) 1 = 0)
    (x : S) (hx : f x = c z)
    (htrans : LinearMap.range
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 1) SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ∃ (α : OpenPartialHomeomorph S SurfaceModel) (g : C(SurfaceModel, ℝ)),
      x ∈ α.source ∧ α x = 0 ∧ α.source ⊆ f ⁻¹' β.source ∧
      ∀ p ∈ α.target, β (f (α.symm p)) =
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![g p, p 1] := by
  set φ := chartAt SurfaceModel x
  set G : SurfaceModel → SurfaceModel := fun p => β (f (φ.symm p))
  obtain ⟨hG, hℓ⟩ := normal_derivative_ne_zero f hf c hcsmooth z β hβsmooth hβinv hβc x hx htrans
  have hxφ : x ∈ φ.source := mem_chart_source _ x
  have hG0 : G (φ x) 1 = 0 := by
    simp only [G, φ.left_inv hxφ, hx]; exact hβc.self_of_nhds
  obtain ⟨Ψ, hΨs, hΨ0, hΨ1⟩ := planar_normal_coordinate G (φ x) hG hG0 hℓ
  set O : Set S := φ.source ∩ f ⁻¹' β.source
  have hO : IsOpen O := φ.open_source.inter (β.open_source.preimage f.continuous)
  set α₀ := (φ.trans Ψ).restrOpen O hO
  have hxα₀ : x ∈ α₀.source := by
    simp only [α₀, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source]
    exact ⟨⟨hxφ, hΨs⟩, hxφ, by simpa [hx] using hβz⟩
  have hα₀x : α₀ x = 0 := hΨ0
  have hα₀O : α₀.source ⊆ O := fun p hp => by
    simp only [α₀, OpenPartialHomeomorph.restrOpen_source] at hp; exact hp.2
  have key : ∀ p ∈ α₀.target, β (f (α₀.symm p)) 1 = p 1 := by
    intro p hp
    have hy : α₀.symm p ∈ α₀.source := α₀.map_target hp
    have hyp : α₀ (α₀.symm p) = p := α₀.right_inv hp
    have hys : α₀.symm p ∈ (φ.trans Ψ).source := by
      simp only [α₀, OpenPartialHomeomorph.restrOpen_source] at hy; exact hy.1
    rw [OpenPartialHomeomorph.trans_source] at hys
    have hα₀y : α₀ (α₀.symm p) = Ψ (φ (α₀.symm p)) := rfl
    have hpΨ : p ∈ Ψ.target := by
      rw [← hyp, hα₀y]; exact Ψ.map_source hys.2
    have hΨsymm : Ψ.symm p = φ (α₀.symm p) := by
      calc Ψ.symm p = Ψ.symm (Ψ (φ (α₀.symm p))) := by rw [← hα₀y, hyp]
        _ = φ (α₀.symm p) := Ψ.left_inv hys.2
    have := hΨ1 p hpΨ
    rw [hΨsymm] at this
    simpa only [G, φ.left_inv hys.1] using this
  have h0t : (0 : SurfaceModel) ∈ α₀.target := hα₀x ▸ α₀.map_source hxα₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp α₀.open_target 0 h0t
  set ρ' := ρ / 2 with hρ'
  have hρ'pos : 0 < ρ' := by positivity
  let r : SurfaceModel → SurfaceModel := fun p => (ρ' / max ρ' ‖p‖) • p
  have hrc : Continuous r := by
    apply Continuous.smul _ continuous_id
    exact continuous_const.div (continuous_const.max continuous_norm)
      (fun p => (lt_of_lt_of_le hρ'pos (le_max_left _ _)).ne')
  have hrt : ∀ p, r p ∈ α₀.target := by
    intro p
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    have hm : 0 < max ρ' ‖p‖ := lt_of_lt_of_le hρ'pos (le_max_left _ _)
    calc ‖r p‖ = ρ' / max ρ' ‖p‖ * ‖p‖ := by
          simp only [r, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hρ'pos, abs_of_pos hm]
      _ ≤ ρ' := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hm]
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) hρ'pos.le
      _ < ρ := by rw [hρ']; linarith
  have hrid : ∀ p, ‖p‖ < ρ' → r p = p := by
    intro p hp
    simp [r, max_eq_left hp.le, hρ'pos.ne']
  have hcont : ContinuousOn (fun p => β (f (α₀.symm p))) α₀.target := by
    refine β.continuousOn.comp (f.continuous.comp_continuousOn α₀.continuousOn_symm) ?_
    intro p hp
    exact (hα₀O (α₀.map_target hp)).2
  let g : C(SurfaceModel, ℝ) :=
    ⟨fun p => β (f (α₀.symm (r p))) 0,
      (EuclideanSpace.proj (0 : Fin 2) : SurfaceModel →L[ℝ] ℝ).continuous.comp
        (hcont.comp_continuous hrc hrt)⟩
  let α := α₀.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : SurfaceModel) ρ')
    Metric.isOpen_ball)
  refine ⟨α, g, ?_, ?_, ?_, ?_⟩
  · simp only [α, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.ofSet_source]
    refine ⟨hxα₀, ?_⟩
    show α₀ x ∈ Metric.ball 0 ρ'
    rw [hα₀x]; exact Metric.mem_ball_self hρ'pos
  · exact hα₀x
  · intro p hp
    simp only [α, OpenPartialHomeomorph.trans_source] at hp
    exact (hα₀O hp.1).2
  · intro p hp
    simp only [α, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.ofSet_target,
      OpenPartialHomeomorph.ofSet_symm] at hp
    have hpb : ‖p‖ < ρ' := by simpa using hp.1
    have hpt : p ∈ α₀.target := hp.2
    have hsymm : α.symm p = α₀.symm p := rfl
    rw [hsymm]
    ext i
    fin_cases i
    · simp [g, hrid p hpb]
    · simpa using key p hpt

#print axioms exists_transverse_normal_form

/-- At a cusp of the target curve, transversality says that the differential
of `f` is onto.  Since both tangent spaces are the two-dimensional model
space, it is consequently an isomorphism. -/
theorem mfderiv_bijective_at_cusp
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : C(S, S)) (c : C(Circle, S)) (z : Circle)
    (hz : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      SurfaceModelWithCorners c z = 0)
    (x : S)
    (htrans : LinearMap.range
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    Function.Bijective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap := by
  have hrange : LinearMap.range
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap = ⊤ := by
    have hc0 :
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          SurfaceModelWithCorners c z).toLinearMap = 0 := by
      rw [hz]
      rfl
    have hcrange : LinearMap.range
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          SurfaceModelWithCorners c z).toLinearMap = ⊥ :=
      LinearMap.range_eq_bot.mpr hc0
    calc
      LinearMap.range
          (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap =
          LinearMap.range
            (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔ ⊥ :=
        (sup_bot_eq _).symm
      _ = LinearMap.range
            (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
          LinearMap.range
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
              SurfaceModelWithCorners c z).toLinearMap :=
        congrArg _ hcrange.symm
      _ = ⊤ := htrans
  have hsurj : Function.Surjective
      (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap :=
    LinearMap.range_eq_top.mp hrange
  haveI : FiniteDimensional ℝ (TangentSpace SurfaceModelWithCorners x) :=
    inferInstanceAs (FiniteDimensional ℝ SurfaceModel)
  haveI : FiniteDimensional ℝ (TangentSpace SurfaceModelWithCorners (f x)) :=
    inferInstanceAs (FiniteDimensional ℝ SurfaceModel)
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

/-- A smooth surface map transverse to a cusp is represented by a local
homeomorphism near the point of the fibre. -/
theorem exists_localHomeomorph_at_cusp
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace SurfaceModel S]
    [IsManifold SurfaceModelWithCorners ∞ S]
    (f : C(S, S)) (hf : ContMDiff SurfaceModelWithCorners SurfaceModelWithCorners ∞ f)
    (c : C(Circle, S)) (z : Circle)
    (hz : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      SurfaceModelWithCorners c z = 0)
    (x : S) (hx : f x = c z)
    (htrans : LinearMap.range
        (mfderiv SurfaceModelWithCorners SurfaceModelWithCorners f x).toLinearMap ⊔
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        SurfaceModelWithCorners c z).toLinearMap = ⊤) :
    ∃ Φ : OpenPartialHomeomorph S S, x ∈ Φ.source ∧ ∀ p ∈ Φ.source, Φ p = f p := by
  let I := SurfaceModelWithCorners
  let φ : OpenPartialHomeomorph S SurfaceModel := chartAt SurfaceModel x
  let ψ : OpenPartialHomeomorph S SurfaceModel := chartAt SurfaceModel (f x)
  let G : SurfaceModel → SurfaceModel := fun q ↦ ψ (f (φ.symm q))
  let x₀ : SurfaceModel := φ x
  have hmd : MDifferentiableAt I I f x := (hf.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hb := mfderiv_bijective_at_cusp f c z hz x htrans
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ SurfaceModel)
  haveI : FiniteDimensional ℝ (TangentSpace I (f x)) :=
    inferInstanceAs (FiniteDimensional ℝ SurfaceModel)
  let A : SurfaceModel →L[ℝ] SurfaceModel := mfderiv I I f x
  have hAb : Function.Bijective A := hb
  let L : SurfaceModel ≃L[ℝ] SurfaceModel :=
    ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hAb.1) (LinearMap.range_eq_top.mpr hAb.2)
  have hL : (L : SurfaceModel →L[ℝ] SurfaceModel) = mfderiv I I f x := by
    exact ContinuousLinearEquiv.coe_ofBijective A
      (LinearMap.ker_eq_bot.mpr hAb.1) (LinearMap.range_eq_top.mpr hAb.2)
  have hGderiv : HasFDerivAt G (L : SurfaceModel →L[ℝ] SurfaceModel) x₀ := by
    have hm := hmd.hasMFDerivAt.2
    rw [I.range_eq_univ, hasFDerivWithinAt_univ] at hm
    simpa [G, x₀, φ, ψ, I, writtenInExtChartAt] using (hL ▸ hm)
  have hGdiff : ContDiffAt ℝ ∞ G x₀ := by
    have hc := (contMDiffAt_iff.mp (hf.contMDiffAt (x := x))).2
    rw [I.range_eq_univ, contDiffWithinAt_univ] at hc
    simpa [G, x₀, φ, ψ, I, writtenInExtChartAt] using hc
  let Ψ : OpenPartialHomeomorph SurfaceModel SurfaceModel :=
    hGdiff.toOpenPartialHomeomorph G hGderiv (by simp)
  have hxΨ : x₀ ∈ Ψ.source :=
    hGdiff.mem_toOpenPartialHomeomorph_source hGderiv (by simp)
  let Φ₀ : OpenPartialHomeomorph S S := φ.trans (Ψ.trans ψ.symm)
  let O : Set S := Φ₀.source ∩ f ⁻¹' ψ.source
  have hO : IsOpen O := Φ₀.open_source.inter (ψ.open_source.preimage f.continuous)
  let Φ : OpenPartialHomeomorph S S := Φ₀.restrOpen O hO
  have hxφ : x ∈ φ.source := by simpa [φ] using mem_chart_source SurfaceModel x
  have hGx : G x₀ = ψ (f x) := by
    simp [G, x₀, φ, ψ, hxφ]
  have hxΦ₀ : x ∈ Φ₀.source := by
    simp only [Φ₀, OpenPartialHomeomorph.trans_source]
    refine ⟨hxφ, hxΨ, ?_⟩
    change G x₀ ∈ ψ.target
    rw [hGx]
    exact ψ.map_source (by simpa [ψ] using mem_chart_source SurfaceModel (f x))
  have hxO : x ∈ O :=
    ⟨hxΦ₀, by simpa [ψ] using (mem_chart_source SurfaceModel (f x))⟩
  refine ⟨Φ, ?_, ?_⟩
  · simpa [Φ] using ⟨hxΦ₀, hxO⟩
  · intro p hp
    have hpO : p ∈ O := by
      simpa only [Φ, OpenPartialHomeomorph.restrOpen_source] using hp |>.2
    have hpφ : p ∈ φ.source := by
      have hp₀ := hpO.1
      simp only [Φ₀, OpenPartialHomeomorph.trans_source] at hp₀
      exact hp₀.1
    have hfpψ : f p ∈ ψ.source := hpO.2
    rw [show Φ p = ψ.symm (Ψ (φ p)) by rfl]
    rw [hGdiff.toOpenPartialHomeomorph_coe hGderiv (by simp)]
    change ψ.symm (G (φ p)) = f p
    rw [show G (φ p) = ψ (f p) by
      simp [G, φ, ψ, writtenInExtChartAt, φ.left_inv hpφ]]
    exact ψ.left_inv hfpψ

#print axioms exists_localHomeomorph_at_cusp
end ConstructionTargets.T00J02Closure
