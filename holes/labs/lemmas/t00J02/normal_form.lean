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

end ConstructionTargets.T00J02Closure
