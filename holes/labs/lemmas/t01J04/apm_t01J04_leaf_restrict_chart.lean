import Mathlib
import ConstructionTargets.SardGenuineSmoothManifoldVector
import ConstructionTargets.SardSmoothNeighborhoodImplicitChart

open scoped ContDiff Manifold Topology

noncomputable section

abbrev apm_t01J04_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A smooth manifold-with-boundary structure on `S` for which the displayed
map is a smooth immersion into the ambient manifold.  Thus the existentially
chosen atlas is not unrelated to the ambient smooth structure. -/
def apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary
    (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    (IX : ModelWithCorners ℝ (apm_t01J04_Euclidean n)
      (apm_t01J04_Euclidean n))
    (S : Type*) [TopologicalSpace S] (ι : S → X) : Prop :=
  (n = 0 ∧
    ∃ charts : ChartedSpace (apm_t01J04_Euclidean n) S,
      let _ := charts
      IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
          (⊤ : ℕ∞) S ∧
        ContMDiff (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) IX
          (⊤ : ℕ∞) ι ∧
        ∀ z, Function.Injective
          (mfderiv (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) IX ι z)) ∨
  (∃ hn : NeZero n,
    let _ := hn
    ∃ charts : ChartedSpace (EuclideanHalfSpace n) S,
      let _ := charts
      IsManifold (modelWithCornersEuclideanHalfSpace n) (⊤ : ℕ∞) S ∧
        ContMDiff (modelWithCornersEuclideanHalfSpace n) IX (⊤ : ℕ∞) ι ∧
        ∀ z, Function.Injective
          (mfderiv (modelWithCornersEuclideanHalfSpace n) IX ι z))

/-!
# Blueprint for t01J04 (revision 2026-10-17)

The statement block above (the abbreviation, the predicate) and the signature of
`apm_t01j04` at the bottom are byte-identical to `problems/t01J04/lean/Main.lean`.

Leaves are the top-level theorems named `apm_t01J04_leaf_*`; each ends in
`sorry`.  Everything else is proved here.  See `BLUEPRINT.md`.

Route: `ρ = ‖φ(·) - φ(y)‖²` in the chart `φ` at `y`; Sard gives a regular value
`r` of `ρ ∘ f`; `V = {ρ < r}`; `f⁻¹(cl V) = {ρ ∘ f ≤ r}`; every point of that set
has an ambient chart of `X` in which the set is the half-space `{v 0 ≥ 0}`;
those charts, restricted, form the half-space atlas.
-/

open Set

/-! ## Part A: the target side and Sard -/

/-- Squared distance from `y`, measured in the preferred chart at `y`. -/
def apm_t01J04_bp_rho (m : ℕ) {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (apm_t01J04_Euclidean m) Y] (y z : Y) : ℝ :=
  ‖chartAt (apm_t01J04_Euclidean m) y z - chartAt (apm_t01J04_Euclidean m) y y‖ ^ 2

/-- The open chart ball `{ρ < r}` (inside the chart source). -/
def apm_t01J04_bp_ball (m : ℕ) {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (apm_t01J04_Euclidean m) Y] (y : Y) (r : ℝ) : Set Y :=
  {z | z ∈ (chartAt (apm_t01J04_Euclidean m) y).source ∧ apm_t01J04_bp_rho m y z < r}

/-- LEAF A1 (chart ball).  Small chart balls at `y` are neighbourhoods of `y`,
their closures lie in `U`, and the closure is exactly the closed chart ball
`{ρ ≤ r}` inside the chart source. -/
lemma apm_t01J04_leaf_chart_ball_aux_closure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) {r : ℝ} (hr : r ≠ 0) :
    closure (Metric.ball x r) = Metric.closedBall x r :=
  closure_ball x hr

set_option maxHeartbeats 2000000
theorem apm_t01J04_leaf_chart_ball
    (m : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    (y : Y) (U : Set Y) (hU : U ∈ 𝓝 y) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℝ, 0 < r → r < a →
      apm_t01J04_bp_ball m y r ∈ 𝓝 y ∧
      closure (apm_t01J04_bp_ball m y r) ⊆ U ∧
      closure (apm_t01J04_bp_ball m y r) =
        {z | z ∈ (chartAt (apm_t01J04_Euclidean m) y).source ∧
          apm_t01J04_bp_rho m y z ≤ r} := by
  let e := chartAt (apm_t01J04_Euclidean m) y
  let p := e y
  have hyp : p ∈ e.target := mem_chart_target _ y
  have hpre : e.symm ⁻¹' U ∈ 𝓝 p := by
    have hinv : e.symm p = y := e.left_inv (mem_chart_source _ y)
    have hm := e.symm.map_nhds_eq hyp
    rw [hinv] at hm
    rw [← hm] at hU
    exact hU
  have hO : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 p :=
    Filter.inter_mem (e.open_target.mem_nhds hyp) hpre
  rcases Metric.mem_nhds_iff.1 hO with ⟨d, hd, hdO⟩
  let s := d / 2
  have hs : 0 < s := half_pos hd
  have hclosed : Metric.closedBall p s ⊆ e.target ∩ e.symm ⁻¹' U :=
    (Metric.closedBall_subset_ball (half_lt_self hd)).trans hdO
  refine ⟨s ^ 2, sq_pos_of_pos hs, ?_⟩
  intro r hr hra
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsra : Real.sqrt r < s := by
    exact (Real.sqrt_lt' hs).2 hra
  let B := Metric.ball p (Real.sqrt r)
  let K := Metric.closedBall p (Real.sqrt r)
  have hKtarget : K ⊆ e.target :=
    (Metric.closedBall_subset_closedBall hsra.le).trans (hclosed.trans inter_subset_left)
  have hKU : K ⊆ e.symm ⁻¹' U :=
    (Metric.closedBall_subset_closedBall hsra.le).trans (hclosed.trans inter_subset_right)
  have hBeq : apm_t01J04_bp_ball m y r = e.symm '' B := by
    set_option maxHeartbeats 800000 in
      ext z
      constructor
      · rintro ⟨hzs, hzρ⟩
        refine ⟨e z, ?_, e.left_inv hzs⟩
        rw [Metric.mem_ball, dist_eq_norm]
        dsimp [apm_t01J04_bp_rho, e, p] at hzρ
        exact Real.lt_sqrt_of_sq_lt hzρ
      · rintro ⟨v, hv, rfl⟩
        have hvt : v ∈ e.target := hKtarget (Metric.ball_subset_closedBall hv)
        refine ⟨e.map_target hvt, ?_⟩
        rw [apm_t01J04_bp_rho, e.right_inv hvt]
        have hv' : ‖v - p‖ < Real.sqrt r := by simpa [Metric.mem_ball, dist_eq_norm] using hv
        exact (Real.lt_sqrt (norm_nonneg _)).1 hv'
  have hKeq : {z | z ∈ e.source ∧ apm_t01J04_bp_rho m y z ≤ r} = e.symm '' K := by
    set_option maxHeartbeats 800000 in
      ext z
      constructor
      · rintro ⟨hzs, hzρ⟩
        refine ⟨e z, ?_, e.left_inv hzs⟩
        rw [Metric.mem_closedBall, dist_eq_norm]
        dsimp [apm_t01J04_bp_rho, e, p] at hzρ
        exact Real.le_sqrt_of_sq_le hzρ
      · rintro ⟨v, hv, rfl⟩
        have hvt : v ∈ e.target := hKtarget hv
        refine ⟨e.map_target hvt, ?_⟩
        rw [apm_t01J04_bp_rho, e.right_inv hvt]
        have hv' : ‖v - p‖ ≤ Real.sqrt r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
        exact (Real.le_sqrt (norm_nonneg _) (le_of_lt hr)).1 hv'
  have hKcompact : IsCompact (e.symm '' K) :=
    ((isCompact_closedBall p (Real.sqrt r)).image_of_continuousOn
      (e.continuousOn_symm.mono hKtarget))
  have hKclosed : IsClosed (e.symm '' K) := hKcompact.isClosed
  have hcl : closure (e.symm '' B) = e.symm '' K := by
    apply Subset.antisymm
    · apply closure_minimal
      · exact image_mono Metric.ball_subset_closedBall
      · exact hKclosed
    · change e.symm '' Metric.closedBall p (Real.sqrt r) ⊆
        closure (e.symm '' Metric.ball p (Real.sqrt r))
      rw [← apm_t01J04_leaf_chart_ball_aux_closure
        (E := apm_t01J04_Euclidean m) p hsr.ne']
      have hc : ContinuousOn e.symm
          (closure (Metric.ball p (Real.sqrt r))) := by
        rw [apm_t01J04_leaf_chart_ball_aux_closure
          (E := apm_t01J04_Euclidean m) p hsr.ne']
        exact e.continuousOn_symm.mono hKtarget
      exact hc.image_closure
  have hnh : apm_t01J04_bp_ball m y r ∈ 𝓝 y := by
    rw [hBeq]
    have hBn : B ∈ 𝓝 p := Metric.ball_mem_nhds p hsr
    have hm := e.symm.map_nhds_eq hyp
    rw [e.left_inv (mem_chart_source _ y)] at hm
    rw [← hm]
    change e.symm ⁻¹' (e.symm '' B) ∈ 𝓝 p
    filter_upwards [hBn] with v hv
    exact ⟨v, hv, rfl⟩
  refine ⟨hnh, ?_, ?_⟩
  · rw [hBeq, hcl]
    rintro z ⟨v, hv, rfl⟩
    exact hKU hv
  · calc
      closure (apm_t01J04_bp_ball m y r) = closure (e.symm '' B) :=
        congrArg closure hBeq
      _ = e.symm '' K := hcl
      _ = {z | z ∈ e.source ∧ apm_t01J04_bp_rho m y z ≤ r} := hKeq.symm
set_option maxHeartbeats 200000

/-- The function `ρ ∘ f` is smooth on the open set `f⁻¹(chart source)`. -/
theorem apm_t01J04_bp_rho_comp_smooth
    (n m : ℕ) (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean m) (⊤ : ℕ∞) Y]
    (f : X → Y)
    (hf : ContMDiff 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, apm_t01J04_Euclidean m)
      (⊤ : ℕ∞) f) (y : Y) :
    ContMDiffOn 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x => apm_t01J04_bp_rho m y (f x))
      (f ⁻¹' (chartAt (apm_t01J04_Euclidean m) y).source) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun v : apm_t01J04_Euclidean m =>
      ‖v - chartAt (apm_t01J04_Euclidean m) y y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have h1 : ContMDiffOn 𝓘(ℝ, apm_t01J04_Euclidean m) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (apm_t01J04_bp_rho m y) (chartAt (apm_t01J04_Euclidean m) y).source :=
    hq.contMDiff.comp_contMDiffOn contMDiffOn_chart
  exact h1.comp hf.contMDiffOn (fun x hx => hx)

/-- LEAF A2 (Sard).  A function smooth on an open subset of a second-countable
manifold has a regular value in every interval `(0, a)`.  "Regular" means: the
manifold derivative is surjective at every point of the open set on that level.
Route: apply `T93A04ManifoldWork.null_critical` (imported, sorry-free) to `h`
restricted to the open submanifold `W` (a `TopologicalSpace.Opens`, second
countable), with `volume` on `ℝ`; the null critical-value set cannot contain
`Ioo 0 a`; compare `mfderiv` on `W` with `mfderiv` on `X` (open inclusion). -/
theorem apm_t01J04_leaf_sard_regular_value
    (n : ℕ) (X : Type*) [TopologicalSpace X] [SecondCountableTopology X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X]
    (W : Set X) (hW : IsOpen W) (h : X → ℝ)
    (hh : ContMDiffOn 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) h W)
    (a : ℝ) (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ r < a ∧ ∀ x ∈ W, h x = r →
      Function.Surjective (mfderiv 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) h x) := by
  let Wo : TopologicalSpace.Opens X := ⟨W, hW⟩
  let h' : Wo → ℝ := fun x => h x
  have hh' : ContMDiff 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ)
      (⊤ : ℕ∞) h' := by
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact (hh x x.2).contMDiffAt (hW.mem_nhds x.2)
  let C : Set ℝ := h' '' {x | ¬ Function.Surjective
    (mfderiv 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) h' x)}
  have hC : MeasureTheory.volume C = 0 :=
    T93A04ManifoldWork.null_critical MeasureTheory.volume h' hh'
  have hnot : ¬ Ioo (0 : ℝ) a ⊆ C := by
    intro hsub
    have hz : MeasureTheory.volume (Ioo (0 : ℝ) a) = 0 :=
      MeasureTheory.measure_mono_null hsub hC
    have hp : MeasureTheory.volume (Ioo (0 : ℝ) a) ≠ 0 := by
      simpa [Real.volume_Ioo] using ha
    exact hp hz
  obtain ⟨r, ⟨hr0, hra⟩, hrreg⟩ := Set.not_subset.mp hnot
  refine ⟨r, hr0, hra, ?_⟩
  intro x hx hxr
  by_contra hcrit
  apply hrreg
  refine ⟨⟨x, hx⟩, ?_, hxr⟩
  intro hs
  apply hcrit
  have hd := mfderiv_comp (⟨x, hx⟩ : Wo)
    (((hh x hx).contMDiffAt (hW.mem_nhds hx)).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val
      (I := 𝓘(ℝ, apm_t01J04_Euclidean n))
      (n := (1 : WithTop ℕ∞))).mdifferentiableAt (by simp))
  rw [show h' = h ∘ (Subtype.val : Wo → X) from rfl, hd] at hs
  exact Function.Surjective.of_comp hs

/-! ## Part B: ambient charts of `X` adapted to the sublevel set -/

/-- LEAF B1 (Euclidean interior model).  Around any point of an open subset of
`ℝⁿ` there is a smooth local diffeomorphism with values in `{v 0 > 0}`. -/
theorem apm_t01J04_leaf_euclidean_interior
    (n : ℕ) [NeZero n] (O : Set (apm_t01J04_Euclidean n)) (hO : IsOpen O)
    (p : apm_t01J04_Euclidean n) (hp : p ∈ O) :
    ∃ Φ : OpenPartialHomeomorph (apm_t01J04_Euclidean n) (apm_t01J04_Euclidean n),
      p ∈ Φ.source ∧ Φ.source ⊆ O ∧
      ContDiffOn ℝ (⊤ : ℕ∞) Φ Φ.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φ.symm Φ.target ∧
      ∀ v ∈ Φ.source, 0 < Φ v 0 := by
  let e : apm_t01J04_Euclidean n ≃ₜ apm_t01J04_Euclidean n :=
    Homeomorph.addLeft (EuclideanSpace.single (0 : Fin n) (1 : ℝ) - p)
  let S : Set (apm_t01J04_Euclidean n) := O ∩ {v | 0 < e v 0}
  have hcoord : Continuous (fun v : apm_t01J04_Euclidean n => v (0 : Fin n)) :=
    PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) (0 : Fin n)
  have hS : IsOpen S := hO.inter (isOpen_lt continuous_const
    (hcoord.comp e.continuous))
  let Φ : OpenPartialHomeomorph (apm_t01J04_Euclidean n)
      (apm_t01J04_Euclidean n) := e.toOpenPartialHomeomorph.restrOpen S hS
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · change p ∈ Set.univ ∩ S
    simp [S, e, hp]
  · intro v hv
    exact hv.2.1
  · have he : ContDiff ℝ (⊤ : ℕ∞) (e : apm_t01J04_Euclidean n →
        apm_t01J04_Euclidean n) := by
      simpa [e] using
        (contDiff_const.add contDiff_id : ContDiff ℝ (⊤ : ℕ∞)
          (fun v : apm_t01J04_Euclidean n =>
            (EuclideanSpace.single (0 : Fin n) (1 : ℝ) - p) + v))
    simpa [Φ] using he.contDiffOn
  · have hes : ContDiff ℝ (⊤ : ℕ∞) (e.symm : apm_t01J04_Euclidean n →
        apm_t01J04_Euclidean n) := by
      have h := (contDiff_const.add contDiff_id : ContDiff ℝ (⊤ : ℕ∞)
        (fun v : apm_t01J04_Euclidean n =>
          -(EuclideanSpace.single (0 : Fin n) (1 : ℝ) - p) + v))
      convert h using 1
    simpa [Φ] using hes.contDiffOn
  · intro v hv
    exact hv.2.2

/-- LEAF B2 (linear algebra).  A nonzero functional on `ℝⁿ` is, up to sign, the
first coordinate of some linear automorphism. -/
def apm_t01J04_leaf_linear_first_coordinate_aux_split
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V →ₗ[ℝ] ℝ) (u : V) (hu : f u = 1) :
    V ≃ₗ[ℝ] LinearMap.ker f × ℝ where
  toFun v := (⟨v - (f v) • u, by simp [hu]⟩, f v)
  invFun z := z.1.1 + z.2 • u
  left_inv v := by simp [hu]
  right_inv z := by
    ext
    · simp [hu]
    · simp [hu]
  map_add' x y := by
    ext <;> simp [add_smul] <;> module
  map_smul' c x := by
    ext <;> simp [mul_smul] <;> module

theorem apm_t01J04_leaf_linear_first_coordinate
    (n : ℕ) [NeZero n] (ℓ : apm_t01J04_Euclidean n →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ D : apm_t01J04_Euclidean n ≃L[ℝ] apm_t01J04_Euclidean n,
      ∀ v, D v 0 = -ℓ v := by
  let c : apm_t01J04_Euclidean n →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0
  have hc : c ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h (PiLp.single 2 (0 : Fin n) (1 : ℝ))
    simpa [c] using this
  have hℓs : Function.Surjective (ℓ : apm_t01J04_Euclidean n →ₗ[ℝ] ℝ) :=
    by
      obtain ⟨w, hw⟩ : ∃ w, ℓ w ≠ 0 := by
        simpa [DFunLike.ne_iff] using hℓ
      intro r
      refine ⟨(r / ℓ w) • w, ?_⟩
      simp [hw]
  obtain ⟨u, hu⟩ := hℓs 1
  have hℓ0 : (ℓ : apm_t01J04_Euclidean n →ₗ[ℝ] ℝ) ≠ 0 := by
    intro hz
    have hz' := LinearMap.congr_fun hz u
    simp [hu] at hz'
  have hcs : Function.Surjective c := by
    intro r
    refine ⟨PiLp.single 2 (0 : Fin n) r, ?_⟩
    simp [c]
  obtain ⟨e, he⟩ := hcs 1
  let A := apm_t01J04_leaf_linear_first_coordinate_aux_split
    (ℓ : apm_t01J04_Euclidean n →ₗ[ℝ] ℝ) u hu
  let B := apm_t01J04_leaf_linear_first_coordinate_aux_split c e he
  let N : LinearMap.ker (ℓ : apm_t01J04_Euclidean n →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      LinearMap.ker c := LinearEquiv.ofFinrankEq _ _ (by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero
      (f := (ℓ : apm_t01J04_Euclidean n →ₗ[ℝ] ℝ)) hℓ0
    have h2 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := c) hc
    omega)
  let E : apm_t01J04_Euclidean n ≃ₗ[ℝ] apm_t01J04_Euclidean n :=
    A.trans ((N.prodCongr (LinearEquiv.neg ℝ)).trans B.symm)
  refine ⟨E.toContinuousLinearEquiv, ?_⟩
  intro v
  change c (E v) = -ℓ v
  simp [E, A, B, N, he,
    apm_t01J04_leaf_linear_first_coordinate_aux_split]

/-- LEAF B3 (scalar submersion normal form in `ℝⁿ`).  If `g` is smooth on an
open set and `D` is an automorphism whose first coordinate is `-dg(p)`, then
near `p` there is a smooth local diffeomorphism whose first coordinate is
`g p - g`.  Route: the map `v ↦ D v + (g p - g v + dg(p) v) • e₀` has strict
derivative `D` at `p`; take `HasStrictFDerivAt.toOpenPartialHomeomorph` and shrink
it with the imported, sorry-free
`SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_neighborhood_restriction`. -/
theorem apm_t01J04_leaf_euclidean_normal_form
    (n : ℕ) [NeZero n] (g : apm_t01J04_Euclidean n → ℝ)
    (O : Set (apm_t01J04_Euclidean n)) (hO : IsOpen O)
    (p : apm_t01J04_Euclidean n) (hp : p ∈ O)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g O)
    (D : apm_t01J04_Euclidean n ≃L[ℝ] apm_t01J04_Euclidean n)
    (hD : ∀ v, D v 0 = -(fderiv ℝ g p) v) :
    ∃ Φ : OpenPartialHomeomorph (apm_t01J04_Euclidean n) (apm_t01J04_Euclidean n),
      p ∈ Φ.source ∧ Φ.source ⊆ O ∧
      ContDiffOn ℝ (⊤ : ℕ∞) Φ Φ.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φ.symm Φ.target ∧
      ∀ v ∈ Φ.source, Φ v 0 = g p - g v := by
  let e0 : apm_t01J04_Euclidean n := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  let L : apm_t01J04_Euclidean n →L[ℝ] ℝ := fderiv ℝ g p
  let q : apm_t01J04_Euclidean n → ℝ := fun v => g p - g v + L v
  let F : apm_t01J04_Euclidean n → apm_t01J04_Euclidean n :=
    fun v => D v + q v • e0
  have hgp : HasFDerivAt g L p := by
    exact ((hg p hp).contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt
  have hq : HasFDerivAt q
      (0 : apm_t01J04_Euclidean n →L[ℝ] ℝ) p := by
    have hlin : HasFDerivAt (fun v : apm_t01J04_Euclidean n => L v) L p :=
      L.hasFDerivAt
    convert ((hasFDerivAt_const (g p) p).sub hgp).add hlin using 1 <;>
      simp [q, L]
  have hFderiv : HasFDerivAt F (D : apm_t01J04_Euclidean n →L[ℝ]
      apm_t01J04_Euclidean n) p := by
    have hD' : HasFDerivAt (fun v : apm_t01J04_Euclidean n => D v)
        (D : apm_t01J04_Euclidean n →L[ℝ] apm_t01J04_Euclidean n) p :=
      D.toContinuousLinearMap.hasFDerivAt
    convert hD'.add (hq.smul_const e0) using 1 <;> simp [F]
  have hq_smooth : ContDiffOn ℝ (⊤ : ℕ∞) q O := by
    exact ((contDiffOn_const.sub hg).add L.contDiff.contDiffOn)
  have hF_smooth : ContDiffOn ℝ (⊤ : ℕ∞) F O := by
    exact D.contDiff.contDiffOn.add (hq_smooth.smul contDiffOn_const)
  have hF_at : ContDiffAt ℝ (⊤ : ℕ∞) F p :=
    (hF_smooth p hp).contDiffAt (hO.mem_nhds hp)
  let chart := hF_at.toOpenPartialHomeomorph F hFderiv (by simp)
  let U := O ∩ chart.source
  have hU : IsOpen U := hO.inter chart.open_source
  have hpchart : p ∈ chart.source := by
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source hF_at hFderiv (by simp)
  have hpU : p ∈ U := ⟨hp, hpchart⟩
  have hUs : U ⊆ chart.source := inter_subset_right
  have hchart_coe : (chart : apm_t01J04_Euclidean n → apm_t01J04_Euclidean n) = F := by
    exact ContDiffAt.toOpenPartialHomeomorph_coe hF_at hFderiv (by simp)
  have hchart_smooth : ContDiffOn ℝ (⊤ : ℕ∞) chart U := by
    rw [hchart_coe]
    exact hF_smooth.mono inter_subset_left
  have hchart_deriv : HasFDerivAt chart
      (D : apm_t01J04_Euclidean n →L[ℝ] apm_t01J04_Euclidean n) p := by
    rw [hchart_coe]
    exact hFderiv
  obtain ⟨Φ, hpΦ, hΦU, -, hΦeq, -, hΦ, hΦs⟩ :=
    SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_neighborhood_restriction
      chart U hU p hpU hUs hchart_smooth D hchart_deriv
  refine ⟨Φ, hpΦ, hΦU.trans inter_subset_left, hΦ, hΦs, ?_⟩
  intro v hv
  rw [show Φ v = chart v by rw [hΦeq]]
  rw [hchart_coe]
  simp [F, q, e0, hD]
  dsimp [L]
  ring

/-- LEAF B4 (maximal atlas).  Composing an ambient chart of the maximal atlas
with a smooth local diffeomorphism of the model gives a chart of the maximal
atlas. -/
theorem apm_t01J04_leaf_trans_mem_maximalAtlas
    (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X]
    (ψ₀ : OpenPartialHomeomorph X (apm_t01J04_Euclidean n))
    (hψ₀ : ψ₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X)
    (Φ : OpenPartialHomeomorph (apm_t01J04_Euclidean n) (apm_t01J04_Euclidean n))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Φ.source)
    (hΦs : ContDiffOn ℝ (⊤ : ℕ∞) Φ.symm Φ.target) :
    ψ₀.trans Φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X := by
  sorry

/-- LEAF B5 (chart glue).  A function smooth on an open set `W` of `X` is smooth
in the preferred chart at `x ∈ W`, and a surjective manifold derivative gives a
nonzero Euclidean derivative there. -/
theorem apm_t01J04_leaf_in_chart
    (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X]
    (W : Set X) (hW : IsOpen W) (h : X → ℝ)
    (hh : ContMDiffOn 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) h W)
    (x : X) (hx : x ∈ W) :
    ContDiffOn ℝ (⊤ : ℕ∞) (h ∘ (chartAt (apm_t01J04_Euclidean n) x).symm)
        ((chartAt (apm_t01J04_Euclidean n) x).target ∩
          (chartAt (apm_t01J04_Euclidean n) x).symm ⁻¹' W) ∧
      (Function.Surjective (mfderiv 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) h x) →
        fderiv ℝ (h ∘ (chartAt (apm_t01J04_Euclidean n) x).symm)
          (chartAt (apm_t01J04_Euclidean n) x x) ≠ 0) := by
  sorry

/-- Bookkeeping: preferred chart followed by a Euclidean local diffeomorphism. -/
theorem apm_t01J04_bp_ambient_chart
    (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X]
    (O : Set X) (x : X)
    (Φ : OpenPartialHomeomorph (apm_t01J04_Euclidean n) (apm_t01J04_Euclidean n))
    (hxΦ : chartAt (apm_t01J04_Euclidean n) x x ∈ Φ.source)
    (hΦO : Φ.source ⊆ (chartAt (apm_t01J04_Euclidean n) x).target ∩
      (chartAt (apm_t01J04_Euclidean n) x).symm ⁻¹' O)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Φ.source)
    (hΦs : ContDiffOn ℝ (⊤ : ℕ∞) Φ.symm Φ.target) :
    ∃ ψ : OpenPartialHomeomorph X (apm_t01J04_Euclidean n),
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X ∧
      x ∈ ψ.source ∧ ψ.source ⊆ O ∧
      ∀ z ∈ ψ.source, ψ z = Φ (chartAt (apm_t01J04_Euclidean n) x z) ∧
        chartAt (apm_t01J04_Euclidean n) x z ∈ Φ.source ∧
        (chartAt (apm_t01J04_Euclidean n) x).symm
          (chartAt (apm_t01J04_Euclidean n) x z) = z := by
  set ψ₀ := chartAt (apm_t01J04_Euclidean n) x
  refine ⟨ψ₀.trans Φ, apm_t01J04_leaf_trans_mem_maximalAtlas n X ψ₀
    (IsManifold.chart_mem_maximalAtlas x) Φ hΦ hΦs, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source _ x, hxΦ⟩
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have h2 := (hΦO hz.2).2
    rwa [mem_preimage, ψ₀.left_inv hz.1] at h2
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact ⟨rfl, hz.2, ψ₀.left_inv hz.1⟩

/-- Interior points: an ambient chart inside an open set, with positive first
coordinate. -/
theorem apm_t01J04_bp_interior_chart
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X]
    (O : Set X) (hO : IsOpen O) (x : X) (hx : x ∈ O) :
    ∃ ψ : OpenPartialHomeomorph X (apm_t01J04_Euclidean n),
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X ∧
      x ∈ ψ.source ∧ ψ.source ⊆ O ∧ ∀ z ∈ ψ.source, 0 < ψ z 0 := by
  set ψ₀ := chartAt (apm_t01J04_Euclidean n) x
  have hO' : IsOpen (ψ₀.target ∩ ψ₀.symm ⁻¹' O) := ψ₀.isOpen_inter_preimage_symm hO
  have hp : ψ₀ x ∈ ψ₀.target ∩ ψ₀.symm ⁻¹' O :=
    ⟨ψ₀.map_source (mem_chart_source _ x), by
      rw [mem_preimage, ψ₀.left_inv (mem_chart_source _ x)]; exact hx⟩
  obtain ⟨Φ, hpΦ, hΦO, hΦ, hΦs, hpos⟩ :=
    apm_t01J04_leaf_euclidean_interior n _ hO' _ hp
  obtain ⟨ψ, hψ, hxψ, hψO, hψeq⟩ :=
    apm_t01J04_bp_ambient_chart n X O x Φ hpΦ hΦO hΦ hΦs
  refine ⟨ψ, hψ, hxψ, hψO, fun z hz => ?_⟩
  obtain ⟨h1, h2, -⟩ := hψeq z hz
  rw [h1]
  exact hpos _ h2

/-- Boundary points: at a regular point `x` of `h`, an ambient chart inside `W`
whose first coordinate is `h x - h`. -/
theorem apm_t01J04_bp_boundary_chart
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X]
    (W : Set X) (hW : IsOpen W) (h : X → ℝ)
    (hh : ContMDiffOn 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) h W)
    (x : X) (hx : x ∈ W)
    (hreg : Function.Surjective (mfderiv 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, ℝ) h x)) :
    ∃ ψ : OpenPartialHomeomorph X (apm_t01J04_Euclidean n),
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X ∧
      x ∈ ψ.source ∧ ψ.source ⊆ W ∧ ∀ z ∈ ψ.source, ψ z 0 = h x - h z := by
  set ψ₀ := chartAt (apm_t01J04_Euclidean n) x
  obtain ⟨hg, hne⟩ := apm_t01J04_leaf_in_chart n X W hW h hh x hx
  have hO : IsOpen (ψ₀.target ∩ ψ₀.symm ⁻¹' W) := ψ₀.isOpen_inter_preimage_symm hW
  have hp : ψ₀ x ∈ ψ₀.target ∩ ψ₀.symm ⁻¹' W :=
    ⟨ψ₀.map_source (mem_chart_source _ x), by
      rw [mem_preimage, ψ₀.left_inv (mem_chart_source _ x)]; exact hx⟩
  obtain ⟨D, hD⟩ := apm_t01J04_leaf_linear_first_coordinate n _ (hne hreg)
  obtain ⟨Φ, hpΦ, hΦO, hΦ, hΦs, hΦ0⟩ :=
    apm_t01J04_leaf_euclidean_normal_form n (h ∘ ψ₀.symm) _ hO (ψ₀ x) hp hg D hD
  obtain ⟨ψ, hψ, hxψ, hψW, hψeq⟩ :=
    apm_t01J04_bp_ambient_chart n X W x Φ hpΦ hΦO hΦ hΦs
  refine ⟨ψ, hψ, hxψ, hψW, fun z hz => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hψeq z hz
  rw [h1, hΦ0 _ h2]
  simp only [Function.comp_apply, ψ₀.left_inv (mem_chart_source _ x)]
  exact congrArg (fun t => h x - h t) h3

/-! ## Part C: the half-space atlas on the subtype -/

/-- An ambient chart of the maximal atlas of `X` together with its restriction to
`S`, which takes values in the half-space. -/
structure apm_t01J04_bp_HalfSliceChart (n : ℕ) [NeZero n] (X : Type*)
    [TopologicalSpace X] [ChartedSpace (apm_t01J04_Euclidean n) X] (S : Set X) where
  amb : OpenPartialHomeomorph X (apm_t01J04_Euclidean n)
  amb_mem : amb ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X
  chart : OpenPartialHomeomorph {x // x ∈ S} (EuclideanHalfSpace n)
  source_eq : chart.source = Subtype.val ⁻¹' amb.source
  target_eq : chart.target = Subtype.val ⁻¹' amb.target
  chart_eq : ∀ u ∈ chart.source, (chart u).val = amb u.val
  symm_eq : ∀ z ∈ chart.target, (chart.symm z).val = amb.symm z.val

/-- LEAF C1 (restriction).  An ambient chart in which `S` is exactly the
half-space `{v 0 ≥ 0}` restricts to a half-space chart of the subtype `S`.
(The point `x₀ ∈ S` is only needed for the junk value of the inverse.) -/
-- BEGIN SEAT AREA
theorem apm_t01J04_leaf_restrict_chart
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X] (S : Set X) (x₀ : X) (hx₀ : x₀ ∈ S)
    (ψ : OpenPartialHomeomorph X (apm_t01J04_Euclidean n))
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X)
    (hslice : ∀ z ∈ ψ.source, z ∈ S ↔ 0 ≤ ψ z 0) :
    ∃ d : apm_t01J04_bp_HalfSliceChart n X S, d.amb = ψ := by
  classical
  let f : {x // x ∈ S} → EuclideanHalfSpace n := fun u =>
    if hu : u.1 ∈ ψ.source then
      ⟨ψ u.1, (hslice u.1 hu).mp u.2⟩
    else 0
  let g : EuclideanHalfSpace n → {x // x ∈ S} := fun v =>
    if hv : v.1 ∈ ψ.target then
      ⟨ψ.symm v.1, (hslice ( ψ.symm v.1) (ψ.map_target hv)).mpr (by
        rw [ψ.right_inv hv]
        exact v.2)⟩
    else ⟨x₀, hx₀⟩
  let c : OpenPartialHomeomorph {x // x ∈ S} (EuclideanHalfSpace n) := {
    source := Subtype.val ⁻¹' ψ.source
    target := Subtype.val ⁻¹' ψ.target
    toFun := f
    invFun := g
    map_source' := by
      intro u hu
      change u.1 ∈ ψ.source at hu
      dsimp [f]
      rw [dif_pos hu]
      exact ψ.map_source hu
    map_target' := by
      intro v hv
      change v.1 ∈ ψ.target at hv
      dsimp [g]
      rw [dif_pos hv]
      exact ψ.map_target hv
    left_inv' := by
      intro u hu
      change u.1 ∈ ψ.source at hu
      apply Subtype.ext
      dsimp [g, f]
      simp only [dif_pos hu]
      simp only [dif_pos (ψ.map_source hu)]
      exact ψ.left_inv hu
    right_inv' := by
      intro v hv
      change v.1 ∈ ψ.target at hv
      apply EuclideanHalfSpace.ext
      dsimp [g, f]
      simp only [dif_pos hv]
      simp only [dif_pos (ψ.map_target hv)]
      exact ψ.right_inv hv
    open_source := ψ.open_source.preimage continuous_subtype_val
    open_target := ψ.open_target.preimage continuous_subtype_val
    continuousOn_toFun := by
      rw [continuousOn_iff_continuous_restrict]
      have h : ContinuousOn (fun u : {x // x ∈ S} => ψ u.1)
          (Subtype.val ⁻¹' ψ.source) :=
        ψ.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h)
      rw [continuousOn_iff_continuous_restrict] at h
      convert Continuous.subtype_mk (p := fun x : apm_t01J04_Euclidean n => 0 ≤ x 0) h
        (fun u => (hslice u.1.1 u.2).mp u.1.2) using 1
      ext u
      have hu : u.1.1 ∈ ψ.source := u.2
      dsimp [f]
      simp only [dif_pos hu]
    continuousOn_invFun := by
      rw [continuousOn_iff_continuous_restrict]
      have h : ContinuousOn (fun v : EuclideanHalfSpace n => ψ.symm v.1)
          (Subtype.val ⁻¹' ψ.target) :=
        ψ.continuousOn_symm.comp continuous_subtype_val.continuousOn (fun _ h => h)
      rw [continuousOn_iff_continuous_restrict] at h
      convert Continuous.subtype_mk (p := fun x : X => x ∈ S) h
        (fun v => (hslice (ψ.symm v.1.1) (ψ.map_target v.2)).mpr (by
          rw [ψ.right_inv v.2]
          exact v.1.2)) using 1
      ext v
      have hv : v.1.1 ∈ ψ.target := v.2
      dsimp [g]
      simp only [dif_pos hv]
  }
  refine ⟨⟨ψ, hψ, c, rfl, rfl, ?_, ?_⟩, rfl⟩
  · intro u hu
    change u.1 ∈ ψ.source at hu
    dsimp [c, f]
    rw [dif_pos hu]
  · intro v hv
    change v.1 ∈ ψ.target at hv
    dsimp [c, g]
    rw [dif_pos hv]
-- END SEAT AREA

/-- LEAF C2 (overlaps).  Transition maps between restricted charts are smooth in
the sense of the half-space model. -/
theorem apm_t01J04_leaf_overlap
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X] (S : Set X)
    (d d' : apm_t01J04_bp_HalfSliceChart n X S) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (modelWithCornersEuclideanHalfSpace n ∘ (d.chart.symm ≫ₕ d'.chart) ∘
        (modelWithCornersEuclideanHalfSpace n).symm)
      ((modelWithCornersEuclideanHalfSpace n).symm ⁻¹' (d.chart.symm ≫ₕ d'.chart).source ∩
        range (modelWithCornersEuclideanHalfSpace n)) := by
  sorry

/-- The charted space on `S` given by a choice of restricted chart at each point. -/
@[reducible] def apm_t01J04_bp_charted
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X] (S : Set X)
    (d : {x // x ∈ S} → apm_t01J04_bp_HalfSliceChart n X S)
    (hd : ∀ u, u ∈ (d u).chart.source) :
    ChartedSpace (EuclideanHalfSpace n) {x // x ∈ S} where
  atlas := range fun u => (d u).chart
  chartAt u := (d u).chart
  mem_chart_source := hd
  chart_mem_atlas u := ⟨u, rfl⟩

theorem apm_t01J04_bp_isManifold
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X] (S : Set X)
    (d : {x // x ∈ S} → apm_t01J04_bp_HalfSliceChart n X S)
    (hd : ∀ u, u ∈ (d u).chart.source) :
    letI := apm_t01J04_bp_charted n X S d hd
    IsManifold (modelWithCornersEuclideanHalfSpace n) (⊤ : ℕ∞) {x // x ∈ S} := by
  letI := apm_t01J04_bp_charted n X S d hd
  apply isManifold_of_contDiffOn
  rintro e e' ⟨u, rfl⟩ ⟨u', rfl⟩
  exact apm_t01J04_leaf_overlap n X S (d u) (d u')

/-- LEAF C3 (smooth inclusion).  For the restricted atlas, `Subtype.val` is smooth
into `X`: in charts it is the ambient transition map `chartAt (u.val) ∘ amb.symm`,
restricted to the half-space.  `hS` is supplied by the assembly (it is
`apm_t01J04_bp_isManifold`), so that the `…_of_mem_maximalAtlas` API is usable. -/
theorem apm_t01J04_leaf_smooth_inclusion
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X] (S : Set X)
    (d : {x // x ∈ S} → apm_t01J04_bp_HalfSliceChart n X S)
    (hd : ∀ u, u ∈ (d u).chart.source)
    (hS : letI := apm_t01J04_bp_charted n X S d hd
      IsManifold (modelWithCornersEuclideanHalfSpace n) (⊤ : ℕ∞) {x // x ∈ S}) :
    letI := apm_t01J04_bp_charted n X S d hd
    ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, apm_t01J04_Euclidean n)
      (⊤ : ℕ∞) (Subtype.val : {x // x ∈ S} → X) := by
  sorry

/-- LEAF C4 (immersion).  For the restricted atlas, the manifold derivative of
`Subtype.val` is injective at every point: in charts it is the derivative of an
ambient transition map (an isomorphism), taken within the half-space, which has
unique derivatives.  `hsm` (the conclusion of leaf C3, passed in by the assembly)
gives `MDifferentiableAt`, so `mfderiv` is the honest `fderivWithin`. -/
theorem apm_t01J04_leaf_injective_mfderiv
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X] (S : Set X)
    (d : {x // x ∈ S} → apm_t01J04_bp_HalfSliceChart n X S)
    (hd : ∀ u, u ∈ (d u).chart.source)
    (hsm : letI := apm_t01J04_bp_charted n X S d hd
      ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, apm_t01J04_Euclidean n)
        (⊤ : ℕ∞) (Subtype.val : {x // x ∈ S} → X)) :
    letI := apm_t01J04_bp_charted n X S d hd
    ∀ z, Function.Injective (mfderiv (modelWithCornersEuclideanHalfSpace n)
      𝓘(ℝ, apm_t01J04_Euclidean n) (Subtype.val : {x // x ∈ S} → X) z) := by
  sorry

/-- A set covered by ambient half-space slice charts is an embedded smooth
manifold with boundary, in the sense of the registered predicate. -/
theorem apm_t01J04_bp_predicate_of_cover
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X] (S : Set X)
    (hcov : ∀ x ∈ S, ∃ ψ : OpenPartialHomeomorph X (apm_t01J04_Euclidean n),
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X ∧
      x ∈ ψ.source ∧ ∀ z ∈ ψ.source, z ∈ S ↔ 0 ≤ ψ z 0) :
    apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) {x // x ∈ S} Subtype.val := by
  have hd : ∀ u : {x // x ∈ S}, ∃ d : apm_t01J04_bp_HalfSliceChart n X S,
      u ∈ d.chart.source := by
    intro u
    obtain ⟨ψ, hψ, hu, hsl⟩ := hcov u.1 u.2
    obtain ⟨d, rfl⟩ := apm_t01J04_leaf_restrict_chart n X S u.1 u.2 ψ hψ hsl
    exact ⟨d, by rw [d.source_eq]; exact hu⟩
  choose d hd using hd
  have hman := apm_t01J04_bp_isManifold n X S d hd
  have hsm := apm_t01J04_leaf_smooth_inclusion n X S d hd hman
  exact Or.inr ⟨inferInstance, apm_t01J04_bp_charted n X S d hd, hman, hsm,
    apm_t01J04_leaf_injective_mfderiv n X S d hd hsm⟩

/-! ## Assembly -/

/-- The positive-dimensional case. -/
theorem apm_t01J04_bp_positive
    (n m : ℕ) [NeZero n] (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X]
    [IsManifold 𝓘(ℝ, apm_t01J04_Euclidean m) (⊤ : ℕ∞) Y]
    (f : X → Y)
    (hf : ContMDiff 𝓘(ℝ, apm_t01J04_Euclidean n) 𝓘(ℝ, apm_t01J04_Euclidean m)
      (⊤ : ℕ∞) f)
    (y : Y) (U : Set Y) (hU : U ∈ 𝓝 y) :
    ∃ V : Set Y, V ∈ 𝓝 y ∧ closure V ⊆ U ∧
      apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X
        (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
        {x : X // x ∈ f ⁻¹' closure V} Subtype.val := by
  obtain ⟨a, ha, hball⟩ := apm_t01J04_leaf_chart_ball m Y y U hU
  set W : Set X := f ⁻¹' (chartAt (apm_t01J04_Euclidean m) y).source with hWdef
  have hW : IsOpen W :=
    hf.continuous.isOpen_preimage _ (chartAt (apm_t01J04_Euclidean m) y).open_source
  set h : X → ℝ := fun x => apm_t01J04_bp_rho m y (f x) with hdef
  have hh := apm_t01J04_bp_rho_comp_smooth n m X Y f hf y
  obtain ⟨r, hr0, hra, hreg⟩ := apm_t01J04_leaf_sard_regular_value n X W hW h hh a ha
  obtain ⟨hVn, hVU, hVeq⟩ := hball r hr0 hra
  refine ⟨apm_t01J04_bp_ball m y r, hVn, hVU, ?_⟩
  have hS : f ⁻¹' closure (apm_t01J04_bp_ball m y r) = {x | x ∈ W ∧ h x ≤ r} := by
    rw [hVeq]; rfl
  rw [hS]
  apply apm_t01J04_bp_predicate_of_cover
  rintro x ⟨hxW, hxr⟩
  rcases lt_or_eq_of_le hxr with hlt | heq
  · have hO : IsOpen (W ∩ h ⁻¹' Iio r) :=
      hh.continuousOn.isOpen_inter_preimage hW isOpen_Iio
    obtain ⟨ψ, hψ, hxψ, hψO, hpos⟩ :=
      apm_t01J04_bp_interior_chart n X _ hO x ⟨hxW, hlt⟩
    refine ⟨ψ, hψ, hxψ, fun z hz => ?_⟩
    have hz' := hψO hz
    exact ⟨fun _ => (hpos z hz).le, fun _ => ⟨hz'.1, le_of_lt hz'.2⟩⟩
  · obtain ⟨ψ, hψ, hxψ, hψW, hψ0⟩ :=
      apm_t01J04_bp_boundary_chart n X W hW h hh x hxW (hreg x hxW heq)
    refine ⟨ψ, hψ, hxψ, fun z hz => ?_⟩
    rw [hψ0 z hz, heq]
    constructor
    · rintro ⟨-, hz'⟩
      linarith
    · intro h0
      exact ⟨hψW hz, by linarith⟩

theorem apm_t01j04
    (n m : ℕ)
    (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace Y]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
      (⊤ : ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m))
      (⊤ : ℕ∞) Y]
    [BoundarylessManifold
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) X]
    [BoundarylessManifold
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) Y]
    (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) f)
    (y : Y) (U : Set Y) (hU : U ∈ nhds y) :
    ∃ V : Set Y,
      V ∈ nhds y ∧
      closure V ⊆ U ∧
      apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X
        (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
        {x : X // x ∈ f ⁻¹' closure V} Subtype.val := by
  by_cases hn : n = 0
  · subst n
    letI : DiscreteTopology X := ChartedSpace.discreteTopology
      (apm_t01J04_Euclidean 0) X
    obtain ⟨V, hVy, hVclosed, hVU⟩ := exists_mem_nhds_isClosed_subset hU
    refine ⟨V, hVy, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · rwa [hVclosed.closure_eq]
    · let charts : ChartedSpace (apm_t01J04_Euclidean 0)
          {x : X // x ∈ f ⁻¹' closure V} :=
        ChartedSpace.of_discreteTopology
      refine ⟨charts, ?_, ?_, ?_⟩
      · exact IsManifold.of_discreteTopology _
      · exact contMDiff_of_discreteTopology
      · intro z v w hvw
        unfold TangentSpace at v w
        exact Subsingleton.elim v w
  · haveI : NeZero n := ⟨hn⟩
    exact apm_t01J04_bp_positive n m X Y f hf y U hU

end

#print axioms apm_t01j04
#print axioms T93A04ManifoldWork.null_critical
#print axioms SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_neighborhood_restriction
