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
  sorry

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
  sorry

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
  sorry

/-- LEAF B2 (linear algebra).  A nonzero functional on `ℝⁿ` is, up to sign, the
first coordinate of some linear automorphism. -/
theorem apm_t01J04_leaf_linear_first_coordinate
    (n : ℕ) [NeZero n] (ℓ : apm_t01J04_Euclidean n →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ D : apm_t01J04_Euclidean n ≃L[ℝ] apm_t01J04_Euclidean n,
      ∀ v, D v 0 = -ℓ v := by
  sorry

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
  sorry

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
theorem apm_t01J04_leaf_restrict_chart
    (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X] (S : Set X) (x₀ : X) (hx₀ : x₀ ∈ S)
    (ψ : OpenPartialHomeomorph X (apm_t01J04_Euclidean n))
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, apm_t01J04_Euclidean n) (⊤ : ℕ∞) X)
    (hslice : ∀ z ∈ ψ.source, z ∈ S ↔ 0 ≤ ψ z 0) :
    ∃ d : apm_t01J04_bp_HalfSliceChart n X S, d.amb = ψ := by
  sorry

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
