import Mathlib
import ConstructionTargets.RadialSquaredFiber
import ConstructionTargets.ManifoldRegularFiberGlobalAtlas
import ConstructionTargets.TransverseIncidenceChosenAtlas
import ConstructionTargets.SardGenuineSmoothManifoldVector

/-! # Blueprint for APM t96J05 -/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t96j05_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t96j05_I (n : ℕ) := 𝓘(ℝ, apm_t96j05_E n)

def apm_t96j05_IsEmbeddedSmoothSubmanifold {m n : ℕ}
    (X : Set (apm_t96j05_E n)) : Prop :=
  ∃ charts : ChartedSpace (apm_t96j05_E m) X,
    let _ := charts
    IsManifold (apm_t96j05_I m) ∞ X ∧
    ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ∞
      (fun x : X ↦ x.1)

abbrev apm_t96j05_radialLevel {n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) :=
  {x : X // ‖x.1‖ = r}

def apm_t96j05_IsEmbeddedSmoothRadialLevel {m n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) : Prop :=
  ∃ k : ℕ, k ≤ m ∧ ∃ charts : ChartedSpace (apm_t96j05_E k)
      (apm_t96j05_radialLevel X r),
    letI := charts
    IsManifold (apm_t96j05_I k) ∞
        (apm_t96j05_radialLevel X r) ∧
      ContMDiff (apm_t96j05_I k) (apm_t96j05_I n) ∞
        (fun x : apm_t96j05_radialLevel X r ↦ x.1.1)

/-- The constant-radius branch: the radial level is all of `X`, so its
existing atlas and smooth ambient inclusion transport to the literal subtype. -/
theorem apm_t96j05_constant_radius_level
    {m n : ℕ} {X : Set (apm_t96j05_E n)}
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X)
    {r : ℝ} (hr : 0 < r) (hall : ∀ x : X, ‖x.1‖ = r) :
    Nonempty X →
      Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsEmbeddedSmoothRadialLevel (m := m) X r := by
  intro hne
  rcases hX with ⟨charts, hman, hinc⟩
  letI : ChartedSpace (apm_t96j05_E m) X := charts
  letI : IsManifold (apm_t96j05_I m) ∞ X := hman
  let U : TopologicalSpace.Opens X :=
    ⟨{x : X | ‖x.1‖ = r}, by
      have hu : {x : X | ‖x.1‖ = r} = Set.univ := by
        ext x
        simp [hall x]
      rw [hu]
      exact isOpen_univ⟩
  letI : ChartedSpace (apm_t96j05_E m) U := inferInstance
  have hlevel : Nonempty (apm_t96j05_radialLevel X r) := by
    rcases hne with ⟨x⟩
    exact ⟨⟨x, hall x⟩⟩
  let chartsU : ChartedSpace (apm_t96j05_E m)
      (apm_t96j05_radialLevel X r) := by
    change ChartedSpace (apm_t96j05_E m) U
    infer_instance
  refine ⟨hlevel, m, le_rfl, ?_⟩
  refine ⟨chartsU, ?_, ?_⟩
  · change IsManifold (apm_t96j05_I m) ∞ U
    infer_instance
  change ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ∞
    ((fun x : X ↦ x.1) ∘ (fun x : U ↦ x.1))
  exact hinc.comp contMDiff_subtype_val

/-- LIBRARY (manifold Sard plus connected-image selection).  For a smooth
squared-radius map which is not constant on a positive sphere, choose an
attained positive radius at which its manifold derivative is surjective. -/
lemma apm_t96j05_exists_regular_radius_aux_nontrivial
    {m n : ℕ} (hm : 0 < m) {X : Set (apm_t96j05_E n)}
    [Nonempty X] [ChartedSpace (apm_t96j05_E m) X]
    [IsManifold (apm_t96j05_I m) ∞ X] : Nontrivial X := by
  let x : X := Classical.choice inferInstance
  have hdim : 0 < Module.finrank ℝ (apm_t96j05_E m) := by simpa using hm
  letI : Nontrivial (apm_t96j05_E m) :=
    Module.nontrivial_of_finrank_pos hdim
  by_contra h
  haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
  have ht : (chartAt (apm_t96j05_E m) x).target =
      ({chartAt (apm_t96j05_E m) x x} : Set (apm_t96j05_E m)) := by
    ext y
    constructor
    · intro hy
      have hs : (chartAt (apm_t96j05_E m) x).symm y = x := Subsingleton.elim _ _
      rw [Set.mem_singleton_iff]
      calc
        y = chartAt (apm_t96j05_E m) x
            ((chartAt (apm_t96j05_E m) x).symm y) :=
          ((chartAt (apm_t96j05_E m) x).right_inv hy).symm
        _ = chartAt (apm_t96j05_E m) x x := congrArg _ hs
    · intro hy
      rw [Set.mem_singleton_iff.mp hy]
      exact (chartAt (apm_t96j05_E m) x).map_source
        (mem_chart_source (apm_t96j05_E m) x)
  have hopen : IsOpen ({chartAt (apm_t96j05_E m) x x} :
      Set (apm_t96j05_E m)) := ht ▸ (chartAt (apm_t96j05_E m) x).open_target
  exact not_isOpen_singleton _ hopen

lemma apm_t96j05_exists_regular_radius_aux_nonconstant
    {m n : ℕ} (hm : 0 < m) {X : Set (apm_t96j05_E n)}
    [Nonempty X] [ChartedSpace (apm_t96j05_E m) X]
    [IsManifold (apm_t96j05_I m) ∞ X]
    (hnconst : ¬ ∃ r : ℝ, 0 < r ∧ ∀ x : X, ‖x.1‖ = r) :
    ¬ ∃ c : ℝ, ∀ x : X, ‖x.1‖ ^ 2 = c := by
  letI : Nontrivial X := apm_t96j05_exists_regular_radius_aux_nontrivial hm
  rintro ⟨c, hc⟩
  have hc0 : 0 ≤ c := by
    rw [← hc (Classical.choice (inferInstance : Nonempty X))]
    exact sq_nonneg _
  rcases hc0.eq_or_lt with hcz | hcpos
  · have hall0 : ∀ x : X, x.1 = 0 := by
      intro x
      have hs : ‖x.1‖ ^ 2 = 0 := (hc x).trans hcz.symm
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    apply hxy
    apply Subtype.ext
    rw [hall0 x, hall0 y]
  · apply hnconst
    refine ⟨Real.sqrt c, Real.sqrt_pos.2 hcpos, ?_⟩
    intro x
    apply (sq_eq_sq₀ (norm_nonneg x.1) (Real.sqrt_nonneg c)).mp
    rw [Real.sq_sqrt hc0]
    exact hc x

-- BEGIN SEAT AREA
theorem apm_t96j05_exists_regular_radius
    {m n : ℕ} (hm : 0 < m) {X : Set (apm_t96j05_E n)}
    [Nonempty X] [ChartedSpace (apm_t96j05_E m) X]
    [IsManifold (apm_t96j05_I m) ∞ X]
    (hconn : IsConnected (Set.univ : Set X))
    (hsm : ContMDiff (apm_t96j05_I m) 𝓘(ℝ, ℝ) ∞
      (fun x : X => ‖x.1‖ ^ 2))
    (hnconst : ¬ ∃ r : ℝ, 0 < r ∧ ∀ x : X, ‖x.1‖ = r) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty (apm_t96j05_radialLevel X r) ∧
      ∀ x : X, ‖x.1‖ ^ 2 = r ^ 2 →
        Function.Surjective
          (mfderiv (apm_t96j05_I m) 𝓘(ℝ, ℝ)
            (fun y : X => ‖y.1‖ ^ 2) x) := by
  let f : X → ℝ := fun x => ‖x.1‖ ^ 2
  have hnonconstant : ¬ ∃ c : ℝ, ∀ x : X, f x = c := by
    simpa [f] using apm_t96j05_exists_regular_radius_aux_nonconstant hm hnconst
  have hxy : ∃ x y : X, f x ≠ f y := by
    by_contra h
    push_neg at h
    apply hnonconstant
    refine ⟨f (Classical.choice (inferInstance : Nonempty X)), ?_⟩
    intro x
    exact h x _
  obtain ⟨x, y, hxy⟩ := hxy
  obtain hlt | hlt := lt_or_gt_of_ne hxy
  · let a := f x
    let b := f y
    have hab : a < b := hlt
    have hrange : Set.Ioo a b ⊆ Set.range f := by
      intro c hc
      have hi : c ∈ Set.Icc (f x) (f y) := ⟨hc.1.le, hc.2.le⟩
      obtain ⟨z, -, hz⟩ := hconn.isPreconnected.intermediate_value
        (Set.mem_univ x) (Set.mem_univ y) hsm.continuous.continuousOn hi
      exact ⟨z, hz⟩
    let C : Set ℝ := f '' {z | ¬ Function.Surjective
      (mfderiv (apm_t96j05_I m) 𝓘(ℝ, ℝ) f z)}
    have hC : MeasureTheory.volume C = 0 :=
      T93A04ManifoldWork.null_critical MeasureTheory.volume f hsm
    have hnot : ¬ Set.Ioo a b ⊆ C := by
      intro hsub
      have hz : MeasureTheory.volume (Set.Ioo a b) = 0 :=
        MeasureTheory.measure_mono_null hsub hC
      have hp : MeasureTheory.volume (Set.Ioo a b) ≠ 0 := by
        simpa [Real.volume_Ioo] using hab
      exact hp hz
    obtain ⟨c, hc, hcreg⟩ := Set.not_subset.mp hnot
    obtain ⟨z, hz⟩ := hrange hc
    have ha0 : 0 ≤ a := sq_nonneg ‖x.1‖
    have hc0 : 0 < c := ha0.trans_lt hc.1
    have hsqrt : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc0.le
    refine ⟨Real.sqrt c, Real.sqrt_pos.2 hc0, ?_, ?_⟩
    · refine ⟨⟨z, ?_⟩⟩
      apply (sq_eq_sq₀ (norm_nonneg z.1) (Real.sqrt_nonneg c)).mp
      rw [hsqrt]
      exact hz
    · intro w hw
      by_contra hwcrit
      apply hcreg
      refine ⟨w, hwcrit, ?_⟩
      change f w = c
      exact hw.trans hsqrt
  · let a := f y
    let b := f x
    have hab : a < b := hlt
    have hrange : Set.Ioo a b ⊆ Set.range f := by
      intro c hc
      have hi : c ∈ Set.Icc (f y) (f x) := ⟨hc.1.le, hc.2.le⟩
      obtain ⟨z, -, hz⟩ := hconn.isPreconnected.intermediate_value
        (Set.mem_univ y) (Set.mem_univ x) hsm.continuous.continuousOn hi
      exact ⟨z, hz⟩
    let C : Set ℝ := f '' {z | ¬ Function.Surjective
      (mfderiv (apm_t96j05_I m) 𝓘(ℝ, ℝ) f z)}
    have hC : MeasureTheory.volume C = 0 :=
      T93A04ManifoldWork.null_critical MeasureTheory.volume f hsm
    have hnot : ¬ Set.Ioo a b ⊆ C := by
      intro hsub
      have hz : MeasureTheory.volume (Set.Ioo a b) = 0 :=
        MeasureTheory.measure_mono_null hsub hC
      have hp : MeasureTheory.volume (Set.Ioo a b) ≠ 0 := by
        simpa [Real.volume_Ioo] using hab
      exact hp hz
    obtain ⟨c, hc, hcreg⟩ := Set.not_subset.mp hnot
    obtain ⟨z, hz⟩ := hrange hc
    have ha0 : 0 ≤ a := sq_nonneg ‖y.1‖
    have hc0 : 0 < c := ha0.trans_lt hc.1
    have hsqrt : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc0.le
    refine ⟨Real.sqrt c, Real.sqrt_pos.2 hc0, ?_, ?_⟩
    · refine ⟨⟨z, ?_⟩⟩
      apply (sq_eq_sq₀ (norm_nonneg z.1) (Real.sqrt_nonneg c)).mp
      rw [hsqrt]
      exact hz
    · intro w hw
      by_contra hwcrit
      apply hcreg
      refine ⟨w, hwcrit, ?_⟩
      change f w = c
      exact hw.trans hsqrt
-- END SEAT AREA

/-- A positive attained regular squared-radius fiber has the required global
atlas and smooth inclusion after fixed-model and predicate transport. -/
theorem apm_t96j05_regular_radius_level
    {m n : ℕ} {X : Set (apm_t96j05_E n)}
    [ChartedSpace (apm_t96j05_E m) X]
    [IsManifold (apm_t96j05_I m) ∞ X]
    (hinc : ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ∞
      (fun x : X ↦ x.1))
    {r : ℝ} (hr : 0 < r)
    (hlevel : Nonempty (apm_t96j05_radialLevel X r))
    (hsm : ContMDiff (apm_t96j05_I m) 𝓘(ℝ, ℝ) ∞
      (fun x : X => ‖x.1‖ ^ 2))
    (hreg : ∀ x : X, ‖x.1‖ ^ 2 = r ^ 2 →
      Function.Surjective
        (mfderiv (apm_t96j05_I m) 𝓘(ℝ, ℝ)
          (fun y : X => ‖y.1‖ ^ 2) x)) :
    apm_t96j05_IsEmbeddedSmoothRadialLevel (m := m) X r := by
  let f : X → ℝ := fun x => ‖x.1‖ ^ 2
  let P : X → Prop := fun x => f x = r ^ 2
  let Q : X → Prop := fun x => ‖x.1‖ = r
  have hPQ : P = Q := by
    funext x
    exact propext
      (ConstructionTargets.RadialSquaredFiber.norm_sq_eq_sq_iff hr)
  let fiberAtlas : ChartedSpace
      (ConstructionTargets.ManifoldRegularFiberCharts.Model
        (E := apm_t96j05_E m) (F := ℝ)) (Subtype P) :=
    ConstructionTargets.ManifoldRegularFiberGlobalAtlas.chartedSpace
      f (r ^ 2) hsm hreg
  let radialAtlas : ChartedSpace
      (ConstructionTargets.ManifoldRegularFiberCharts.Model
        (E := apm_t96j05_E m) (F := ℝ)) (Subtype Q) :=
    ConstructionTargets.PredicateSubtypeAtlasTransport.chartedSpace
      hPQ fiberAtlas
  refine ⟨Module.finrank ℝ (apm_t96j05_E m) - Module.finrank ℝ ℝ, ?_,
    radialAtlas, ?_⟩
  · simp
  · letI := radialAtlas
    constructor
    · apply ConstructionTargets.PredicateSubtypeAtlasTransport.isManifold
        hPQ fiberAtlas
      exact ConstructionTargets.ManifoldRegularFiberGlobalAtlas.isManifold
        f (r ^ 2) hsm hreg
    · have hfiber :
          letI := fiberAtlas
          ContMDiff
            (apm_t96j05_I
              (Module.finrank ℝ (apm_t96j05_E m) - Module.finrank ℝ ℝ))
            (apm_t96j05_I m) ∞
            (Subtype.val : Subtype P → X) := by
          exact ConstructionTargets.ManifoldRegularFiberGlobalAtlas.smooth_inclusion
            f (r ^ 2) hsm hreg
      have hradial :
          ContMDiff
            (apm_t96j05_I
              (Module.finrank ℝ (apm_t96j05_E m) - Module.finrank ℝ ℝ))
            (apm_t96j05_I m) ∞
            (Subtype.val : Subtype Q → X) := by
        exact ConstructionTargets.PredicateSubtypeAtlasTransport.smooth_inclusion
          hPQ fiberAtlas hfiber
      exact hinc.comp hradial

theorem apm_t96j05
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (X : Set (apm_t96j05_E n))
    (hXne : X.Nonempty)
    (hXconn : IsConnected (Set.univ : Set X))
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsEmbeddedSmoothRadialLevel (m := m) X r := by
  have _ := hmn
  rcases hX with ⟨charts, hman, hinc⟩
  letI : ChartedSpace (apm_t96j05_E m) X := charts
  letI : IsManifold (apm_t96j05_I m) ∞ X := hman
  letI : Nonempty X := hXne.to_subtype
  by_cases hc : ∃ r : ℝ, 0 < r ∧ ∀ x : X, ‖x.1‖ = r
  · rcases hc with ⟨r, hr, hall⟩
    refine ⟨r, hr, ?_⟩
    exact apm_t96j05_constant_radius_level
      ⟨charts, hman, hinc⟩ hr hall inferInstance
  · have hsm : ContMDiff (apm_t96j05_I m) 𝓘(ℝ, ℝ) ∞
        (fun x : X => ‖x.1‖ ^ 2) := by
      exact (contDiff_norm_sq ℝ).contMDiff.comp hinc
    rcases apm_t96j05_exists_regular_radius hm hXconn hsm hc with
      ⟨r, hr, hlevel, hreg⟩
    exact ⟨r, hr, hlevel,
      apm_t96j05_regular_radius_level hinc hr hlevel hsm hreg⟩

#print axioms apm_t96j05
