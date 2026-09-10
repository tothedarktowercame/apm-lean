import Mathlib.Topology.MetricSpace.HausdorffDimension
import ConstructionTargets.SardFiniteOrderRankLocusLocalAggregation
import ConstructionTargets.FixedTargetChartDimensionDropNullity
import ConstructionTargets.FixedChartNullForcesNonsurjectivity
import ConstructionTargets.SingularHomologyRetractNonvanishing
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.T95J04FinalProductComparison

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace ConstructionTargets.OpenDomainHausdorffNullity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
theorem image_null {f : E → F} {U s : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hs : s ⊆ U) (n : ℕ)
    (hn : Module.finrank ℝ E < n) : μH[n] (f '' s) = 0 := by
  have hdim : dimH (f '' s) ≤ dimH s := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x (hs hx)
    obtain ⟨C, t, ht, hLip⟩ :=
      ((hf.mono hball) x (Metric.mem_ball_self hr)).exists_lipschitzOnWith
        (convex_ball x r)
    refine ⟨C, t, ?_, hLip⟩
    have ht' : t ∈ 𝓝 x := by
      simpa only [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds x hr)] using ht
    exact mem_nhdsWithin_of_mem_nhds ht'
  have hle : dimH s ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
    exact (dimH_mono (subset_univ s)).trans_eq (Real.dimH_univ_eq_finrank E)
  have hlt : dimH (f '' s) < (n : ℝ≥0∞) :=
    (hdim.trans hle).trans_lt (by exact_mod_cast hn)
  simpa using (hausdorffMeasure_of_dimH_lt (d := (n : ℝ≥0)) hlt)
#print axioms image_null
end ConstructionTargets.OpenDomainHausdorffNullity

/-!
# APM t95J04 — low-dimensional maps to spheres and six-manifolds

Part (a) uses genuine finite-dimensional Mathlib manifolds and `ContMDiff`
maps.  The Sard/dimension consequence—nullity of the image and hence failure
of surjectivity—is in the conclusion, not stored in the definition of a
“smooth map.”  Part (b) uses the concrete metric spheres and their products.

## Statement repairs

None.

## Encoding questions

Non-diffeomorphism in part (b) is stated via the stronger conclusion that the
underlying spaces are not homeomorphic.  This avoids introducing a surrogate
diffeomorphism predicate while still implying the source claim.
-/

open Set MeasureTheory
open scoped ContDiff Manifold ENNReal

noncomputable section

abbrev T95J04E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev T95J04I (n : ℕ) := 𝓘(ℝ, T95J04E n)
abbrev T95J04Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev T95J04SphereSix := T95J04Sphere 6
abbrev T95J04SphereTwoFour := T95J04Sphere 2 × T95J04Sphere 4
abbrev T95J04SphereThreeThree := T95J04Sphere 3 × T95J04Sphere 3

def t95J04NullHomotopic {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) : Prop :=
  ∃ y : Y,
    ContinuousMap.Homotopic ⟨f, hf⟩ (ContinuousMap.const X y)

/-- An explicit coordinate point on every sphere used in the statement. -/
lemma t95J04_sphere_nonempty (n : ℕ) : Nonempty (T95J04Sphere n) := by
  exact ⟨⟨EuclideanSpace.single 0 1, by simp [T95J04Sphere]⟩⟩

lemma t95J04_sphereSix_nonempty : Nonempty T95J04SphereSix :=
  t95J04_sphere_nonempty 6

lemma t95J04_sphereTwoFour_nonempty : Nonempty T95J04SphereTwoFour :=
  Nonempty.map2 (fun x y ↦ (x, y))
    (t95J04_sphere_nonempty 2) (t95J04_sphere_nonempty 4)

lemma t95J04_sphereThreeThree_nonempty : Nonempty T95J04SphereThreeThree :=
  Nonempty.map2 (fun x y ↦ (x, y))
    (t95J04_sphere_nonempty 3) (t95J04_sphere_nonempty 3)

/-- The complement of a point in one of the target spheres is contractible.
This generalizes the stereographic-projection construction compiled in
`t94J05`. -/
lemma t95J04_contractibleSpace_sphere_complement (n : ℕ)
    (q : T95J04Sphere n) :
    ContractibleSpace {y : T95J04Sphere n // y ≠ q} := by
  let hs := stereographic (norm_eq_of_mem_sphere q)
  have hsource : ({y : T95J04Sphere n | y ≠ q} : Set (T95J04Sphere n)) =
      hs.source := by
    ext y
    simp [hs]
  have htarget : hs.target = Set.univ := stereographic_target _
  let eSource : {y : T95J04Sphere n // y ≠ q} ≃ₜ hs.source :=
    Homeomorph.setCongr hsource
  let eTarget : hs.target ≃ₜ
      (ℝ ∙ (q : EuclideanSpace ℝ (Fin (n + 1))))ᗮ :=
    (Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ _)
  let e : {y : T95J04Sphere n // y ≠ q} ≃ₜ
      (ℝ ∙ (q : EuclideanSpace ℝ (Fin (n + 1))))ᗮ :=
    eSource.trans (hs.toHomeomorphSourceTarget.trans eTarget)
  exact e.contractibleSpace

/-- Once Sard supplies a missed point, stereographic projection closes the
null-homotopy part of the first conjunct. This is the arbitrary-domain,
arbitrary-sphere-dimension version of `t94J05`'s construction. -/
lemma t95J04_nullHomotopic_of_not_surjective {X : Type*}
    [TopologicalSpace X] (n : ℕ) (f : X → T95J04Sphere n)
    (hf : Continuous f) (hnot_surj : ¬ Function.Surjective f) :
    t95J04NullHomotopic f hf := by
  obtain ⟨q, hq⟩ : ∃ q : T95J04Sphere n, ∀ x, f x ≠ q := by
    simpa [Function.Surjective] using hnot_surj
  let g : C(X, {y : T95J04Sphere n // y ≠ q}) :=
    ⟨fun x ↦ ⟨f x, hq x⟩, hf.subtype_mk _⟩
  letI : ContractibleSpace {y : T95J04Sphere n // y ≠ q} :=
    t95J04_contractibleSpace_sphere_complement n q
  have hg0 : g.Nullhomotopic := by
    simpa using (id_nullhomotopic {y : T95J04Sphere n // y ≠ q}).comp_left g
  rcases hg0 with ⟨p, hg⟩
  let inclusion : C({y : T95J04Sphere n // y ≠ q}, T95J04Sphere n) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hcomp := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl inclusion) hg
  refine ⟨p, ?_⟩
  simpa [g, inclusion] using hcomp

theorem apm_t95j04 :
    (∀ (k n : ℕ), k < n →
      ∀ (M : Type*) [TopologicalSpace M] [T2Space M]
        [SecondCountableTopology M] [CompactSpace M]
        [ChartedSpace (T95J04E k) M] [IsManifold (T95J04I k) ∞ M]
        (f : M → T95J04Sphere n),
        ∀ hf : ContMDiff (T95J04I k) (T95J04I n) ∞ f,
        μH[n] (Set.range f) = 0 ∧
        ¬ Function.Surjective f ∧
        t95J04NullHomotopic f hf.continuous) ∧
    SimplyConnectedSpace T95J04SphereSix ∧
    SimplyConnectedSpace T95J04SphereTwoFour ∧
    SimplyConnectedSpace T95J04SphereThreeThree ∧
    ¬ Nonempty (T95J04SphereSix ≃ₜ T95J04SphereTwoFour) ∧
    ¬ Nonempty (T95J04SphereSix ≃ₜ T95J04SphereThreeThree) ∧
    ¬ Nonempty (T95J04SphereTwoFour ≃ₜ T95J04SphereThreeThree) := by
  refine ⟨?_,
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 6 (by norm_num),
    ?_, ?_,
    ConstructionTargets.SingularHomologyRetractNonvanishing.sphereSix_not_homeomorphic_sphereTwo_product_sphereFour,
    ConstructionTargets.SingularHomologyRetractNonvanishing.sphereSix_not_homeomorphic_sphereThree_product_sphereThree,
    ConstructionTargets.T95J04FinalProductComparison.sphereTwo_product_sphereFour_not_homeomorphic_sphereThree_product_sphereThree⟩
  rotate_left 1
  · letI := ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 2 (by norm_num)
    letI := ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 4 (by norm_num)
    exact ConstructionTargets.SimplyConnectedSphereProducts.simplyConnectedSpace_prod
  · letI := ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 3 (by norm_num)
    exact ConstructionTargets.SimplyConnectedSphereProducts.simplyConnectedSpace_prod
  -- Remaining: Sard/nullity/non-surjectivity/null-homotopy.  All three
  -- simple-connectivity and all three nonhomeomorphism conjuncts are closed.
  intro k n hkn M _ _ _ _ _ _ f hf
  letI : Fact (Module.finrank ℝ (T95J04E (n+1)) = n+1) := ⟨by simp [T95J04E]⟩
  let g : M → T95J04E (n+1) := fun x => (f x).val
  have hg : ContMDiff (T95J04I k) 𝓘(ℝ,T95J04E (n+1)) ∞ g :=
    (contMDiff_coe_sphere (E := T95J04E (n+1)) (n := n)).comp hf
  have hn : μH[n] (Set.range g) = 0 := by
    rw [← Set.image_univ]
    apply SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open
    intro x _
    let e := chartAt (T95J04E k) x
    have hq : ContDiffOn ℝ 1 (g ∘ e.symm) e.target :=
      ((hg.comp_contMDiffOn contMDiffOn_chart_symm).contDiffOn).of_le (by simp)
    have hz := ConstructionTargets.OpenDomainHausdorffNullity.image_null
      e.open_target hq (Subset.refl _) n (by simpa using hkn)
    refine ⟨e.source, e.open_source, mem_chart_source _ x, measure_mono_null ?_ hz⟩
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨e y, e.map_source hy.2, congrArg g (e.left_inv hy.2)⟩
  have hnull : μH[n] (Set.range f) = 0 := by
    have he := (isometry_subtype_coe : Isometry (Subtype.val : T95J04Sphere n → T95J04E (n+1))).hausdorffMeasure_image
      (Or.inl (by positivity : (0:ℝ) ≤ n)) (Set.range f)
    have him : Subtype.val '' Set.range f = Set.range g := by
      ext y
      simp [g]
    rw [him] at he
    exact he.symm.trans hn
  letI : Nonempty (T95J04Sphere n) := t95J04_sphere_nonempty n
  let q : T95J04Sphere n := Classical.choice inferInstance
  have hc := ConstructionTargets.FixedTargetChartDimensionDropNullity.fixed_extChartAt_range_inter_source_null
    (T95J04I k) (T95J04I n) f (hf.of_le (by simp)) (by simpa using hkn) volume q
  have hnot := ConstructionTargets.FixedChartNullForcesNonsurjectivity.not_surjective_of_fixedChart_coordinateNull
    (T95J04I n) volume f q hc
  exact ⟨hnull, hnot, t95J04_nullHomotopic_of_not_surjective n f hf.continuous hnot⟩
#print axioms apm_t95j04
