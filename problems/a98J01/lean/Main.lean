import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a98J01

## Statement repairs

None.

## Encoding notes

The interval function is represented by a globally measurable real function and
then restricted to `[a,b]`. Continuity of its restriction to the large compact set
is expressed by `ContinuousOn f K`, i.e. continuity in the subspace topology on `K`.
-/

/-- A measurable real function becomes continuous after refining the real-line
topology to a Polish topology with exactly the same Borel sets.  This is the
short route to Lusin's theorem supplied by Mathlib's Polish-space API. -/
lemma apm_a98j01_polish_refinement {f : ℝ → ℝ} (hf : Measurable f) :
    ∃ t' : TopologicalSpace ℝ,
      t' ≤ (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ) ∧
      @Continuous ℝ ℝ t'
        (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ) f ∧
      @PolishSpace ℝ t' ∧
      @borel ℝ t' =
        @borel ℝ (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ) := by
  let hreal : @PolishSpace ℝ
      (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ) :=
    inferInstance
  obtain ⟨t', ht', hcont, hpolish⟩ := hf.exists_continuous
  refine ⟨t', ht', hcont, hpolish, ?_⟩
  exact MeasureTheory.borel_eq_borel_of_le
    (t := t')
    (t' := (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ))
    hpolish hreal ht'

/-- A continuous bijection from a compact space to a Hausdorff space is a
homeomorphism.  This local copy follows the compiled proof in solved sibling
`t92J02`; problem bundles themselves are not importable Lean modules. -/
lemma apm_a98j01_homeomorph_of_compact_to_T2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {g : X → Y}
    (hcompact : IsCompact (Set.univ : Set X)) (hg : Continuous g)
    (hbij : Function.Bijective g) :
    ∃ h : X ≃ₜ Y, (h : X → Y) = g := by
  classical
  letI : CompactSpace X := ⟨by simpa using hcompact⟩
  let e : X ≃ Y := Equiv.ofBijective g hbij
  have hecont : Continuous e := by simpa [e] using hg
  let h : X ≃ₜ Y := e.toHomeomorphOfContinuousClosed hecont hecont.isClosedMap
  exact ⟨h, by rfl⟩

theorem apm_a98j01
    {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : Set ℝ,
        K ⊆ Icc a b ∧
        IsCompact K ∧
        volume (Icc a b \ K) < ENNReal.ofReal ε ∧
        ContinuousOn f K := by
  intro ε hε
  let t0 : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hb0 : (inferInstance : MeasurableSpace ℝ) = @borel ℝ t0 :=
    BorelSpace.measurable_eq
  have hIcc_meas : MeasurableSet (Icc a b) := measurableSet_Icc
  have hfinite0 : volume (Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨t', ht', hf', hp', hborel⟩ := apm_a98j01_polish_refinement hf
  letI : TopologicalSpace ℝ := t'
  letI : PolishSpace ℝ := hp'
  letI : BorelSpace ℝ :=
    ⟨hb0.trans hborel.symm⟩
  obtain ⟨K, hKI, hK', hdiff⟩ :=
    hIcc_meas.exists_isCompact_diff_lt hfinite0
      (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have hid : @Continuous ℝ ℝ t' t0 id := continuous_id_of_le ht'
  have hK0 : @IsCompact ℝ t0 K := by
    simpa only [id_eq, image_id'] using
      (@IsCompact.image ℝ ℝ t' t0 K id hK' hid)
  refine ⟨K, hKI, hK0, hdiff, ?_⟩
  let tK' : TopologicalSpace K := TopologicalSpace.induced ((↑) : K → ℝ) t'
  let tK0 : TopologicalSpace K := TopologicalSpace.induced ((↑) : K → ℝ) t0
  have hKle : tK' ≤ tK0 := induced_mono ht'
  have hKuniv : @IsCompact K tK' Set.univ := by
    exact isCompact_iff_isCompact_univ.mp hK'
  have hT2 : @T2Space K tK0 := by
    letI : TopologicalSpace K := tK0
    infer_instance
  obtain ⟨e, he⟩ := @apm_a98j01_homeomorph_of_compact_to_T2
    K K tK' tK0 hT2 id hKuniv (continuous_id_of_le hKle)
      Function.bijective_id
  have hinv : @Continuous K K tK0 tK' id := by
    let ee : K ≃ K := @Homeomorph.toEquiv K K tK' tK0 e
    have hee : ee.toFun = id := he
    have heinv : ee.invFun = id := by
      funext x
      apply ee.injective
      calc
        ee (ee.invFun x) = x := ee.right_inv x
        _ = ee (id x) := (congrFun hee x).symm
    rw [← heinv]
    exact @Homeomorph.continuous_invFun K K tK' tK0 e
  have hcoe : @Continuous K ℝ tK' t' ((↑) : K → ℝ) := continuous_induced_dom
  have hc : @Continuous K ℝ tK0 t0 (fun x => f x) :=
    @Continuous.comp K ℝ ℝ tK0 t' t0 _ _ hf'
      (@Continuous.comp K K ℝ tK0 tK' t' _ _ hcoe hinv)
  exact (@continuousOn_iff_continuous_restrict ℝ ℝ t0 t0 f K).mpr hc
