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
  /-
  Boundary (closer hop 1): the earlier simple-function/Egorov route is no
  longer necessary.  A renewed Mathlib search found
  `Measurable.exists_continuous`; the compiled helper
  `apm_a98j01_polish_refinement` packages its output and proves, using
  `MeasureTheory.borel_eq_borel_of_le`, that the refined Polish topology has
  exactly the original Borel sets.

  The remaining short route is to use compact inner regularity for `volume`
  in that refined topology to choose `K ⊆ Icc a b` with small complement.
  The identity from the refined topology to the usual topology is continuous,
  so refined compactness implies ordinary compactness.  Finally, on `K`, that
  continuous bijection from a compact space to the Hausdorff ordinary real
  line is a homeomorphism; composing its inverse with refined continuity of
  `f` gives `ContinuousOn f K` in the ordinary topology.

  Closer hop 2 found the required compact-to-Hausdorff construction in solved
  sibling `t92J02`.  Since problem bundles are not importable modules, the
  proof is localized above as `apm_a98j01_homeomorph_of_compact_to_T2`, using
  `Equiv.toHomeomorphOfContinuousClosed`.  The open bridge is now only the
  bookkeeping needed to instantiate this lemma for the two induced topologies
  on subtype `K` while performing refined-topology inner regularity.
  -/
  sorry
