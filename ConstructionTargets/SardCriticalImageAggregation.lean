import Mathlib

/-! # Countable aggregation of null critical images -/

open Set MeasureTheory
noncomputable section

/-- Once every member of a countable source cover contributes a null restricted
critical image, the full critical image is null.  The patches and the critical
set are abstract: chart construction and local Morse--Sard belong in separate
theorems. -/
theorem criticalImage_null_of_countable_local_null
    {M F : Type*} [MeasurableSpace F] (μ : Measure F)
    (f : M → F) (critical centers : Set M) (patch : M → Set M)
    (hcenters : centers.Countable)
    (hcover : critical ⊆ ⋃ x ∈ centers, patch x)
    (hlocal : ∀ x ∈ centers, μ (f '' (critical ∩ patch x)) = 0) :
    μ (f '' critical) = 0 := by
  letI : Countable centers := hcenters.to_subtype
  apply measure_mono_null (t := ⋃ x : centers, f '' (critical ∩ patch x))
  · rintro y ⟨z, hz, rfl⟩
    have hz' := hcover hz
    simp only [mem_iUnion] at hz'
    obtain ⟨x, hxc, hzx⟩ := hz'
    exact mem_iUnion_of_mem (⟨x, hxc⟩ : centers) ⟨z, ⟨hz, hzx⟩, rfl⟩
  · exact measure_iUnion_null fun x => hlocal x x.property

#print axioms criticalImage_null_of_countable_local_null
