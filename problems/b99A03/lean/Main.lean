import Mathlib

/-!
# APM b99A03

## Statement repairs

None.

## Encoding questions

A complete finite set of left-coset representatives is encoded by the predicate
`apmLeftTransversal`: its represented cosets are pairwise distinct and cover every
left coset.  The equality with the mapped minimal polynomial simultaneously records
that the conjugate product has coefficients in the image of the base field and that
the corresponding polynomial over the base field is the minimal polynomial.
-/

noncomputable section

def apmLeftCoset {G : Type*} [Group G] (H : Subgroup G) (σ : G) : Set G :=
  {g | σ⁻¹ * g ∈ H}

def apmLeftTransversal {G : Type*} [Group G] [DecidableEq G]
    (H : Subgroup G) (s : Finset G) : Prop :=
  (∀ σ ∈ s, ∀ τ ∈ s, apmLeftCoset H σ = apmLeftCoset H τ → σ = τ) ∧
    ∀ g : G, ∃ σ ∈ s, apmLeftCoset H g = apmLeftCoset H σ

def apmConjugateProduct
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [DecidableEq (E ≃ₐ[F] E)] (α : E) (s : Finset (E ≃ₐ[F] E)) : Polynomial E :=
  ∏ σ ∈ s, (Polynomial.X - Polynomial.C (σ α))

theorem apm_b99a03
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    [DecidableEq (E ≃ₐ[F] E)]
    (α : E) (s : Finset (E ≃ₐ[F] E))
    (hs : apmLeftTransversal
      (IntermediateField.adjoin F {α}).fixingSubgroup s) :
    (∀ σ τ : E ≃ₐ[F] E,
        apmLeftCoset (IntermediateField.adjoin F {α}).fixingSubgroup σ =
            apmLeftCoset (IntermediateField.adjoin F {α}).fixingSubgroup τ ↔
          σ α = τ α) ∧
      (∀ τ : E ≃ₐ[F] E,
        apmLeftTransversal (IntermediateField.adjoin F {α}).fixingSubgroup
          (s.image fun σ => τ * σ)) ∧
      apmConjugateProduct F E α s =
        (minpoly F α).map (algebraMap F E) := by
  classical
  have hfix (φ : E ≃ₐ[F] E) :
      φ ∈ (IntermediateField.adjoin F {α}).fixingSubgroup ↔ φ α = α := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h
      exact h α (IntermediateField.subset_adjoin F {α} (Set.mem_singleton α))
    · intro h x hx
      refine IntermediateField.adjoin_induction F ?_ ?_ ?_ ?_ ?_ hx
      · intro y hy
        simpa [Set.mem_singleton_iff.mp hy] using h
      · intro y
        exact φ.commutes y
      · intro x y _ _ hx hy
        simp [hx, hy]
      · intro x _ hx
        simp [hx]
      · intro x y _ _ hx hy
        simp [hx, hy]
  have hmem (σ g : E ≃ₐ[F] E) :
      g ∈ apmLeftCoset (IntermediateField.adjoin F {α}).fixingSubgroup σ ↔
        g α = σ α := by
    change σ⁻¹ * g ∈ (IntermediateField.adjoin F {α}).fixingSubgroup ↔ _
    rw [hfix]
    constructor
    · intro h
      have := congrArg σ h
      simpa using this
    · intro h
      have := congrArg σ.symm h
      simpa using this
  have hcoset (σ τ : E ≃ₐ[F] E) :
      apmLeftCoset (IntermediateField.adjoin F {α}).fixingSubgroup σ =
          apmLeftCoset (IntermediateField.adjoin F {α}).fixingSubgroup τ ↔
        σ α = τ α := by
    constructor
    · intro h
      have hσ : σ ∈ apmLeftCoset
          (IntermediateField.adjoin F {α}).fixingSubgroup τ := by
        rw [← h]
        exact (hmem σ σ).2 rfl
      exact (hmem τ σ).1 hσ
    · intro h
      ext g
      rw [hmem, hmem, h]
  refine ⟨hcoset, ?_, ?_⟩
  · intro τ
    constructor
    · intro a ha b hb hab
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb
      have himage := (hcoset (τ * σ) (τ * ρ)).1 hab
      have hvalue : σ α = ρ α := by
        have := congrArg τ.symm himage
        simpa using this
      have hσρ := hs.1 σ hσ ρ hρ ((hcoset σ ρ).2 hvalue)
      exact congrArg (fun ω => τ * ω) hσρ
    · intro g
      obtain ⟨σ, hσ, hσg⟩ := hs.2 (τ⁻¹ * g)
      refine ⟨τ * σ, Finset.mem_image.mpr ⟨σ, hσ, rfl⟩, ?_⟩
      apply (hcoset g (τ * σ)).2
      have hvalue := (hcoset (τ⁻¹ * g) σ).1 hσg
      have := congrArg τ hvalue
      simpa using this
  · let c : ConjRootClass F E := ConjRootClass.mk F α
    have hcarrier : s.image (fun σ => σ α) = c.carrier.toFinset := by
      ext x
      simp only [Finset.mem_image, Set.mem_toFinset]
      constructor
      · rintro ⟨σ, _, rfl⟩
        change ConjRootClass.mk F (σ α) = ConjRootClass.mk F α
        rw [ConjRootClass.mk_eq_mk, isConjRoot_iff_exists_algEquiv]
        exact ⟨σ, rfl⟩
      · intro hx
        change ConjRootClass.mk F x = ConjRootClass.mk F α at hx
        rw [ConjRootClass.mk_eq_mk, isConjRoot_iff_exists_algEquiv] at hx
        obtain ⟨σ, hσx⟩ := hx
        obtain ⟨τ, hτ, hστ⟩ := hs.2 σ
        refine ⟨τ, hτ, ?_⟩
        rw [← hσx]
        exact ((hcoset σ τ).1 hστ).symm
    rw [← ConjRootClass.minpoly_mk α,
      ConjRootClass.minpoly.map_eq_prod c, ← hcarrier]
    unfold apmConjugateProduct
    rw [Finset.prod_image]
    intro σ hσ τ hτ hvalue
    exact hs.1 σ hσ τ hτ ((hcoset σ τ).2 hvalue)
