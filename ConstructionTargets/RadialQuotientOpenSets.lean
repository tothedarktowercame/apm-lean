import ConstructionTargets.Surfaces

open Set Topology
noncomputable section

namespace ConstructionTargets.RadialQuotientOpenSets

universe u
variable {A : Type u} [TopologicalSpace A]

omit [TopologicalSpace A] in
theorem preimage_image_eq_of_eqvGen_invariant
    [Setoid A] (U : Set A)
    (hU : ∀ ⦃x y : A⦄, x ≈ y → (x ∈ U ↔ y ∈ U)) :
    Quotient.mk' ⁻¹' (Quotient.mk' '' U) = U := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have heq : y ≈ x := Quotient.exact hxy
    exact (hU heq).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isOpen_quotient_image_of_eqvGen_invariant
    [Setoid A] (U : Set A) (hOpen : IsOpen U)
    (hU : ∀ ⦃x y : A⦄, x ≈ y → (x ∈ U ↔ y ∈ U)) :
    IsOpen (Quotient.mk' '' U : Set (Quotient (inferInstance : Setoid A))) := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  rw [preimage_image_eq_of_eqvGen_invariant U hU]
  exact hOpen

omit [TopologicalSpace A] in
theorem eqvGen_preserves_of_rel_preserves
    (R : A → A → Prop) (ρ : A → ℝ)
    (hR : ∀ ⦃x y⦄, R x y → ρ x = ρ y)
    ⦃x y : A⦄ (hxy : Relation.EqvGen R x y) : ρ x = ρ y := by
  induction hxy with
  | rel x y h => exact hR h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem isOpen_radial_image
    (R : A → A → Prop) (ρ : A → ℝ) (hρ : Continuous ρ)
    (hR : ∀ ⦃x y⦄, R x y → ρ x = ρ y) (I : Set ℝ) (hI : IsOpen I) :
    IsOpen ((fun x : A => Quotient.mk (Relation.EqvGen.setoid R) x) '' (ρ ⁻¹' I) :
      Set (Quotient (Relation.EqvGen.setoid R))) := by
  letI : Setoid A := Relation.EqvGen.setoid R
  apply isOpen_quotient_image_of_eqvGen_invariant (ρ ⁻¹' I)
    (hρ.isOpen_preimage I hI)
  intro x y hxy
  change ρ x ∈ I ↔ ρ y ∈ I
  rw [show ρ x = ρ y from eqvGen_preserves_of_rel_preserves R ρ hR hxy]

open ConstructionTargets.Surfaces

theorem norm_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    ‖((edgePoint edgeCount edge t : Disk) : ℂ)‖ = 1 := by
  change ‖Complex.exp _‖ = 1
  rw [Complex.norm_exp]
  simp

theorem surfaceRel_norm_eq (orientable : Bool) (genus : ℕ)
    {x y : Disk} (h : SurfaceRel orientable genus x y) :
    ‖(x : ℂ)‖ = ‖(y : ℂ)‖ := by
  simp only [SurfaceRel] at h
  split at h
  · rcases h with ⟨j, hj, t, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      rw [norm_edgePoint, norm_edgePoint]
    · rcases h with ⟨rfl, rfl⟩
      rw [norm_edgePoint, norm_edgePoint]
  · rcases h with ⟨j, hj, t, rfl, rfl⟩
    rw [norm_edgePoint, norm_edgePoint]

end ConstructionTargets.RadialQuotientOpenSets
