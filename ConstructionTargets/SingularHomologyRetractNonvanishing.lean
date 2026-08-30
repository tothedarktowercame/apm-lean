import ConstructionTargets.SphereHomology

/-! # Singular-homology nonvanishing from retracts

A split inclusion stays split after applying integral singular homology.  Thus
nonvanishing of a retract's homology forces nonvanishing of the ambient
space's homology.  Applying this to `X → X × Y → X` distinguishes `S⁶` from
`S² × S⁴` and from `S³ × S³` without a Künneth theorem.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace ConstructionTargets.SingularHomologyRetractNonvanishing

open ConstructionTargets.SphereHomology

abbrev IntegralHomology (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- Integral singular homology of an ambient space is nonzero whenever the
same-degree homology of a retract is nonzero. -/
theorem integralHomology_not_isZero_of_split_retract
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X] (k : ℕ)
    (i : C(A, X)) (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A)
    (hA : ¬ IsZero (IntegralHomology k A)) :
    ¬ IsZero (IntegralHomology k X) := by
  intro hX
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)
  have hi : F.map (TopCat.ofHom i) = 0 := hX.eq_of_tgt _ _
  apply hA
  rw [IsZero.iff_id_eq_zero]
  have hsplit :
      F.map (TopCat.ofHom i) ≫ F.map (TopCat.ofHom r) = 𝟙 _ := by
    rw [← F.map_comp]
    have hTop : TopCat.ofHom i ≫ TopCat.ofHom r = 𝟙 (TopCat.of A) := by
      ext x
      exact DFunLike.congr_fun hir x
    rw [hTop, F.map_id]
  rw [← hsplit, hi, zero_comp]

/-- A nonempty second factor makes the first factor a retract of the product,
so nonzero integral homology of the first factor survives in the product. -/
theorem integralHomology_product_not_isZero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (y : Y) (hX : ¬ IsZero (IntegralHomology k X)) :
    ¬ IsZero (IntegralHomology k (X × Y)) := by
  let i : C(X, X × Y) :=
    ⟨fun x ↦ (x, y), continuous_id.prodMk continuous_const⟩
  let r : C(X × Y, X) := ⟨Prod.fst, continuous_fst⟩
  apply integralHomology_not_isZero_of_split_retract k i r
  · ext x
    rfl
  · exact hX

/-- The top-dimensional integral singular homology of every positive sphere
is nonzero. -/
theorem positiveSphere_topHomology_not_isZero (n : ℕ) (hn : 0 < n) :
    ¬ IsZero (ModuleHomology n n) := by
  intro h
  have hz : IsZero (ModuleCat.of ℤ ℤ) :=
    h.of_iso (sphereModuleTopHomologyIsoInt n hn).symm
  have hid : 𝟙 (ModuleCat.of ℤ ℤ) = 0 := (IsZero.iff_id_eq_zero _).mp hz
  have hone := ConcreteCategory.congr_hom hid (1 : ℤ)
  norm_num at hone

private noncomputable def spherePoint (n : ℕ) : Sphere n :=
  ⟨EuclideanSpace.single 0 1, by simp [Sphere]⟩

private theorem no_homeomorph_sphere_product_sphere
    (a b n : ℕ) (ha : 0 < a) (han : a ≠ n) :
    ¬ Nonempty ((Sphere a × Sphere b) ≃ₜ Sphere n) := by
  rintro ⟨e⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) a).obj
    (ModuleCat.of ℤ ℤ)
  have hproduct : ¬ IsZero (IntegralHomology a (Sphere a × Sphere b)) :=
    integralHomology_product_not_isZero a (spherePoint b)
      (positiveSphere_topHomology_not_isZero a ha)
  have hsphere : IsZero (ModuleHomology n a) :=
    sphereModuleHomology_isZero_of_ne_zero_top n a (by omega) han
  let eIso : TopCat.of (Sphere a × Sphere b) ≅ TopCat.of (Sphere n) :=
    TopCat.isoOfHomeo e
  exact hproduct (hsphere.of_iso (F.mapIso eIso))

/-- `S⁶` is not homeomorphic to `S² × S⁴`, using the `S²` retract and H₂. -/
theorem sphereSix_not_homeomorphic_sphereTwo_product_sphereFour :
    ¬ Nonempty (Sphere 6 ≃ₜ (Sphere 2 × Sphere 4)) := by
  intro h
  exact no_homeomorph_sphere_product_sphere 2 4 6 (by omega) (by omega)
    (Nonempty.map Homeomorph.symm h)

/-- `S⁶` is not homeomorphic to `S³ × S³`, using the first `S³` retract and
H₃. -/
theorem sphereSix_not_homeomorphic_sphereThree_product_sphereThree :
    ¬ Nonempty (Sphere 6 ≃ₜ (Sphere 3 × Sphere 3)) := by
  intro h
  exact no_homeomorph_sphere_product_sphere 3 3 6 (by omega) (by omega)
    (Nonempty.map Homeomorph.symm h)

#print axioms integralHomology_not_isZero_of_split_retract
#print axioms integralHomology_product_not_isZero
#print axioms positiveSphere_topHomology_not_isZero
#print axioms sphereSix_not_homeomorphic_sphereTwo_product_sphereFour
#print axioms sphereSix_not_homeomorphic_sphereThree_product_sphereThree

end ConstructionTargets.SingularHomologyRetractNonvanishing
