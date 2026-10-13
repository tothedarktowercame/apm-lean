import Mathlib

open Matrix

noncomputable section

def apmIntegralMatrix {n : Type*} [Fintype n]
    (A : Matrix n n ℚ) : Prop :=
  ∀ i j, ∃ z : ℤ, A i j = z

noncomputable def apmReduction (n : Type*) [Fintype n] [DecidableEq n]
    (p m : ℕ) (h : p ^ (m - 1) ∣ p ^ m) :
    Matrix.GeneralLinearGroup n (ZMod (p ^ m)) →*
      Matrix.GeneralLinearGroup n (ZMod (p ^ (m - 1))) :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom h _)

theorem apm_b96a01_part_a :
    ∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (A : AddSubgroup V) (s : Finset V),
      A = AddSubgroup.closure (s : Set V) →
        ∃ (ι : Type*) (b : Module.Basis ι ℚ V) (u : Finset ι),
          A = AddSubgroup.closure (b '' (u : Set ι)) := by
  intro V _ _ _ A s hs
  let N : Submodule ℤ V := A.toIntSubmodule
  have hN : N = Submodule.span ℤ (s : Set V) := by
    simp [N, hs, AddSubgroup.toIntSubmodule_closure]
  letI : Module.Finite ℤ N := by
    rw [hN]
    infer_instance
  letI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  letI : Module.IsTorsionFree ℤ V := by infer_instance
  letI : Module.IsTorsionFree ℤ N := by infer_instance
  let nb := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := N)
  let n := nb.1
  let bA : Module.Basis (Fin n) ℤ N := nb.2
  let v : Fin n → V := fun j ↦ (bA j : V)
  have hvZ : LinearIndependent ℤ v := by
    exact bA.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hvQ : LinearIndependent ℚ v := by
    exact hvZ.localization (Rₛ := ℚ) (nonZeroDivisors ℤ)
  let hset : LinearIndepOn ℚ id (Set.range v) := hvQ.linearIndepOn_id
  let t : Set V := hset.extend (Set.subset_univ _)
  let b0 : Module.Basis t ℚ V := Module.Basis.extend hset
  have hv_mem : ∀ j, v j ∈ t := by
    intro j
    exact hset.subset_extend (Set.subset_univ _) (Set.mem_range_self j)
  let e : Fin n → t := fun j ↦ ⟨v j, hv_mem j⟩
  have heinj : Function.Injective e := by
    intro j k hjk
    apply hvQ.injective
    change v j = v k
    exact congr_arg (fun z : t ↦ (z : V)) hjk
  let q := Module.finrank ℚ V
  let I := ULift (Fin q)
  let eqv : t ≃ I := (b0.indexEquiv (Module.finBasis ℚ V)).trans Equiv.ulift.symm
  let b : Module.Basis I ℚ V := b0.reindex eqv
  let e' : Fin n → I := eqv ∘ e
  have heinj' : Function.Injective e' := eqv.injective.comp heinj
  let u : Finset I := Finset.univ.map ⟨e', heinj'⟩
  refine ⟨I, b, u, ?_⟩
  have hb_e : ∀ j, b (e' j) = v j := by
    intro j
    simp [b, e', eqv, b0, Module.Basis.extend_apply_self hset (e j), e]
  have himage : b '' (u : Set I) = Set.range v := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      simp only [u, Finset.coe_map, Finset.coe_univ, Set.image_univ,
        Set.mem_range] at hj
      obtain ⟨k, rfl⟩ := hj
      exact ⟨k, (hb_e k).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨e' j, ?_, hb_e j⟩
      simp [u]
  rw [himage]
  rw [← Submodule.span_int_eq_addSubgroupClosure,
    ← AddSubgroup.toIntSubmodule_toAddSubgroup A]
  congr 1
  change N = Submodule.span ℤ (Set.range v)
  symm
  convert congrArg (Submodule.map N.subtype) bA.span_eq
  · rw [Submodule.map_span, ← Set.range_comp]
    rfl
  · exact (Submodule.map_subtype_top N).symm

-- BEGIN SEAT AREA
lemma apm_b96a01_part_b_aux_finite_orbit
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)) [Finite G] :
    ∃ s : Finset (n → ℚ),
      (∀ j : n, Pi.single j 1 ∈ AddSubgroup.closure (s : Set (n → ℚ))) ∧
      ∀ g : G, ∀ x ∈ AddSubgroup.closure (s : Set (n → ℚ)),
        (g.1 : Matrix n n ℚ) *ᵥ x ∈ AddSubgroup.closure (s : Set (n → ℚ)) := by
  letI : Fintype G := Fintype.ofFinite G
  let s : Finset (n → ℚ) := Finset.univ.image fun p : G × n ↦
    (p.1.1 : Matrix n n ℚ) *ᵥ Pi.single p.2 1
  refine ⟨s, ?_, ?_⟩
  · intro j
    apply AddSubgroup.subset_closure
    simp only [s, Finset.mem_coe, Finset.mem_image]
    refine ⟨((1 : G), j), Finset.mem_univ _, ?_⟩
    exact Matrix.one_mulVec _
  · intro g x hx
    let F : (n → ℚ) →+ (n → ℚ) :=
      { toFun := fun x ↦ (g.1 : Matrix n n ℚ) *ᵥ x
        map_zero' := Matrix.mulVec_zero _
        map_add' := fun x y ↦ Matrix.mulVec_add _ _ _ }
    change F x ∈ AddSubgroup.closure (s : Set (n → ℚ))
    refine AddSubgroup.closure_induction
      (p := fun y _ ↦ F y ∈ AddSubgroup.closure (s : Set (n → ℚ)))
      ?_ (by simp) ?_ ?_ hx
    · intro y hy
      simp only [s, Finset.mem_coe, Finset.mem_image] at hy
      obtain ⟨p, -, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      simp only [s, Finset.mem_coe, Finset.mem_image]
      refine ⟨(g * p.1, p.2), Finset.mem_univ _, ?_⟩
      dsimp [F]
      rw [← Matrix.mulVec_mulVec]
    · intro y z hy hz ihy ihz
      simpa only [map_add] using AddSubgroup.add_mem _ ihy ihz
    · intro y hy ihy
      simpa only [map_neg] using AddSubgroup.neg_mem _ ihy

lemma apm_b96a01_part_b_aux_lattice_basis_conjugacy
    (n : Type*) [Fintype n] [DecidableEq n]
    (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)) [Finite G]
    (horbit : ∃ s : Finset (n → ℚ),
      (∀ j : n, Pi.single j 1 ∈ AddSubgroup.closure (s : Set (n → ℚ))) ∧
      ∀ g : G, ∀ x ∈ AddSubgroup.closure (s : Set (n → ℚ)),
        (g.1 : Matrix n n ℚ) *ᵥ x ∈ AddSubgroup.closure (s : Set (n → ℚ))) :
    ∃ P : Matrix n n ℚ, IsUnit P ∧
      ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹) := by
  sorry

theorem apm_b96a01_part_b :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → ∃ P : Matrix n n ℚ, IsUnit P ∧
        ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹) := by
  intro n _ _ G hG
  letI : Finite G := hG
  exact apm_b96a01_part_b_aux_lattice_basis_conjugacy n G
    (apm_b96a01_part_b_aux_finite_orbit n G)
-- END SEAT AREA

theorem apm_b96a01_part_c :
    ∀ (n : Type*) [Fintype n] [DecidableEq n] (p m : ℕ)
      (hdiv : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      ∀ a b, a ∈ (apmReduction n p m hdiv).ker →
        b ∈ (apmReduction n p m hdiv).ker → a * b = b * a := by
  sorry

theorem apm_b96a01_part_d_nonabelian :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G → ¬(∀ a b : G, a * b = b * a) →
      ∀ p : ℕ, p.Prime →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  sorry

theorem apm_b96a01_part_d_abelian :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G → (∀ a b : G, a * b = b * a) →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  sorry

theorem apm_b96a01_part_d :
    ∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ := by
  intro n _ _ G hG hs p hp hex
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · exact apm_b96a01_part_d_abelian n G hG hs hcomm p hp hex
  · exact apm_b96a01_part_d_nonabelian n G hG hs hcomm p hp

theorem apm_b96a01 :
    (∀ (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (A : AddSubgroup V) (s : Finset V),
      A = AddSubgroup.closure (s : Set V) →
        ∃ (ι : Type*) (b : Module.Basis ι ℚ V) (u : Finset ι),
          A = AddSubgroup.closure (b '' (u : Set ι))) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → ∃ P : Matrix n n ℚ, IsUnit P ∧
        ∀ g : G, apmIntegralMatrix (P * (g.1 : Matrix n n ℚ) * P⁻¹)) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n] (p m : ℕ)
      (hdiv : p ^ (m - 1) ∣ p ^ m), 2 ≤ m →
      ∀ a b, a ∈ (apmReduction n p m hdiv).ker →
        b ∈ (apmReduction n p m hdiv).ker → a * b = b * a) ∧
    (∀ (n : Type*) [Fintype n] [DecidableEq n]
      (G : Subgroup (Matrix.GeneralLinearGroup n ℚ)),
      Finite G → IsSimpleGroup G →
      ∀ p : ℕ, p.Prime → ¬(Fintype.card n = 1 ∧ p = 2) →
        ∃ ρ : G →* Matrix.GeneralLinearGroup n (ZMod p),
          Function.Injective ρ) := by
  exact ⟨apm_b96a01_part_a, apm_b96a01_part_b,
    apm_b96a01_part_c, apm_b96a01_part_d⟩

#print axioms apm_b96a01
