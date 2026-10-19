import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.WedgePermutationCover

/-!
# APM t00A02: finite coverings of surfaces and a projective-plane wedge

The elementary quotient and fibre calculations are copied from the registered
statement.  Four independent top-level obligations remain below.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev apm_t00A02_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00A02_I2 := 𝓘(ℝ, apm_t00A02_E2)
abbrev apm_t00A02_Sphere2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

abbrev apm_t00A02_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t00A02_isGenusFiveSurface
    (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (X ≃ₜ ConstructionTargets.Surfaces.Surface true 5)

def apm_t00A02_isNfoldCover {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (n : ℕ) (p : E → B) : Prop :=
  IsCoveringMap p ∧ ∀ b : B, Nat.card {e : E // p e = b} = n

def apm_t00A02_isRegularCover {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) : Prop :=
  ∀ x y : E, p x = p y →
    ∃ h : E ≃ₜ E, (∀ z : E, p (h z) = p z) ∧ h x = y

inductive apm_t00A02_antipodalRel :
    apm_t00A02_Sphere2 → apm_t00A02_Sphere2 → Prop
  | antipodal (x : apm_t00A02_Sphere2) :
      apm_t00A02_antipodalRel x (-x)

def apm_t00A02_RP2 :=
  Quotient (Relation.EqvGen.setoid apm_t00A02_antipodalRel)

noncomputable instance : TopologicalSpace apm_t00A02_RP2 :=
  TopologicalSpace.coinduced
    (fun x : apm_t00A02_Sphere2 ↦
      Quotient.mk (Relation.EqvGen.setoid apm_t00A02_antipodalRel) x)
    inferInstance

def apm_t00A02_antipodalCover : apm_t00A02_Sphere2 → apm_t00A02_RP2 :=
  fun x ↦ Quotient.mk _ x

@[simp] lemma apm_t00A02_antipodalCover_neg (x : apm_t00A02_Sphere2) :
    apm_t00A02_antipodalCover (-x) = apm_t00A02_antipodalCover x := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ (apm_t00A02_antipodalRel.antipodal x))

lemma apm_t00A02_antipodal_eqvGen_iff
    (x y : apm_t00A02_Sphere2) :
    Relation.EqvGen apm_t00A02_antipodalRel x y ↔ y = x ∨ y = -x := by
  constructor
  · intro h
    induction h with
    | rel x y h => cases h; exact Or.inr rfl
    | refl => exact Or.inl rfl
    | symm x y _ ih => rcases ih with rfl | h <;> simp_all
    | trans x y z _ _ ih₁ ih₂ =>
        rcases ih₁ with rfl | h₁ <;> rcases ih₂ with rfl | h₂ <;> simp_all
  · rintro (rfl | rfl)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ (apm_t00A02_antipodalRel.antipodal x)

lemma apm_t00A02_antipodalCover_eq_iff
    (x y : apm_t00A02_Sphere2) :
    apm_t00A02_antipodalCover x = apm_t00A02_antipodalCover y ↔
      y = x ∨ y = -x := by
  unfold apm_t00A02_antipodalCover
  constructor
  · intro h
    exact (apm_t00A02_antipodal_eqvGen_iff x y).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((apm_t00A02_antipodal_eqvGen_iff x y).mpr h)

lemma apm_t00A02_antipodalCover_surjective :
    Function.Surjective apm_t00A02_antipodalCover := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, rfl⟩

lemma apm_t00A02_antipodalCover_fiber_card
    (b : apm_t00A02_RP2) :
    Nat.card {e : apm_t00A02_Sphere2 //
      apm_t00A02_antipodalCover e = b} = 2 := by
  obtain ⟨x, rfl⟩ := apm_t00A02_antipodalCover_surjective b
  have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro hx
    have hs := x.property
    simp [hx] at hs
  have hneg : (-x : apm_t00A02_Sphere2) ≠ x := by
    intro h
    apply hx0
    have h' : -(x : EuclideanSpace ℝ (Fin 3)) = x := congrArg Subtype.val h
    have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      rw [two_smul]
      simpa using (congrArg
        (fun z ↦ z + (x : EuclideanSpace ℝ (Fin 3))) h').symm
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  let e : Bool ≃ {z : apm_t00A02_Sphere2 //
      apm_t00A02_antipodalCover z = apm_t00A02_antipodalCover x} :=
    { toFun := fun q ↦ q.casesOn
        ⟨x, rfl⟩ ⟨-x, apm_t00A02_antipodalCover_neg x⟩
      invFun := fun z ↦ if z.1 = x then false else true
      left_inv := by
        intro q
        cases q <;> simp [hneg]
      right_inv := by
        intro z
        apply Subtype.ext
        rcases (apm_t00A02_antipodalCover_eq_iff x z.1).mp z.2.symm with h | h
        · simp [h]
        · simp [h, hneg] }
  rw [Nat.card_congr e.symm]
  simp

inductive apm_t00A02_wedgeRel (r₀ : apm_t00A02_RP2) :
    Sum apm_t00A02_RP2 apm_t00A02_RP2 →
      Sum apm_t00A02_RP2 apm_t00A02_RP2 → Prop
  | base : apm_t00A02_wedgeRel r₀ (Sum.inl r₀) (Sum.inr r₀)

def apm_t00A02_wedge (r₀ : apm_t00A02_RP2) :=
  Quotient (Relation.EqvGen.setoid (apm_t00A02_wedgeRel r₀))

noncomputable instance (r₀ : apm_t00A02_RP2) :
    TopologicalSpace (apm_t00A02_wedge r₀) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t00A02_RP2 apm_t00A02_RP2 ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t00A02_wedgeRel r₀)) z)
    inferInstance

structure apm_t00A02_coverWitness (B : Type) [TopologicalSpace B]
    (n : ℕ) (regular : Bool) where
  E : Type
  topology : TopologicalSpace E
  p : E → B
  covering : @apm_t00A02_isNfoldCover E B topology _ n p
  connected : @IsConnected E topology (Set.univ : Set E)
  regularity : if regular then
    @apm_t00A02_isRegularCover E B topology _ p
  else ¬@apm_t00A02_isRegularCover E B topology _ p

lemma apm_t00A02_coverWitness.regular
    {B : Type} [TopologicalSpace B] {n : ℕ}
    (w : apm_t00A02_coverWitness B n true) :
    @apm_t00A02_isRegularCover w.E B w.topology _ w.p := by
  simpa using w.regularity

lemma apm_t00A02_coverWitness.not_regular
    {B : Type} [TopologicalSpace B] {n : ℕ}
    (w : apm_t00A02_coverWitness B n false) :
    ¬@apm_t00A02_isRegularCover w.E B w.topology _ w.p := by
  simpa using w.regularity

/-! ## Remaining independently assignable obligations -/

abbrev apm_t00A02_antipodalCover_isCoveringMap_aux_G := ZMod 2

def apm_t00A02_antipodalCover_isCoveringMap_aux_vadd
    (g : apm_t00A02_antipodalCover_isCoveringMap_aux_G)
    (x : apm_t00A02_Sphere2) : apm_t00A02_Sphere2 :=
  if g = 0 then x else -x

local instance : AddAction apm_t00A02_antipodalCover_isCoveringMap_aux_G
    apm_t00A02_Sphere2 where
  vadd := apm_t00A02_antipodalCover_isCoveringMap_aux_vadd
  zero_vadd x := by
    change apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 0 x = x
    simp [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd]
  add_vadd g h x := by
    change apm_t00A02_antipodalCover_isCoveringMap_aux_vadd (g + h) x =
      apm_t00A02_antipodalCover_isCoveringMap_aux_vadd g
        (apm_t00A02_antipodalCover_isCoveringMap_aux_vadd h x)
    fin_cases g <;> fin_cases h
    · change apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 0 x =
        apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 0
          (apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 0 x)
      simp [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd]
    · change apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 1 x =
        apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 0
          (apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 1 x)
      simp [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd,
        show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 1 x =
        apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 1
          (apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 0 x)
      simp [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd,
        show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 0 x =
        apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 1
          (apm_t00A02_antipodalCover_isCoveringMap_aux_vadd 1 x)
      simp [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd,
        show (1 : ZMod 2) ≠ 0 by decide]

local instance : ContinuousConstVAdd
    apm_t00A02_antipodalCover_isCoveringMap_aux_G apm_t00A02_Sphere2 where
  continuous_const_vadd g := by
    fin_cases g
    · simpa [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd] using
        (continuous_id : Continuous (id : apm_t00A02_Sphere2 → apm_t00A02_Sphere2))
    · exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

theorem apm_t00A02_antipodalCover_isCoveringMap :
    IsCoveringMap apm_t00A02_antipodalCover := by
  let G := apm_t00A02_antipodalCover_isCoveringMap_aux_G
  have hfree : ∀ g : G, ∀ x : apm_t00A02_Sphere2, g +ᵥ x = x → g = 0 := by
    intro g x hg
    fin_cases g
    · rfl
    · exfalso
      have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
        intro hx
        have hs := x.property
        simp [hx] at hs
      apply hx0
      have h' : -(x : EuclideanSpace ℝ (Fin 3)) = x := by
        simpa [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd] using
          congrArg Subtype.val hg
      have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
        rw [two_smul]
        simpa using (congrArg
          (fun z ↦ z + (x : EuclideanSpace ℝ (Fin 3))) h').symm
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hq : Topology.IsQuotientMap apm_t00A02_antipodalCover :=
    isQuotientMap_quotient_mk'
  have horbit : ∀ {x y : apm_t00A02_Sphere2},
      apm_t00A02_antipodalCover x = apm_t00A02_antipodalCover y ↔
        x ∈ AddAction.orbit G y := by
    intro x y
    rw [apm_t00A02_antipodalCover_eq_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨(1 : ZMod 2), by
          change apm_t00A02_antipodalCover_isCoveringMap_aux_vadd
            (1 : ZMod 2) (-x) = x
          simp only [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd,
            if_neg (show (1 : ZMod 2) ≠ 0 by decide), neg_neg]⟩
    · rintro ⟨g, rfl⟩
      fin_cases g
      · left
        change y = apm_t00A02_antipodalCover_isCoveringMap_aux_vadd (0 : ZMod 2) y
        norm_num [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd]
      · right
        change y = -apm_t00A02_antipodalCover_isCoveringMap_aux_vadd (1 : ZMod 2) y
        norm_num [apm_t00A02_antipodalCover_isCoveringMap_aux_vadd]
  letI : IsCancelVAdd G apm_t00A02_Sphere2 :=
    isCancelVAdd_iff_eq_zero_of_vadd_eq.mpr hfree
  exact (hq.isAddQuotientCoveringMap_of_properlyDiscontinuousVAdd horbit).isCoveringMap _ _

/-- Transport a shared RP2-wedge witness to this file's wedge at any basepoint. -/
lemma apm_t00A02_shared_cover_adapter_aux_norm
    (x y : apm_t00A02_Sphere2) :
    ‖(x : EuclideanSpace ℝ (Fin 3))‖ = ‖(y : EuclideanSpace ℝ (Fin 3))‖ :=
  (mem_sphere_zero_iff_norm.mp x.property).trans
    (mem_sphere_zero_iff_norm.mp y.property).symm

set_option maxHeartbeats 4000000 in
noncomputable def apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph
    (x y : apm_t00A02_Sphere2) :
    apm_t00A02_Sphere2 ≃ₜ apm_t00A02_Sphere2 := by
  let ρ : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Submodule.reflection ((ℝ ∙ ((x : EuclideanSpace ℝ (Fin 3)) - y))ᗮ)
  have hρ : ρ (x : EuclideanSpace ℝ (Fin 3)) = y := by
    apply Submodule.reflection_sub
    exact (mem_sphere_zero_iff_norm.mp x.property).trans
      (mem_sphere_zero_iff_norm.mp y.property).symm
  exact
    { toFun := fun z ↦ ⟨ρ z, by
          exact mem_sphere_zero_iff_norm.mpr (ρ.norm_map z |>.trans
            (mem_sphere_zero_iff_norm.mp z.property))⟩
      invFun := fun z ↦ ⟨ρ.symm z, by
          exact mem_sphere_zero_iff_norm.mpr (ρ.symm.norm_map z |>.trans
            (mem_sphere_zero_iff_norm.mp z.property))⟩
      left_inv := fun z ↦ Subtype.ext (ρ.symm_apply_apply z)
      right_inv := fun z ↦ Subtype.ext (ρ.apply_symm_apply z)
      continuous_toFun := continuous_induced_rng.mpr
        (ρ.continuous.comp continuous_subtype_val)
      continuous_invFun := continuous_induced_rng.mpr
        (ρ.symm.continuous.comp continuous_subtype_val) }

lemma apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph_map
    (x y : apm_t00A02_Sphere2) :
    apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y x = y := by
  apply Subtype.ext
  dsimp [apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph]
  exact Submodule.reflection_sub ((mem_sphere_zero_iff_norm.mp x.property).trans
    (mem_sphere_zero_iff_norm.mp y.property).symm)

noncomputable def apm_t00A02_shared_cover_adapter_aux_rpHomeomorph
    (x y : apm_t00A02_Sphere2) :
    ConstructionTargets.WedgePermutationCover.RP2 ≃ₜ apm_t00A02_RP2 where
  toFun := Quotient.lift
    (fun z ↦ Quotient.mk _
      (apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y z)) (by
      intro a b hab
      apply Quotient.sound
      induction hab with
      | rel a b h =>
          cases h
          exact Relation.EqvGen.rel _ _ (by
            rw [show (apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y) (-a) =
              -(apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y a) by
                apply Subtype.ext
                dsimp [apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph]
                exact map_neg _ _]
            exact apm_t00A02_antipodalRel.antipodal
              (apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y a))
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  invFun := Quotient.lift
    (fun z ↦ Quotient.mk _
      ((apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y).symm z)) (by
      intro a b hab
      apply Quotient.sound
      induction hab with
      | rel a b h =>
          cases h
          exact Relation.EqvGen.rel _ _ (by
            rw [show (apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y).symm (-a) =
              -(apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y).symm a by
                apply Subtype.ext
                dsimp [apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph]
                exact map_neg _ _]
            exact ConstructionTargets.WedgePermutationCover.AntipodalRel.antipodal
              ((apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y).symm a))
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
  left_inv := by rintro ⟨z⟩; change Quotient.mk _ _ = Quotient.mk _ z; simp
  right_inv := by rintro ⟨z⟩; change Quotient.mk _ _ = Quotient.mk _ z; simp
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng.comp
      (apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y).continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng.comp
      (apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y).symm.continuous

noncomputable def apm_t00A02_shared_cover_adapter_aux_wedgeHomeomorph
    (r₀ : apm_t00A02_RP2) :
    ConstructionTargets.WedgePermutationCover.Wedge
        ConstructionTargets.WedgePermutationCover.RP2
        ConstructionTargets.WedgePermutationCover.RP2
        ConstructionTargets.WedgePermutationCover.rpBase
        ConstructionTargets.WedgePermutationCover.rpBase ≃ₜ
      apm_t00A02_wedge r₀ := by
  let y : apm_t00A02_Sphere2 := Classical.choose (Quotient.exists_rep r₀)
  have hy : apm_t00A02_antipodalCover y = r₀ := Classical.choose_spec (Quotient.exists_rep r₀)
  let x : apm_t00A02_Sphere2 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let e := apm_t00A02_shared_cover_adapter_aux_rpHomeomorph x y
  have he : e ConstructionTargets.WedgePermutationCover.rpBase = r₀ := by
      change Quotient.mk _
        (apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph x y x) = _
      rw [apm_t00A02_shared_cover_adapter_aux_sphereHomeomorph_map]
      exact hy
  exact
      { toFun := Quotient.lift (fun z ↦ Quotient.mk _ (Sum.map e e z)) (by
            intro a b hab
            apply Quotient.sound
            induction hab with
            | rel a b h => cases h; exact Relation.EqvGen.rel _ _ (by
                simpa [he] using (apm_t00A02_wedgeRel.base (r₀ := r₀)))
            | refl => exact Relation.EqvGen.refl _
            | symm _ _ _ ih => exact ih.symm
            | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
        invFun := Quotient.lift (fun z ↦ Quotient.mk _ (Sum.map e.symm e.symm z)) (by
            intro a b hab
            apply Quotient.sound
            induction hab with
            | rel a b h =>
                cases h
                have hes : e.symm r₀ =
                    ConstructionTargets.WedgePermutationCover.rpBase := by
                  rw [← he]; simp
                exact Relation.EqvGen.rel _ _ (by
                  simpa [hes] using
                    (ConstructionTargets.WedgePermutationCover.WedgeRel.base
                      (a := ConstructionTargets.WedgePermutationCover.rpBase)
                      (b := ConstructionTargets.WedgePermutationCover.rpBase)))
            | refl => exact Relation.EqvGen.refl _
            | symm _ _ _ ih => exact ih.symm
            | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)
        left_inv := by
          rintro ⟨z⟩
          cases z with
          | inl v => change Quotient.mk _ (Sum.inl _) = Quotient.mk _ (Sum.inl _); rw [e.symm_apply_apply]
          | inr v => change Quotient.mk _ (Sum.inr _) = Quotient.mk _ (Sum.inr _); rw [e.symm_apply_apply]
        right_inv := by
          rintro ⟨z⟩
          cases z with
          | inl v => change Quotient.mk _ (Sum.inl _) = Quotient.mk _ (Sum.inl _); rw [e.apply_symm_apply]
          | inr v => change Quotient.mk _ (Sum.inr _) = Quotient.mk _ (Sum.inr _); rw [e.apply_symm_apply]
        continuous_toFun := by
          apply Continuous.quotient_lift
          exact continuous_coinduced_rng.comp (e.continuous.sumMap e.continuous)
        continuous_invFun := by
          apply Continuous.quotient_lift
          exact continuous_coinduced_rng.comp
            (e.symm.continuous.sumMap e.symm.continuous) }

theorem apm_t00A02_shared_cover_adapter
    (r : Bool) (r₀ : apm_t00A02_RP2) :
    Nonempty (ConstructionTargets.WedgePermutationCover.CoverWitness
      (ConstructionTargets.WedgePermutationCover.Wedge
        ConstructionTargets.WedgePermutationCover.RP2
        ConstructionTargets.WedgePermutationCover.RP2
        ConstructionTargets.WedgePermutationCover.rpBase
        ConstructionTargets.WedgePermutationCover.rpBase) 4 r) →
    Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 r) := by
  intro hw
  obtain ⟨w⟩ := ConstructionTargets.WedgePermutationCover.coverWitness_homeomorph_base
    (apm_t00A02_shared_cover_adapter_aux_wedgeHomeomorph r₀) hw
  refine ⟨?_⟩
  exact { E := w.E
          topology := w.topology
          p := w.p
          covering := w.covering
          connected := w.connected
          regularity := w.regularity }

/-- Assembly: the shared regular RP2-wedge cover, moved to this file's wedge. -/
theorem apm_t00A02_regular_wedge_cover
    (hanti : IsCoveringMap apm_t00A02_antipodalCover)
    (r₀ : apm_t00A02_RP2) :
    Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 true) := by
  exact apm_t00A02_shared_cover_adapter true r₀
    ConstructionTargets.WedgePermutationCover.rp2Wedge_regular_four_cover

/-- LIBRARY: construct the irregular four-sheeted cover from involutions
`(12)` and `(14)(23)`. -/
theorem apm_t00A02_irregular_wedge_cover
    (hanti : IsCoveringMap apm_t00A02_antipodalCover)
    (r₀ : apm_t00A02_RP2) :
    Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 false) := by
  exact apm_t00A02_shared_cover_adapter false r₀
    ConstructionTargets.WedgePermutationCover.rp2Wedge_irregular_four_cover

/-- LIBRARY: finite-cover Euler characteristic plus classification of closed
orientable surfaces, specialized to degree ten over genus five. -/
theorem apm_t00A02_connected_ten_cover_homeomorph :
    ∀ (F E₁ E₂ : Type)
        [TopologicalSpace F] [T2Space F] [CompactSpace F]
        [PathConnectedSpace F] [ChartedSpace apm_t00A02_E2 F]
        [IsManifold apm_t00A02_I2 (⊤ : ℕ∞) F]
        [TopologicalSpace E₁] [PathConnectedSpace E₁]
        [TopologicalSpace E₂] [PathConnectedSpace E₂]
        (_hF : apm_t00A02_isGenusFiveSurface F)
        (p₁ : E₁ → F) (p₂ : E₂ → F),
      apm_t00A02_isNfoldCover 10 p₁ →
      apm_t00A02_isNfoldCover 10 p₂ → Nonempty (E₁ ≃ₜ E₂) := by
  sorry

theorem apm_t00a02 :
    (∀ (F E₁ E₂ : Type)
        [TopologicalSpace F] [T2Space F] [CompactSpace F]
        [PathConnectedSpace F] [ChartedSpace apm_t00A02_E2 F]
        [IsManifold apm_t00A02_I2 (⊤ : ℕ∞) F]
        [TopologicalSpace E₁] [PathConnectedSpace E₁]
        [TopologicalSpace E₂] [PathConnectedSpace E₂]
        (hF : apm_t00A02_isGenusFiveSurface F)
        (p₁ : E₁ → F) (p₂ : E₂ → F),
      apm_t00A02_isNfoldCover 10 p₁ →
      apm_t00A02_isNfoldCover 10 p₂ → Nonempty (E₁ ≃ₜ E₂)) ∧
    apm_t00A02_isNfoldCover 2 apm_t00A02_antipodalCover ∧
    (∀ r₀ : apm_t00A02_RP2,
      Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 true) ∧
      Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 false)) := by
  have hanti := apm_t00A02_antipodalCover_isCoveringMap
  exact ⟨apm_t00A02_connected_ten_cover_homeomorph,
    ⟨hanti, apm_t00A02_antipodalCover_fiber_card⟩,
    fun r₀ ↦ ⟨apm_t00A02_regular_wedge_cover hanti r₀,
      apm_t00A02_irregular_wedge_cover hanti r₀⟩⟩

#print axioms apm_t00a02
