import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.DeckGroupQuotientFundamentalGroup

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

-- BEGIN SEAT AREA
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
-- END SEAT AREA

/-- LIBRARY: construct the regular four-sheeted cover from the two commuting
fixed-point-free involutions `(12)(34)` and `(13)(24)`. -/
theorem apm_t00A02_regular_wedge_cover
    (hanti : IsCoveringMap apm_t00A02_antipodalCover)
    (r₀ : apm_t00A02_RP2) :
    Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 true) := by
  sorry

/-- LIBRARY: construct the irregular four-sheeted cover from involutions
`(12)` and `(14)(23)`. -/
theorem apm_t00A02_irregular_wedge_cover
    (hanti : IsCoveringMap apm_t00A02_antipodalCover)
    (r₀ : apm_t00A02_RP2) :
    Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 false) := by
  sorry

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
