import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.TwoOpenFreeProductMapping
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.IntegralOpenCoverMayerVietoris
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.SurfaceSchoenflies
import ConstructionTargets.T97A04FrozenH1Coordinate
import ConstructionTargets.BoundaryTorusIntegralHomologyComplete
import ConstructionTargets.CircleSingularHomology
import ConstructionTargets.ProjectiveQuotientExactSplitting
import ConstructionTargets.SingularHomologyHomotopy

/-! # Blueprint for APM t03J02 -/

open CategoryTheory

noncomputable section

abbrev apm_t03J02_Torus := Circle × Circle

inductive apm_t03J02_glueRel
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Sum apm_t03J02_Torus apm_t03J02_Torus →
      Sum apm_t03J02_Torus apm_t03J02_Torus → Prop
  | glue (z : Circle) :
      apm_t03J02_glueRel j₁ j₂ (Sum.inl (j₁ z)) (Sum.inr (j₂ z))

def apm_t03J02_space (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :=
  Quotient (Relation.EqvGen.setoid (apm_t03J02_glueRel j₁ j₂))

noncomputable instance (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    TopologicalSpace (apm_t03J02_space j₁ j₂) :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t03J02_Torus apm_t03J02_Torus ↦
      Quotient.mk (Relation.EqvGen.setoid (apm_t03J02_glueRel j₁ j₂)) z)
    inferInstance

def apm_t03J02_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Sum apm_t03J02_Torus apm_t03J02_Torus → apm_t03J02_space j₁ j₂ :=
  fun z => Quotient.mk _ z

lemma apm_t03J02_continuous_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Continuous (apm_t03J02_quotientMap j₁ j₂) := by
  exact continuous_coinduced_rng

lemma apm_t03J02_surjective_quotientMap
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    Function.Surjective (apm_t03J02_quotientMap j₁ j₂) := by
  exact Quotient.mk_surjective

lemma apm_t03J02_glue_eq
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (z : Circle) :
    apm_t03J02_quotientMap j₁ j₂ (Sum.inl (j₁ z)) =
      apm_t03J02_quotientMap j₁ j₂ (Sum.inr (j₂ z)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (apm_t03J02_glueRel.glue z)

lemma apm_t03J02_gluedDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) {x y}
    (hxy : Relation.EqvGen (apm_t03J02_glueRel j₁ j₂) x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
    cases hab with
    | glue z => exact hfg z
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t03J02_gluedDesc
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) :
    C(apm_t03J02_space j₁ j₂, Y) := by
  let raw : Sum apm_t03J02_Torus apm_t03J02_Torus → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy =>
      apm_t03J02_gluedDesc_respects j₁ j₂ f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy =>
      apm_t03J02_gluedDesc_respects j₁ j₂ f g hfg hxy)⟩

@[simp] lemma apm_t03J02_gluedDesc_inl
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) (x : apm_t03J02_Torus) :
    apm_t03J02_gluedDesc j₁ j₂ f g hfg
      (apm_t03J02_quotientMap j₁ j₂ (.inl x)) = f x := rfl

@[simp] lemma apm_t03J02_gluedDesc_inr
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z)) (x : apm_t03J02_Torus) :
    apm_t03J02_gluedDesc j₁ j₂ f g hfg
      (apm_t03J02_quotientMap j₁ j₂ (.inr x)) = g x := rfl

lemma apm_t03J02_gluedDesc_unique
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (f g : C(apm_t03J02_Torus, Y))
    (hfg : ∀ z, f (j₁ z) = g (j₂ z))
    (u : C(apm_t03J02_space j₁ j₂, Y))
    (hul : ∀ x, u (apm_t03J02_quotientMap j₁ j₂ (.inl x)) = f x)
    (hur : ∀ x, u (apm_t03J02_quotientMap j₁ j₂ (.inr x)) = g x) :
    u = apm_t03J02_gluedDesc j₁ j₂ f g hfg := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (x | x)
  · exact hul x
  · exact hur x

def apm_t03J02_gluedInl
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    C(apm_t03J02_Torus, apm_t03J02_space j₁ j₂) :=
  ⟨fun x ↦ apm_t03J02_quotientMap j₁ j₂ (.inl x),
    (apm_t03J02_continuous_quotientMap j₁ j₂).comp continuous_inl⟩

def apm_t03J02_gluedInr
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    C(apm_t03J02_Torus, apm_t03J02_space j₁ j₂) :=
  ⟨fun x ↦ apm_t03J02_quotientMap j₁ j₂ (.inr x),
    (apm_t03J02_continuous_quotientMap j₁ j₂).comp continuous_inr⟩

def apm_t03J02_CompatibleMaps
    (j₁ j₂ : C(Circle, apm_t03J02_Torus))
    (Y : Type*) [TopologicalSpace Y] :=
  {fg : C(apm_t03J02_Torus, Y) × C(apm_t03J02_Torus, Y) //
    ∀ z, fg.1 (j₁ z) = fg.2 (j₂ z)}

def apm_t03J02_gluedDescEquiv
    {Y : Type*} [TopologicalSpace Y]
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    apm_t03J02_CompatibleMaps j₁ j₂ Y ≃
      C(apm_t03J02_space j₁ j₂, Y) where
  toFun fg := apm_t03J02_gluedDesc j₁ j₂ fg.1.1 fg.1.2 fg.2
  invFun u := ⟨(u.comp (apm_t03J02_gluedInl j₁ j₂),
      u.comp (apm_t03J02_gluedInr j₁ j₂)), fun z ↦ by
        exact congrArg u (apm_t03J02_glue_eq j₁ j₂ z)⟩
  left_inv fg := by
    apply Subtype.ext
    apply Prod.ext <;> ext x <;> rfl
  right_inv u := by
    symm
    apply apm_t03J02_gluedDesc_unique j₁ j₂
        (u.comp (apm_t03J02_gluedInl j₁ j₂))
        (u.comp (apm_t03J02_gluedInr j₁ j₂))
        (fun z ↦ congrArg u (apm_t03J02_glue_eq j₁ j₂ z))
    · intro x
      rfl
    · intro x
      rfl

def apm_t03J02_basepoint
    (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (z₀ : Circle) :
    apm_t03J02_space j₁ j₂ :=
  Quotient.mk _ (Sum.inl (j₁ z₀))

abbrev apm_t03J02_generator := Fin 2 × Fin 2

def apm_t03J02_commutatorRelation (i : Fin 2) :
    FreeGroup apm_t03J02_generator :=
  FreeGroup.of (i, 0) * FreeGroup.of (i, 1) *
    (FreeGroup.of (i, 0))⁻¹ * (FreeGroup.of (i, 1))⁻¹

abbrev apm_t03J02_freeProductZ2Z2 :=
  PresentedGroup (Set.range apm_t03J02_commutatorRelation)

abbrev apm_t03J02_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

theorem apm_t03J02_isPushout (j₁ j₂ : C(Circle, apm_t03J02_Torus)) :
    CategoryTheory.IsPushout (TopCat.ofHom j₁) (TopCat.ofHom j₂)
      (TopCat.ofHom (apm_t03J02_gluedInl j₁ j₂))
      (TopCat.ofHom (apm_t03J02_gluedInr j₁ j₂)) := by
  sorry

def apm_t03J02_overlapToLeft
    {X : Type*} [TopologicalSpace X] (U V : Set X) : C((U ∩ V : Set X), U) :=
  ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def apm_t03J02_overlapToRight
    {X : Type*} [TopologicalSpace X] (U V : Set X) : C((U ∩ V : Set X), V) :=
  ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-! ### Replacing the collar (2026-11-03)

An arbitrary embedded circle has no cheap collar, so the open cover is not built on the quotient
`X`.  It is built on `Cyl ⊆ X × ℝ`: the left torus at height `-1`, the right torus at height `1`,
and the glued circle at all heights between.  There the cover is `s < 1/2`, `s > -1/2` and every
homotopy is linear in `s`.  `X` is homotopy equivalent to `Cyl` because each pair (torus, circle)
has the following neighbourhood deformation, from Tietze and straight lines in the flat torus. -/

open unitInterval

/-- `H` deforms the torus to a map carrying `{β < 1}` into the circle, fixing the circle. -/
structure apm_t03J02_Retractile (j : C(Circle, apm_t03J02_Torus)) where
  H : C(apm_t03J02_Torus × I, apm_t03J02_Torus)
  β : C(apm_t03J02_Torus, ℝ)
  H_zero : ∀ x, H (x, 0) = x
  H_fix : ∀ z t, H (j z, t) = j z
  β_nonneg : ∀ x, 0 ≤ β x
  β_le_one : ∀ x, β x ≤ 1
  β_fix : ∀ z, β (j z) = 0
  H_one : ∀ x, β x < 1 → H (x, 1) ∈ Set.range j

/-- Tietze extends the inverse of `j` to a map to `ℂ`; normalising gives a retraction `k` of an
open `N` onto the circle.  Straight lines in the flat torus join `x` to `k x` when they are close;
cut off with a function of the distance to the circle. -/
theorem apm_t03J02_exists_retractile (j : C(Circle, apm_t03J02_Torus))
    (hj : Topology.IsEmbedding j) : Nonempty (apm_t03J02_Retractile j) := by
  sorry

section Glued
variable (j₁ j₂ : C(Circle, apm_t03J02_Torus))

/-- The glued circle in the quotient. -/
def apm_t03J02_gluedCircle : C(Circle, apm_t03J02_space j₁ j₂) :=
  (apm_t03J02_gluedInl j₁ j₂).comp j₁

variable {j₁ j₂}

theorem apm_t03J02_inl_eq_inl_iff (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) {x y : apm_t03J02_Torus} :
    apm_t03J02_gluedInl j₁ j₂ x = apm_t03J02_gluedInl j₁ j₂ y ↔ x = y := by
  sorry

theorem apm_t03J02_inr_eq_inr_iff (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) {x y : apm_t03J02_Torus} :
    apm_t03J02_gluedInr j₁ j₂ x = apm_t03J02_gluedInr j₁ j₂ y ↔ x = y := by
  sorry

theorem apm_t03J02_inl_eq_inr_iff (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) {x y : apm_t03J02_Torus} :
    apm_t03J02_gluedInl j₁ j₂ x = apm_t03J02_gluedInr j₁ j₂ y ↔
      ∃ z, x = j₁ z ∧ y = j₂ z := by
  sorry

theorem apm_t03J02_t2Space (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    T2Space (apm_t03J02_space j₁ j₂) := by
  sorry

theorem apm_t03J02_compactSpace : CompactSpace (apm_t03J02_space j₁ j₂) := by
  sorry

variable (j₁ j₂)

/-- The left torus at height `-1`, the right at `1`, and the glued circle at every height between. -/
def apm_t03J02_cylSet : Set (apm_t03J02_space j₁ j₂ × ℝ) :=
  {p | (p.2 = -1 ∧ p.1 ∈ Set.range (apm_t03J02_gluedInl j₁ j₂)) ∨
    (p.2 = 1 ∧ p.1 ∈ Set.range (apm_t03J02_gluedInr j₁ j₂)) ∨
    (p.1 ∈ Set.range (apm_t03J02_gluedCircle j₁ j₂) ∧ p.2 ∈ Set.Icc (-1 : ℝ) 1)}

abbrev apm_t03J02_Cyl := ↥(apm_t03J02_cylSet j₁ j₂)

/-- The deformation of the quotient obtained by gluing two `Retractile`s, together with the height
function it is paired with. -/
structure apm_t03J02_Deform where
  E : C(apm_t03J02_space j₁ j₂ × I, apm_t03J02_space j₁ j₂)
  B : C(apm_t03J02_space j₁ j₂, ℝ)
  E_zero : ∀ x, E (x, 0) = x
  mem₁ : ∀ p ∈ apm_t03J02_cylSet j₁ j₂, ∀ t : I, (E (p.1, t), p.2) ∈ apm_t03J02_cylSet j₁ j₂
  mem₂ : ∀ p ∈ apm_t03J02_cylSet j₁ j₂, ∀ t : I,
    (E (p.1, 1), (1 - (t : ℝ)) * p.2 + t * B p.1) ∈ apm_t03J02_cylSet j₁ j₂
  fibre : ∀ x, ∃ s, (x, s) ∈ apm_t03J02_cylSet j₁ j₂

variable {j₁ j₂}

def apm_t03J02_exists_deform_aux_E
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) :
    C(apm_t03J02_space j₁ j₂ × I, apm_t03J02_space j₁ j₂) :=
  ContinuousMap.uncurry (apm_t03J02_gluedDesc j₁ j₂
    (ContinuousMap.curry ((apm_t03J02_gluedInl j₁ j₂).comp R₁.H))
    (ContinuousMap.curry ((apm_t03J02_gluedInr j₁ j₂).comp R₂.H))
    (fun z ↦ by
      ext t
      simp only [ContinuousMap.curry_apply, ContinuousMap.comp_apply]
      rw [R₁.H_fix, R₂.H_fix]
      exact apm_t03J02_glue_eq j₁ j₂ z))

def apm_t03J02_exists_deform_aux_B
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) :
    C(apm_t03J02_space j₁ j₂, ℝ) :=
  apm_t03J02_gluedDesc j₁ j₂
    ⟨fun x ↦ -R₁.β x, by fun_prop⟩ R₂.β
    (fun z ↦ by dsimp; rw [R₁.β_fix, R₂.β_fix]; simp)

lemma apm_t03J02_exists_deform_aux_E_circle
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) (z : Circle) (t : I) :
    apm_t03J02_exists_deform_aux_E R₁ R₂ (apm_t03J02_gluedCircle j₁ j₂ z, t) =
      apm_t03J02_gluedCircle j₁ j₂ z := by
  change apm_t03J02_gluedInl j₁ j₂ (R₁.H (j₁ z, t)) = _
  rw [R₁.H_fix]
  rfl

lemma apm_t03J02_exists_deform_aux_B_circle
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) (z : Circle) :
    apm_t03J02_exists_deform_aux_B R₁ R₂ (apm_t03J02_gluedCircle j₁ j₂ z) = 0 := by
  change -R₁.β (j₁ z) = 0
  rw [R₁.β_fix, neg_zero]

theorem apm_t03J02_exists_deform_aux_mem₁
    (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂)
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) :
    ∀ p ∈ apm_t03J02_cylSet j₁ j₂, ∀ t : I,
      (apm_t03J02_exists_deform_aux_E R₁ R₂ (p.1, t), p.2) ∈
        apm_t03J02_cylSet j₁ j₂ := by
  rintro ⟨x, s⟩ h t
  rcases h with ⟨hs, a, rfl⟩ | ⟨hs, a, rfl⟩ | ⟨⟨z, rfl⟩, hs⟩
  · exact Or.inl ⟨hs, ⟨R₁.H (a, t), rfl⟩⟩
  · exact Or.inr (Or.inl ⟨hs, ⟨R₂.H (a, t), rfl⟩⟩)
  · refine Or.inr (Or.inr ⟨?_, hs⟩)
    change apm_t03J02_exists_deform_aux_E R₁ R₂ (apm_t03J02_gluedCircle j₁ j₂ z, t) ∈ _
    rw [apm_t03J02_exists_deform_aux_E_circle]
    exact ⟨z, rfl⟩

theorem apm_t03J02_exists_deform_aux_mem₂
    (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂)
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) :
    ∀ p ∈ apm_t03J02_cylSet j₁ j₂, ∀ t : I,
      (apm_t03J02_exists_deform_aux_E R₁ R₂ (p.1, 1),
        (1 - (t : ℝ)) * p.2 + t * apm_t03J02_exists_deform_aux_B R₁ R₂ p.1) ∈
          apm_t03J02_cylSet j₁ j₂ := by
  rintro ⟨x, s⟩ h ⟨t, ht₀, ht₁⟩
  rcases h with ⟨hs, a, rfl⟩ | ⟨hs, a, rfl⟩ | ⟨⟨z, rfl⟩, hs⟩
  · change s = -1 at hs
    subst hs
    have hb₀ := R₁.β_nonneg a
    have hb₁ := R₁.β_le_one a
    change (apm_t03J02_gluedInl j₁ j₂ (R₁.H (a, 1)),
      (1 - t) * (-1) + t * (-R₁.β a)) ∈ apm_t03J02_cylSet j₁ j₂
    by_cases hb : R₁.β a < 1
    · obtain ⟨z, hz⟩ := R₁.H_one a hb
      rw [← hz]
      refine Or.inr (Or.inr ⟨⟨z, rfl⟩, ?_, ?_⟩)
      · change -1 ≤ (1 - t) * (-1) + t * (-R₁.β a); nlinarith
      · change (1 - t) * (-1) + t * (-R₁.β a) ≤ 1; nlinarith
    · have hb' : R₁.β a = 1 := le_antisymm hb₁ (not_lt.1 hb)
      refine Or.inl ⟨?_, ⟨R₁.H (a, 1), rfl⟩⟩
      change (1 - t) * (-1) + t * (-R₁.β a) = -1
      rw [hb']; ring
  · change s = 1 at hs
    subst hs
    have hb₀ := R₂.β_nonneg a
    have hb₁ := R₂.β_le_one a
    change (apm_t03J02_gluedInr j₁ j₂ (R₂.H (a, 1)),
      (1 - t) * 1 + t * R₂.β a) ∈ apm_t03J02_cylSet j₁ j₂
    by_cases hb : R₂.β a < 1
    · obtain ⟨z, hz⟩ := R₂.H_one a hb
      have hg : apm_t03J02_gluedInr j₁ j₂ (j₂ z) = apm_t03J02_gluedCircle j₁ j₂ z :=
        (apm_t03J02_glue_eq j₁ j₂ z).symm
      rw [← hz, hg]
      refine Or.inr (Or.inr ⟨⟨z, rfl⟩, ?_, ?_⟩)
      · change -1 ≤ (1 - t) * 1 + t * R₂.β a; nlinarith
      · change (1 - t) * 1 + t * R₂.β a ≤ 1; nlinarith
    · have hb' : R₂.β a = 1 := le_antisymm hb₁ (not_lt.1 hb)
      refine Or.inr (Or.inl ⟨?_, ⟨R₂.H (a, 1), rfl⟩⟩)
      change (1 - t) * 1 + t * R₂.β a = 1
      rw [hb']; ring
  · have hs₁ : -1 ≤ s := hs.1
    have hs₂ : s ≤ 1 := hs.2
    change (apm_t03J02_exists_deform_aux_E R₁ R₂ (apm_t03J02_gluedCircle j₁ j₂ z, 1),
      (1 - t) * s + t * apm_t03J02_exists_deform_aux_B R₁ R₂
        (apm_t03J02_gluedCircle j₁ j₂ z)) ∈ apm_t03J02_cylSet j₁ j₂
    rw [apm_t03J02_exists_deform_aux_E_circle, apm_t03J02_exists_deform_aux_B_circle]
    refine Or.inr (Or.inr ⟨⟨z, rfl⟩, ?_, ?_⟩)
    · change -1 ≤ (1 - t) * s + t * 0; nlinarith
    · change (1 - t) * s + t * 0 ≤ 1; nlinarith

theorem apm_t03J02_exists_deform_aux_fibre
    (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    ∀ x : apm_t03J02_space j₁ j₂, ∃ s, (x, s) ∈ apm_t03J02_cylSet j₁ j₂ := by
  intro x
  refine Quotient.inductionOn x ?_
  rintro (a | a)
  · exact ⟨-1, Or.inl ⟨rfl, ⟨a, rfl⟩⟩⟩
  · exact ⟨1, Or.inr (Or.inl ⟨rfl, ⟨a, rfl⟩⟩)⟩

/-- `E = H₁` on the left and `H₂` on the right, `B = -β₁` on the left and `β₂` on the right.  Use
`apm_t03J02_gluedDesc` with target `C(I, X)` and uncurry for `E`. -/
theorem apm_t03J02_exists_deform (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂)
    (R₁ : apm_t03J02_Retractile j₁) (R₂ : apm_t03J02_Retractile j₂) :
    Nonempty (apm_t03J02_Deform j₁ j₂) := by
  exact ⟨⟨apm_t03J02_exists_deform_aux_E R₁ R₂,
    apm_t03J02_exists_deform_aux_B R₁ R₂,
    fun x ↦ by
      refine Quotient.inductionOn x ?_
      rintro (a | a)
      · change apm_t03J02_gluedInl j₁ j₂ (R₁.H (a, 0)) = _
        rw [R₁.H_zero]
        rfl
      · change apm_t03J02_gluedInr j₁ j₂ (R₂.H (a, 0)) = _
        rw [R₂.H_zero]
        rfl,
    apm_t03J02_exists_deform_aux_mem₁ hj₁ hj₂ R₁ R₂,
    apm_t03J02_exists_deform_aux_mem₂ hj₁ hj₂ R₁ R₂,
    apm_t03J02_exists_deform_aux_fibre hj₁ hj₂⟩⟩

/-- `c = fst`, `b x = (E (x, 1), B x)`.  `c ∘ b` is homotopic to the identity through `E`.
`b ∘ c` goes to `id` in two stages: `(x, s) ↦ (E (x, t), s)`, then
`(x, s) ↦ (E (x, 1), (1 - t) s + t B x)`. -/
theorem apm_t03J02_homotopyEquiv_cyl (D : apm_t03J02_Deform j₁ j₂) :
    Nonempty (ContinuousMap.HomotopyEquiv (apm_t03J02_space j₁ j₂) (apm_t03J02_Cyl j₁ j₂)) := by
  let c : C(apm_t03J02_Cyl j₁ j₂, apm_t03J02_space j₁ j₂) :=
    ⟨fun p ↦ p.1.1, continuous_subtype_val.fst⟩
  let b : C(apm_t03J02_space j₁ j₂, apm_t03J02_Cyl j₁ j₂) :=
    ⟨fun x ↦ ⟨(D.E (x, 1), D.B x), by
        obtain ⟨s, hs⟩ := D.fibre x
        simpa using D.mem₂ (x, s) hs 1⟩,
      by fun_prop⟩
  have hcb : (c.comp b).Homotopic (ContinuousMap.id _) := by
    apply ContinuousMap.Homotopic.symm
    let H : C(I × apm_t03J02_space j₁ j₂, apm_t03J02_space j₁ j₂) :=
      ⟨fun p ↦ D.E (p.2, p.1), by fun_prop⟩
    exact ⟨⟨H, D.E_zero, fun _ ↦ rfl⟩⟩
  let F : ContinuousMap.Homotopy (ContinuousMap.id (apm_t03J02_Cyl j₁ j₂))
      ⟨fun p ↦ ⟨(D.E (p.1.1, 1), p.1.2), D.mem₁ p.1 p.2 1⟩, by fun_prop⟩ :=
    { toContinuousMap := ⟨fun p ↦ ⟨(D.E (p.2.1.1, p.1), p.2.1.2), D.mem₁ p.2.1 p.2.2 p.1⟩,
        by fun_prop⟩,
      map_zero_left := by
        intro p
        apply Subtype.ext
        simp only [ContinuousMap.id_apply]
        rw [D.E_zero],
      map_one_left := by intro p; rfl }
  let G : ContinuousMap.Homotopy
      ⟨fun p : apm_t03J02_Cyl j₁ j₂ ↦ ⟨(D.E (p.1.1, 1), p.1.2), D.mem₁ p.1 p.2 1⟩,
        by fun_prop⟩ (b.comp c) :=
    { toContinuousMap := ⟨(fun p ↦
        ⟨(D.E (p.2.1.1, 1), (1 - (p.1 : ℝ)) * p.2.1.2 + p.1 * D.B p.2.1.1),
          D.mem₂ p.2.1 p.2.2 p.1⟩), by fun_prop⟩,
      map_zero_left := by intro p; apply Subtype.ext; simp,
      map_one_left := by intro p; apply Subtype.ext; simp [b, c] }
  exact ⟨⟨b, c, hcb, ContinuousMap.Homotopic.symm
    (ContinuousMap.Homotopic.trans ⟨F⟩ ⟨G⟩)⟩⟩

variable (j₁ j₂)

def apm_t03J02_cylLeft : Set (apm_t03J02_Cyl j₁ j₂) := {p | p.1.2 < 1 / 2}
def apm_t03J02_cylRight : Set (apm_t03J02_Cyl j₁ j₂) := {p | -(1 / 2) < p.1.2}

variable {j₁ j₂}

/-- Inverse `x ↦ (inl x, -1)`; homotopy `(x, s) ↦ (x, (1 - t) s - t)`.  Below height `1/2` the first
coordinate lies in the range of `inl`, which is a closed embedding by compactness and `T2`. -/
theorem apm_t03J02_cylLeft_equiv (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    ∃ e : ContinuousMap.HomotopyEquiv (apm_t03J02_cylLeft j₁ j₂) apm_t03J02_Torus,
      ∀ p, apm_t03J02_gluedInl j₁ j₂ (e.toFun p) = p.1.1.1 := by
  sorry

theorem apm_t03J02_cylRight_equiv (hj₁ : Topology.IsEmbedding j₁) (hj₂ : Topology.IsEmbedding j₂) :
    ∃ e : ContinuousMap.HomotopyEquiv (apm_t03J02_cylRight j₁ j₂) apm_t03J02_Torus,
      ∀ p, apm_t03J02_gluedInr j₁ j₂ (e.toFun p) = p.1.1.1 := by
  sorry

/-- Inverse `z ↦ (gluedCircle z, 0)`; homotopy `(x, s) ↦ (x, (1 - t) s)`. -/
theorem apm_t03J02_cylOverlap_equiv (hj₁ : Topology.IsEmbedding j₁)
    (hj₂ : Topology.IsEmbedding j₂) :
    ∃ e : ContinuousMap.HomotopyEquiv
        (apm_t03J02_cylLeft j₁ j₂ ∩ apm_t03J02_cylRight j₁ j₂ : Set (apm_t03J02_Cyl j₁ j₂)) Circle,
      ∀ p, apm_t03J02_gluedCircle j₁ j₂ (e.toFun p) = p.1.1.1 := by
  sorry

end Glued
