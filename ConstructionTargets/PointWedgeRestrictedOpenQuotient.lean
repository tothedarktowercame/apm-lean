import ConstructionTargets.PointWedgeQuotient

open Set Topology

noncomputable section

namespace ConstructionTargets.PointWedgeRestrictedOpenQuotient

open ConstructionTargets.PointWedgeQuotient

universe u v

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Representatives whose left and right coordinates lie in the prescribed subsets. -/
def restrictedPreimage (A : Set X) (B : Set Y) : Set (Sum X Y)
  | .inl x => x ∈ A
  | .inr y => y ∈ B

theorem restrictedPreimage_isOpen {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) :
    IsOpen (restrictedPreimage A B) := by
  rw [isOpen_sum_iff]
  exact ⟨hA, hB⟩

/-- The saturated restricted part of a point wedge. -/
def restrictedOpen (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :
    Set (Wedge x₀ y₀) :=
  quotientMap x₀ y₀ '' restrictedPreimage A B

theorem restrictedOpen_isOpen {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    IsOpen (restrictedOpen x₀ y₀ A B) := by
  exact isOpen_image_of_basepoints_mem _ (restrictedPreimage_isOpen hA hB) hx hy

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem quotientMap_preimage_restrictedOpen {x₀ : X} {y₀ : Y}
    {A : Set X} {B : Set Y} (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    quotientMap x₀ y₀ ⁻¹' restrictedOpen x₀ y₀ A B = restrictedPreimage A B := by
  exact preimage_image_of_basepoints_mem _ hx hy

theorem quotientMap_isQuotientMap (x₀ : X) (y₀ : Y) :
    IsQuotientMap (quotientMap x₀ y₀) := by
  exact ⟨surjective_quotientMap x₀ y₀, rfl⟩

/-- The restriction of the wedge quotient map to any open saturated pair of
subspaces is again a quotient map. This is the topology needed to identify
the resulting open subtype with the wedge of the two subtypes. -/
theorem restrictedOpen_quotientMap_isQuotientMap
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    IsQuotientMap
      ((restrictedOpen x₀ y₀ A B).restrictPreimage (quotientMap x₀ y₀)) := by
  apply (quotientMap_isQuotientMap x₀ y₀).restrictPreimage_isOpen
  exact restrictedOpen_isOpen hA hB hx hy

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem restrictedDomain_eq
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    {a : Sum X Y | quotientMap x₀ y₀ a ∈ restrictedOpen x₀ y₀ A B} =
      restrictedPreimage A B := by
  exact quotientMap_preimage_restrictedOpen hx hy

private def sumSubtypeEmbedding {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) :
    IsOpenEmbedding (Sum.map ((↑) : A → X) ((↑) : B → Y)) := by
  apply IsOpenEmbedding.sumElim
  · exact IsOpenEmbedding.inl.comp hA.isOpenEmbedding_subtypeVal
  · exact IsOpenEmbedding.inr.comp hB.isOpenEmbedding_subtypeVal
  · exact Function.Injective.sumMap Subtype.val_injective Subtype.val_injective

/-- The restricted representatives are homeomorphic to the coproduct of the
two open subspaces. -/
def restrictedPreimageHomeomorphSum
    {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) :
    {a : Sum X Y // a ∈ restrictedPreimage A B} ≃ₜ Sum A B :=
  (Homeomorph.setCongr (by
    ext a
    cases a with
    | inl x =>
        constructor
        · intro hx
          exact ⟨.inl ⟨x, hx⟩, rfl⟩
        · rintro ⟨s, hs⟩
          change x ∈ A
          cases s with
          | inl z =>
              have hz : z.1 = x := Sum.inl.inj hs
              exact hz ▸ z.2
          | inr z => simp at hs
    | inr y =>
        constructor
        · intro hy
          exact ⟨.inr ⟨y, hy⟩, rfl⟩
        · rintro ⟨s, hs⟩
          change y ∈ B
          cases s with
          | inl z => simp at hs
          | inr z =>
              have hz : z.1 = y := Sum.inr.inj hs
              exact hz ▸ z.2)).trans
    (sumSubtypeEmbedding hA hB).isEmbedding.toHomeomorph.symm

@[simp] theorem restrictedPreimageHomeomorphSum_left
    {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (x : X) (hx : x ∈ A) :
    restrictedPreimageHomeomorphSum hA hB ⟨.inl x, hx⟩ =
      .inl ⟨x, hx⟩ := by
  change (sumSubtypeEmbedding hA hB).isEmbedding.toHomeomorph.symm
    ⟨Sum.inl x, ⟨Sum.inl ⟨x, hx⟩, rfl⟩⟩ = Sum.inl ⟨x, hx⟩
  simpa using (sumSubtypeEmbedding hA hB).isEmbedding.toHomeomorph_symm_apply
    (Sum.inl ⟨x, hx⟩)

@[simp] theorem restrictedPreimageHomeomorphSum_right
    {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (y : Y) (hy : y ∈ B) :
    restrictedPreimageHomeomorphSum hA hB ⟨.inr y, hy⟩ =
      .inr ⟨y, hy⟩ := by
  change (sumSubtypeEmbedding hA hB).isEmbedding.toHomeomorph.symm
    ⟨Sum.inr y, ⟨Sum.inr ⟨y, hy⟩, rfl⟩⟩ = Sum.inr ⟨y, hy⟩
  simpa using (sumSubtypeEmbedding hA hB).isEmbedding.toHomeomorph_symm_apply
    (Sum.inr ⟨y, hy⟩)

abbrev RestrictedDomain (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :=
  {a : Sum X Y | quotientMap x₀ y₀ a ∈ restrictedOpen x₀ y₀ A B}

def restrictedDomainHomeomorphSum
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    RestrictedDomain x₀ y₀ A B ≃ₜ Sum A B :=
  (Homeomorph.setCongr (restrictedDomain_eq hx hy)).trans
    (restrictedPreimageHomeomorphSum hA hB)

@[simp] theorem restrictedDomainHomeomorphSum_left
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (x : X) (hx' : x ∈ A) :
    restrictedDomainHomeomorphSum hA hB hx hy
      ⟨.inl x, ⟨.inl x, hx', rfl⟩⟩ = .inl ⟨x, hx'⟩ := by
  exact restrictedPreimageHomeomorphSum_left hA hB x hx'

@[simp] theorem restrictedDomainHomeomorphSum_right
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (y : Y) (hy' : y ∈ B) :
    restrictedDomainHomeomorphSum hA hB hx hy
      ⟨.inr y, ⟨.inr y, hy', rfl⟩⟩ = .inr ⟨y, hy'⟩ := by
  exact restrictedPreimageHomeomorphSum_right hA hB y hy'

theorem smallQuotient_eq_of_eqvGen
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    {a b : Sum X Y} (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    ∀ (ha : a ∈ restrictedPreimage A B) (hb : b ∈ restrictedPreimage A B),
      quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)
          ((restrictedPreimageHomeomorphSum hA hB) ⟨a, ha⟩) =
        quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)
          ((restrictedPreimageHomeomorphSum hA hB) ⟨b, hb⟩) := by
  induction hab with
  | rel a b hab =>
      cases hab
      intro ha hb
      rw [restrictedPreimageHomeomorphSum_left,
        restrictedPreimageHomeomorphSum_right]
      apply Quotient.sound
      exact Relation.EqvGen.rel (Sum.inl (⟨x₀, ha⟩ : A))
        (Sum.inr (⟨y₀, hb⟩ : B)) Rel.base
  | refl a =>
      intro ha hb
      congr
  | symm a b _ ih =>
      intro ha hb
      exact (ih hb ha).symm
  | trans a b c hab hbc ihab ihbc =>
      intro ha hc
      have hb : b ∈ restrictedPreimage A B :=
        (mem_iff_of_eqvGen (a := a) (b := b) hx hy hab).mp ha
      exact (ihab ha hb).trans (ihbc hb hc)

def restrictedQuotientMap
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y} :
    RestrictedDomain x₀ y₀ A B → {z // z ∈ restrictedOpen x₀ y₀ A B} :=
  (restrictedOpen x₀ y₀ A B).restrictPreimage (quotientMap x₀ y₀)

def smallToRestrictedRep
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (s : Sum A B) : {z // z ∈ restrictedOpen x₀ y₀ A B} :=
  match s with
  | .inl x => ⟨quotientMap x₀ y₀ (.inl x.1), ⟨.inl x.1, x.2, rfl⟩⟩
  | .inr y => ⟨quotientMap x₀ y₀ (.inr y.1), ⟨.inr y.1, y.2, rfl⟩⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem smallToRestrictedRep_respects
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) (a b : Sum A B)
    (hab : Relation.EqvGen
      (Rel (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)) a b) :
    smallToRestrictedRep (x₀ := x₀) (y₀ := y₀) a =
      smallToRestrictedRep (x₀ := x₀) (y₀ := y₀) b := by
  induction hab with
  | rel a b hab =>
      cases hab
      apply Subtype.ext
      exact Quotient.sound
        (Relation.EqvGen.rel (Sum.inl x₀) (Sum.inr y₀) Rel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def smallToRestricted
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    Wedge (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) →
      {z // z ∈ restrictedOpen x₀ y₀ A B} :=
  Quotient.lift (smallToRestrictedRep (x₀ := x₀) (y₀ := y₀))
    (smallToRestrictedRep_respects hx hy)

def restrictedToSmall
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    {z // z ∈ restrictedOpen x₀ y₀ A B} →
      Wedge (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) := fun z =>
  quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)
    (restrictedDomainHomeomorphSum hA hB hx hy
      (Function.surjInv
        (restrictedOpen_quotientMap_isQuotientMap hA hB hx hy).surjective z))

theorem restrictedToSmall_comp_restrictedQuotientMap
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (a : RestrictedDomain x₀ y₀ A B) :
    restrictedToSmall hA hB hx hy (restrictedQuotientMap a) =
      quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)
        (restrictedDomainHomeomorphSum hA hB hx hy a) := by
  let q := restrictedQuotientMap
    (x₀ := x₀) (y₀ := y₀) (A := A) (B := B)
  let hs := (restrictedOpen_quotientMap_isQuotientMap hA hB hx hy).surjective
  let chosen := Function.surjInv hs (q a)
  have hq : q chosen = q a := Function.rightInverse_surjInv hs (q a)
  have hval : quotientMap x₀ y₀ chosen.1 = quotientMap x₀ y₀ a.1 :=
    congrArg Subtype.val hq
  have heqv : Relation.EqvGen (Rel x₀ y₀) chosen.1 a.1 :=
    Quotient.exact hval
  have hchosen : chosen.1 ∈ restrictedPreimage A B := by
    rw [← restrictedDomain_eq hx hy]
    exact chosen.2
  have ha : a.1 ∈ restrictedPreimage A B := by
    rw [← restrictedDomain_eq hx hy]
    exact a.2
  change quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)
      ((restrictedPreimageHomeomorphSum hA hB) ⟨chosen.1, hchosen⟩) =
    quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)
      ((restrictedPreimageHomeomorphSum hA hB) ⟨a.1, ha⟩)
  exact smallQuotient_eq_of_eqvGen hA hB hx hy heqv hchosen ha

omit [TopologicalSpace X] [TopologicalSpace Y] in
@[simp] theorem smallToRestricted_quotientMap_left
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) (x : A) :
    smallToRestricted hx hy
        (quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inl x)) =
      ⟨quotientMap x₀ y₀ (.inl x.1), ⟨.inl x.1, x.2, rfl⟩⟩ := rfl

omit [TopologicalSpace X] [TopologicalSpace Y] in
@[simp] theorem smallToRestricted_quotientMap_right
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) (y : B) :
    smallToRestricted hx hy
        (quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inr y)) =
      ⟨quotientMap x₀ y₀ (.inr y.1), ⟨.inr y.1, y.2, rfl⟩⟩ := rfl

theorem continuous_smallToRestrictedRep
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y} :
    Continuous (smallToRestrictedRep
      (x₀ := x₀) (y₀ := y₀) (A := A) (B := B)) := by
  rw [continuous_sum_dom]
  constructor
  · apply Continuous.subtype_mk
    exact (continuous_quotientMap x₀ y₀).comp
      (continuous_inl.comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact (continuous_quotientMap x₀ y₀).comp
      (continuous_inr.comp continuous_subtype_val)

theorem continuous_smallToRestricted
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    Continuous (smallToRestricted hx hy) := by
  apply (quotientMap_isQuotientMap
    (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)).continuous_iff.mpr
  exact continuous_smallToRestrictedRep

theorem continuous_restrictedToSmall
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    Continuous (restrictedToSmall hA hB hx hy) := by
  apply (restrictedOpen_quotientMap_isQuotientMap hA hB hx hy).continuous_iff.mpr
  convert (continuous_quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)).comp
    (restrictedDomainHomeomorphSum hA hB hx hy).continuous using 1
  funext a
  exact restrictedToSmall_comp_restrictedQuotientMap hA hB hx hy a

@[simp] theorem restrictedToSmall_left
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (x : X) (hx' : x ∈ A) :
    restrictedToSmall hA hB hx hy
        ⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, hx', rfl⟩⟩ =
      quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inl ⟨x, hx'⟩) := by
  let a : RestrictedDomain x₀ y₀ A B :=
    ⟨.inl x, ⟨.inl x, hx', rfl⟩⟩
  have hz : (⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, hx', rfl⟩⟩ :
      {z // z ∈ restrictedOpen x₀ y₀ A B}) = restrictedQuotientMap a := by
    apply Subtype.ext
    rfl
  rw [hz, restrictedToSmall_comp_restrictedQuotientMap]
  exact congrArg (quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B))
    (restrictedDomainHomeomorphSum_left hA hB hx hy x hx')

@[simp] theorem restrictedToSmall_right
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (y : Y) (hy' : y ∈ B) :
    restrictedToSmall hA hB hx hy
        ⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, hy', rfl⟩⟩ =
      quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inr ⟨y, hy'⟩) := by
  let a : RestrictedDomain x₀ y₀ A B :=
    ⟨.inr y, ⟨.inr y, hy', rfl⟩⟩
  have hz : (⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, hy', rfl⟩⟩ :
      {z // z ∈ restrictedOpen x₀ y₀ A B}) = restrictedQuotientMap a := by
    apply Subtype.ext
    rfl
  rw [hz, restrictedToSmall_comp_restrictedQuotientMap]
  exact congrArg (quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B))
    (restrictedDomainHomeomorphSum_right hA hB hx hy y hy')

theorem restrictedToSmall_smallToRestricted
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (w : Wedge (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)) :
    restrictedToSmall hA hB hx hy (smallToRestricted hx hy w) = w := by
  refine Quotient.inductionOn w ?_
  intro s
  cases s with
  | inl x => exact restrictedToSmall_left hA hB hx hy x.1 x.2
  | inr y => exact restrictedToSmall_right hA hB hx hy y.1 y.2

theorem smallToRestricted_restrictedToSmall
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (z : {z // z ∈ restrictedOpen x₀ y₀ A B}) :
    smallToRestricted hx hy (restrictedToSmall hA hB hx hy z) = z := by
  obtain ⟨a, rfl⟩ :=
    (restrictedOpen_quotientMap_isQuotientMap hA hB hx hy).surjective z
  change smallToRestricted hx hy
      (restrictedToSmall hA hB hx hy (restrictedQuotientMap a)) =
    restrictedQuotientMap a
  rw [restrictedToSmall_comp_restrictedQuotientMap]
  generalize heq : restrictedDomainHomeomorphSum hA hB hx hy a = s
  cases s with
  | inl x =>
      let c : RestrictedDomain x₀ y₀ A B :=
        ⟨.inl x.1, ⟨.inl x.1, x.2, rfl⟩⟩
      have hc : restrictedDomainHomeomorphSum hA hB hx hy c = .inl x := by
        exact restrictedDomainHomeomorphSum_left hA hB hx hy x.1 x.2
      have hac : a = c :=
        (restrictedDomainHomeomorphSum hA hB hx hy).injective (heq.trans hc.symm)
      subst a
      rfl
  | inr y =>
      let c : RestrictedDomain x₀ y₀ A B :=
        ⟨.inr y.1, ⟨.inr y.1, y.2, rfl⟩⟩
      have hc : restrictedDomainHomeomorphSum hA hB hx hy c = .inr y := by
        exact restrictedDomainHomeomorphSum_right hA hB hx hy y.1 y.2
      have hac : a = c :=
        (restrictedDomainHomeomorphSum hA hB hx hy).injective (heq.trans hc.symm)
      subst a
      rfl

def restrictedOpenHomeomorphWedge
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    {z // z ∈ restrictedOpen x₀ y₀ A B} ≃ₜ
      Wedge (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) where
  toFun := restrictedToSmall hA hB hx hy
  invFun := smallToRestricted hx hy
  left_inv := smallToRestricted_restrictedToSmall hA hB hx hy
  right_inv := restrictedToSmall_smallToRestricted hA hB hx hy
  continuous_toFun := continuous_restrictedToSmall hA hB hx hy
  continuous_invFun := continuous_smallToRestricted hx hy

@[simp] theorem restrictedOpenHomeomorphWedge_left
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (x : X) (hx' : x ∈ A) :
    restrictedOpenHomeomorphWedge hA hB hx hy
        ⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, hx', rfl⟩⟩ =
      quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inl ⟨x, hx'⟩) :=
  restrictedToSmall_left hA hB hx hy x hx'

@[simp] theorem restrictedOpenHomeomorphWedge_right
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (y : Y) (hy' : y ∈ B) :
    restrictedOpenHomeomorphWedge hA hB hx hy
        ⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, hy', rfl⟩⟩ =
      quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inr ⟨y, hy'⟩) :=
  restrictedToSmall_right hA hB hx hy y hy'

@[simp] theorem restrictedOpenHomeomorphWedge_symm_left
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (x : A) :
    (restrictedOpenHomeomorphWedge hA hB hx hy).symm
        (quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inl x)) =
      ⟨quotientMap x₀ y₀ (.inl x.1), ⟨.inl x.1, x.2, rfl⟩⟩ := rfl

@[simp] theorem restrictedOpenHomeomorphWedge_symm_right
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B)
    (y : B) :
    (restrictedOpenHomeomorphWedge hA hB hx hy).symm
        (quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) (.inr y)) =
      ⟨quotientMap x₀ y₀ (.inr y.1), ⟨.inr y.1, y.2, rfl⟩⟩ := rfl

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem restrictedOpen_leftBase_eq_rightBase
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    (⟨quotientMap x₀ y₀ (.inl x₀), ⟨.inl x₀, hx, rfl⟩⟩ :
      {z // z ∈ restrictedOpen x₀ y₀ A B}) =
    ⟨quotientMap x₀ y₀ (.inr y₀), ⟨.inr y₀, hy, rfl⟩⟩ := by
  apply Subtype.ext
  exact Quotient.sound
    (Relation.EqvGen.rel (Sum.inl x₀) (Sum.inr y₀) Rel.base)

theorem restrictedOpenHomeomorphWedge_base_glue
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    restrictedOpenHomeomorphWedge hA hB hx hy
        ⟨quotientMap x₀ y₀ (.inl x₀), ⟨.inl x₀, hx, rfl⟩⟩ =
      restrictedOpenHomeomorphWedge hA hB hx hy
        ⟨quotientMap x₀ y₀ (.inr y₀), ⟨.inr y₀, hy, rfl⟩⟩ := by
  exact congrArg (restrictedOpenHomeomorphWedge hA hB hx hy)
    (restrictedOpen_leftBase_eq_rightBase hx hy)

#print axioms restrictedPreimage_isOpen
#print axioms restrictedOpen_isOpen
#print axioms quotientMap_preimage_restrictedOpen
#print axioms quotientMap_isQuotientMap
#print axioms restrictedOpen_quotientMap_isQuotientMap
#print axioms restrictedDomain_eq
#print axioms restrictedPreimageHomeomorphSum
#print axioms restrictedPreimageHomeomorphSum_left
#print axioms restrictedPreimageHomeomorphSum_right
#print axioms restrictedOpenHomeomorphWedge
#print axioms restrictedOpenHomeomorphWedge_left
#print axioms restrictedOpenHomeomorphWedge_right
#print axioms restrictedOpenHomeomorphWedge_symm_left
#print axioms restrictedOpenHomeomorphWedge_symm_right
#print axioms restrictedOpen_leftBase_eq_rightBase
#print axioms restrictedOpenHomeomorphWedge_base_glue

end ConstructionTargets.PointWedgeRestrictedOpenQuotient
