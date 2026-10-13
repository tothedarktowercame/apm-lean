import Mathlib
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.DeckGroupQuotientFundamentalGroup

/-!
# APM t01A04 — the fundamental group and double covers of `T² ∨ S¹`

## Statement repairs

None.

## Encoding note

The wedge and both covering total spaces are concrete quotients.  For the
kernel detecting the extra-circle generator, two torus copies are attached at
the two points of a doubled circle.  For the kernel detecting one torus
generator, two circle copies are attached at the two points over the basepoint
of a doubled torus.  The theorem exhibits the actual covering maps and pins
their induced fundamental-group ranges to the two parity kernels.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t01a04_Torus := Circle × Circle
abbrev apm_t01a04_Parity := Multiplicative (ZMod 2)

inductive apm_t01a04_wedgeRel :
    Sum apm_t01a04_Torus Circle → Sum apm_t01a04_Torus Circle → Prop
  | base : apm_t01a04_wedgeRel (.inl (1, 1)) (.inr 1)

def apm_t01a04_X := Quotient (Relation.EqvGen.setoid apm_t01a04_wedgeRel)

noncomputable instance : TopologicalSpace apm_t01a04_X :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t01a04_Torus Circle =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a04_wedgeRel) z)
    inferInstance

def apm_t01a04_basepoint : apm_t01a04_X := Quotient.mk _ (.inl (1, 1))

def apm_t01a04_sheetPoint (i : Fin 2) : Circle :=
  if i = 0 then 1 else Circle.exp Real.pi

@[simp] lemma apm_t01a04_sheetPoint_zero :
    apm_t01a04_sheetPoint 0 = 1 := by
  simp [apm_t01a04_sheetPoint]

@[simp] lemma apm_t01a04_sheetPoint_one :
    apm_t01a04_sheetPoint 1 = Circle.exp Real.pi := by
  simp [apm_t01a04_sheetPoint]

@[simp] lemma apm_t01a04_sheetPoint_sq (i : Fin 2) :
    apm_t01a04_sheetPoint i ^ 2 = 1 := by
  fin_cases i <;> simp [apm_t01a04_sheetPoint, Circle.exp, Complex.exp_mul_I]
  ext
  norm_num

inductive apm_t01a04_circleCoverRel :
    Sum (Fin 2 × apm_t01a04_Torus) Circle →
      Sum (Fin 2 × apm_t01a04_Torus) Circle → Prop
  | glue (i : Fin 2) :
      apm_t01a04_circleCoverRel (.inl (i, (1, 1)))
        (.inr (apm_t01a04_sheetPoint i))

def apm_t01a04_CircleCover :=
  Quotient (Relation.EqvGen.setoid apm_t01a04_circleCoverRel)

noncomputable instance : TopologicalSpace apm_t01a04_CircleCover :=
  TopologicalSpace.coinduced
    (fun z : Sum (Fin 2 × apm_t01a04_Torus) Circle =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a04_circleCoverRel) z)
    inferInstance

def apm_t01a04_circleCoverBase : apm_t01a04_CircleCover :=
  Quotient.mk _ (.inl (0, (1, 1)))

inductive apm_t01a04_torusCoverRel :
    Sum apm_t01a04_Torus (Fin 2 × Circle) →
      Sum apm_t01a04_Torus (Fin 2 × Circle) → Prop
  | glue (i : Fin 2) :
      apm_t01a04_torusCoverRel
        (.inl (apm_t01a04_sheetPoint i, 1)) (.inr (i, 1))

def apm_t01a04_TorusCover :=
  Quotient (Relation.EqvGen.setoid apm_t01a04_torusCoverRel)

noncomputable instance : TopologicalSpace apm_t01a04_TorusCover :=
  TopologicalSpace.coinduced
    (fun z : Sum apm_t01a04_Torus (Fin 2 × Circle) =>
      Quotient.mk (Relation.EqvGen.setoid apm_t01a04_torusCoverRel) z)
    inferInstance

def apm_t01a04_torusCoverBase : apm_t01a04_TorusCover :=
  Quotient.mk _ (.inl (1, 1))

def apm_t01a04_circleCoverRaw :
    Sum (Fin 2 × apm_t01a04_Torus) Circle → Sum apm_t01a04_Torus Circle
  | .inl q => .inl q.2
  | .inr z => .inr (z ^ 2)

lemma apm_t01a04_circleCoverRaw_respects {x y}
    (h : Relation.EqvGen apm_t01a04_circleCoverRel x y) :
    Relation.EqvGen apm_t01a04_wedgeRel
      (apm_t01a04_circleCoverRaw x) (apm_t01a04_circleCoverRaw y) := by
  induction h with
  | rel a b hab =>
    cases hab with
    | glue i =>
      simp [apm_t01a04_circleCoverRaw]
      exact Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The representative-level map descends continuously to the first concrete
quotient total space. -/
def apm_t01a04_circleCoverMap : C(apm_t01a04_CircleCover, apm_t01a04_X) := by
  let q : apm_t01a04_CircleCover → apm_t01a04_X :=
    Quotient.map' apm_t01a04_circleCoverRaw
      (fun _ _ h => apm_t01a04_circleCoverRaw_respects h)
  exact ⟨q, by
    apply Continuous.quotient_map'
    apply continuous_sum_dom.2
    constructor
    · simpa [apm_t01a04_circleCoverRaw] using
        (continuous_inl.comp continuous_snd)
    · have hp : Continuous (fun z : Circle ↦ z ^ 2) := by fun_prop
      simpa [apm_t01a04_circleCoverRaw] using continuous_inr.comp hp⟩

@[simp] lemma apm_t01a04_circleCoverMap_base :
    apm_t01a04_circleCoverMap apm_t01a04_circleCoverBase = apm_t01a04_basepoint := rfl

def apm_t01a04_torusCoverRaw :
    Sum apm_t01a04_Torus (Fin 2 × Circle) → Sum apm_t01a04_Torus Circle
  | .inl q => .inl (q.1 ^ 2, q.2)
  | .inr q => .inr q.2

lemma apm_t01a04_torusCoverRaw_respects {x y}
    (h : Relation.EqvGen apm_t01a04_torusCoverRel x y) :
    Relation.EqvGen apm_t01a04_wedgeRel
      (apm_t01a04_torusCoverRaw x) (apm_t01a04_torusCoverRaw y) := by
  induction h with
  | rel a b hab =>
    cases hab with
    | glue i =>
      simp [apm_t01a04_torusCoverRaw]
      exact Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The representative-level map descends continuously to the second concrete
quotient total space. -/
def apm_t01a04_torusCoverMap : C(apm_t01a04_TorusCover, apm_t01a04_X) := by
  let q : apm_t01a04_TorusCover → apm_t01a04_X :=
    Quotient.map' apm_t01a04_torusCoverRaw
      (fun _ _ h => apm_t01a04_torusCoverRaw_respects h)
  exact ⟨q, by
    apply Continuous.quotient_map'
    apply continuous_sum_dom.2
    constructor
    · have hp : Continuous (fun q : apm_t01a04_Torus ↦ (q.1 ^ 2, q.2)) := by fun_prop
      simpa [apm_t01a04_torusCoverRaw] using continuous_inl.comp hp
    · simpa [apm_t01a04_torusCoverRaw] using continuous_inr.comp continuous_snd⟩

@[simp] lemma apm_t01a04_torusCoverMap_base :
    apm_t01a04_torusCoverMap apm_t01a04_torusCoverBase = apm_t01a04_basepoint := by
  simp [apm_t01a04_torusCoverMap, apm_t01a04_torusCoverBase,
    apm_t01a04_torusCoverRaw, apm_t01a04_basepoint]

/-- The first descended map is onto: torus representatives lift to either
torus sheet, while circle representatives lift through circle squaring. -/
lemma apm_t01a04_circleCoverMap_surjective :
    Function.Surjective apm_t01a04_circleCoverMap := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hs : Function.Surjective (fun z : Circle ↦ z ^ 2) :=
    (Circle.isQuotientCoveringMap_npow 2).surjective
  intro x
  refine Quotient.inductionOn x ?_
  rintro (q | z)
  · exact ⟨Quotient.mk _ (.inl (0, q)), rfl⟩
  · rcases hs z with ⟨w, hw⟩
    exact ⟨Quotient.mk _ (.inr w), by
      simp [apm_t01a04_circleCoverMap, apm_t01a04_circleCoverRaw, hw]⟩

/-- The second descended map is onto: its torus part lifts through squaring in
the first coordinate, and either attached circle sheet lifts the circle part. -/
lemma apm_t01a04_torusCoverMap_surjective :
    Function.Surjective apm_t01a04_torusCoverMap := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hs : Function.Surjective (fun z : Circle ↦ z ^ 2) :=
    (Circle.isQuotientCoveringMap_npow 2).surjective
  intro x
  refine Quotient.inductionOn x ?_
  rintro (q | z)
  · rcases hs q.1 with ⟨w, hw⟩
    exact ⟨Quotient.mk _ (.inl (w, q.2)), by
      simp [apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw, hw]⟩
  · exact ⟨Quotient.mk _ (.inr (0, z)), rfl⟩

abbrev apm_t01a04_piOne := FundamentalGroup apm_t01a04_X apm_t01a04_basepoint

/-- Why this unblocks `apm_t01a04`: this is the missing local
evenly-covered-neighborhood construction for the two concrete quotient maps.
Surjectivity and basepoint preservation are already proved separately. -/
theorem apm_t01A04_bridge_quotient_maps_are_coverings :
    IsCoveringMap apm_t01a04_circleCoverMap ∧
    IsCoveringMap apm_t01a04_torusCoverMap := by
  sorry

/-- Why this unblocks `apm_t01a04`: this is the Seifert--van Kampen
presentation of `T² ∨ S¹`, together with the two parity characters and the
covering-subgroup range computation for the already constructed based maps. -/
-- BEGIN SEAT AREA
theorem apm_t01A04_bridge_piOne_presentation_and_ranges :
    ∃ (a b c : apm_t01a04_piOne)
      (phic phia : apm_t01a04_piOne →* apm_t01a04_Parity),
      a * b = b * a ∧
      Subgroup.closure {a, b, c} = ⊤ ∧
      (∀ (G : Type) [Group G] (ga gb gc : G), ga * gb = gb * ga →
        ∃! F : apm_t01a04_piOne →* G,
          F a = ga ∧ F b = gb ∧ F c = gc) ∧
      phic a = Multiplicative.ofAdd 0 ∧
      phic b = Multiplicative.ofAdd 0 ∧
      phic c = Multiplicative.ofAdd 1 ∧
      phia a = Multiplicative.ofAdd 1 ∧
      phia b = Multiplicative.ofAdd 0 ∧
      phia c = Multiplicative.ofAdd 0 ∧
      Function.Surjective phic ∧ Function.Surjective phia ∧
      phic.ker.index = 2 ∧ phia.ker.index = 2 ∧ phic.ker ≠ phia.ker ∧
      MonoidHom.range
        (apm_t01a04_circleCoverMap_base ▸
          FundamentalGroup.map apm_t01a04_circleCoverMap
            apm_t01a04_circleCoverBase) = phic.ker ∧
      MonoidHom.range
        (apm_t01a04_torusCoverMap_base ▸
          FundamentalGroup.map apm_t01a04_torusCoverMap
            apm_t01a04_torusCoverBase) = phia.ker := by
  sorry
-- END SEAT AREA

/-- Why this unblocks `apm_t01a04`: this is the missing singular `H₂`
distinction. The circle-doubled total space has two independent torus
fundamental classes whereas the torus-doubled total space has one, so the
concrete quotient spaces cannot be homeomorphic. -/
theorem apm_t01A04_bridge_total_spaces_not_homeomorphic :
    ¬Nonempty (apm_t01a04_CircleCover ≃ₜ apm_t01a04_TorusCover) := by
  sorry

theorem apm_t01a04 :
    ∃ (a b c : apm_t01a04_piOne)
      (φc φa : apm_t01a04_piOne →* apm_t01a04_Parity)
      (pc : C(apm_t01a04_CircleCover, apm_t01a04_X))
      (pa : C(apm_t01a04_TorusCover, apm_t01a04_X))
      (hpc : pc apm_t01a04_circleCoverBase = apm_t01a04_basepoint)
      (hpa : pa apm_t01a04_torusCoverBase = apm_t01a04_basepoint),
      a * b = b * a ∧
      Subgroup.closure {a, b, c} = ⊤ ∧
      (∀ (G : Type) [Group G] (ga gb gc : G), ga * gb = gb * ga →
        ∃! F : apm_t01a04_piOne →* G,
          F a = ga ∧ F b = gb ∧ F c = gc) ∧
      φc a = Multiplicative.ofAdd 0 ∧
      φc b = Multiplicative.ofAdd 0 ∧
      φc c = Multiplicative.ofAdd 1 ∧
      φa a = Multiplicative.ofAdd 1 ∧
      φa b = Multiplicative.ofAdd 0 ∧
      φa c = Multiplicative.ofAdd 0 ∧
      Function.Surjective φc ∧ Function.Surjective φa ∧
      φc.ker.index = 2 ∧ φa.ker.index = 2 ∧ φc.ker ≠ φa.ker ∧
      IsCoveringMap pc ∧ IsCoveringMap pa ∧
      MonoidHom.range
        (hpc ▸ FundamentalGroup.map pc apm_t01a04_circleCoverBase) = φc.ker ∧
      MonoidHom.range
        (hpa ▸ FundamentalGroup.map pa apm_t01a04_torusCoverBase) = φa.ker ∧
      ¬Nonempty (apm_t01a04_CircleCover ≃ₜ apm_t01a04_TorusCover) := by
  rcases apm_t01A04_bridge_piOne_presentation_and_ranges with
    ⟨a, b, c, φc, φa, hab, hgen, huniv, hca, hcb, hcc,
      haa, hab0, hac, hsc, hsa, hic, hia, hne, hrc, hra⟩
  rcases apm_t01A04_bridge_quotient_maps_are_coverings with ⟨hcovc, hcova⟩
  refine ⟨a, b, c, φc, φa,
    apm_t01a04_circleCoverMap, apm_t01a04_torusCoverMap,
    apm_t01a04_circleCoverMap_base, apm_t01a04_torusCoverMap_base, ?_⟩
  exact ⟨hab, hgen, huniv, hca, hcb, hcc, haa, hab0, hac,
    hsc, hsa, hic, hia, hne, hcovc, hcova, hrc, hra,
    apm_t01A04_bridge_total_spaces_not_homeomorphic⟩

#print axioms apm_t01a04
