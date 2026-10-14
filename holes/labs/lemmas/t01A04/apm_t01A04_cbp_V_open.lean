import Mathlib
import ConstructionTargets.GenericTargetNaturalSourceReconstruction
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.CircleUniversalCover

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

/-- The canonical first torus generator, represented by one positive turn in
the first circle coordinate and then included into the wedge quotient. -/
def apm_t01A04_loopA : apm_t01a04_piOne :=
  Path.Homotopic.Quotient.mk
    ((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
      (show Continuous (fun z : Circle =>
          Quotient.mk _ (Sum.inl (z, (1 : Circle)))) from
        (continuous_coinduced_rng : Continuous (fun w : Sum apm_t01a04_Torus Circle =>
          (Quotient.mk _ w : apm_t01a04_X))).comp
            (continuous_inl.comp (continuous_id.prodMk continuous_const))))

/-- The canonical second torus generator, represented by one positive turn in
the second circle coordinate and then included into the wedge quotient. -/
def apm_t01A04_loopB : apm_t01a04_piOne :=
  Path.Homotopic.Quotient.mk
    ((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
      (show Continuous (fun z : Circle =>
          Quotient.mk _ (Sum.inl ((1 : Circle), z))) from
        (continuous_coinduced_rng : Continuous (fun w : Sum apm_t01a04_Torus Circle =>
          (Quotient.mk _ w : apm_t01a04_X))).comp
            (continuous_inl.comp (continuous_const.prodMk continuous_id))))

/-- The canonical extra-circle generator, represented by one positive turn in
the circle summand and then included into the wedge quotient. -/
def apm_t01A04_loopC : apm_t01a04_piOne :=
  Path.Homotopic.Quotient.mk
    (((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
      (show Continuous (fun z : Circle => Quotient.mk _ (Sum.inr z)) from
        (continuous_coinduced_rng : Continuous (fun w : Sum apm_t01a04_Torus Circle =>
          (Quotient.mk _ w : apm_t01a04_X))).comp continuous_inr)).cast
      (Quotient.sound (Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base))
      (Quotient.sound (Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base)))

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRaw :
    Sum apm_t01a04_Torus Circle → apm_t01a04_Torus
  | .inl q => q
  | .inr _ => (1, 1)

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRaw_respects
    {u v : Sum apm_t01a04_Torus Circle}
    (h : Relation.EqvGen apm_t01a04_wedgeRel u v) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRaw u =
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRaw v := by
  induction h with
  | rel _ _ h => cases h <;> rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction :
    apm_t01a04_X → apm_t01a04_Torus :=
  Quotient.lift apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRaw
    (fun _ _ h =>
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRaw_respects h)

@[simp] lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction_inl
    (q : apm_t01a04_Torus) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction
        (Quotient.mk _ (Sum.inl q)) = q := rfl

@[simp] lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction_inr
    (z : Circle) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction
        (Quotient.mk _ (Sum.inr z)) = (1, 1) := rfl

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRaw :
    Sum apm_t01a04_Torus Circle → Circle
  | .inl _ => 1
  | .inr z => z

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRaw_respects
    {u v : Sum apm_t01a04_Torus Circle}
    (h : Relation.EqvGen apm_t01a04_wedgeRel u v) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRaw u =
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRaw v := by
  induction h with
  | rel _ _ h => cases h <;> rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction :
    apm_t01a04_X → Circle :=
  Quotient.lift apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRaw
    (fun _ _ h =>
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRaw_respects h)

@[simp] lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction_inl
    (q : apm_t01a04_Torus) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction
        (Quotient.mk _ (Sum.inl q)) = 1 := rfl

@[simp] lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction_inr
    (z : Circle) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction
        (Quotient.mk _ (Sum.inr z)) = z := rfl

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_inl_ne_base
    {q : apm_t01a04_Torus} (hq : q ≠ (1, 1)) :
    (Quotient.mk _ (Sum.inl q) : apm_t01a04_X) ≠ apm_t01a04_basepoint := by
  intro h
  have := congrArg
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction h
  exact hq this

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_inr_ne_base
    {z : Circle} (hz : z ≠ 1) :
    (Quotient.mk _ (Sum.inr z) : apm_t01a04_X) ≠ apm_t01a04_basepoint := by
  intro h
  have := congrArg
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction h
  exact hz this

/-- Torus-sheet case away from the wedge point: a neighbourhood of `q` in the
torus avoiding `(1,1)` is evenly covered by its two copies in sheets `0, 1`.
The torus retraction above shows the image of that neighbourhood is open in
`X` and misses the circle summand. -/
def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw :
    Sum (Fin 2 × apm_t01a04_Torus) Circle → apm_t01a04_Torus
  | .inl q => q.2
  | .inr _ => (1, 1)

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw_respects
    {u v} (h : Relation.EqvGen apm_t01a04_circleCoverRel u v) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw u =
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw v := by
  induction h with
  | rel _ _ h => cases h <;> rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction :
    apm_t01a04_CircleCover → apm_t01a04_Torus :=
  Quotient.lift
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw
    (fun _ _ h =>
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw_respects h)

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw :
    Sum (Fin 2 × apm_t01a04_Torus) Circle → Fin 2 := by
  classical
  exact fun
    | .inl q => q.1
    | .inr z => if z = 1 then 0 else 1

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw_respects
    {u v} (h : Relation.EqvGen apm_t01a04_circleCoverRel u v) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw u =
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw v := by
  classical
  induction h with
  | rel _ _ h =>
      cases h with
      | glue i =>
        fin_cases i
        · simp [apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw]
        · change (1 : Fin 2) = if Circle.exp Real.pi = 1 then 0 else 1
          rw [if_neg]
          intro h
          have hr := congrArg (fun z : Circle => z.1.re) h
          norm_num [Circle.exp, Complex.exp_mul_I] at hr
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheet :
    apm_t01a04_CircleCover → Fin 2 :=
  Quotient.lift
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw
    (fun _ _ h =>
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw_respects h)

theorem apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus
    (q : apm_t01a04_Torus) (hq : q ≠ (1, 1)) :
    IsEvenlyCovered apm_t01a04_circleCoverMap (Quotient.mk _ (Sum.inl q))
      (apm_t01a04_circleCoverMap ⁻¹' {Quotient.mk _ (Sum.inl q)}) := by
  let V : Set apm_t01a04_Torus := {p | p ≠ (1, 1)}
  let U : Set apm_t01a04_X :=
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction ⁻¹' V
  have hbcont : Continuous
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction := by
    apply continuous_coinduced_dom.mpr
    apply continuous_sum_dom.2
    exact ⟨continuous_id, continuous_const⟩
  have htcont : Continuous
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction := by
    apply continuous_coinduced_dom.mpr
    apply continuous_sum_dom.2
    exact ⟨continuous_snd, continuous_const⟩
  have hcompat (e : apm_t01a04_CircleCover) :
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction
          (apm_t01a04_circleCoverMap e) =
        apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e := by
    refine Quotient.inductionOn e ?_
    rintro (p | z) <;> rfl
  have hU : IsOpen U :=
    (isOpen_compl_singleton : IsOpen ({(1, 1)}ᶜ : Set apm_t01a04_Torus)).preimage hbcont
  have hqU : (Quotient.mk _ (Sum.inl q) : apm_t01a04_X) ∈ U := hq
  have hopenpre : IsOpen (apm_t01a04_circleCoverMap ⁻¹' U) := by
    exact hU.preimage apm_t01a04_circleCoverMap.continuous
  let E : apm_t01a04_circleCoverMap ⁻¹' U ≃ₜ U × Fin 2 :=
    { toFun := fun e =>
        (⟨apm_t01a04_circleCoverMap e.1, e.2⟩,
          apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheet e.1)
      invFun := fun y =>
        ⟨Quotient.mk _ (Sum.inl (y.2,
            apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction y.1)), by
          exact y.1.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        refine Quotient.inductionOn e ?_ he
        rintro (p | z) he
        · rfl
        · exfalso
          change (1, 1) ≠ (1, 1) at he
          exact he rfl
      right_inv := by
        rintro ⟨⟨x, hx⟩, i⟩
        apply Prod.ext
        · apply Subtype.ext
          refine Quotient.inductionOn x ?_ hx
          rintro (p | z) hx
          · rfl
          · exfalso
            change (1, 1) ≠ (1, 1) at hx
            exact hx rfl
        · simp [apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheet,
            apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheetRaw]
      continuous_toFun := by
        apply Continuous.prodMk
        · exact Continuous.subtype_mk
            (apm_t01a04_circleCoverMap.continuous.comp continuous_subtype_val) _
        · rw [continuous_def]
          intro s hs
          rw [isOpen_induced_iff]
          refine ⟨apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheet ⁻¹' s ∩
              apm_t01a04_circleCoverMap ⁻¹' U, ?_, ?_⟩
          · change @IsOpen _ (TopologicalSpace.coinduced
                (fun z : Sum (Fin 2 × apm_t01a04_Torus) Circle =>
                  Quotient.mk (Relation.EqvGen.setoid apm_t01a04_circleCoverRel) z)
                inferInstance)
              (apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus_aux_sheet ⁻¹' s ∩
                apm_t01a04_circleCoverMap ⁻¹' U)
            rw [isOpen_coinduced]
            apply isOpen_sum_iff.mpr
            constructor
            · change IsOpen {p : Fin 2 × apm_t01a04_Torus | p.1 ∈ s ∧ p.2 ≠ (1, 1)}
              exact (hs.preimage continuous_fst).inter
                ((isOpen_compl_singleton : IsOpen ({(1, 1)}ᶜ : Set apm_t01a04_Torus)).preimage
                  continuous_snd)
            · simpa [U, V, apm_t01a04_circleCoverMap,
                apm_t01a04_circleCoverRaw,
                apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction,
                apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRaw] using
                (isOpen_empty : IsOpen (∅ : Set Circle))
          · ext e
            simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
              Subtype.coe_prop, and_true]
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Sum (Fin 2 × apm_t01a04_Torus) Circle =>
            (Quotient.mk _ u : apm_t01a04_CircleCover))).comp
          (continuous_inl.comp
            (continuous_snd.prodMk
              (hbcont.comp (continuous_subtype_val.comp continuous_fst)))) }
  refine (show IsEvenlyCovered apm_t01a04_circleCoverMap
      (Quotient.mk _ (Sum.inl q)) (Fin 2) from ?_).to_isEvenlyCovered_preimage
  refine ⟨inferInstance, U, hqU, hU, hopenpre, E, ?_⟩
  intro e
  rfl

/-- Circle-summand case away from the wedge point: near `z ≠ 1` the cover is
the squaring map `Circle → Circle` restricted to an arc avoiding `1`, which is
evenly covered by arcs around the two square roots of `z`; neither root is
`±1` (the glued sheet points), so these arcs can be chosen to miss them. -/
def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw :
    Sum (Fin 2 × apm_t01a04_Torus) Circle → Circle
  | .inl q => apm_t01a04_sheetPoint q.1
  | .inr w => w

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw_respects
    {u v : Sum (Fin 2 × apm_t01a04_Torus) Circle}
    (h : Relation.EqvGen apm_t01a04_circleCoverRel u v) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw u =
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw v := by
  induction h with
  | rel _ _ h => cases h <;> rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction :
    apm_t01a04_CircleCover → Circle :=
  Quotient.lift
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw
    (fun _ _ h =>
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw_respects h)

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_base_continuous :
    Continuous apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.2
  exact ⟨continuous_const, continuous_id⟩

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_total_continuous :
    Continuous
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.2
  constructor
  · exact
      (continuous_of_discreteTopology : Continuous apm_t01a04_sheetPoint).comp
        continuous_fst
  · exact continuous_id

@[simp] lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_total_inr
    (w : Circle) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction
      (Quotient.mk _ (Sum.inr w)) = w := rfl

lemma apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_square
    (e : apm_t01a04_CircleCover) :
    (apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction
      (apm_t01a04_circleCoverMap e)) =
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction e ^ 2 := by
  refine Quotient.inductionOn e ?_
  rintro (q | w)
  · simp [apm_t01a04_circleCoverMap, apm_t01a04_circleCoverRaw,
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction,
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw]
  · rfl

theorem apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle
    (z : Circle) (hz : z ≠ 1) :
    IsEvenlyCovered apm_t01a04_circleCoverMap (Quotient.mk _ (Sum.inr z))
      (apm_t01a04_circleCoverMap ⁻¹' {Quotient.mk _ (Sum.inr z)}) := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hc := IsQuotientCoveringMap.isCoveringMap _ _
    (Circle.isQuotientCoveringMap_npow 2) z
  rcases hc with ⟨hd, U, hzU, hU, hpU, H, hH⟩
  let V : Set Circle := U \ {1}
  have hzV : z ∈ V := ⟨hzU, hz⟩
  have hV : IsOpen V := hU.sdiff isClosed_singleton
  let UX : Set apm_t01a04_X :=
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction ⁻¹' V
  have hUX : IsOpen UX := hV.preimage
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_base_continuous
  have hzUX : (Quotient.mk _ (Sum.inr z) : apm_t01a04_X) ∈ UX := hzV
  let W : Set Circle := (fun w : Circle ↦ w ^ 2) ⁻¹' V
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have hpre : apm_t01a04_circleCoverMap ⁻¹' UX =
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction ⁻¹' W := by
    ext e
    change
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction
          (apm_t01a04_circleCoverMap e) ∈ V ↔
        apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction e ^ 2 ∈ V
    rw [apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_square]
  have hopenpre : IsOpen (apm_t01a04_circleCoverMap ⁻¹' UX) := by
    rw [hpre]
    exact hW.preimage
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_total_continuous
  have himage (e : apm_t01a04_CircleCover)
      (he : e ∈ apm_t01a04_circleCoverMap ⁻¹' UX) :
      apm_t01a04_circleCoverMap e = Quotient.mk _ (Sum.inr
        (apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction e ^ 2)) := by
    refine Quotient.inductionOn e ?_ he
    rintro (q | w) he
    · exfalso
      change (1 : Circle) ∈ V at he
      exact he.2 rfl
    · rfl
  let I := (fun w : Circle ↦ w ^ 2) ⁻¹' {z}
  have hWV : W ⊆ (fun w : Circle ↦ w ^ 2) ⁻¹' U := fun w hw => hw.1
  let HW : W ≃ₜ V × I :=
    { toFun := fun w =>
        let y := H ⟨w.1, hWV w.2⟩
        (⟨y.1.1, ⟨y.1.2, by
          rw [hH ⟨w.1, hWV w.2⟩]
          exact w.2.2⟩⟩, y.2)
      invFun := fun y =>
        ⟨(H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1, by
          constructor
          · have hh := hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))
            have hh' : (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 2 = y.1.1 := by
              simpa using hh.symm
            change (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 2 ∈ U
            rw [hh']
            exact y.1.2.1
          · have hh := hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))
            have hh' : (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 2 = y.1.1 := by
              simpa using hh.symm
            change (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 ^ 2 ≠ 1
            rw [hh']
            exact y.1.2.2⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro y; ext <;> simp
      continuous_toFun := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          simpa only [Function.comp_apply] using
            (continuous_subtype_val.comp continuous_fst).comp (H.continuous.comp
              (Continuous.subtype_mk continuous_subtype_val _))
        · exact continuous_snd.comp (H.continuous.comp
            (Continuous.subtype_mk continuous_subtype_val _))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (H.symm.continuous.comp
          ((Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _).prodMk
            continuous_snd)) }
  have hHW (w : W) : (HW w).1.1 = w.1 ^ 2 := by
    exact hH ⟨w.1, hWV w.2⟩
  let E : apm_t01a04_circleCoverMap ⁻¹' UX ≃ₜ W :=
    { toFun := fun e =>
        ⟨apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction e.1,
          by
            change apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction
                e.1 ^ 2 ∈ V
            rw [← apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_square]
            exact e.2⟩
      invFun := fun w => ⟨Quotient.mk _ (Sum.inr w.1), by exact w.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        refine Quotient.inductionOn e ?_ he
        rintro (q | w) he
        · exfalso
          change (1 : Circle) ∈ V at he
          exact he.2 rfl
        · rfl
      right_inv := by rintro ⟨w, hw⟩; rfl
      continuous_toFun :=
        Continuous.subtype_mk
          (apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_total_continuous.comp
            continuous_subtype_val) (fun e => by
              change apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction
                  e.1 ^ 2 ∈ V
              rw [← apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_square]
              exact e.2)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Sum (Fin 2 × apm_t01a04_Torus) Circle =>
            (Quotient.mk _ u : apm_t01a04_CircleCover))).comp
              (continuous_inr.comp continuous_subtype_val) }
  let B : UX ≃ₜ V :=
    { toFun := fun x =>
        ⟨apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction x.1, x.2⟩
      invFun := fun v => ⟨Quotient.mk _ (Sum.inr v.1), v.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        refine Quotient.inductionOn x ?_ hx
        rintro (q | w) hx
        · exact (hx.2 rfl).elim
        · rfl
      right_inv := by rintro ⟨v, hv⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_base_continuous.comp
          continuous_subtype_val) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Sum apm_t01a04_Torus Circle =>
            (Quotient.mk _ u : apm_t01a04_X))).comp
              (continuous_inr.comp continuous_subtype_val) }
  refine (show IsEvenlyCovered apm_t01a04_circleCoverMap
      (Quotient.mk _ (Sum.inr z)) I from ?_).to_isEvenlyCovered_preimage
  refine ⟨hd, UX, hzUX, hUX, hopenpre, ?_, ?_⟩
  · exact E.trans (HW.trans (.prodCongr B.symm (.refl I)))
  · intro e
    change ((E.trans (HW.trans (.prodCongr B.symm (.refl I)))) e).1.1 = _
    change Quotient.mk _ (Sum.inr (HW (E e)).1.1) = apm_t01a04_circleCoverMap e.1
    rw [hHW]
    exact (himage e.1 e.2).symm

/-- Away from the wedge point, the circle-doubled quotient is locally either
an identity sheet over the torus or the ordinary circle-squaring cover. -/
theorem apm_t01A04_circleCoverMap_evenlyCovered_away
    (x : apm_t01a04_X) (hx : x ≠ apm_t01a04_basepoint) :
    IsEvenlyCovered apm_t01a04_circleCoverMap x
      (apm_t01a04_circleCoverMap ⁻¹' {x}) := by
  induction x using Quotient.inductionOn with
  | h u =>
    cases u with
    | inl q =>
      refine apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus q ?_
      rintro rfl
      exact hx rfl
    | inr z =>
      refine apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle z ?_
      rintro rfl
      exact hx (Quotient.sound
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base)))

lemma apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_glue (i : Fin 2) :
    (Quotient.mk _ (.inl (i, ((1 : Circle), (1 : Circle)))) :
        apm_t01a04_CircleCover) =
      Quotient.mk _ (.inr (apm_t01a04_sheetPoint i)) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t01a04_circleCoverRel.glue i))

lemma apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_mem_fiber
    (i : Fin 2) :
    Quotient.mk _ (.inl (i, ((1 : Circle), (1 : Circle)))) ∈
      apm_t01a04_circleCoverMap ⁻¹' {apm_t01a04_basepoint} := by
  change apm_t01a04_circleCoverMap
      (Quotient.mk _ (.inl (i, ((1 : Circle), (1 : Circle))))) =
    apm_t01a04_basepoint
  rfl

/-- Pure topology: two disjoint open sheets over an open `U`, each mapped
homeomorphically onto `U` by `f`, each meeting the fiber over `x` once, make
`x` evenly covered (the fiber is the two-point discrete space). -/
lemma apm_t01A04_isEvenlyCovered_of_two_sheets {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (x : X)
    (U : Set X) (hxU : x ∈ U) (hU : IsOpen U)
    (V : Fin 2 → Set E) (hV : ∀ i, IsOpen (V i))
    (hdisj : Pairwise (Function.onFun Disjoint V))
    (hcover : f ⁻¹' U = ⋃ i, V i)
    (hsheet : ∀ i, ∃ h : V i ≃ₜ U, ∀ y, (h y : X) = f y) :
    IsEvenlyCovered f x (f ⁻¹' {x}) := by
  classical
  choose h hh using hsheet
  let ind : f ⁻¹' U → Fin 2 := fun e => if e.1 ∈ V 0 then 0 else 1
  have mem_sheet (e : f ⁻¹' U) : e.1 ∈ V (ind e) := by
    by_cases he : e.1 ∈ V 0
    · simpa [ind, he]
    · have he' : e.1 ∈ ⋃ i, V i := by
        rw [← hcover]
        exact e.2
      simp only [mem_iUnion] at he'
      obtain ⟨i, hi⟩ := he'
      fin_cases i
      · exact (he hi).elim
      · simpa [ind, he] using hi
  have ind_eq (i : Fin 2) (e : V i) : ind ⟨e.1, by
      rw [hcover]
      exact mem_iUnion.2 ⟨i, e.2⟩⟩ = i := by
    by_cases hi : i = 0
    · subst i
      simp [ind, e.2]
    · have hi' : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst i
      have hn : e.1 ∉ V 0 := fun he0 =>
        Set.disjoint_left.1 (hdisj (by decide : (0 : Fin 2) ≠ 1)) he0 e.2
      simp [ind, hn]
  let toF : f ⁻¹' U → U × Fin 2 := fun e =>
    (⟨f e.1, e.2⟩, ind e)
  let invF : U × Fin 2 → f ⁻¹' U := fun y =>
    ⟨(h y.2).symm y.1, by
      change f ((h y.2).symm y.1) ∈ U
      rw [← hh y.2]
      exact (h y.2 ((h y.2).symm y.1)).2⟩
  have hleft : Function.LeftInverse invF toF := by
    intro e
    apply Subtype.ext
    dsimp [toF, invF]
    let a : V (ind e) := ⟨e.1, mem_sheet e⟩
    have hu : h (ind e) a = (⟨f e.1, e.2⟩ : U) :=
      Subtype.ext (hh (ind e) a)
    calc
      ↑((h (ind e)).symm ⟨f e.1, e.2⟩) =
          ↑((h (ind e)).symm (h (ind e) a)) :=
        congrArg (fun z : U => ((h (ind e)).symm z : E)) hu.symm
      _ = e.1 := congrArg Subtype.val ((h (ind e)).symm_apply_apply a)
  have hright : Function.RightInverse invF toF := by
    rintro ⟨u, i⟩
    have hi := ind_eq i ((h i).symm u)
    dsimp [toF, invF]
    apply Prod.ext
    · apply Subtype.ext
      calc
        f ((h i).symm u) = ↑(h i ((h i).symm u)) :=
          (hh i ((h i).symm u)).symm
        _ = u := congrArg Subtype.val ((h i).apply_symm_apply u)
    · exact hi
  have hto : Continuous toF := by
    apply continuous_of_continuousOn_iUnion_of_isOpen
      (s := fun i => Subtype.val ⁻¹' V i)
    · intro i
      rw [continuousOn_iff_continuous_restrict]
      apply (((h i).continuous.comp
          (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
            (fun e => e.2))) |>.prodMk
              (continuous_const : Continuous (fun _ : (Subtype.val ⁻¹' V i) => i))).congr
      intro e
      have hi : ind e.1 = i := ind_eq i ⟨e.1.1, e.2⟩
      apply Prod.ext
      · apply Subtype.ext
        exact hh i ⟨e.1.1, e.2⟩
      · exact hi.symm
    · intro i
      exact (hV i).preimage continuous_subtype_val
    · apply Set.eq_univ_of_forall
      intro e
      exact mem_iUnion.2 ⟨ind e, mem_sheet e⟩
  have hinv : Continuous invF := by
    apply continuous_of_continuousOn_iUnion_of_isOpen
      (s := fun i : Fin 2 => Prod.snd ⁻¹' {i})
    · intro i
      rw [continuousOn_iff_continuous_restrict]
      apply Continuous.subtype_mk
      have hc : Continuous (fun y : (Prod.snd ⁻¹' {i} : Set (U × Fin 2)) =>
          (h i).symm y.1.1) :=
        (h i).symm.continuous.comp
          ((continuous_fst : Continuous (Prod.fst : U × Fin 2 → U)).comp
            continuous_subtype_val)
      apply (continuous_subtype_val.comp hc).congr
      intro y
      have hyi : y.1.2 = i := y.2
      change ((h i).symm y.1.1 : E) = ((h y.1.2).symm y.1.1 : E)
      rw [hyi]
    · intro i
      exact (isOpen_discrete {i}).preimage continuous_snd
    · ext y
      simp
  let H : f ⁻¹' U ≃ₜ U × Fin 2 :=
    { toEquiv := ⟨toF, invF, hleft, hright⟩
      continuous_toFun := hto
      continuous_invFun := hinv }
  have hev : IsEvenlyCovered f x (Fin 2) := by
    refine ⟨inferInstance, U, hxU, hU, ?_, H, ?_⟩
    · rw [hcover]
      exact isOpen_iUnion hV
    · intro e
      rfl
  exact hev.to_isEvenlyCovered_preimage

lemma apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_fiber_points
    (e : apm_t01a04_CircleCover)
    (he : apm_t01a04_circleCoverMap e = apm_t01a04_basepoint) :
    ∃ i : Fin 2,
      e = Quotient.mk _ (.inl (i, ((1 : Circle), (1 : Circle)))) := by
  refine Quotient.inductionOn e ?_ he
  rintro (q | z) he
  · have hq := congrArg
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction he
    have hq' : q.2 = ((1 : Circle), (1 : Circle)) := by
      simpa [apm_t01a04_circleCoverMap, apm_t01a04_circleCoverRaw,
        apm_t01a04_basepoint] using hq
    refine ⟨q.1, ?_⟩
    congr
    exact Prod.ext rfl hq'
  · have hz := congrArg
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction he
    change z ^ 2 = 1 at hz
    rcases sq_eq_one_iff.mp (congrArg Subtype.val hz) with hz | hz
    · refine ⟨0, ?_⟩
      rw [apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_glue]
      apply congrArg (fun w : Circle => Quotient.mk _ (Sum.inr w))
      exact Subtype.ext hz
    · refine ⟨1, ?_⟩
      rw [apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_glue]
      apply congrArg (fun w : Circle => Quotient.mk _ (Sum.inr w))
      apply Subtype.ext
      simpa [Circle.exp, Complex.exp_mul_I] using hz

/-- Basepoint neighbourhood in `X` for the circle cover (same set as the torus
cover's `apm_t01A04_tbp_U`, defined later; its openness proof transfers verbatim). -/
def apm_t01A04_cbp_U : Set apm_t01a04_X :=
  (fun r => (Quotient.mk _ r : apm_t01a04_X)) ''
    {r | Sum.elim (fun q : apm_t01a04_Torus => 0 < (q.1 : ℂ).re ∧ 0 < (q.2 : ℂ).re)
      (fun z : Circle => 0 < (z : ℂ).re) r}

/-- Sheet `i`: torus sheet `i` with both coordinates of positive real part, plus
the arc of the circle summand around `sheetPoint i` on which `z²` has positive
real part. -/
def apm_t01A04_cbp_V (i : Fin 2) : Set apm_t01a04_CircleCover :=
  (fun r => (Quotient.mk _ r : apm_t01a04_CircleCover)) ''
    {r | Sum.elim (fun p : Fin 2 × apm_t01a04_Torus =>
        p.1 = i ∧ 0 < (p.2.1 : ℂ).re ∧ 0 < (p.2.2 : ℂ).re)
      (fun z : Circle =>
        0 < ((z : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧ 0 < ((z : ℂ) ^ 2).re) r}

lemma apm_t01A04_cbp_U_open : apm_t01a04_basepoint ∈ apm_t01A04_cbp_U ∧ IsOpen apm_t01A04_cbp_U := by
  sorry

-- BEGIN SEAT AREA
lemma apm_t01A04_cbp_V_open_aux_invariant (i : Fin 2)
    {u v : Sum (Fin 2 × apm_t01a04_Torus) Circle}
    (h : Relation.EqvGen apm_t01a04_circleCoverRel u v) :
    (Sum.elim (fun p : Fin 2 × apm_t01a04_Torus =>
        p.1 = i ∧ 0 < (p.2.1 : ℂ).re ∧ 0 < (p.2.2 : ℂ).re)
      (fun z : Circle =>
        0 < ((z : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
          0 < ((z : ℂ) ^ 2).re) u ↔
    Sum.elim (fun p : Fin 2 × apm_t01a04_Torus =>
        p.1 = i ∧ 0 < (p.2.1 : ℂ).re ∧ 0 < (p.2.2 : ℂ).re)
      (fun z : Circle =>
        0 < ((z : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
          0 < ((z : ℂ) ^ 2).re) v) := by
  induction h with
  | rel _ _ h =>
      cases h with
      | glue j =>
        simp only [Sum.elim_inl, Sum.elim_inr, Prod.fst, Prod.snd,
          apm_t01a04_sheetPoint_sq]
        fin_cases i <;> fin_cases j <;>
          simp [apm_t01a04_sheetPoint, Circle.exp, Complex.exp_mul_I] <;>
          norm_num
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t01A04_cbp_V_open (i : Fin 2) : IsOpen (apm_t01A04_cbp_V i) := by
  change IsOpen ((fun r => (Quotient.mk _ r : apm_t01a04_CircleCover)) '' _)
  rw [isOpen_coinduced]
  have heq :
      (fun r : Sum (Fin 2 × apm_t01a04_Torus) Circle =>
        (Quotient.mk _ r : apm_t01a04_CircleCover)) ⁻¹'
        ((fun r => (Quotient.mk _ r : apm_t01a04_CircleCover)) ''
          {r | Sum.elim (fun p : Fin 2 × apm_t01a04_Torus =>
              p.1 = i ∧ 0 < (p.2.1 : ℂ).re ∧ 0 < (p.2.2 : ℂ).re)
            (fun z : Circle =>
              0 < ((z : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
                0 < ((z : ℂ) ^ 2).re) r}) =
        {r | Sum.elim (fun p : Fin 2 × apm_t01a04_Torus =>
            p.1 = i ∧ 0 < (p.2.1 : ℂ).re ∧ 0 < (p.2.2 : ℂ).re)
          (fun z : Circle =>
            0 < ((z : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
              0 < ((z : ℂ) ^ 2).re) r} := by
    ext r
    constructor
    · rintro ⟨s, hs, hrs⟩
      exact (apm_t01A04_cbp_V_open_aux_invariant i (Quotient.exact hrs)).mp hs
    · intro hr
      exact ⟨r, hr, rfl⟩
  rw [heq, isOpen_sum_iff]
  constructor
  · exact ((isOpen_discrete ({i} : Set (Fin 2))).preimage
        continuous_fst).inter
      ((isOpen_lt continuous_const
        (Complex.continuous_re.comp
          (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).inter
        (isOpen_lt continuous_const
          (Complex.continuous_re.comp
            (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))))
  · exact (isOpen_lt continuous_const
      (Complex.continuous_re.comp
        (continuous_subtype_val.mul continuous_const))).inter
      (isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_subtype_val.pow 2)))
-- END SEAT AREA

lemma apm_t01A04_cbp_V_disjoint : Pairwise (Function.onFun Disjoint apm_t01A04_cbp_V) := by
  sorry

lemma apm_t01A04_cbp_preimage :
    apm_t01a04_circleCoverMap ⁻¹' apm_t01A04_cbp_U = ⋃ i, apm_t01A04_cbp_V i := by
  sorry

/-- On each sheet the cover map is a homeomorphism onto `U` (inverse: identity
on torus sheet `i`, square root on the arc around `sheetPoint i`). -/
lemma apm_t01A04_cbp_sheet_homeomorph (i : Fin 2) :
    ∃ h : apm_t01A04_cbp_V i ≃ₜ apm_t01A04_cbp_U, ∀ y,
      (h y : apm_t01a04_X) = apm_t01a04_circleCoverMap y := by
  sorry

/-- The two sheets over the basepoint (see the plan above). -/
lemma apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_sheets :
    ∃ (U : Set apm_t01a04_X) (V : Fin 2 → Set apm_t01a04_CircleCover),
      apm_t01a04_basepoint ∈ U ∧ IsOpen U ∧ (∀ i, IsOpen (V i)) ∧
      Pairwise (Function.onFun Disjoint V) ∧
      apm_t01a04_circleCoverMap ⁻¹' U = ⋃ i, V i ∧
      ∀ i, ∃ h : V i ≃ₜ U, ∀ y,
        (h y : apm_t01a04_X) = apm_t01a04_circleCoverMap y := by
  obtain ⟨hb, hU⟩ := apm_t01A04_cbp_U_open
  exact ⟨apm_t01A04_cbp_U, apm_t01A04_cbp_V, hb, hU, apm_t01A04_cbp_V_open, apm_t01A04_cbp_V_disjoint,
    apm_t01A04_cbp_preimage, apm_t01A04_cbp_sheet_homeomorph⟩

/-- Basepoint case.  Plan (from the first attempt): take
`U = mk '' (inl '' {q | 0 < q.1.re ∧ 0 < q.2.re} ∪ inr '' {z | 0 < z.re})`,
open and saturated in `X`.  Its preimage is the disjoint union over `i : Fin 2`
of `mk '' (inl '' ({i} × T) ∪ inr '' Aᵢ)` with `Aᵢ` the arc about
`sheetPoint i = ±1` on which squaring is a homeomorphism onto `{z | 0 < z.re}`;
the glue `aux_glue` attaches `Aᵢ` to torus sheet `i`. -/
theorem apm_t01A04_circleCoverMap_evenlyCovered_basepoint :
    IsEvenlyCovered apm_t01a04_circleCoverMap apm_t01a04_basepoint
      (apm_t01a04_circleCoverMap ⁻¹' {apm_t01a04_basepoint}) := by
  obtain ⟨U, V, hxU, hU, hV, hdisj, hcover, hsheet⟩ := apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_sheets
  exact apm_t01A04_isEvenlyCovered_of_two_sheets apm_t01a04_circleCoverMap apm_t01a04_basepoint
    U hxU hU V hV hdisj hcover hsheet

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_inl_ne
    {q : apm_t01a04_Torus}
    (h : (Quotient.mk _ (Sum.inl q) : apm_t01a04_X) ≠
      apm_t01a04_basepoint) :
    q ≠ (1, 1) := by
  intro hq
  apply h
  subst q
  rfl

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_inr_ne
    {z : Circle}
    (h : (Quotient.mk _ (Sum.inr z) : apm_t01a04_X) ≠
      apm_t01a04_basepoint) :
    z ≠ 1 := by
  intro hz
  apply h
  subst z
  exact (Quotient.sound
    (Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base)).symm

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_reduce
    (hT : ∀ q : apm_t01a04_Torus, q ≠ (1, 1) →
      IsEvenlyCovered apm_t01a04_torusCoverMap
        (Quotient.mk _ (Sum.inl q))
        (apm_t01a04_torusCoverMap ⁻¹' {Quotient.mk _ (Sum.inl q)}))
    (hC : ∀ z : Circle, z ≠ 1 →
      IsEvenlyCovered apm_t01a04_torusCoverMap
        (Quotient.mk _ (Sum.inr z))
        (apm_t01a04_torusCoverMap ⁻¹' {Quotient.mk _ (Sum.inr z)}))
    (x : apm_t01a04_X) (hx : x ≠ apm_t01a04_basepoint) :
    IsEvenlyCovered apm_t01a04_torusCoverMap x
      (apm_t01a04_torusCoverMap ⁻¹' {x}) := by
  refine Quotient.inductionOn x ?_ hx
  rintro (q | z) h
  · exact hT q (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_inl_ne h)
  · exact hC z (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_inr_ne h)

def apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw :
    Sum apm_t01a04_Torus (Fin 2 × Circle) → apm_t01a04_Torus
  | .inl q => q
  | .inr q => (apm_t01a04_sheetPoint q.1, 1)

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw_respects
    {u v : Sum apm_t01a04_Torus (Fin 2 × Circle)}
    (h : Relation.EqvGen apm_t01a04_torusCoverRel u v) :
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw u =
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw v := by
  induction h with
  | rel _ _ h => cases h <;> rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction :
    apm_t01a04_TorusCover → apm_t01a04_Torus :=
  Quotient.lift
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw
    (fun _ _ h =>
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw_respects h)

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_base_continuous :
    Continuous apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.2
  exact ⟨continuous_id, continuous_const⟩

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_total_continuous :
    Continuous
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.2
  constructor
  · exact continuous_id
  · exact
      ((continuous_of_discreteTopology : Continuous apm_t01a04_sheetPoint).comp
        continuous_fst).prodMk continuous_const

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_square
    (e : apm_t01a04_TorusCover) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction
        (apm_t01a04_torusCoverMap e) =
      ((apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e).1 ^ 2,
        (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e).2) := by
  refine Quotient.inductionOn e ?_
  rintro (q | q)
  · rfl
  · simp [apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw,
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction,
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRaw]

/-- Torus-summand case: near `q ≠ (1,1)` the cover is `(z, w) ↦ (z², w)`
on the torus summand; the two square-root arcs in the first coordinate give the
two sheets (the glued points `(±1, 1)` lie over the excluded base point). -/
lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_product
    {E₁ X₁ E₂ X₂ I J : Type*}
    [TopologicalSpace E₁] [TopologicalSpace X₁]
    [TopologicalSpace E₂] [TopologicalSpace X₂]
    [TopologicalSpace I] [TopologicalSpace J]
    {f : E₁ → X₁} {g : E₂ → X₂} {x : X₁} {y : X₂}
    (hf : IsEvenlyCovered f x I) (hg : IsEvenlyCovered g y J) :
    IsEvenlyCovered (fun p : E₁ × E₂ ↦ (f p.1, g p.2)) (x, y) (I × J) := by
  rcases hf with ⟨hdI, U, hxU, hU, hfU, Hf, hHf⟩
  rcases hg with ⟨hdJ, V, hyV, hV, hgV, Hg, hHg⟩
  letI : DiscreteTopology I := hdI
  letI : DiscreteTopology J := hdJ
  refine ⟨inferInstance, U ×ˢ V, ⟨hxU, hyV⟩, hU.prod hV, ?_, ?_, ?_⟩
  · simpa using hfU.prod hgV
  · exact
      { toFun := fun p ↦
          (⟨((Hf ⟨p.1.1, p.2.1⟩).1.1, (Hg ⟨p.1.2, p.2.2⟩).1.1),
             (Hf ⟨p.1.1, p.2.1⟩).1.2, (Hg ⟨p.1.2, p.2.2⟩).1.2⟩,
           ((Hf ⟨p.1.1, p.2.1⟩).2, (Hg ⟨p.1.2, p.2.2⟩).2))
        invFun := fun z ↦
          ⟨((Hf.symm (⟨z.1.1.1, z.1.2.1⟩, z.2.1)).1,
             (Hg.symm (⟨z.1.1.2, z.1.2.2⟩, z.2.2)).1), by
            exact ⟨(Hf.symm (⟨z.1.1.1, z.1.2.1⟩, z.2.1)).2,
              (Hg.symm (⟨z.1.1.2, z.1.2.2⟩, z.2.2)).2⟩⟩
        left_inv := by
          intro p
          apply Subtype.ext
          exact Prod.ext
            (congrArg Subtype.val (Hf.symm_apply_apply ⟨p.1.1, p.2.1⟩))
            (congrArg Subtype.val (Hg.symm_apply_apply ⟨p.1.2, p.2.2⟩))
        right_inv := by intro z; ext <;> simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
  · intro p
    exact Prod.ext (hHf ⟨p.1.1, p.2.1⟩) (hHg ⟨p.1.2, p.2.2⟩)

theorem apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus
    (q : apm_t01a04_Torus) (hq : q ≠ (1, 1)) :
    IsEvenlyCovered apm_t01a04_torusCoverMap (Quotient.mk _ (Sum.inl q))
      (apm_t01a04_torusCoverMap ⁻¹' {Quotient.mk _ (Sum.inl q)}) := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have hsq := IsQuotientCoveringMap.isCoveringMap _ _
    (Circle.isQuotientCoveringMap_npow 2) q.1
  have hid : IsEvenlyCovered (fun w : Circle ↦ w) q.2 Unit := by
    let H : (fun w : Circle ↦ w) ⁻¹' Set.univ ≃ₜ Set.univ × Unit :=
      { toFun := fun w ↦ (⟨w.1, Set.mem_univ _⟩, ())
        invFun := fun w ↦ ⟨w.1.1, Set.mem_univ _⟩
        left_inv := by intro w; rfl
        right_inv := by rintro ⟨⟨w, hw⟩, ⟨⟩⟩; rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact ⟨inferInstance, Set.univ, Set.mem_univ _, isOpen_univ,
      by simp, H, fun w ↦ rfl⟩
  have hc := apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_product hsq hid
  rcases hc with ⟨hd, U, hqU, hU, hpU, H, hH⟩
  let V : Set apm_t01a04_Torus := U \ {(1, 1)}
  have hqV : q ∈ V := ⟨hqU, hq⟩
  have hV : IsOpen V := hU.sdiff isClosed_singleton
  let UX : Set apm_t01a04_X :=
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction ⁻¹' V
  have hUX : IsOpen UX := hV.preimage
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_base_continuous
  have hqUX : (Quotient.mk _ (Sum.inl q) : apm_t01a04_X) ∈ UX := hqV
  let W : Set apm_t01a04_Torus :=
    (fun p : apm_t01a04_Torus ↦ (p.1 ^ 2, p.2)) ⁻¹' V
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have hpre : apm_t01a04_torusCoverMap ⁻¹' UX =
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction ⁻¹' W := by
    ext e
    change apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction
        (apm_t01a04_torusCoverMap e) ∈ V ↔
      ((apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e).1 ^ 2,
       (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e).2) ∈ V
    rw [apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_square]
  have hopenpre : IsOpen (apm_t01a04_torusCoverMap ⁻¹' UX) := by
    rw [hpre]
    exact hW.preimage
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_total_continuous
  have himage (e : apm_t01a04_TorusCover)
      (he : e ∈ apm_t01a04_torusCoverMap ⁻¹' UX) :
      apm_t01a04_torusCoverMap e = Quotient.mk _ (Sum.inl
        ((apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e).1 ^ 2,
         (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e).2)) := by
    refine Quotient.inductionOn e ?_ he
    rintro (p | p) he
    · rfl
    · exfalso
      change ((1 : Circle), (1 : Circle)) ∈ V at he
      exact he.2 rfl
  let I := ((fun x : Circle ↦ x ^ 2) ⁻¹' {q.1}) × Unit
  have hWV : W ⊆ (fun p : apm_t01a04_Torus ↦ (p.1 ^ 2, p.2)) ⁻¹' U :=
    fun p hp ↦ hp.1
  have havoid (w : W) : (H ⟨w.1, hWV w.2⟩).1.1 ≠ (1, 1) := by
    intro hy
    exact w.2.2 ((hH ⟨w.1, hWV w.2⟩).symm.trans hy)
  let HW : W ≃ₜ V × I :=
    { toFun := fun w ↦
        (⟨(H ⟨w.1, hWV w.2⟩).1.1,
          ⟨(H ⟨w.1, hWV w.2⟩).1.2, havoid w⟩⟩,
          (H ⟨w.1, hWV w.2⟩).2)
      invFun := fun y ↦
        ⟨(H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1, by
          constructor
          · exact (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).2
          · have hh :
                (fun p : apm_t01a04_Torus ↦ (p.1 ^ 2, p.2))
                    (H.symm (⟨y.1.1, y.1.2.1⟩, y.2)).1 = y.1.1 := by
              calc
                _ = (H (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))).1.1 :=
                  (hH (H.symm (⟨y.1.1, y.1.2.1⟩, y.2))).symm
                _ = y.1.1 := congrArg (fun z ↦ z.1.1)
                  (H.apply_symm_apply (⟨y.1.1, y.1.2.1⟩, y.2))
            rw [hh]
            exact y.1.2.2⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro y; ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hHW (w : W) : (HW w).1.1 = (w.1.1 ^ 2, w.1.2) := hH ⟨w.1, hWV w.2⟩
  let E : apm_t01a04_torusCoverMap ⁻¹' UX ≃ₜ W :=
    { toFun := fun e ↦
        ⟨apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction e.1,
          by
            change ((apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction
              e.1).1 ^ 2,
              (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction
                e.1).2) ∈ V
            rw [← apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_square]
            exact e.2⟩
      invFun := fun w ↦ ⟨Quotient.mk _ (Sum.inl w.1), w.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        refine Quotient.inductionOn e ?_ he
        rintro (p | p) he
        · rfl
        · exfalso
          change ((1 : Circle), (1 : Circle)) ∈ V at he
          exact he.2 rfl
      right_inv := by rintro ⟨w, hw⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_total_continuous.comp
          continuous_subtype_val) (fun e ↦ by
            change ((apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction
              e.1).1 ^ 2,
              (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_totalRetraction
                e.1).2) ∈ V
            rw [← apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_square]
            exact e.2)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Sum apm_t01a04_Torus (Fin 2 × Circle) ↦
            (Quotient.mk _ u : apm_t01a04_TorusCover))).comp
              (continuous_inl.comp continuous_subtype_val) }
  let B : UX ≃ₜ V :=
    { toFun := fun x ↦
        ⟨apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction x.1, x.2⟩
      invFun := fun v ↦ ⟨Quotient.mk _ (Sum.inl v.1), v.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        refine Quotient.inductionOn x ?_ hx
        rintro (p | z) hx
        · rfl
        · exact (hx.2 rfl).elim
      right_inv := by rintro ⟨v, hv⟩; rfl
      continuous_toFun := Continuous.subtype_mk
        (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus_aux_base_continuous.comp
          continuous_subtype_val) _
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun u : Sum apm_t01a04_Torus Circle ↦
            (Quotient.mk _ u : apm_t01a04_X))).comp
              (continuous_inl.comp continuous_subtype_val) }
  refine (show IsEvenlyCovered apm_t01a04_torusCoverMap
      (Quotient.mk _ (Sum.inl q)) I from ?_).to_isEvenlyCovered_preimage
  refine ⟨hd, UX, hqUX, hUX, hopenpre, ?_, ?_⟩
  · exact E.trans (HW.trans (.prodCongr B.symm (.refl I)))
  · intro e
    change Quotient.mk _ (Sum.inl (HW (E e)).1.1) = apm_t01a04_torusCoverMap e.1
    rw [hHW]
    exact (himage e.1 e.2).symm

def apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw :
    Sum apm_t01a04_Torus (Fin 2 × Circle) → Circle
  | .inl _ => 1
  | .inr q => q.2

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw_respects
    {u v : Sum apm_t01a04_Torus (Fin 2 × Circle)}
    (h : Relation.EqvGen apm_t01a04_torusCoverRel u v) :
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw u =
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw v := by
  induction h with
  | rel _ _ h => cases h <;> rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction :
    apm_t01a04_TorusCover → Circle :=
  Quotient.lift
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw
    (fun _ _ h =>
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRaw_respects h)

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_total_continuous :
    Continuous
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.2
  exact ⟨continuous_const, continuous_snd⟩

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_compat
    (e : apm_t01a04_TorusCover) :
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction
        (apm_t01a04_torusCoverMap e) =
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_totalRetraction e := by
  refine Quotient.inductionOn e ?_
  rintro (q | q) <;> rfl

/-- Circle-summand case: near `z ≠ 1` the cover is the identity on each of the
two circle sheets `(i, ·)`, `i : Fin 2`. -/
lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetPoint_one_ne :
    apm_t01a04_sheetPoint (1 : Fin 2) ≠ 1 := by
  intro h
  have hr := congrArg (fun z : Circle => z.1.re) h
  norm_num [apm_t01a04_sheetPoint, Circle.exp, Complex.exp_mul_I] at hr

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_fin_cases (i : Fin 2) :
    i = 0 ∨ i = 1 := by
  have hi : i.val ≤ 1 := Nat.le_of_lt_succ i.isLt
  exact (Nat.le_one_iff_eq_zero_or_eq_one.mp hi).elim
    (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))

def apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw :
    Sum apm_t01a04_Torus (Fin 2 × Circle) → Fin 2 := by
  classical
  exact fun
    | .inl q => if q.1 = 1 then 0 else 1
    | .inr q => q.1

lemma apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw_respects
    {u v} (h : Relation.EqvGen apm_t01a04_torusCoverRel u v) :
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw u =
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw v := by
  induction h with
  | rel _ _ h =>
      cases h with
      | glue i =>
          classical
          have hi := apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_fin_cases i
          exact hi.elim
            (fun hi0 => by
              subst i
              change (if apm_t01a04_sheetPoint (0 : Fin 2) = 1 then 0 else 1) = 0
              rw [if_pos apm_t01a04_sheetPoint_zero])
            (fun hi1 => by
              subst i
              have hne :=
                apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetPoint_one_ne
              change (if apm_t01a04_sheetPoint (1 : Fin 2) = 1 then 0 else 1) = 1
              rw [if_neg hne])
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheet :
    apm_t01a04_TorusCover → Fin 2 :=
  Quotient.lift
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw
    (fun _ _ h =>
      apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw_respects h)

theorem apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle
    (z : Circle) (hz : z ≠ 1) :
    IsEvenlyCovered apm_t01a04_torusCoverMap (Quotient.mk _ (Sum.inr z))
      (apm_t01a04_torusCoverMap ⁻¹' {Quotient.mk _ (Sum.inr z)}) := by
  let V : Set Circle := {w | w ≠ 1}
  let U : Set apm_t01a04_X :=
    apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction ⁻¹' V
  have hU : IsOpen U :=
    (isOpen_compl_singleton : IsOpen ({1}ᶜ : Set Circle)).preimage
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_base_continuous
  have hzU : (Quotient.mk _ (Sum.inr z) : apm_t01a04_X) ∈ U := hz
  have hopenpre : IsOpen (apm_t01a04_torusCoverMap ⁻¹' U) :=
    hU.preimage apm_t01a04_torusCoverMap.continuous
  let E : apm_t01a04_torusCoverMap ⁻¹' U ≃ₜ U × Fin 2 :=
    { toFun := fun e =>
        (⟨apm_t01a04_torusCoverMap e.1, e.2⟩,
          apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheet e.1)
      invFun := fun y =>
        ⟨Quotient.mk _ (Sum.inr (y.2,
            apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction y.1)), by
          exact y.1.2⟩
      left_inv := by
        rintro ⟨e, he⟩
        apply Subtype.ext
        refine Quotient.inductionOn e ?_ he
        rintro (q | q) he
        · exfalso
          change (1 : Circle) ≠ 1 at he
          exact he rfl
        · rfl
      right_inv := by
        rintro ⟨⟨x, hx⟩, i⟩
        apply Prod.ext
        · apply Subtype.ext
          refine Quotient.inductionOn x ?_ hx
          rintro (q | w) hx
          · exfalso
            change (1 : Circle) ≠ 1 at hx
            exact hx rfl
          · rfl
        · simp [apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheet,
            apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw]
      continuous_toFun := by
        apply Continuous.prodMk
        · exact Continuous.subtype_mk
            (apm_t01a04_torusCoverMap.continuous.comp continuous_subtype_val) _
        · rw [continuous_def]
          intro s hs
          rw [isOpen_induced_iff]
          refine ⟨apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheet ⁻¹' s ∩
              apm_t01a04_torusCoverMap ⁻¹' U, ?_, ?_⟩
          · change @IsOpen _ (TopologicalSpace.coinduced
                (fun q : Sum apm_t01a04_Torus (Fin 2 × Circle) =>
                  Quotient.mk (Relation.EqvGen.setoid apm_t01a04_torusCoverRel) q)
                inferInstance)
              (apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheet ⁻¹' s ∩
                apm_t01a04_torusCoverMap ⁻¹' U)
            rw [isOpen_coinduced]
            apply isOpen_sum_iff.mpr
            constructor
            · simpa [U, V, apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw,
                apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheet,
                apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle_aux_sheetRaw] using
                (isOpen_empty : IsOpen (∅ : Set apm_t01a04_Torus))
            · change IsOpen {q : Fin 2 × Circle | q.1 ∈ s ∧ q.2 ≠ 1}
              exact (hs.preimage continuous_fst).inter
                ((isOpen_compl_singleton : IsOpen ({1}ᶜ : Set Circle)).preimage
                  continuous_snd)
          · ext e
            simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
              Subtype.coe_prop, and_true]
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (continuous_coinduced_rng : Continuous
          (fun q : Sum apm_t01a04_Torus (Fin 2 × Circle) =>
            (Quotient.mk _ q : apm_t01a04_TorusCover))).comp
          (continuous_inr.comp
            (continuous_snd.prodMk
              (apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circle_aux_base_continuous.comp
                (continuous_subtype_val.comp continuous_fst)))) }
  refine (show IsEvenlyCovered apm_t01a04_torusCoverMap
      (Quotient.mk _ (Sum.inr z)) (Fin 2) from ?_).to_isEvenlyCovered_preimage
  refine ⟨inferInstance, U, hzU, hU, hopenpre, E, ?_⟩
  intro e
  rfl

/-- Away from the wedge point, the torus-doubled quotient is locally either
circle squaring in the first torus coordinate or an identity circle sheet. -/
theorem apm_t01A04_torusCoverMap_evenlyCovered_away
    (x : apm_t01a04_X) (hx : x ≠ apm_t01a04_basepoint) :
    IsEvenlyCovered apm_t01a04_torusCoverMap x
      (apm_t01a04_torusCoverMap ⁻¹' {x}) :=
  apm_t01A04_torusCoverMap_evenlyCovered_away_aux_reduce
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus
    apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle x hx

lemma apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_glue (i : Fin 2) :
    (Quotient.mk _
        (.inl (apm_t01a04_sheetPoint i, (1 : Circle))) :
      apm_t01a04_TorusCover) =
      Quotient.mk _ (.inr (i, (1 : Circle))) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t01a04_torusCoverRel.glue i))

lemma apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_mem_fiber
    (i : Fin 2) :
    Quotient.mk _ (.inl (apm_t01a04_sheetPoint i, (1 : Circle))) ∈
      apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint} := by
  change apm_t01a04_torusCoverMap
      (Quotient.mk _
        (.inl (apm_t01a04_sheetPoint i, (1 : Circle)))) =
    apm_t01a04_basepoint
  simp [apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw,
    apm_t01a04_basepoint]

lemma apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_square_root
    (z : Circle) (hz : z ^ 2 = 1) :
    ∃ i : Fin 2, z = apm_t01a04_sheetPoint i := by
  have hz' : (z : ℂ) ^ 2 = 1 := congrArg Subtype.val hz
  rcases (sq_eq_one_iff.mp hz') with h | h
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa using h
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [apm_t01a04_sheetPoint_one, Circle.coe_exp, Complex.exp_pi_mul_I]
    exact h

lemma apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_sheetPoint_injective :
    Function.Injective apm_t01a04_sheetPoint := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    exact Circle.exp_pi_ne_one hij.symm
  · exfalso
    exact Circle.exp_pi_ne_one hij
  · rfl

lemma apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_sheets_aux_fiber_points
    (e : apm_t01a04_TorusCover)
    (he : apm_t01a04_torusCoverMap e = apm_t01a04_basepoint) :
    ∃ i : Fin 2,
      e = Quotient.mk _
        (.inl (apm_t01a04_sheetPoint i, (1 : Circle))) := by
  refine Quotient.inductionOn e ?_ he
  rintro (q | q) he
  · have hq := congrArg
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction he
    have hq' : (q.1 ^ 2, q.2) = ((1 : Circle), (1 : Circle)) := by
      simpa [apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw,
        apm_t01a04_basepoint] using hq
    obtain ⟨i, hi⟩ :=
      apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_square_root
        q.1 (congrArg Prod.fst hq')
    have hq2 : q.2 = (1 : Circle) :=
      congrArg (fun p : apm_t01a04_Torus => p.2) hq'
    refine ⟨i, ?_⟩
    apply congrArg (fun t : apm_t01a04_Torus =>
      Quotient.mk _ (Sum.inl t))
    exact Prod.ext hi hq2
  · have hq := congrArg
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction he
    have hz : q.2 = 1 := by
      simpa [apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw,
        apm_t01a04_basepoint] using hq
    refine ⟨q.1, ?_⟩
    rw [apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_glue]
    apply congrArg (fun t : Fin 2 × Circle =>
      Quotient.mk _ (Sum.inr t))
    exact Prod.ext rfl hz

/-- Basepoint neighbourhood in `X` for the torus cover: positive real parts. -/
def apm_t01A04_tbp_U : Set apm_t01a04_X :=
  (fun r => (Quotient.mk _ r : apm_t01a04_X)) ''
    {r | Sum.elim (fun q : apm_t01a04_Torus => 0 < (q.1 : ℂ).re ∧ 0 < (q.2 : ℂ).re)
      (fun z : Circle => 0 < (z : ℂ).re) r}

/-- Sheet `i` over it: torus points with first coordinate near `sheetPoint i`
(and `q.1²` of positive real part), plus circle sheet `i`. -/
def apm_t01A04_tbp_V (i : Fin 2) : Set apm_t01a04_TorusCover :=
  (fun r => (Quotient.mk _ r : apm_t01a04_TorusCover)) ''
    {r | Sum.elim (fun q : apm_t01a04_Torus =>
        0 < ((q.1 : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
        0 < ((q.1 : ℂ) ^ 2).re ∧ 0 < (q.2 : ℂ).re)
      (fun p : Fin 2 × Circle => p.1 = i ∧ 0 < (p.2 : ℂ).re) r}

lemma apm_t01A04_tbp_U_open_aux_invariant
    {u v : Sum apm_t01a04_Torus Circle}
    (h : Relation.EqvGen apm_t01a04_wedgeRel u v) :
    (Sum.elim
        (fun q : apm_t01a04_Torus =>
          0 < (q.1 : ℂ).re ∧ 0 < (q.2 : ℂ).re)
        (fun z : Circle => 0 < (z : ℂ).re) u ↔
      Sum.elim
        (fun q : apm_t01a04_Torus =>
          0 < (q.1 : ℂ).re ∧ 0 < (q.2 : ℂ).re)
        (fun z : Circle => 0 < (z : ℂ).re) v) := by
  induction h with
  | rel _ _ h => cases h <;> norm_num
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t01A04_tbp_U_open : apm_t01a04_basepoint ∈ apm_t01A04_tbp_U ∧ IsOpen apm_t01A04_tbp_U := by
  constructor
  · refine ⟨Sum.inl ((1 : Circle), (1 : Circle)), ?_, rfl⟩
    norm_num
  · change IsOpen ((fun r => (Quotient.mk _ r : apm_t01a04_X)) '' _)
    rw [isOpen_coinduced]
    have heq :
        (fun r : Sum apm_t01a04_Torus Circle =>
            (Quotient.mk _ r : apm_t01a04_X)) ⁻¹'
            ((fun r => (Quotient.mk _ r : apm_t01a04_X)) ''
              {r | Sum.elim
                (fun q : apm_t01a04_Torus =>
                  0 < (q.1 : ℂ).re ∧ 0 < (q.2 : ℂ).re)
                (fun z : Circle => 0 < (z : ℂ).re) r}) =
          {r | Sum.elim
            (fun q : apm_t01a04_Torus =>
              0 < (q.1 : ℂ).re ∧ 0 < (q.2 : ℂ).re)
            (fun z : Circle => 0 < (z : ℂ).re) r} := by
      ext r
      constructor
      · rintro ⟨s, hs, hrs⟩
        exact (apm_t01A04_tbp_U_open_aux_invariant
          (Quotient.exact hrs)).mp hs
      · intro hr
        exact ⟨r, hr, rfl⟩
    rw [heq, isOpen_sum_iff]
    constructor
    · exact ((isOpen_lt continuous_const
          (Complex.continuous_re.comp (continuous_subtype_val.comp continuous_fst))).inter
        (isOpen_lt continuous_const
          (Complex.continuous_re.comp (continuous_subtype_val.comp continuous_snd))))
    · exact isOpen_lt continuous_const
        (Complex.continuous_re.comp continuous_subtype_val)

lemma apm_t01A04_tbp_V_open_aux_invariant (i : Fin 2)
    {u v : Sum apm_t01a04_Torus (Fin 2 × Circle)}
    (h : Relation.EqvGen apm_t01a04_torusCoverRel u v) :
    (Sum.elim (fun q : apm_t01a04_Torus =>
        0 < ((q.1 : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
        0 < ((q.1 : ℂ) ^ 2).re ∧ 0 < (q.2 : ℂ).re)
      (fun p : Fin 2 × Circle => p.1 = i ∧ 0 < (p.2 : ℂ).re) u ↔
    Sum.elim (fun q : apm_t01a04_Torus =>
        0 < ((q.1 : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
        0 < ((q.1 : ℂ) ^ 2).re ∧ 0 < (q.2 : ℂ).re)
      (fun p : Fin 2 × Circle => p.1 = i ∧ 0 < (p.2 : ℂ).re) v) := by
  induction h with
  | rel _ _ h =>
      cases h with
      | glue j =>
        simp only [Sum.elim_inl, Sum.elim_inr, Prod.fst, Prod.snd,
          apm_t01a04_sheetPoint_sq]
        fin_cases i <;> fin_cases j <;>
          simp [apm_t01a04_sheetPoint, Circle.exp, Complex.exp_mul_I] <;>
          norm_num
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t01A04_tbp_V_open (i : Fin 2) : IsOpen (apm_t01A04_tbp_V i) := by
  change IsOpen ((fun r => (Quotient.mk _ r : apm_t01a04_TorusCover)) '' _)
  rw [isOpen_coinduced]
  have heq :
      (fun r : Sum apm_t01a04_Torus (Fin 2 × Circle) =>
        (Quotient.mk _ r : apm_t01a04_TorusCover)) ⁻¹'
        ((fun r => (Quotient.mk _ r : apm_t01a04_TorusCover)) ''
          {r | Sum.elim (fun q : apm_t01a04_Torus =>
              0 < ((q.1 : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
              0 < ((q.1 : ℂ) ^ 2).re ∧ 0 < (q.2 : ℂ).re)
            (fun p : Fin 2 × Circle => p.1 = i ∧ 0 < (p.2 : ℂ).re) r}) =
        {r | Sum.elim (fun q : apm_t01a04_Torus =>
            0 < ((q.1 : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
            0 < ((q.1 : ℂ) ^ 2).re ∧ 0 < (q.2 : ℂ).re)
          (fun p : Fin 2 × Circle => p.1 = i ∧ 0 < (p.2 : ℂ).re) r} := by
    ext r
    constructor
    · rintro ⟨s, hs, hrs⟩
      exact (apm_t01A04_tbp_V_open_aux_invariant i (Quotient.exact hrs)).mp hs
    · intro hr
      exact ⟨r, hr, rfl⟩
  rw [heq, isOpen_sum_iff]
  constructor
  · exact ((isOpen_lt continuous_const
        (Complex.continuous_re.comp
          ((continuous_subtype_val.comp continuous_fst).mul continuous_const))).inter
      ((isOpen_lt continuous_const
        (Complex.continuous_re.comp
          ((continuous_subtype_val.comp continuous_fst).pow 2))).inter
        (isOpen_lt continuous_const
          (Complex.continuous_re.comp
            (continuous_subtype_val.comp continuous_snd)))))
  · exact ((isOpen_discrete ({i} : Set (Fin 2))).preimage
        continuous_fst).inter
      (isOpen_lt continuous_const
        (Complex.continuous_re.comp
          (continuous_subtype_val.comp continuous_snd)))

def apm_t01A04_tbp_V_disjoint_aux_raw :
    Sum apm_t01a04_Torus (Fin 2 × Circle) → ℝ
  | .inl q => (q.1 : ℂ).re
  | .inr p => (apm_t01a04_sheetPoint p.1 : ℂ).re

lemma apm_t01A04_tbp_V_disjoint_aux_raw_respects {u v}
    (h : Relation.EqvGen apm_t01a04_torusCoverRel u v) :
    apm_t01A04_tbp_V_disjoint_aux_raw u =
      apm_t01A04_tbp_V_disjoint_aux_raw v := by
  induction h with
  | rel _ _ h => cases h <;> rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_tbp_V_disjoint_aux_value : apm_t01a04_TorusCover → ℝ :=
  Quotient.lift apm_t01A04_tbp_V_disjoint_aux_raw
    (fun _ _ h => apm_t01A04_tbp_V_disjoint_aux_raw_respects h)

lemma apm_t01A04_tbp_V_disjoint_aux_sign (i : Fin 2)
    {e : apm_t01a04_TorusCover} (he : e ∈ apm_t01A04_tbp_V i) :
    if i = 0 then 0 < apm_t01A04_tbp_V_disjoint_aux_value e
    else apm_t01A04_tbp_V_disjoint_aux_value e < 0 := by
  rcases he with ⟨r, hr, rfl⟩
  fin_cases i <;> cases r with
  | inl q =>
      simpa [apm_t01A04_tbp_V_disjoint_aux_value,
        apm_t01A04_tbp_V_disjoint_aux_raw, apm_t01a04_sheetPoint,
        Circle.exp, Complex.exp_mul_I] using hr.1
  | inr p =>
      simp_all [apm_t01A04_tbp_V_disjoint_aux_value,
        apm_t01A04_tbp_V_disjoint_aux_raw, apm_t01a04_sheetPoint,
        Circle.exp, Complex.exp_mul_I]

lemma apm_t01A04_tbp_V_disjoint : Pairwise (Function.onFun Disjoint apm_t01A04_tbp_V) := by
  intro i j hij
  change Disjoint (apm_t01A04_tbp_V i) (apm_t01A04_tbp_V j)
  rw [Set.disjoint_left]
  intro e hei hej
  have hi := apm_t01A04_tbp_V_disjoint_aux_sign i hei
  have hj := apm_t01A04_tbp_V_disjoint_aux_sign j hej
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith

def apm_t01A04_tbp_preimage_aux_basePred :
    Sum apm_t01a04_Torus Circle → Prop
  | .inl q => 0 < (q.1 : ℂ).re ∧ 0 < (q.2 : ℂ).re
  | .inr z => 0 < (z : ℂ).re

def apm_t01A04_tbp_preimage_aux_totalPred (i : Fin 2) :
    Sum apm_t01a04_Torus (Fin 2 × Circle) → Prop
  | .inl q =>
      0 < ((q.1 : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re ∧
      0 < ((q.1 : ℂ) ^ 2).re ∧ 0 < (q.2 : ℂ).re
  | .inr p => p.1 = i ∧ 0 < (p.2 : ℂ).re

lemma apm_t01A04_tbp_preimage_aux_base_invariant {r s}
    (h : Relation.EqvGen apm_t01a04_wedgeRel r s) :
    apm_t01A04_tbp_preimage_aux_basePred r ↔
      apm_t01A04_tbp_preimage_aux_basePred s := by
  induction h with
  | rel _ _ h => cases h; simp [apm_t01A04_tbp_preimage_aux_basePred]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t01A04_tbp_preimage_aux_total_invariant (i : Fin 2) {r s}
    (h : Relation.EqvGen apm_t01a04_torusCoverRel r s) :
    apm_t01A04_tbp_preimage_aux_totalPred i r ↔
      apm_t01A04_tbp_preimage_aux_totalPred i s := by
  induction h with
  | rel _ _ h =>
      cases h with
      | glue j =>
        fin_cases i <;> fin_cases j <;>
          simp [apm_t01A04_tbp_preimage_aux_totalPred, apm_t01a04_sheetPoint,
            Circle.exp, Complex.exp_mul_I]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t01A04_tbp_preimage_aux_mem_U (r) :
    (Quotient.mk _ r : apm_t01a04_X) ∈ apm_t01A04_tbp_U ↔
      apm_t01A04_tbp_preimage_aux_basePred r := by
  constructor
  · rintro ⟨s, hs, hsr⟩
    have hs' : apm_t01A04_tbp_preimage_aux_basePred s := by
      cases s <;> exact hs
    exact (apm_t01A04_tbp_preimage_aux_base_invariant
      (Quotient.exact hsr)).mp hs'
  · intro hr
    refine ⟨r, ?_, rfl⟩
    cases r <;> exact hr

lemma apm_t01A04_tbp_preimage_aux_mem_V (i : Fin 2) (r) :
    (Quotient.mk _ r : apm_t01a04_TorusCover) ∈ apm_t01A04_tbp_V i ↔
      apm_t01A04_tbp_preimage_aux_totalPred i r := by
  constructor
  · rintro ⟨s, hs, hsr⟩
    have hs' : apm_t01A04_tbp_preimage_aux_totalPred i s := by
      cases s <;> exact hs
    exact (apm_t01A04_tbp_preimage_aux_total_invariant i
      (Quotient.exact hsr)).mp hs'
  · intro hr
    refine ⟨r, ?_, rfl⟩
    cases r <;> exact hr

lemma apm_t01A04_tbp_preimage_aux_arc (z : Circle)
    (hz : 0 < ((z : ℂ) ^ 2).re) :
    ∃ i : Fin 2,
      0 < ((z : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re := by
  have hre : (z : ℂ).re ≠ 0 := by
    intro h
    have hz' : ((z : ℂ) ^ 2).re ≤ 0 := by
      simp [pow_two, Complex.mul_re, h, mul_self_nonneg]
    exact (not_lt_of_ge hz') hz
  rcases lt_or_gt_of_ne hre with hre | hre
  · refine ⟨1, ?_⟩
    simp [apm_t01a04_sheetPoint, Circle.exp, Complex.exp_mul_I]
    linarith
  · refine ⟨0, ?_⟩
    simpa [apm_t01a04_sheetPoint] using hre

lemma apm_t01A04_tbp_preimage :
    apm_t01a04_torusCoverMap ⁻¹' apm_t01A04_tbp_U = ⋃ i, apm_t01A04_tbp_V i := by
  ext e
  refine Quotient.inductionOn e ?_
  rintro (q | p)
  · simp only [Set.mem_preimage, Set.mem_iUnion]
    change
      (Quotient.mk _ (Sum.inl (q.1 ^ 2, q.2)) : apm_t01a04_X) ∈
          apm_t01A04_tbp_U ↔
        ∃ i, (Quotient.mk _ (Sum.inl q) : apm_t01a04_TorusCover) ∈
          apm_t01A04_tbp_V i
    simp only [apm_t01A04_tbp_preimage_aux_mem_U,
      apm_t01A04_tbp_preimage_aux_mem_V,
      apm_t01A04_tbp_preimage_aux_basePred,
      apm_t01A04_tbp_preimage_aux_totalPred]
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨i, hi⟩ := apm_t01A04_tbp_preimage_aux_arc q.1 h₁
      exact ⟨i, hi, h₁, h₂⟩
    · rintro ⟨i, -, h₁, h₂⟩
      exact ⟨h₁, h₂⟩
  · simp only [Set.mem_preimage, Set.mem_iUnion]
    change
      (Quotient.mk _ (Sum.inr p.2) : apm_t01a04_X) ∈ apm_t01A04_tbp_U ↔
        ∃ i, (Quotient.mk _ (Sum.inr p) : apm_t01a04_TorusCover) ∈
          apm_t01A04_tbp_V i
    simp only [apm_t01A04_tbp_preimage_aux_mem_U,
      apm_t01A04_tbp_preimage_aux_mem_V,
      apm_t01A04_tbp_preimage_aux_basePred,
      apm_t01A04_tbp_preimage_aux_totalPred]
    constructor
    · intro hp
      exact ⟨p.1, rfl, hp⟩
    · rintro ⟨i, -, hp⟩
      exact hp

noncomputable def apm_t01A04_tbp_sheet_homeomorph_aux_root
    (i : Fin 2) (z : Circle) : Circle :=
  apm_t01a04_sheetPoint i * Circle.exp (Complex.arg z / 2)

lemma apm_t01A04_tbp_sheet_homeomorph_aux_root_sq
    (i : Fin 2) (z : Circle) :
    apm_t01A04_tbp_sheet_homeomorph_aux_root i z ^ 2 = z := by
  rw [apm_t01A04_tbp_sheet_homeomorph_aux_root, mul_pow,
    apm_t01a04_sheetPoint_sq, one_mul, pow_two, ← Circle.exp_add]
  convert Circle.exp_arg z using 1 <;> ring

lemma apm_t01A04_tbp_sheet_homeomorph_aux_branch_unique
    (i : Fin 2) (x y : Circle) (hsq : x ^ 2 = y ^ 2)
    (hx : 0 < ((x : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re)
    (hy : 0 < ((y : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re) :
    x = y := by
  have hsq' : (x : ℂ) ^ 2 = (y : ℂ) ^ 2 := congrArg Subtype.val hsq
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq' with h | h
  · exact Subtype.ext h
  · exfalso
    have hxy :
        ((x : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re =
          -((y : ℂ) * star (apm_t01a04_sheetPoint i : ℂ)).re := by
      rw [h]
      simp
    linarith

/-- On each sheet the cover map is a homeomorphism onto `U` (inverse: square
root on the arc around `sheetPoint i`, identity on circle sheet `i`). -/
lemma apm_t01A04_tbp_sheet_homeomorph (i : Fin 2) :
    ∃ h : apm_t01A04_tbp_V i ≃ₜ apm_t01A04_tbp_U, ∀ y,
      (h y : apm_t01a04_X) = apm_t01a04_torusCoverMap y := by
  sorry

/-- The two sheets over the basepoint (see the plan above). -/
lemma apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_sheets :
    ∃ (U : Set apm_t01a04_X) (V : Fin 2 → Set apm_t01a04_TorusCover),
      apm_t01a04_basepoint ∈ U ∧ IsOpen U ∧ (∀ i, IsOpen (V i)) ∧
      Pairwise (Function.onFun Disjoint V) ∧
      apm_t01a04_torusCoverMap ⁻¹' U = ⋃ i, V i ∧
      ∀ i, ∃ h : V i ≃ₜ U, ∀ y,
        (h y : apm_t01a04_X) = apm_t01a04_torusCoverMap y := by
  obtain ⟨hb, hU⟩ := apm_t01A04_tbp_U_open
  exact ⟨apm_t01A04_tbp_U, apm_t01A04_tbp_V, hb, hU, apm_t01A04_tbp_V_open, apm_t01A04_tbp_V_disjoint,
    apm_t01A04_tbp_preimage, apm_t01A04_tbp_sheet_homeomorph⟩

/-- Basepoint case.  Plan: take
`U = mk '' (inl '' {q | 0 < q.1.re ∧ 0 < q.2.re} ∪ inr '' {z | 0 < z.re})`,
open and saturated in `X`.  Its preimage is the disjoint union over `i : Fin 2`
of `mk '' (inl '' {q | q.1 ∈ Aᵢ ∧ 0 < q.2.re} ∪ inr '' ({i} × {z | 0 < z.re}))`
with `Aᵢ` the arc about `sheetPoint i = ±1` on which squaring is a
homeomorphism onto `{z | 0 < z.re}`; the banked glue lemmas attach circle
sheet `i` at `(sheetPoint i, 1)`. -/
theorem apm_t01A04_torusCoverMap_evenlyCovered_basepoint :
    IsEvenlyCovered apm_t01a04_torusCoverMap apm_t01a04_basepoint
      (apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) := by
  obtain ⟨U, V, hxU, hU, hV, hdisj, hcover, hsheet⟩ := apm_t01A04_torusCoverMap_evenlyCovered_basepoint_aux_sheets
  exact apm_t01A04_isEvenlyCovered_of_two_sheets apm_t01a04_torusCoverMap apm_t01a04_basepoint
    U hxU hU V hV hdisj hcover hsheet

/-- Why this unblocks `apm_t01a04`: this is the missing local
evenly-covered-neighborhood construction for the two concrete quotient maps.
Surjectivity and basepoint preservation are already proved separately. -/
theorem apm_t01A04_bridge_quotient_maps_are_coverings :
    IsCoveringMap apm_t01a04_circleCoverMap ∧
    IsCoveringMap apm_t01a04_torusCoverMap := by
  constructor
  · intro x
    by_cases hx : x = apm_t01a04_basepoint
    · subst x
      exact apm_t01A04_circleCoverMap_evenlyCovered_basepoint
    · exact apm_t01A04_circleCoverMap_evenlyCovered_away x hx
  · intro x
    by_cases hx : x = apm_t01a04_basepoint
    · subst x
      exact apm_t01A04_torusCoverMap_evenlyCovered_basepoint
    · exact apm_t01A04_torusCoverMap_evenlyCovered_away x hx

lemma apm_t01A04_canonical_loops_presentation_aux_rel_iff
    (x y : Sum apm_t01a04_Torus Circle) :
    apm_t01a04_wedgeRel x y ↔
      ConstructionTargets.PointWedgeQuotient.Rel
        ((1, 1) : apm_t01a04_Torus) (1 : Circle) x y := by
  constructor
  · intro h
    cases h
    exact ConstructionTargets.PointWedgeQuotient.Rel.base
  · intro h
    cases h
    exact apm_t01a04_wedgeRel.base

/-- The concrete quotient used in the problem is literally the library's
point-wedge quotient on representatives. -/
def apm_t01A04_canonical_loops_presentation_aux_homeomorph :
    apm_t01a04_X ≃ₜ
      ConstructionTargets.PointWedgeQuotient.Wedge
        ((1, 1) : apm_t01a04_Torus) (1 : Circle) :=
  ConstructionTargets.PointWedgeQuotient.quotientHomeomorphOfRelIff
    apm_t01a04_wedgeRel
    (ConstructionTargets.PointWedgeQuotient.Rel
      ((1, 1) : apm_t01a04_Torus) (1 : Circle))
    apm_t01A04_canonical_loops_presentation_aux_rel_iff

@[simp] lemma apm_t01A04_canonical_loops_presentation_aux_homeomorph_mk
    (z : Sum apm_t01a04_Torus Circle) :
    apm_t01A04_canonical_loops_presentation_aux_homeomorph
        (Quotient.mk _ z) =
      ConstructionTargets.PointWedgeQuotient.quotientMap
        ((1, 1) : apm_t01a04_Torus) (1 : Circle) z := rfl

@[simp] lemma apm_t01A04_canonical_loops_presentation_aux_homeomorph_base :
    apm_t01A04_canonical_loops_presentation_aux_homeomorph
        apm_t01a04_basepoint =
      ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeBase := rfl

noncomputable def apm_t01A04_canonical_loops_presentation_aux_images_aux_transportHom :
    apm_t01a04_piOne →*
      FundamentalGroup
        (ConstructionTargets.PointWedgeQuotient.Wedge
          ((1, 1) : apm_t01a04_Torus) (1 : Circle))
        ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeBase :=
  FundamentalGroup.map
    ⟨apm_t01A04_canonical_loops_presentation_aux_homeomorph,
      apm_t01A04_canonical_loops_presentation_aux_homeomorph.continuous⟩
    apm_t01a04_basepoint

lemma apm_t01A04_canonical_loops_presentation_aux_images_aux_transport_bijective :
    Function.Bijective
      apm_t01A04_canonical_loops_presentation_aux_images_aux_transportHom := by
  constructor
  · intro x y hxy
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    apply Quotient.sound
    convert (Path.Homotopic.Quotient.exact hxy).map
      ⟨apm_t01A04_canonical_loops_presentation_aux_homeomorph.symm,
        apm_t01A04_canonical_loops_presentation_aux_homeomorph.symm.continuous⟩ using 1 <;>
      ext t <;>
      exact (apm_t01A04_canonical_loops_presentation_aux_homeomorph.symm_apply_apply _).symm
  · intro y
    obtain ⟨y⟩ := y
    refine ⟨Path.Homotopic.Quotient.mk
      (y.map apm_t01A04_canonical_loops_presentation_aux_homeomorph.symm.continuous), ?_⟩
    apply Quotient.sound
    convert Path.Homotopic.refl y using 1 <;> ext t <;>
      exact apm_t01A04_canonical_loops_presentation_aux_homeomorph.apply_symm_apply _

noncomputable def apm_t01A04_canonical_loops_presentation_aux_images_aux_transport :
    apm_t01a04_piOne ≃*
      FundamentalGroup
        (ConstructionTargets.PointWedgeQuotient.Wedge
          ((1, 1) : apm_t01a04_Torus) (1 : Circle))
        ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeBase :=
  MulEquiv.ofBijective
    apm_t01A04_canonical_loops_presentation_aux_images_aux_transportHom
    apm_t01A04_canonical_loops_presentation_aux_images_aux_transport_bijective

/-- LIBRARY (van Kampen naturality): some identification of the wedge
fundamental group with `ℤ² * ℤ` sends the three canonical loops to the
standard generators.  `wedgeFundamentalGroupMulEquiv` (transported along
`apm_t01A04_canonical_loops_presentation_aux_homeomorph`) is the candidate, but
the import computes no generator images; composing with a free-product
automorphism is allowed. -/
theorem apm_t01A04_canonical_loops_presentation_aux_images :
    ∃ Φ : apm_t01a04_piOne ≃* ConstructionTargets.GenericTargetNaturalSourceReconstruction.FP,
      Φ apm_t01A04_loopA = Monoid.Coprod.inl (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)) ∧
      Φ apm_t01A04_loopB = Monoid.Coprod.inl (Multiplicative.ofAdd ((0, 1) : ℤ × ℤ)) ∧
      Φ apm_t01A04_loopC = Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ)) := by
  sorry

/-- Pure group theory: a group isomorphic to `ℤ² * ℤ` with the three loops on
the standard generators has the stated presentation.  Commutation is
commutation in `ℤ²`; generation and the universal property come from
`Monoid.Coprod.lift` and the free abelian group `ℤ²` on two commuting
generators. -/
theorem apm_t01A04_canonical_loops_presentation_aux_algebra
    (Φ : apm_t01a04_piOne ≃* ConstructionTargets.GenericTargetNaturalSourceReconstruction.FP)
    (hA : Φ apm_t01A04_loopA = Monoid.Coprod.inl (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)))
    (hB : Φ apm_t01A04_loopB = Monoid.Coprod.inl (Multiplicative.ofAdd ((0, 1) : ℤ × ℤ)))
    (hC : Φ apm_t01A04_loopC = Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) :
    apm_t01A04_loopA * apm_t01A04_loopB =
        apm_t01A04_loopB * apm_t01A04_loopA ∧
    Subgroup.closure
        {apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} = ⊤ ∧
    (∀ (G : Type) [Group G] (ga gb gc : G), ga * gb = gb * ga →
      ∃! F : apm_t01a04_piOne →* G,
        F apm_t01A04_loopA = ga ∧ F apm_t01A04_loopB = gb ∧
          F apm_t01A04_loopC = gc) := by
  let a : ConstructionTargets.GenericTargetNaturalSourceReconstruction.FP :=
    Monoid.Coprod.inl (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ))
  let b : ConstructionTargets.GenericTargetNaturalSourceReconstruction.FP :=
    Monoid.Coprod.inl (Multiplicative.ofAdd ((0, 1) : ℤ × ℤ))
  let c : ConstructionTargets.GenericTargetNaturalSourceReconstruction.FP :=
    Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))
  have hab : a * b = b * a := by
    dsimp [a, b]
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul]
    congr 1
  have hcomm : apm_t01A04_loopA * apm_t01A04_loopB =
      apm_t01A04_loopB * apm_t01A04_loopA := by
    apply Φ.injective
    simpa [hA, hB, a, b] using hab
  have hgen : Subgroup.closure
      {apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} = ⊤ := by
    apply top_unique
    intro x _
    let K := Subgroup.closure
      ({apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} :
        Set apm_t01a04_piOne)
    have haK : apm_t01A04_loopA ∈ K := Subgroup.subset_closure (by simp)
    have hbK : apm_t01A04_loopB ∈ K := Subgroup.subset_closure (by simp)
    have hcK : apm_t01A04_loopC ∈ K := Subgroup.subset_closure (by simp)
    have hall : ∀ y : ConstructionTargets.GenericTargetNaturalSourceReconstruction.FP,
        Φ.symm y ∈ K := by
      intro y
      induction y using Monoid.Coprod.induction_on with
      | inl z =>
          change Φ.symm (Monoid.Coprod.inl z) ∈ K
          let m : ℤ := z.toAdd.1
          let n : ℤ := z.toAdd.2
          rw [show z =
              Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) ^ m *
                Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) ^ n by
                apply Multiplicative.toAdd.injective
                simp [m, n]]
          have ha : Φ.symm (Monoid.Coprod.inl
              (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ))) = apm_t01A04_loopA := by
            apply Φ.injective
            simpa using hA.symm
          have hb : Φ.symm (Monoid.Coprod.inl
              (Multiplicative.ofAdd ((0, 1) : ℤ × ℤ))) = apm_t01A04_loopB := by
            apply Φ.injective
            simpa using hB.symm
          simp only [map_mul, map_zpow, ha, hb]
          exact K.mul_mem (K.zpow_mem haK m) (K.zpow_mem hbK n)
      | inr z =>
          change Φ.symm (Monoid.Coprod.inr z) ∈ K
          let n : ℤ := z.toAdd
          rw [show z = Multiplicative.ofAdd (1 : ℤ) ^ n by
                apply Multiplicative.toAdd.injective
                simp [n]]
          have hc : Φ.symm (Monoid.Coprod.inr
              (Multiplicative.ofAdd (1 : ℤ))) = apm_t01A04_loopC := by
            apply Φ.injective
            simpa using hC.symm
          simp only [map_zpow, hc]
          exact K.zpow_mem hcK n
      | mul u v hu hv =>
          rw [map_mul]
          exact K.mul_mem hu hv
    simpa [K] using hall (Φ x)
  refine ⟨hcomm, hgen, ?_⟩
  intro G _ ga gb gc hgab
  let pairHom : Multiplicative (ℤ × ℤ) →* G :=
    { toFun := fun z => ga ^ z.toAdd.1 * gb ^ z.toAdd.2
      map_one' := by simp
      map_mul' := by
        intro x y
        change ga ^ (x.toAdd.1 + y.toAdd.1) * gb ^ (x.toAdd.2 + y.toAdd.2) =
          (ga ^ x.toAdd.1 * gb ^ x.toAdd.2) *
            (ga ^ y.toAdd.1 * gb ^ y.toAdd.2)
        rw [zpow_add, zpow_add]
        have hg : Commute ga gb := hgab
        have hp := (Commute.zpow_zpow hg.symm x.toAdd.2 y.toAdd.1).eq
        calc
          ga ^ x.toAdd.1 * ga ^ y.toAdd.1 *
                (gb ^ x.toAdd.2 * gb ^ y.toAdd.2) =
              ga ^ x.toAdd.1 *
                (ga ^ y.toAdd.1 * gb ^ x.toAdd.2) * gb ^ y.toAdd.2 := by
                  simp only [mul_assoc]
          _ = ga ^ x.toAdd.1 *
                (gb ^ x.toAdd.2 * ga ^ y.toAdd.1) * gb ^ y.toAdd.2 := by
                  rw [hp.symm]
          _ = (ga ^ x.toAdd.1 * gb ^ x.toAdd.2) *
                (ga ^ y.toAdd.1 * gb ^ y.toAdd.2) := by
                  simp only [mul_assoc] }
  let intHom : Multiplicative ℤ →* G :=
    { toFun := fun z => gc ^ z.toAdd
      map_one' := by simp
      map_mul' := by intro x y; simp [zpow_add] }
  let L : ConstructionTargets.GenericTargetNaturalSourceReconstruction.FP →* G :=
    Monoid.Coprod.lift pairHom intHom
  let F : apm_t01a04_piOne →* G := L.comp Φ.toMonoidHom
  have hFa : F apm_t01A04_loopA = ga := by simp [F, L, pairHom, hA]
  have hFb : F apm_t01A04_loopB = gb := by simp [F, L, pairHom, hB]
  have hFc : F apm_t01A04_loopC = gc := by simp [F, L, intHom, hC]
  refine ⟨F, ⟨hFa, hFb, hFc⟩, ?_⟩
  intro F' hF'
  rcases hF' with ⟨hF'a, hF'b, hF'c⟩
  apply MonoidHom.eq_of_eqOn_dense hgen
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact hF'a.trans hFa.symm
  · exact hF'b.trans hFb.symm
  · exact hF'c.trans hFc.symm

/-- The Seifert--van Kampen presentation on the three fixed geometric loops. -/
theorem apm_t01A04_canonical_loops_presentation :
    apm_t01A04_loopA * apm_t01A04_loopB =
        apm_t01A04_loopB * apm_t01A04_loopA ∧
    Subgroup.closure
        {apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} = ⊤ ∧
    (∀ (G : Type) [Group G] (ga gb gc : G), ga * gb = gb * ga →
      ∃! F : apm_t01a04_piOne →* G,
        F apm_t01A04_loopA = ga ∧ F apm_t01A04_loopB = gb ∧
          F apm_t01A04_loopC = gc) := by
  obtain ⟨Φ, hA, hB, hC⟩ := apm_t01A04_canonical_loops_presentation_aux_images
  exact apm_t01A04_canonical_loops_presentation_aux_algebra Φ hA hB hC

/-- The two parity characters obtained from the universal property of the
canonical presentation.  The presentation conclusion is an explicit input,
so this leaf is independent of its proof. -/
theorem apm_t01A04_canonical_parity_characters
    (huniv : ∀ (G : Type) [Group G] (ga gb gc : G), ga * gb = gb * ga →
      ∃! F : apm_t01a04_piOne →* G,
        F apm_t01A04_loopA = ga ∧ F apm_t01A04_loopB = gb ∧
          F apm_t01A04_loopC = gc) :
    ∃ (phic phia : apm_t01a04_piOne →* apm_t01a04_Parity),
      phic apm_t01A04_loopA = Multiplicative.ofAdd 0 ∧
      phic apm_t01A04_loopB = Multiplicative.ofAdd 0 ∧
      phic apm_t01A04_loopC = Multiplicative.ofAdd 1 ∧
      phia apm_t01A04_loopA = Multiplicative.ofAdd 1 ∧
      phia apm_t01A04_loopB = Multiplicative.ofAdd 0 ∧
      phia apm_t01A04_loopC = Multiplicative.ofAdd 0 ∧
      Function.Surjective phic ∧ Function.Surjective phia ∧
      phic.ker.index = 2 ∧ phia.ker.index = 2 ∧ phic.ker ≠ phia.ker := by
  obtain ⟨phic, hphic, -⟩ := huniv apm_t01a04_Parity
    (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 1) (by simp)
  obtain ⟨phia, hphia, -⟩ := huniv apm_t01a04_Parity
    (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0) (by simp)
  rcases hphic with ⟨hca, hcb, hcc⟩
  rcases hphia with ⟨haa, hab, hac⟩
  have hsc : Function.Surjective phic := by
    intro y
    change ZMod 2 at y
    fin_cases y
    · refine ⟨(1 : apm_t01a04_piOne), ?_⟩
      exact phic.map_one
    · exact ⟨apm_t01A04_loopC, hcc⟩
  have hsa : Function.Surjective phia := by
    intro y
    change ZMod 2 at y
    fin_cases y
    · refine ⟨(1 : apm_t01a04_piOne), ?_⟩
      exact phia.map_one
    · exact ⟨apm_t01A04_loopA, haa⟩
  have hic : phic.ker.index = 2 := by
    rw [Subgroup.index_ker]
    rw [MonoidHom.range_eq_top.mpr hsc]
    simp
  have hia : phia.ker.index = 2 := by
    rw [Subgroup.index_ker]
    rw [MonoidHom.range_eq_top.mpr hsa]
    simp
  have hne : phic.ker ≠ phia.ker := by
    intro heq
    have ha_mem_c : apm_t01A04_loopA ∈ phic.ker := by
      simp [MonoidHom.mem_ker, hca]
    have ha_mem_a : apm_t01A04_loopA ∈ phia.ker := heq ▸ ha_mem_c
    have : (1 : ZMod 2) = 0 := by
      simpa [MonoidHom.mem_ker, haa] using ha_mem_a
    norm_num at this
  exact ⟨phic, phia, hca, hcb, hcc, haa, hab, hac, hsc, hsa, hic, hia, hne⟩

/-- The monodromy calculation for the circle-doubled cover.  Its covering
hypothesis is explicit, so this leaf can be proved before the local covering
construction lands.  The presentation hypotheses identify the supplied
character uniquely from its values on the three generators. -/
lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_range_iff
    (hcov : IsCoveringMap apm_t01a04_circleCoverMap)
    (g : apm_t01a04_piOne) :
    g ∈ MonoidHom.range
        (apm_t01a04_circleCoverMap_base ▸
          FundamentalGroup.map apm_t01a04_circleCoverMap
            apm_t01a04_circleCoverBase) ↔
      hcov.monodromy (FundamentalGroup.toPath g)
          ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ =
        ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ := by
  constructor
  · rintro ⟨a, rfl⟩
    exact hcov.monodromy_map (FundamentalGroup.toPath a)
  · intro hg
    obtain ⟨γ⟩ := g
    let lift := hcov.liftPath γ apm_t01a04_circleCoverBase (by simp)
    have hend : lift 1 = apm_t01a04_circleCoverBase := by
      simpa [IsCoveringMap.monodromy, lift] using congrArg Subtype.val hg
    let δ : Path apm_t01a04_circleCoverBase apm_t01a04_circleCoverBase :=
      ⟨lift, hcov.liftPath_zero _ _ _, hend⟩
    refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
    change (Path.Homotopic.Quotient.mk δ).map apm_t01a04_circleCoverMap =
      Path.Homotopic.Quotient.mk γ
    rw [← Path.Homotopic.Quotient.mk_map]
    congr 1
    ext t
    exact congrFun (hcov.liftPath_lifts γ apm_t01a04_circleCoverBase (by simp)) t

/-- The base fiber of the circle-doubled cover has two points, so monodromy
on it is a parity character. -/
lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_fiber_cases
    (x : apm_t01a04_circleCoverMap ⁻¹' {apm_t01a04_basepoint}) :
    ∃ i : Fin 2, x.1 = Quotient.mk _ (.inl (i, ((1 : Circle), (1 : Circle)))) := by
  rcases x with ⟨x, hx⟩
  refine Quotient.inductionOn x ?_ hx
  rintro (q | z) hx
  · have hq := congrArg
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torusRetraction hx
    change q.2 = ((1 : Circle), (1 : Circle)) at hq
    exact ⟨q.1, congrArg (fun u => Quotient.mk _ (Sum.inl (q.1, u)))
      (Prod.ext (congrArg Prod.fst hq) (congrArg Prod.snd hq))⟩
  · have hz := congrArg
      apm_t01A04_circleCoverMap_evenlyCovered_away_aux_circleRetraction hx
    change z ^ 2 = 1 at hz
    rcases sq_eq_one_iff.mp (congrArg Subtype.val hz) with hz | hz
    · refine ⟨0, ?_⟩
      rw [apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_glue]
      exact congrArg (fun w : Circle => Quotient.mk _ (Sum.inr w)) (Subtype.ext hz)
    · refine ⟨1, ?_⟩
      rw [apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_glue]
      apply congrArg (fun w : Circle => Quotient.mk _ (Sum.inr w))
      apply Subtype.ext
      simpa [Circle.exp, Complex.exp_mul_I] using hz

noncomputable def apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour :
    Sum (Fin 2 × apm_t01a04_Torus) Circle → Fin 2
  := by
    classical
    exact fun
      | .inl q => q.1
      | .inr z => if z = 1 then 0 else 1

lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour_eq
    {a b : Sum (Fin 2 × apm_t01a04_Torus) Circle}
    (h : Relation.EqvGen apm_t01a04_circleCoverRel a b) :
    apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour a =
      apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour b := by
  induction h with
  | rel _ _ h =>
      cases h with
      | glue i =>
        classical
        fin_cases i
        · simp [apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour]
        · simp [apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour]
          intro h
          have hh := congrArg Subtype.val h
          norm_num [apm_t01a04_sheetPoint, Circle.exp, Complex.exp_mul_I] at hh
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character
    (hcov : IsCoveringMap apm_t01a04_circleCoverMap) :
    ∃ ψ : apm_t01a04_piOne →* apm_t01a04_Parity, ∀ g : apm_t01a04_piOne,
      ψ g = 1 ↔ hcov.monodromy (FundamentalGroup.toPath g)
          ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ = ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ := by
  classical
  let b : apm_t01a04_circleCoverMap ⁻¹' {apm_t01a04_basepoint} :=
    ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩
  let o : apm_t01a04_circleCoverMap ⁻¹' {apm_t01a04_basepoint} :=
    ⟨Quotient.mk _ (.inl (1, ((1 : Circle), (1 : Circle)))),
      apm_t01A04_circleCoverMap_evenlyCovered_basepoint_aux_mem_fiber 1⟩
  have hbo : b ≠ o := by
    intro h
    have he := Quotient.exact (congrArg Subtype.val h)
    have hc :=
      apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour_eq he
    norm_num [b, o, apm_t01a04_circleCoverBase,
      apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_colour] at hc
  have hcases (x : apm_t01a04_circleCoverMap ⁻¹' {apm_t01a04_basepoint}) :
      x = b ∨ x = o := by
    obtain ⟨i, hi⟩ :=
      apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character_aux_fiber_cases x
    fin_cases i
    · left; apply Subtype.ext; simpa [b, apm_t01a04_circleCoverBase] using hi
    · right; apply Subtype.ext; simpa [o] using hi
  have hmul (g k : apm_t01a04_piOne) :
      hcov.monodromy (FundamentalGroup.toPath (g * k)) b = b ↔
        (hcov.monodromy (FundamentalGroup.toPath g) b = b ↔
          hcov.monodromy (FundamentalGroup.toPath k) b = b) := by
    have hinj := (hcov.monodromy_bijective (FundamentalGroup.toPath g)).1
    have ht : hcov.monodromy (FundamentalGroup.toPath (g * k)) b =
        hcov.monodromy (FundamentalGroup.toPath g)
          (hcov.monodromy (FundamentalGroup.toPath k) b) := by
      change hcov.monodromy ((FundamentalGroup.toPath k).trans
        (FundamentalGroup.toPath g)) b = _
      exact hcov.monodromy_trans_apply _ _ _
    rcases hcases (hcov.monodromy (FundamentalGroup.toPath g) b) with hg | hg <;>
      rcases hcases (hcov.monodromy (FundamentalGroup.toPath k) b) with hk | hk
    · simp [ht, hg, hk]
    · have hgo : hcov.monodromy (FundamentalGroup.toPath g) o ≠ b := by
        intro h
        apply hbo
        exact hinj (hg.trans h.symm)
      simp [ht, hg, hk, hgo, hbo.symm]
    · simp [ht, hg, hk, hbo.symm]
    · have hogo : hcov.monodromy (FundamentalGroup.toPath g) o = b := by
        rcases hcases (hcov.monodromy (FundamentalGroup.toPath g) o) with h | h
        · exact h
        · exfalso
          apply hbo
          exact hinj (hg.trans h.symm)
      simp [ht, hg, hk, hogo, hbo]
  let ψ : apm_t01a04_piOne → apm_t01a04_Parity := fun g =>
    if hcov.monodromy (FundamentalGroup.toPath g) b = b then 1
    else Multiplicative.ofAdd 1
  have hψmul (g k : apm_t01a04_piOne) : ψ (g * k) = ψ g * ψ k := by
    by_cases hg : hcov.monodromy (FundamentalGroup.toPath g) b = b <;>
      by_cases hk : hcov.monodromy (FundamentalGroup.toPath k) b = b <;>
      simp [ψ, hg, hk, hmul] <;> decide
  refine ⟨{ toFun := ψ, map_one' := by
              have hone : hcov.monodromy (FundamentalGroup.toPath (1 : apm_t01a04_piOne)) b = b := by
                change hcov.monodromy (.refl apm_t01a04_basepoint) b = b
                exact congrFun hcov.monodromy_refl b
              simp [ψ, hone]
            map_mul' := hψmul }, ?_⟩
  intro g
  simp [ψ, b]

def apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_lifts_pathA :
    Path apm_t01a04_circleCoverBase apm_t01a04_circleCoverBase :=
  (ConstructionTargets.CircleUniversalCover.integerLoop 1).map
    (show Continuous (fun z : Circle =>
        Quotient.mk _ (Sum.inl ((0 : Fin 2), (z, (1 : Circle))))) from
      continuous_coinduced_rng.comp
        (continuous_inl.comp
          (continuous_const.prodMk (continuous_id.prodMk continuous_const))))

def apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_lifts_pathB :
    Path apm_t01a04_circleCoverBase apm_t01a04_circleCoverBase :=
  (ConstructionTargets.CircleUniversalCover.integerLoop 1).map
    (show Continuous (fun z : Circle =>
        Quotient.mk _ (Sum.inl ((0 : Fin 2), ((1 : Circle), z)))) from
      continuous_coinduced_rng.comp
        (continuous_inl.comp
          (continuous_const.prodMk (continuous_const.prodMk continuous_id))))

lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_lifts_exp_ne :
    Circle.exp Real.pi ≠ (1 : Circle) := Circle.exp_pi_ne_one

def apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_lifts_pathC :
    Path apm_t01a04_circleCoverBase
      (Quotient.mk _ (Sum.inr (Circle.exp Real.pi))) where
  toFun t := Quotient.mk _ (.inr (Circle.exp (Real.pi * (t : ℝ))))
  continuous_toFun := continuous_coinduced_rng.comp
    (continuous_inr.comp
      (ConstructionTargets.CircleUniversalCover.circleCover_isCoveringMap.continuous.comp
        (continuous_const.mul continuous_subtype_val)))
  source' := by
    simp only [Set.Icc.coe_zero, mul_zero, Circle.exp_zero]
    have h := Quotient.sound (s := Relation.EqvGen.setoid apm_t01a04_circleCoverRel)
      (Relation.EqvGen.rel _ _ (apm_t01a04_circleCoverRel.glue 0))
    simp only [apm_t01a04_sheetPoint_zero] at h
    exact h.symm
  target' := by simp

/-- Explicit lifts: `loopA`, `loopB` lift to closed loops in torus sheet `0`;
`loopC` lifts through squaring to the half-turn from `1` to `-1`, i.e. from
sheet point `0` to sheet point `1`, so it moves the base point. -/
lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_lifts
    (hcov : IsCoveringMap apm_t01a04_circleCoverMap) :
    hcov.monodromy (FundamentalGroup.toPath apm_t01A04_loopA)
          ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ = ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ ∧
    hcov.monodromy (FundamentalGroup.toPath apm_t01A04_loopB)
          ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ = ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ ∧
    hcov.monodromy (FundamentalGroup.toPath apm_t01A04_loopC)
          ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ ≠ ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ := by
  sorry

lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_monodromy_iff
    (phic : apm_t01a04_piOne →* apm_t01a04_Parity)
    (hgen : Subgroup.closure
      {apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} = ⊤)
    (hca : phic apm_t01A04_loopA = Multiplicative.ofAdd 0)
    (hcb : phic apm_t01A04_loopB = Multiplicative.ofAdd 0)
    (hcc : phic apm_t01A04_loopC = Multiplicative.ofAdd 1)
    (hcov : IsCoveringMap apm_t01a04_circleCoverMap)
    (g : apm_t01a04_piOne) :
    hcov.monodromy (FundamentalGroup.toPath g)
          ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ = ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ ↔ phic g = 1 := by
  obtain ⟨ψ, hψ⟩ :=
    apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character hcov
  obtain ⟨hA, hB, hC⟩ :=
    apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_lifts hcov
  have hpar : ∀ x : apm_t01a04_Parity, x ≠ 1 → x = Multiplicative.ofAdd 1 := by
    decide
  have hψ1 : ψ = phic := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hca]; exact (hψ _).2 hA
    · rw [hcb]; exact (hψ _).2 hB
    · rw [hcc]; exact hpar _ (fun h ↦ hC ((hψ _).1 h))
  subst hψ1
  exact (hψ g).symm

theorem apm_t01A04_circleCoverMap_range_eq_parity_kernel
    (phic : apm_t01a04_piOne →* apm_t01a04_Parity)
    (hgen : Subgroup.closure
      {apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} = ⊤)
    (hca : phic apm_t01A04_loopA = Multiplicative.ofAdd 0)
    (hcb : phic apm_t01A04_loopB = Multiplicative.ofAdd 0)
    (hcc : phic apm_t01A04_loopC = Multiplicative.ofAdd 1)
    (hcov : IsCoveringMap apm_t01a04_circleCoverMap) :
    MonoidHom.range
      (apm_t01a04_circleCoverMap_base ▸
        FundamentalGroup.map apm_t01a04_circleCoverMap
          apm_t01a04_circleCoverBase) = phic.ker := by
  ext g
  rw [apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_range_iff hcov]
  rw [apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_monodromy_iff
    phic hgen hca hcb hcc hcov]
  exact MonoidHom.mem_ker

lemma apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_ext
    {G : Type*} [Group G]
    (f g : apm_t01a04_piOne →* G)
    (hgen : Subgroup.closure
      {apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} = ⊤)
    (ha : f apm_t01A04_loopA = g apm_t01A04_loopA)
    (hb : f apm_t01A04_loopB = g apm_t01A04_loopB)
    (hc : f apm_t01A04_loopC = g apm_t01A04_loopC) :
    f = g := by
  apply MonoidHom.eq_of_eqOn_dense hgen
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

/-- Range of the induced map = stabilizer of the base point under monodromy.
Copy `apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_range_iff`; note
`apm_t01a04_torusCoverMap_base` is proved by `simp`, not `rfl`, so the `▸` cast
must be eliminated explicitly (the circle version's `rfl` steps fail here). -/
lemma apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_range_iff_aux
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : C(E, X)) (e : E) (x : X) (p : f e = x)
    (hcov : IsCoveringMap f) (γ : FundamentalGroup X x) :
    γ ∈ MonoidHom.range (p ▸ FundamentalGroup.map f e) ↔
      hcov.monodromy γ (⟨e, p⟩ : f ⁻¹' {x}) = (⟨e, p⟩ : f ⁻¹' {x}) := by
  subst x
  constructor
  · rintro ⟨a, rfl⟩
    exact hcov.monodromy_map (FundamentalGroup.toPath a)
  · intro hγ
    obtain ⟨γ⟩ := γ
    let lift := hcov.liftPath γ e (by simp)
    have hend : lift 1 = e := by
      simpa [IsCoveringMap.monodromy, lift] using congrArg Subtype.val hγ
    let δ : Path e e := ⟨lift, hcov.liftPath_zero _ _ _, hend⟩
    refine ⟨Path.Homotopic.Quotient.mk δ, ?_⟩
    change (Path.Homotopic.Quotient.mk δ).map f = Path.Homotopic.Quotient.mk γ
    rw [← Path.Homotopic.Quotient.mk_map]
    congr 1
    ext t
    exact congrFun (hcov.liftPath_lifts γ e (by simp)) t

theorem apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_range_iff
    (hcov : IsCoveringMap apm_t01a04_torusCoverMap) (γ : apm_t01a04_piOne) :
    γ ∈ MonoidHom.range
      (apm_t01a04_torusCoverMap_base ▸
        FundamentalGroup.map apm_t01a04_torusCoverMap
          apm_t01a04_torusCoverBase) ↔
      hcov.monodromy γ
        (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) = (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) := by
  exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_range_iff_aux
    apm_t01a04_torusCoverMap apm_t01a04_torusCoverBase
      apm_t01a04_basepoint apm_t01a04_torusCoverMap_base hcov γ

/-- The base fiber has two points, so monodromy is a parity character: it is
trivial exactly on loops whose lift from the base point closes up. -/
lemma apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_sheet_one :
    (apm_t01a04_sheetPoint 1 : ℂ) = -1 := by
  apply Complex.ext <;>
    norm_num [apm_t01a04_sheetPoint, Circle.exp, Complex.exp_mul_I]

def apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_rightCoord :
    Sum apm_t01a04_Torus Circle → Circle
  | .inl _ => 1
  | .inr z => z

lemma apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_rightCoord_eq
    {a b : Sum apm_t01a04_Torus Circle}
    (h : Relation.EqvGen apm_t01a04_wedgeRel a b) :
    apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_rightCoord a =
      apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_rightCoord b := by
  induction h with
  | rel _ _ h => cases h; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_leftCoord :
    Sum apm_t01a04_Torus Circle → apm_t01a04_Torus
  | .inl q => q
  | .inr _ => (1, 1)

lemma apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_leftCoord_eq
    {a b : Sum apm_t01a04_Torus Circle}
    (h : Relation.EqvGen apm_t01a04_wedgeRel a b) :
    apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_leftCoord a =
      apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_leftCoord b := by
  induction h with
  | rel _ _ h => cases h; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label :
    Sum apm_t01a04_Torus (Fin 2 × Circle) → Fin 2
  | .inl q => if (q.1 : ℂ) = 1 then 0 else 1
  | .inr q => q.1

lemma apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label_eq
    {a b : Sum apm_t01a04_Torus (Fin 2 × Circle)}
    (h : Relation.EqvGen apm_t01a04_torusCoverRel a b) :
    apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label a =
      apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label b := by
  induction h with
  | rel _ _ h =>
      cases h with
      | glue i =>
        fin_cases i
        · simp [apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label]
        · simp only [apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label]
          split
          · rename_i h
            change (apm_t01a04_sheetPoint 1 : ℂ) = 1 at h
            rw [apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_sheet_one] at h
            norm_num at h
          · rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_fiber_cases
    (x : apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) :
    x = ⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ ∨
      x = ⟨Quotient.mk _ (.inl (apm_t01a04_sheetPoint 1, (1 : Circle))), by
        change Quotient.mk _ (.inl ((apm_t01a04_sheetPoint 1 ^ 2), (1 : Circle))) =
          apm_t01a04_basepoint
        rw [apm_t01a04_sheetPoint_sq]
        rfl⟩ := by
  rcases x with ⟨x, hx⟩
  suffices x = apm_t01a04_torusCoverBase ∨
      x = Quotient.mk _ (.inl (apm_t01a04_sheetPoint 1, (1 : Circle))) by
    rcases this with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  revert hx
  refine Quotient.inductionOn x ?_
  rintro (q | q) hx
  · have heq : (q.1 ^ 2, q.2) = ((1 : Circle), (1 : Circle)) := by
      change Quotient.mk _ (Sum.inl (q.1 ^ 2, q.2)) =
        Quotient.mk _ (Sum.inl ((1 : Circle), (1 : Circle))) at hx
      exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_leftCoord_eq
        (Quotient.exact hx)
    have hsq : q.1 ^ 2 = 1 := congrArg Prod.fst heq
    have hsecond : q.2 = 1 := congrArg Prod.snd heq
    have hsq' : (q.1 : ℂ) ^ 2 = 1 := congrArg Subtype.val hsq
    rcases (sq_eq_one_iff.mp hsq') with h | h
    · left
      have h' : q.1 = (1 : Circle) := Subtype.ext h
      have hq : q = ((1 : Circle), (1 : Circle)) := Prod.ext h' hsecond
      simpa [apm_t01a04_torusCoverBase, hq]
    · right
      have h' : q.1 = apm_t01a04_sheetPoint 1 := by
        apply Subtype.ext
        rw [apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_sheet_one]
        exact h
      have hq : q = (apm_t01a04_sheetPoint 1, (1 : Circle)) := Prod.ext h' hsecond
      simpa [hq]
  · have heq : q.2 = (1 : Circle) := by
      change Quotient.mk _ (Sum.inr q.2) = Quotient.mk _ (Sum.inl (1, 1)) at hx
      exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_rightCoord_eq
        (Quotient.exact hx)
    have hi : q.1 = 0 ∨ q.1 = 1 := by
      omega
    rcases hi with hi | hi
    · left
      have hq : q = (0, (1 : Circle)) := Prod.ext hi heq
      rw [hq]
      simpa [apm_t01a04_torusCoverBase] using
        (Quotient.sound (Relation.EqvGen.rel _ _
          (apm_t01a04_torusCoverRel.glue 0))).symm
    · right
      have hq : q = (1, (1 : Circle)) := Prod.ext hi heq
      rw [hq]
      exact (Quotient.sound (Relation.EqvGen.rel _ _
        (apm_t01a04_torusCoverRel.glue 1))).symm

theorem apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character
    (hcov : IsCoveringMap apm_t01a04_torusCoverMap) :
    ∃ ψ : apm_t01a04_piOne →* apm_t01a04_Parity, ∀ γ : apm_t01a04_piOne,
      ψ γ = 1 ↔
        hcov.monodromy γ
          (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) = (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) := by
  classical
  let b : apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint} :=
    ⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩
  let o : apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint} :=
    ⟨Quotient.mk _ (.inl (apm_t01a04_sheetPoint 1, (1 : Circle))), by
      change Quotient.mk _ (.inl ((apm_t01a04_sheetPoint 1 ^ 2), (1 : Circle))) =
        apm_t01a04_basepoint
      rw [apm_t01a04_sheetPoint_sq]
      rfl⟩
  have hbo : b ≠ o := by
    intro h
    have hh := Quotient.exact (congrArg Subtype.val h)
    have hl := apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label_eq hh
    simp [b, o, apm_t01a04_torusCoverBase,
      apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label] at hl
    norm_num at hl
  have hcases (x : apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) :
      x = b ∨ x = o := by
    simpa [b, o] using
      apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_fiber_cases x
  have hmul (g k : apm_t01a04_piOne) :
      hcov.monodromy (g * k) b = b ↔
        (hcov.monodromy g b = b ↔ hcov.monodromy k b = b) := by
    have hinj := (hcov.monodromy_bijective g).1
    have ht : hcov.monodromy (g * k) b =
        hcov.monodromy g (hcov.monodromy k b) := by
      exact hcov.monodromy_trans_apply k g b
    rcases hcases (hcov.monodromy g b) with hg | hg <;>
      rcases hcases (hcov.monodromy k b) with hk | hk
    · simp [ht, hg, hk]
    · have hgo : hcov.monodromy g o ≠ b := by
        intro h
        apply hbo
        exact hinj (hg.trans h.symm)
      simp [ht, hg, hk, hgo, hbo, hbo.symm]
    · simp [ht, hg, hk, hbo]
    · have hogo : hcov.monodromy g o = b := by
        rcases hcases (hcov.monodromy g o) with h | h
        · exact h
        · exfalso
          apply hbo
          exact hinj (hg.trans h.symm)
      simp [ht, hg, hk, hogo, hbo]
  let ψ : apm_t01a04_piOne → apm_t01a04_Parity := fun g =>
    if hcov.monodromy g b = b then 1 else Multiplicative.ofAdd 1
  have hψmul (g k : apm_t01a04_piOne) : ψ (g * k) = ψ g * ψ k := by
    by_cases hg : hcov.monodromy g b = b <;>
      by_cases hk : hcov.monodromy k b = b <;>
      simp [ψ, hg, hk, hmul] <;> decide
  have hone : hcov.monodromy (1 : apm_t01a04_piOne) b = b := by
    change hcov.monodromy (.refl apm_t01a04_basepoint) b = b
    rw [hcov.monodromy_refl]
    rfl
  refine ⟨{
    toFun := ψ
    map_one' := by simp [ψ, hone]
    map_mul' := hψmul }, ?_⟩
  intro g
  simp [ψ, b]

def apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathA :
    Path apm_t01a04_torusCoverBase
      (Quotient.mk _ (.inl (Circle.exp Real.pi, (1 : Circle)))) where
  toFun t := Quotient.mk _ (.inl (Circle.exp (Real.pi * (t : ℝ)), (1 : Circle)))
  continuous_toFun := continuous_coinduced_rng.comp
    (continuous_inl.comp ((Circle.exp.continuous.comp
      (continuous_const.mul continuous_subtype_val)).prodMk continuous_const))
  source' := by simp [apm_t01a04_torusCoverBase]
  target' := by simp

def apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathB :
    Path apm_t01a04_torusCoverBase apm_t01a04_torusCoverBase :=
  (ConstructionTargets.CircleUniversalCover.integerLoop 1).map
    (show Continuous (fun z : Circle =>
        Quotient.mk _ (Sum.inl ((1 : Circle), z))) from
      continuous_coinduced_rng.comp
        (continuous_inl.comp (continuous_const.prodMk continuous_id)))

def apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathC :
    Path apm_t01a04_torusCoverBase apm_t01a04_torusCoverBase :=
  (((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
    (show Continuous (fun z : Circle =>
        Quotient.mk _ (Sum.inr ((0 : Fin 2), z))) from
      continuous_coinduced_rng.comp
        (continuous_inr.comp (continuous_const.prodMk continuous_id)))).cast
    (by
      have h : (Quotient.mk _ (.inl ((1 : Circle), (1 : Circle))) :
          apm_t01a04_TorusCover) = Quotient.mk _ (.inr ((0 : Fin 2), (1 : Circle))) :=
        Quotient.sound (by simpa using
          Relation.EqvGen.rel _ _ (apm_t01a04_torusCoverRel.glue 0))
      exact h)
    (by
      have h : (Quotient.mk _ (.inl ((1 : Circle), (1 : Circle))) :
          apm_t01a04_TorusCover) = Quotient.mk _ (.inr ((0 : Fin 2), (1 : Circle))) :=
        Quotient.sound (by simpa using
          Relation.EqvGen.rel _ _ (apm_t01a04_torusCoverRel.glue 0))
      exact h))

/-- Explicit lifts from the base point: `loopA` lifts to the half-turn
`(1,1) ↦ (-1,1)` in the torus summand (the cover squares the first
coordinate), so it moves the base point; `loopB` lifts to the closed second
coordinate turn and `loopC` to the closed turn of circle `0`.  The three
explicit lifts are banked above (`_pathA/B/C`); conclude with the
lift-uniqueness API (`IsCoveringMap.liftPath`, `eq_liftPath_iff`), and separate
`⟦inl (-1, 1)⟧` from the base point with a quotient-respecting invariant. -/
theorem apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts
    (hcov : IsCoveringMap apm_t01a04_torusCoverMap) :
    hcov.monodromy apm_t01A04_loopA (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) ≠ (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) ∧
    hcov.monodromy apm_t01A04_loopB (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) = (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) ∧
    hcov.monodromy apm_t01A04_loopC (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) = (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) := by
  let γA : Path apm_t01a04_basepoint apm_t01a04_basepoint :=
    (ConstructionTargets.CircleUniversalCover.integerLoop 1).map
      (show Continuous (fun z : Circle =>
          Quotient.mk _ (Sum.inl (z, (1 : Circle)))) from
        continuous_coinduced_rng.comp
          (continuous_inl.comp (continuous_id.prodMk continuous_const)))
  let γB : Path apm_t01a04_basepoint apm_t01a04_basepoint :=
    (ConstructionTargets.CircleUniversalCover.integerLoop 1).map
      (show Continuous (fun z : Circle =>
          Quotient.mk _ (Sum.inl ((1 : Circle), z))) from
        continuous_coinduced_rng.comp
          (continuous_inl.comp (continuous_const.prodMk continuous_id)))
  let γC : Path apm_t01a04_basepoint apm_t01a04_basepoint :=
    ((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
      (show Continuous (fun z : Circle => Quotient.mk _ (Sum.inr z)) from
        continuous_coinduced_rng.comp continuous_inr)).cast
      (Quotient.sound (Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base))
      (Quotient.sound (Relation.EqvGen.rel _ _ apm_t01a04_wedgeRel.base))
  have hliftA : apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathA =
      hcov.liftPath γA apm_t01a04_torusCoverBase
        (γA.source.trans apm_t01a04_torusCoverMap_base.symm) := by
    apply (hcov.eq_liftPath_iff' _).2
    constructor
    · funext t
      simp [γA, apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathA,
        apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw,
        ConstructionTargets.CircleUniversalCover.integerLoop,
        ConstructionTargets.CircleUniversalCover.circleCover, pow_two,
        ← Circle.exp_add]
      ring
      rfl
    · exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathA.source
  have hliftB : apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathB =
      hcov.liftPath γB apm_t01a04_torusCoverBase
        (γB.source.trans apm_t01a04_torusCoverMap_base.symm) := by
    apply (hcov.eq_liftPath_iff' _).2
    constructor
    · funext t
      simp [γB, apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathB,
        apm_t01a04_torusCoverMap, apm_t01a04_torusCoverRaw]
      dsimp [Quotient.map', Quot.map, Path.map]
      apply Quotient.sound
      simpa [apm_t01a04_torusCoverRaw] using
        (Relation.EqvGen.refl (r := apm_t01a04_wedgeRel)
          (Sum.inl ((1 : Circle),
            ConstructionTargets.CircleUniversalCover.integerLoop 1 t)))
    · exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathB.source
  have hliftC : apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathC =
      hcov.liftPath γC apm_t01a04_torusCoverBase
        (γC.source.trans apm_t01a04_torusCoverMap_base.symm) := by
    apply (hcov.eq_liftPath_iff' _).2
    constructor
    · funext t
      change Quotient.mk _ (Sum.inr
          (ConstructionTargets.CircleUniversalCover.integerLoop 1 t) :
            Sum apm_t01a04_Torus Circle) =
        Quotient.mk _ (Sum.inr
          (ConstructionTargets.CircleUniversalCover.integerLoop 1 t) :
            Sum apm_t01a04_Torus Circle)
      rfl
    · exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathC.source
  have hloopA : apm_t01A04_loopA = Path.Homotopic.Quotient.mk γA := rfl
  have hloopB : apm_t01A04_loopB = Path.Homotopic.Quotient.mk γB := rfl
  have hloopC : apm_t01A04_loopC = Path.Homotopic.Quotient.mk γC := rfl
  rw [hloopA, hloopB, hloopC]
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have heq' := congrArg Subtype.val heq
    change hcov.liftPath γA apm_t01a04_torusCoverBase _ 1 =
      apm_t01a04_torusCoverBase at heq'
    rw [← hliftA] at heq'
    have he : (Quotient.mk _
        (.inl (Circle.exp Real.pi, (1 : Circle))) : apm_t01a04_TorusCover) =
        apm_t01a04_torusCoverBase :=
      apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathA.target.symm.trans
        heq'
    have hh := Quotient.exact he
    have hl :=
      apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character_label_eq hh
    change (if (Circle.exp Real.pi : ℂ) = 1 then (0 : Fin 2) else 1) =
      (if ((1 : Circle) : ℂ) = 1 then (0 : Fin 2) else 1) at hl
    norm_num [Circle.exp, Complex.exp_mul_I] at hl
  · apply Subtype.ext
    change hcov.liftPath γB apm_t01a04_torusCoverBase _ 1 =
      apm_t01a04_torusCoverBase
    rw [← hliftB]
    exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathB.target
  · apply Subtype.ext
    change hcov.liftPath γC apm_t01a04_torusCoverBase _ 1 =
      apm_t01a04_torusCoverBase
    rw [← hliftC]
    exact apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts_pathC.target

/-- The monodromy calculation for the torus-doubled cover.  As above, the
covering fact is an input rather than a dependency on another admitted leaf. -/
theorem apm_t01A04_torusCoverMap_range_eq_parity_kernel
    (phia : apm_t01a04_piOne →* apm_t01a04_Parity)
    (hgen : Subgroup.closure
      {apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC} = ⊤)
    (haa : phia apm_t01A04_loopA = Multiplicative.ofAdd 1)
    (hab : phia apm_t01A04_loopB = Multiplicative.ofAdd 0)
    (hac : phia apm_t01A04_loopC = Multiplicative.ofAdd 0)
    (hcov : IsCoveringMap apm_t01a04_torusCoverMap) :
    MonoidHom.range
      (apm_t01a04_torusCoverMap_base ▸
        FundamentalGroup.map apm_t01a04_torusCoverMap
          apm_t01a04_torusCoverBase) = phia.ker := by
  obtain ⟨ψ, hψ⟩ :=
    apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character hcov
  obtain ⟨hA, hB, hC⟩ :=
    apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_lifts hcov
  have hpar : ∀ x : apm_t01a04_Parity, x ≠ 1 → x = Multiplicative.ofAdd 1 := by
    decide
  have hψphia : ψ = phia := by
    apply apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_ext ψ phia hgen
    · rw [haa]; exact hpar _ (fun h ↦ hA ((hψ _).1 h))
    · rw [hab]; exact (hψ _).2 hB
    · rw [hac]; exact (hψ _).2 hC
  subst hψphia
  ext γ
  rw [apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_range_iff hcov,
    MonoidHom.mem_ker, hψ]

/-- Why this unblocks `apm_t01a04`: this is the Seifert--van Kampen
presentation of `T² ∨ S¹`, together with the two parity characters and the
covering-subgroup range computation for the already constructed based maps. -/
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
  rcases apm_t01A04_canonical_loops_presentation with ⟨hab, hgen, huniv⟩
  rcases apm_t01A04_canonical_parity_characters huniv with
    ⟨phic, phia, hca, hcb, hcc, haa, hab0, hac, hsc, hsa, hic, hia, hne⟩
  rcases apm_t01A04_bridge_quotient_maps_are_coverings with ⟨hcovc, hcova⟩
  refine ⟨apm_t01A04_loopA, apm_t01A04_loopB, apm_t01A04_loopC,
    phic, phia, hab, hgen, huniv, hca, hcb, hcc,
    haa, hab0, hac, hsc, hsa, hic, hia, hne, ?_, ?_⟩
  · exact apm_t01A04_circleCoverMap_range_eq_parity_kernel
      phic hgen hca hcb hcc hcovc
  · exact apm_t01A04_torusCoverMap_range_eq_parity_kernel
      phia hgen haa hab0 hac hcova

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
