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
theorem apm_t01A04_circleCoverMap_evenlyCovered_away_aux_torus
    (q : apm_t01a04_Torus) (hq : q ≠ (1, 1)) :
    IsEvenlyCovered apm_t01a04_circleCoverMap (Quotient.mk _ (Sum.inl q))
      (apm_t01a04_circleCoverMap ⁻¹' {Quotient.mk _ (Sum.inl q)}) := by
  sorry

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

/-- Basepoint case.  Plan (from the first attempt): take
`U = mk '' (inl '' {q | 0 < q.1.re ∧ 0 < q.2.re} ∪ inr '' {z | 0 < z.re})`,
open and saturated in `X`.  Its preimage is the disjoint union over `i : Fin 2`
of `mk '' (inl '' ({i} × T) ∪ inr '' Aᵢ)` with `Aᵢ` the arc about
`sheetPoint i = ±1` on which squaring is a homeomorphism onto `{z | 0 < z.re}`;
the glue `aux_glue` attaches `Aᵢ` to torus sheet `i`. -/
theorem apm_t01A04_circleCoverMap_evenlyCovered_basepoint :
    IsEvenlyCovered apm_t01a04_circleCoverMap apm_t01a04_basepoint
      (apm_t01a04_circleCoverMap ⁻¹' {apm_t01a04_basepoint}) := by
  sorry

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

/-- Torus-summand case: near `q ≠ (1,1)` the cover is `(z, w) ↦ (z², w)`
on the torus summand; the two square-root arcs in the first coordinate give the
two sheets (the glued points `(±1, 1)` lie over the excluded base point). -/
theorem apm_t01A04_torusCoverMap_evenlyCovered_away_aux_torus
    (q : apm_t01a04_Torus) (hq : q ≠ (1, 1)) :
    IsEvenlyCovered apm_t01a04_torusCoverMap (Quotient.mk _ (Sum.inl q))
      (apm_t01a04_torusCoverMap ⁻¹' {Quotient.mk _ (Sum.inl q)}) := by
  sorry

/-- Circle-summand case: near `z ≠ 1` the cover is the identity on each of the
two circle sheets `(i, ·)`, `i : Fin 2`. -/
theorem apm_t01A04_torusCoverMap_evenlyCovered_away_aux_circle
    (z : Circle) (hz : z ≠ 1) :
    IsEvenlyCovered apm_t01a04_torusCoverMap (Quotient.mk _ (Sum.inr z))
      (apm_t01a04_torusCoverMap ⁻¹' {Quotient.mk _ (Sum.inr z)}) := by
  sorry

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
  sorry

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
lemma apm_t01A04_circleCoverMap_range_eq_parity_kernel_aux_character
    (hcov : IsCoveringMap apm_t01a04_circleCoverMap) :
    ∃ ψ : apm_t01a04_piOne →* apm_t01a04_Parity, ∀ g : apm_t01a04_piOne,
      ψ g = 1 ↔ hcov.monodromy (FundamentalGroup.toPath g)
          ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ = ⟨apm_t01a04_circleCoverBase, apm_t01a04_circleCoverMap_base⟩ := by
  sorry

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
theorem apm_t01A04_torusCoverMap_range_eq_parity_kernel_aux_character
    (hcov : IsCoveringMap apm_t01a04_torusCoverMap) :
    ∃ ψ : apm_t01a04_piOne →* apm_t01a04_Parity, ∀ γ : apm_t01a04_piOne,
      ψ γ = 1 ↔
        hcov.monodromy γ
          (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) = (⟨apm_t01a04_torusCoverBase, apm_t01a04_torusCoverMap_base⟩ :
          apm_t01a04_torusCoverMap ⁻¹' {apm_t01a04_basepoint}) := by
  sorry

/-- Explicit lifts from the base point: `loopA` lifts to the half-turn
`(1,1) ↦ (-1,1)` in the torus summand (the cover squares the first
coordinate), so it moves the base point; `loopB` lifts to the closed second
coordinate turn and `loopC` to the closed turn of circle `0`. -/
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
  sorry

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
