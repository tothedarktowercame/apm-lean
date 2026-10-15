import Mathlib
import ConstructionTargets.t97A04Closure
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.IntegralOpenCoverMayerVietoris
import ConstructionTargets.TwoOpenAttachOneCell

/-! # Blueprint for APM t99A01 -/

open CategoryTheory

noncomputable section

namespace APMT99A01

abbrev Disk := Metric.closedBall (0 : ℂ) 1

def circleInDisk (z : Circle) : Disk :=
  ⟨z, by simpa [Metric.mem_closedBall, dist_zero_right] using z.property.le⟩

inductive AttachRel {r : ℕ} (degree : Fin r → ℕ) :
    Sum Circle (Fin r × Disk) → Sum Circle (Fin r × Disk) → Prop
  | boundary (i : Fin r) (z : Circle) :
      AttachRel degree (Sum.inl (z ^ degree i))
        (Sum.inr (i, circleInDisk z))

def AttachSpace {r : ℕ} (degree : Fin r → ℕ) :=
  Quotient (Relation.EqvGen.setoid (AttachRel degree))

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) :
    TopologicalSpace (AttachSpace degree) :=
  TopologicalSpace.coinduced (fun x ↦ Quotient.mk _ x) inferInstance

def degreeX : Fin 1 → ℕ := ![2]
def degreeY : Fin 2 → ℕ := ![2, 4]
def degreeZ : Fin 3 → ℕ := ![2, 4, 5]

abbrev X := AttachSpace degreeX
abbrev Y := AttachSpace degreeY
abbrev Z := AttachSpace degreeZ

def basepoint {r : ℕ} (degree : Fin r → ℕ) : AttachSpace degree :=
  Quotient.mk _ (Sum.inl (1 : Circle))

abbrev H (k : ℕ) (W : Type) [TopologicalSpace W] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of W))

/-- The cellular boundary contributed by the attaching maps. -/
def degreeMap {r : ℕ} (degree : Fin r → ℕ) : (Fin r → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ i, (degree i : ℤ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, Pi.smul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_assoc, mul_comm]

abbrev DegreeKernel {r : ℕ} (degree : Fin r → ℕ) :=
  LinearMap.ker (degreeMap degree)

abbrev DegreeCokernel {r : ℕ} (degree : Fin r → ℕ) :=
  ℤ ⧸ LinearMap.range (degreeMap degree)

end APMT99A01

def APMT99A01.circlePower (d : ℕ) : C(Circle, Circle) where
  toFun z := z ^ d
  continuous_toFun := continuous_pow d

def APMT99A01.intTimesNat (d : ℕ) : ℤ →ₗ[ℤ] ℤ where
  toFun x := (d : ℤ) * x
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp [mul_assoc, mul_comm]

/-- The gcd of all attaching degrees.  For an empty family this is `0`, so
`ZMod (degreeGCD degree)` is `ZMod 0 = ℤ`, as required for the bare circle. -/
def APMT99A01.degreeGCD {r : ℕ} (degree : Fin r → ℕ) : ℕ :=
  Finset.univ.gcd degree

/-- The formula on representatives for including the first `r` disks in an
attaching space with `r+1` disks. -/
def APMT99A01.attachCastSuccRaw {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    Sum Circle (Fin r × APMT99A01.Disk) →
      Sum Circle (Fin (r + 1) × APMT99A01.Disk)
  | Sum.inl z => Sum.inl z
  | Sum.inr (i, z) => Sum.inr (Fin.castSucc i, z)

/-- The explicit inclusion which is the identity on the base circle and sends
disk `i` to disk `Fin.castSucc i`. -/
def APMT99A01.attachCastSucc {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    APMT99A01.AttachSpace (degree ∘ Fin.castSucc) →
      APMT99A01.AttachSpace degree :=
  Quotient.lift
    (fun x => Quotient.mk _ (APMT99A01.attachCastSuccRaw degree x))
    (by
      intro a b hab
      apply Quotient.sound
      induction hab with
      | rel a b hab =>
          cases hab with
          | boundary i z =>
              exact Relation.EqvGen.rel _ _
                (APMT99A01.AttachRel.boundary (degree := degree) (Fin.castSucc i) z)
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂)

/-- The positively oriented base-circle loop, regarded as a loop in the
attaching space.  This fixes the coordinate used throughout the induction. -/
noncomputable def APMT99A01.baseCircleLoop {r : ℕ} (degree : Fin r → ℕ) :
    Path (APMT99A01.basepoint degree) (APMT99A01.basepoint degree) :=
  (ConstructionTargets.CircleUniversalCover.integerLoop 1).map
    ((continuous_coinduced_rng.comp continuous_inl) :
      Continuous (fun z : Circle =>
        Quotient.mk (Relation.EqvGen.setoid (APMT99A01.AttachRel degree))
          (Sum.inl z)))

/-- The fundamental-group class of the chosen positive base-circle loop. -/
noncomputable def APMT99A01.baseCircleClass {r : ℕ} (degree : Fin r → ℕ) :
    FundamentalGroup (APMT99A01.AttachSpace degree) (APMT99A01.basepoint degree) :=
  Path.Homotopic.Quotient.mk (APMT99A01.baseCircleLoop degree)

/-- A cyclic coordinate together with its normalization on the base circle. -/
def APMT99A01.PiOneCoordinate {r : ℕ} (degree : Fin r → ℕ) : Prop :=
  ∃ e : FundamentalGroup (APMT99A01.AttachSpace degree)
      (APMT99A01.basepoint degree) ≃*
        Multiplicative (ZMod (APMT99A01.degreeGCD degree)),
    e (APMT99A01.baseCircleClass degree) = Multiplicative.ofAdd 1

/-- The centre of the last disk in a successor attaching space. -/
def APMT99A01.lastDiskCentre {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    APMT99A01.AttachSpace degree :=
  Quotient.mk _ (Sum.inr (Fin.last r,
    (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk)))

/-- The complement of the centre of the last disk. -/
def APMT99A01.succCircleSide {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    Set (APMT99A01.AttachSpace degree) :=
  {q | q ≠ APMT99A01.lastDiskCentre degree}

/-- The open interior of the last disk. -/
def APMT99A01.succDiskSide {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    Set (APMT99A01.AttachSpace degree) :=
  {q | ∃ z : APMT99A01.Disk, ‖(z : ℂ)‖ < 1 ∧
    q = Quotient.mk _ (Sum.inr (Fin.last r, z))}

/-- **Leaf (circle fundamental group, 40--80 lines).** The empty attaching
family is just the circle.  The target is `ZMod 0`, hence additive `ℤ` written
multiplicatively. -/
def t99A01_piOne_attach_empty_aux_projection (degree : Fin 0 → ℕ) :
    APMT99A01.AttachSpace degree → Circle :=
  Quotient.lift
    (Sum.elim id (fun p : Fin 0 × APMT99A01.Disk ↦ Fin.elim0 p.1))
    (by
      intro a b hab
      induction hab with
      | rel a b hab =>
          cases hab with
          | boundary i z => exact Fin.elim0 i
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

def t99A01_piOne_attach_empty_aux_homeomorph (degree : Fin 0 → ℕ) :
    APMT99A01.AttachSpace degree ≃ₜ Circle where
  toFun := t99A01_piOne_attach_empty_aux_projection degree
  invFun := fun z ↦ Quotient.mk _ (Sum.inl z)
  left_inv q := by
    induction q using Quotient.ind with
    | _ x =>
      cases x with
      | inl z => rfl
      | inr p => exact Fin.elim0 p.1
  right_inv z := rfl
  continuous_toFun := by
    apply continuous_coinduced_dom.mpr
    apply continuous_sum_dom.mpr
    constructor
    · exact continuous_id
    · rw [continuous_iff_continuousAt]
      intro p
      exact Fin.elim0 p.1
  continuous_invFun := continuous_coinduced_rng.comp continuous_inl

noncomputable def t99A01_piOne_attach_empty_aux_piOneEquiv
    (degree : Fin 0 → ℕ) :
    FundamentalGroup (APMT99A01.AttachSpace degree) (APMT99A01.basepoint degree) ≃*
      FundamentalGroup Circle 1 := by
  let h := t99A01_piOne_attach_empty_aux_homeomorph degree
  exact
    { toFun := FundamentalGroup.map ⟨h, h.continuous⟩ _
      invFun := FundamentalGroup.mapOfEq ⟨h.symm, h.symm.continuous⟩
        (h.symm_apply_apply (APMT99A01.basepoint degree))
      left_inv := by
        intro p
        induction p using Path.Homotopic.Quotient.ind with
        | mk p =>
          rw [FundamentalGroup.map_apply]
          change (FundamentalGroup.mapOfEq _ _)
            (Path.Homotopic.Quotient.mk (p.map h.continuous)) = _
          rw [FundamentalGroup.mapOfEq_apply]
          apply Path.Homotopic.Quotient.eq.mpr
          convert Path.Homotopic.refl p using 1
          ext t
          exact h.symm_apply_apply (p t)
      right_inv := by
        intro p
        induction p using Path.Homotopic.Quotient.ind with
        | mk p =>
          change (FundamentalGroup.map _ _)
            ((FundamentalGroup.mapOfEq _ _)
              (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) = _
          rw [FundamentalGroup.mapOfEq_apply]
          rw [FundamentalGroup.map_apply]
          apply Path.Homotopic.Quotient.eq.mpr
          convert Path.Homotopic.refl p using 1
      map_mul' := map_mul _ }

lemma t99A01_piOne_attach_empty (degree : Fin 0 → ℕ) :
    APMT99A01.PiOneCoordinate degree := by
  let e₀ := (t99A01_piOne_attach_empty_aux_piOneEquiv degree).trans
    ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt
  have hgcd : APMT99A01.degreeGCD degree = 0 := by
    simp [APMT99A01.degreeGCD]
  unfold APMT99A01.PiOneCoordinate
  rw [hgcd]
  refine ⟨e₀, ?_⟩
  change ConstructionTargets.CircleUniversalCover.circleWindingHom
      ((t99A01_piOne_attach_empty_aux_piOneEquiv degree)
        (APMT99A01.baseCircleClass degree)) = Multiplicative.ofAdd 1
  dsimp [t99A01_piOne_attach_empty_aux_piOneEquiv]
  rw [FundamentalGroup.map_apply]
  change ConstructionTargets.CircleUniversalCover.circleWindingHom
      (Path.Homotopic.Quotient.mk
        ((APMT99A01.baseCircleLoop degree).map
          (t99A01_piOne_attach_empty_aux_homeomorph degree).continuous)) =
        Multiplicative.ofAdd 1
  have hloop :
      (APMT99A01.baseCircleLoop degree).map
          (t99A01_piOne_attach_empty_aux_homeomorph degree).continuous =
        ConstructionTargets.CircleUniversalCover.integerLoop 1 := by
    ext t
    rfl
  rw [hloop]
  simp [ConstructionTargets.CircleUniversalCover.circleWindingHom_mk]

/-- **Leaf (successor cover, 70--130 lines).**  The centre complement and the
open last-disk interior form the van Kampen cover.  This formulation records
exactly the four hypotheses needed by `apm_t92J05_twoOpen_attach_one_cell`. -/
lemma t99A01_piOne_attach_succ_cover_aux_centre {r : ℕ}
    (degree : Fin (r + 1) → ℕ)
    (x : Sum Circle (Fin (r + 1) × APMT99A01.Disk)) :
    Relation.EqvGen (APMT99A01.AttachRel degree)
        (Sum.inr (Fin.last r,
          (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk))) x ↔
      x = Sum.inr (Fin.last r,
        (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk)) := by
  let c : APMT99A01.Disk := ⟨0, by simp [Metric.mem_closedBall]⟩
  let P := fun x : Sum Circle (Fin (r + 1) × APMT99A01.Disk) =>
    x = Sum.inr (Fin.last r, c)
  have hrel : ∀ a b, APMT99A01.AttachRel degree a b → (P a ↔ P b) := by
    intro a b h
    cases h with
    | boundary i z =>
      constructor
      · intro h; cases h
      · intro h
        have hz : APMT99A01.circleInDisk z ≠ c := by
          intro he
          have hv := congrArg (fun w : APMT99A01.Disk => (w : ℂ)) he
          change (z : ℂ) = 0 at hv
          have hn := Circle.norm_coe z
          rw [hv, norm_zero] at hn
          norm_num at hn
        have hp : (i, APMT99A01.circleInDisk z) = (Fin.last r, c) :=
          Sum.inr.inj h
        exact False.elim (hz (Prod.mk.inj hp).2)
  constructor
  · intro h
    have hinv : ∀ a b, Relation.EqvGen (APMT99A01.AttachRel degree) a b →
        (P a ↔ P b) := by
      intro a b hab
      induction hab with
      | rel a b hab => exact hrel a b hab
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (hinv _ _ h).mp rfl
  · rintro rfl
    exact Relation.EqvGen.refl _

lemma t99A01_piOne_attach_succ_cover_aux_interior {r : ℕ}
    (degree : Fin (r + 1) → ℕ)
    (x y : Sum Circle (Fin (r + 1) × APMT99A01.Disk))
    (h : Relation.EqvGen (APMT99A01.AttachRel degree) x y) :
    (∃ z : APMT99A01.Disk, ‖(z : ℂ)‖ < 1 ∧
        x = Sum.inr (Fin.last r, z)) ↔
      ∃ z : APMT99A01.Disk, ‖(z : ℂ)‖ < 1 ∧
        y = Sum.inr (Fin.last r, z) := by
  let P := fun x : Sum Circle (Fin (r + 1) × APMT99A01.Disk) =>
    ∃ z : APMT99A01.Disk, ‖(z : ℂ)‖ < 1 ∧ x = Sum.inr (Fin.last r, z)
  have hrel : ∀ a b, APMT99A01.AttachRel degree a b → (P a ↔ P b) := by
    intro a b hab
    cases hab with
    | boundary i z =>
      constructor
      · rintro ⟨w, hw, hbad⟩
        cases hbad
      · rintro ⟨w, hw, he⟩
        have hp : (i, APMT99A01.circleInDisk z) = (Fin.last r, w) :=
          Sum.inr.inj he
        have hi : i = Fin.last r := (Prod.mk.inj hp).1
        subst i
        have hw' : w = APMT99A01.circleInDisk z := (Prod.mk.inj hp).2.symm
        subst w
        simp [APMT99A01.circleInDisk, Circle.norm_coe] at hw
  induction h with
  | rel a b hab => exact hrel a b hab
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma t99A01_piOne_attach_succ_cover_aux_basic {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    IsOpen (APMT99A01.succCircleSide degree) ∧
      IsOpen (APMT99A01.succDiskSide degree) ∧
      APMT99A01.succCircleSide degree ∪ APMT99A01.succDiskSide degree = Set.univ ∧
      Set.Nonempty (APMT99A01.succCircleSide degree ∩
        APMT99A01.succDiskSide degree) := by
  let c : APMT99A01.Disk := ⟨0, by simp [Metric.mem_closedBall]⟩
  let mk : Sum Circle (Fin (r + 1) × APMT99A01.Disk) →
      APMT99A01.AttachSpace degree := Quotient.mk _
  have hCpre : mk ⁻¹' APMT99A01.succCircleSide degree =
      ({Sum.inr (Fin.last r, c)}ᶜ :
        Set (Sum Circle (Fin (r + 1) × APMT99A01.Disk))) := by
    ext x
    simp only [Set.mem_preimage, APMT99A01.succCircleSide, Set.mem_setOf_eq,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h hx
      apply h
      change Quotient.mk _ x = Quotient.mk _ (Sum.inr (Fin.last r, c))
      rw [hx]
    · intro h he
      apply h
      have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
          (Sum.inr (Fin.last r, c)) x := Quotient.exact he.symm
      exact (t99A01_piOne_attach_succ_cover_aux_centre degree x).mp hr
  have hDpre : mk ⁻¹' APMT99A01.succDiskSide degree =
      {x | ∃ z : APMT99A01.Disk, ‖(z : ℂ)‖ < 1 ∧
        x = Sum.inr (Fin.last r, z)} := by
    ext x
    simp only [Set.mem_preimage, APMT99A01.succDiskSide, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, he⟩
      have hr : Relation.EqvGen (APMT99A01.AttachRel degree) x
          (Sum.inr (Fin.last r, z)) := Quotient.exact he
      exact (t99A01_piOne_attach_succ_cover_aux_interior degree x _ hr).mpr
        ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  have hC : IsOpen (APMT99A01.succCircleSide degree) := by
    rw [isOpen_coinduced]
    change IsOpen (mk ⁻¹' APMT99A01.succCircleSide degree)
    rw [hCpre]
    exact isOpen_compl_singleton
  have hD : IsOpen (APMT99A01.succDiskSide degree) := by
    rw [isOpen_coinduced]
    change IsOpen (mk ⁻¹' APMT99A01.succDiskSide degree)
    rw [hDpre, isOpen_sum_iff]
    constructor
    · simp
    · have heq : Sum.inr ⁻¹'
          {x : Sum Circle (Fin (r + 1) × APMT99A01.Disk) |
            ∃ z : APMT99A01.Disk, ‖(z : ℂ)‖ < 1 ∧
              x = Sum.inr (Fin.last r, z)} =
          {p : Fin (r + 1) × APMT99A01.Disk |
            p.1 = Fin.last r ∧ ‖(p.2 : ℂ)‖ < 1} := by
          ext p
          constructor
          · rintro ⟨z, hz, he⟩
            have hp : p = (Fin.last r, z) := Sum.inr.inj he
            subst p
            exact ⟨rfl, hz⟩
          · rintro ⟨hp, hz⟩
            exact ⟨p.2, hz, congrArg Sum.inr (Prod.ext hp rfl)⟩
      rw [heq]
      exact (isOpen_discrete {Fin.last r}).prod
        (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)
  refine ⟨hC, hD, Set.eq_univ_of_forall ?_, ?_⟩
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    cases x with
    | inl z =>
        left
        intro he
        have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
            (Sum.inr (Fin.last r, c)) (Sum.inl z) := Quotient.exact he.symm
        have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree
          (Sum.inl z)).mp hr
        cases hx
    | inr p =>
        rcases p with ⟨i, z⟩
        by_cases hi : i = Fin.last r
        · subst i
          by_cases hz : ‖(z : ℂ)‖ < 1
          · right; exact ⟨z, hz, rfl⟩
          · left
            intro he
            have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
                (Sum.inr (Fin.last r, c)) (Sum.inr (Fin.last r, z)) :=
              Quotient.exact he.symm
            have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
            have hzc : z = c := (Prod.mk.inj (Sum.inr.inj hx)).2
            subst z
            simp [c] at hz
        · left
          intro he
          have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
              (Sum.inr (Fin.last r, c)) (Sum.inr (i, z)) := Quotient.exact he.symm
          have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
          exact hi (Prod.mk.inj (Sum.inr.inj hx)).1
  · let z : APMT99A01.Disk :=
      ⟨(1 / 2 : ℂ), by
        rw [Metric.mem_closedBall, dist_zero_right]
        norm_num [norm_div]⟩
    refine ⟨Quotient.mk _ (Sum.inr (Fin.last r, z)), ?_, ⟨z, ?_, rfl⟩⟩
    · intro he
      have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
          (Sum.inr (Fin.last r, c)) (Sum.inr (Fin.last r, z)) :=
        Quotient.exact he.symm
      have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
      have hzc : z = c := (Prod.mk.inj (Sum.inr.inj hx)).2
      have hv := congrArg (fun w : APMT99A01.Disk => (w : ℂ)) hzc
      norm_num [z, c] at hv
    · norm_num [z]

noncomputable def t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall
    (z : Metric.ball (0 : ℂ) 1) : APMT99A01.Disk :=
  ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using z.2 : ‖(z : ℂ)‖ < 1).le⟩

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_eqv {r : ℕ}
    (degree : Fin (r + 1) → ℕ) {z w : APMT99A01.Disk}
    (hz : ‖(z : ℂ)‖ < 1) (hw : ‖(w : ℂ)‖ < 1)
    (h : Relation.EqvGen (APMT99A01.AttachRel degree)
      (Sum.inr (Fin.last r, z)) (Sum.inr (Fin.last r, w))) : z = w := by
  let P := fun x : Sum Circle (Fin (r + 1) × APMT99A01.Disk) =>
    x = Sum.inr (Fin.last r, z)
  have hrel : ∀ a b, APMT99A01.AttachRel degree a b → (P a ↔ P b) := by
    intro a b hab
    cases hab with
    | boundary i u =>
      constructor
      · intro bad; cases bad
      · intro bad
        have hp : (i, APMT99A01.circleInDisk u) = (Fin.last r, z) :=
          Sum.inr.inj bad
        have he : APMT99A01.circleInDisk u = z := (Prod.mk.inj hp).2
        have hn := congrArg (fun v : APMT99A01.Disk => ‖(v : ℂ)‖) he
        simp [APMT99A01.circleInDisk] at hn
        linarith
  have hinv : ∀ a b, Relation.EqvGen (APMT99A01.AttachRel degree) a b →
      (P a ↔ P b) := by
    intro a b hab
    induction hab with
    | rel a b hab => exact hrel a b hab
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have he := (hinv _ _ h).mp rfl
  exact (Prod.mk.inj (Sum.inr.inj he)).2.symm

noncomputable def t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g {r : ℕ}
    (degree : Fin (r + 1) → ℕ) (z : Metric.ball (0 : ℂ) 1) :
    APMT99A01.succDiskSide degree :=
  ⟨Quotient.mk _ (Sum.inr (Fin.last r,
      t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall z)),
    ⟨_, by simpa only [t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall,
      Metric.mem_ball, dist_zero_right] using z.2, rfl⟩⟩

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g_cont_bij {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    Continuous (t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g degree) ∧
      Function.Bijective
        (t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g degree) := by
  constructor
  · apply Continuous.subtype_mk
    exact continuous_coinduced_rng.comp
      (continuous_inr.comp (continuous_const.prodMk
        (Continuous.subtype_mk continuous_subtype_val _)))
  constructor
  · intro z w h
    have he := Quotient.exact (congrArg Subtype.val h)
    have hu' := t99A01_piOne_attach_succ_cover_aux_connectivity_aux_eqv degree
      (by simpa only [t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall,
        Metric.mem_ball, dist_zero_right] using z.2)
      (by simpa only [t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall,
        Metric.mem_ball, dist_zero_right] using w.2) he
    apply Subtype.ext
    exact congrArg (fun x : APMT99A01.Disk => (x : ℂ)) hu'
  · rintro ⟨q, z, hz, rfl⟩
    let w : Metric.ball (0 : ℂ) 1 :=
      ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩
    refine ⟨w, Subtype.ext ?_⟩
    rfl

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g_open {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    IsOpenMap (t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g degree) := by
  intro U hU
  let d := t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall
  let F : Metric.ball (0 : ℂ) 1 →
      Sum Circle (Fin (r + 1) × APMT99A01.Disk) :=
    fun z => Sum.inr (Fin.last r, d z)
  have hopenC : IsOpen ((fun z : Metric.ball (0 : ℂ) 1 => (z : ℂ)) '' U) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap U hU
  have hopenD : IsOpen (d '' U) := by
    have heq : d '' U = Subtype.val ⁻¹'
        ((fun z : Metric.ball (0 : ℂ) 1 => (z : ℂ)) '' U) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, he⟩
        exact ⟨w, hw, Subtype.ext he⟩
    rw [heq]
    exact hopenC.preimage continuous_subtype_val
  have hopenF : IsOpen (F '' U) := by
    rw [isOpen_sum_iff]
    constructor
    · convert (isOpen_empty : IsOpen (∅ : Set Circle)) using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
      rintro ⟨z, -, h⟩
      cases h
    · rw [isOpen_prod_iff]
      intro i z hiz
      rcases hiz with ⟨w, hw, he⟩
      have hp := Sum.inr.inj he
      refine ⟨{Fin.last r}, d '' U, isOpen_discrete _, hopenD,
        (Prod.mk.inj hp).1.symm, ⟨w, hw, (Prod.mk.inj hp).2⟩, ?_⟩
      rintro ⟨j, v⟩ ⟨hj, hv⟩
      simp only [Set.mem_singleton_iff] at hj
      rcases hv with ⟨w, hw, rfl⟩
      subst j
      exact ⟨w, hw, rfl⟩
  have hsat : (Quotient.mk _ :
      Sum Circle (Fin (r + 1) × APMT99A01.Disk) → APMT99A01.AttachSpace degree) ⁻¹'
      ((Quotient.mk _) '' (F '' U)) = F '' U := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hzU, rfl⟩, hxy⟩
      have hr := Quotient.exact hxy
      have hx := (t99A01_piOne_attach_succ_cover_aux_interior degree _ _ hr).mp
        ⟨d z, by simpa only [d,
          t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall,
          Metric.mem_ball, dist_zero_right] using z.2, rfl⟩
      rcases hx with ⟨u, hu, hxu⟩
      have he : u = d z := t99A01_piOne_attach_succ_cover_aux_connectivity_aux_eqv degree
        hu (by simpa only [d,
          t99A01_piOne_attach_succ_cover_aux_connectivity_aux_diskOfBall,
          Metric.mem_ball, dist_zero_right] using z.2)
        (by rw [hxu] at hr; simpa only [F] using hr.symm)
      subst u
      refine ⟨z, hzU, ?_⟩
      exact hxu.symm
    · rintro ⟨z, hz, rfl⟩
      exact ⟨F z, ⟨z, hz, rfl⟩, rfl⟩
  have hquot : IsOpen ((Quotient.mk _) '' (F '' U) :
      Set (APMT99A01.AttachSpace degree)) := by
    rw [isOpen_coinduced]
    change IsOpen ((Quotient.mk _ :
      Sum Circle (Fin (r + 1) × APMT99A01.Disk) → APMT99A01.AttachSpace degree) ⁻¹'
        ((Quotient.mk _) '' (F '' U)))
    rw [hsat]
    exact hopenF
  have heq : t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g degree '' U =
      Subtype.val ⁻¹' ((Quotient.mk _) '' (F '' U) :
        Set (APMT99A01.AttachSpace degree)) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨F z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨z, hz, hx⟩, hxq⟩
      refine ⟨z, hz, Subtype.ext ?_⟩
      exact (congrArg (Quotient.mk _) hx).trans hxq
  rw [heq]
  exact hquot.preimage continuous_subtype_val

noncomputable def t99A01_piOne_attach_succ_cover_aux_connectivity_aux_homeomorph
    {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    Metric.ball (0 : ℂ) 1 ≃ₜ APMT99A01.succDiskSide degree := by
  obtain ⟨hc, hb⟩ :=
    t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g_cont_bij degree
  exact (Equiv.ofBijective _ hb).toHomeomorphOfContinuousOpen hc
    (t99A01_piOne_attach_succ_cover_aux_connectivity_aux_g_open degree)

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_disk_path {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    IsPathConnected (APMT99A01.succDiskSide degree) := by
  let e := t99A01_piOne_attach_succ_cover_aux_connectivity_aux_homeomorph degree
  letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  apply isPathConnected_iff_pathConnectedSpace.mpr
  exact e.surjective.pathConnectedSpace e.continuous

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_disk_simple {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    IsSimplyConnected (APMT99A01.succDiskSide degree) := by
  let e := t99A01_piOne_attach_succ_cover_aux_connectivity_aux_homeomorph degree
  letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  letI : SimplyConnectedSpace (Metric.ball (0 : ℂ) 1) :=
    SimplyConnectedSpace.ofContractible _
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_circle_path :
    IsPathConnected (Set.univ : Set Circle) := by
  have h : IsPathConnected
      (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
        (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
    ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
      isPathConnected_univ
  simpa using h

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_polar_open :
    IsPathConnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
  let T := Circle × Set.Ioo (0 : ℝ) 1
  let f : T → ℂ := fun p => (p.2.1 : ℂ) * (p.1.1 : ℂ)
  have hT : IsPathConnected (Set.univ : Set T) := by
    have hI : IsPathConnected (Set.Ioo (0 : ℝ) 1) :=
      (convex_Ioo (0 : ℝ) 1).isPathConnected (by exact ⟨1 / 2, by norm_num⟩)
    have hIsub : IsPathConnected (Set.univ : Set (Set.Ioo (0 : ℝ) 1)) := by
      letI : PathConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
        isPathConnected_iff_pathConnectedSpace.mp hI
      exact isPathConnected_univ
    rcases t99A01_piOne_attach_succ_cover_aux_connectivity_aux_circle_path with
      ⟨c, -, hc⟩
    rcases hIsub with ⟨a, -, ha⟩
    refine ⟨(c, a), Set.mem_univ _, ?_⟩
    intro y hy
    exact ⟨(hc (Set.mem_univ y.1)).somePath.prod
      (ha (Set.mem_univ y.2)).somePath, fun _ => Set.mem_univ _⟩
  have hf : Continuous f := by
    exact (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst)
  have him : f '' Set.univ = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    ext z
    constructor
    · rintro ⟨⟨w, ρ⟩, -, rfl⟩
      change 0 < ‖(ρ.1 : ℂ) * (w.1 : ℂ)‖ ∧
        ‖(ρ.1 : ℂ) * (w.1 : ℂ)‖ < 1
      rw [norm_mul, Circle.norm_coe, mul_one]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ρ.2.1]
      exact ρ.2
    · intro hz
      let w : Circle := ⟨z / (‖z‖ : ℂ), by
        simp [Submonoid.unitSphere, div_self (ne_of_gt hz.1)]⟩
      let ρ : Set.Ioo (0 : ℝ) 1 := ⟨‖z‖, hz⟩
      refine ⟨⟨w, ρ⟩, Set.mem_univ _, ?_⟩
      dsimp [f, w, ρ]
      push_cast
      field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hz.1]
  rw [← him]
  exact hT.image hf

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_overlap {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    IsPathConnected (APMT99A01.succCircleSide degree ∩
      APMT99A01.succDiskSide degree) := by
  let S : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < 1}
  let g : S → APMT99A01.AttachSpace degree := fun z =>
    Quotient.mk _ (Sum.inr (Fin.last r,
      (⟨z.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using z.2.2.le⟩ :
        APMT99A01.Disk)))
  have hg : Continuous g := continuous_coinduced_rng.comp
    (continuous_inr.comp (continuous_const.prodMk
      (Continuous.subtype_mk continuous_subtype_val _)))
  have him : g '' Set.univ = APMT99A01.succCircleSide degree ∩
      APMT99A01.succDiskSide degree := by
    ext q
    constructor
    · rintro ⟨z, -, rfl⟩
      constructor
      · intro he
        have hr := Quotient.exact he.symm
        have hc := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
        have hz := congrArg (fun x : APMT99A01.Disk => (x : ℂ))
          (Prod.mk.inj (Sum.inr.inj hc)).2
        exact (ne_of_gt z.2.1) (by simpa [hz])
      · exact ⟨_, z.2.2, rfl⟩
    · rintro ⟨hq, z, hz, rfl⟩
      have h0 : 0 < ‖(z : ℂ)‖ := by
        apply lt_of_le_of_ne (norm_nonneg _)
        intro hn
        have zz : (z : ℂ) = 0 := norm_eq_zero.mp hn.symm
        apply hq
        apply Quotient.sound
        have zeq : z = (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk) :=
          Subtype.ext zz
        rw [zeq]
      let w : S := ⟨z, h0, hz⟩
      exact ⟨w, Set.mem_univ _, rfl⟩
  rw [← him]
  letI : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp (by
    simpa [S] using t99A01_piOne_attach_succ_cover_aux_connectivity_aux_polar_open)
  exact isPathConnected_univ.image hg

lemma t99A01_piOne_attach_succ_cover_aux_connectivity_aux_polar_closed :
    IsPathConnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ 1} := by
  let T := Circle × Set.Ioc (0 : ℝ) 1
  let f : T → ℂ := fun p => (p.2.1 : ℂ) * (p.1.1 : ℂ)
  have hT : IsPathConnected (Set.univ : Set T) := by
    have hI : IsPathConnected (Set.Ioc (0 : ℝ) 1) :=
      (convex_Ioc (0 : ℝ) 1).isPathConnected (by exact ⟨1, by norm_num⟩)
    have hIsub : IsPathConnected (Set.univ : Set (Set.Ioc (0 : ℝ) 1)) := by
      letI : PathConnectedSpace (Set.Ioc (0 : ℝ) 1) :=
        isPathConnected_iff_pathConnectedSpace.mp hI
      exact isPathConnected_univ
    rcases t99A01_piOne_attach_succ_cover_aux_connectivity_aux_circle_path with
      ⟨c, -, hc⟩
    rcases hIsub with ⟨a, -, ha⟩
    refine ⟨(c, a), Set.mem_univ _, ?_⟩
    intro y hy
    exact ⟨(hc (Set.mem_univ y.1)).somePath.prod
      (ha (Set.mem_univ y.2)).somePath, fun _ => Set.mem_univ _⟩
  have hf : Continuous f := by
    exact (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst)
  have him : f '' Set.univ = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ 1} := by
    ext z
    constructor
    · rintro ⟨⟨w, ρ⟩, -, rfl⟩
      change 0 < ‖(ρ.1 : ℂ) * (w.1 : ℂ)‖ ∧
        ‖(ρ.1 : ℂ) * (w.1 : ℂ)‖ ≤ 1
      rw [norm_mul, Circle.norm_coe, mul_one]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ρ.2.1]
      exact ρ.2
    · intro hz
      let w : Circle := ⟨z / (‖z‖ : ℂ), by
        simp [Submonoid.unitSphere, div_self (ne_of_gt hz.1)]⟩
      let ρ : Set.Ioc (0 : ℝ) 1 := ⟨‖z‖, hz⟩
      refine ⟨⟨w, ρ⟩, Set.mem_univ _, ?_⟩
      dsimp [f, w, ρ]
      push_cast
      field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hz.1]
  rw [← him]
  exact hT.image hf

lemma t99A01_piOne_attach_succ_cover_aux_connectivity {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    IsPathConnected (APMT99A01.succCircleSide degree ∩
        APMT99A01.succDiskSide degree) ∧
      IsPathConnected (APMT99A01.succCircleSide degree) ∧
      IsPathConnected (APMT99A01.succDiskSide degree) ∧
      IsSimplyConnected (APMT99A01.succDiskSide degree) := by
  refine ⟨t99A01_piOne_attach_succ_cover_aux_connectivity_aux_overlap degree, ?_,
    t99A01_piOne_attach_succ_cover_aux_connectivity_aux_disk_path degree,
    t99A01_piOne_attach_succ_cover_aux_connectivity_aux_disk_simple degree⟩
  let cMap : Circle → APMT99A01.AttachSpace degree := fun z =>
    Quotient.mk _ (Sum.inl z)
  let dMap : Fin (r + 1) → APMT99A01.Disk → APMT99A01.AttachSpace degree :=
    fun i z => Quotient.mk _ (Sum.inr (i, z))
  let C : Set (APMT99A01.AttachSpace degree) := cMap '' Set.univ
  let D : Fin (r + 1) → Set (APMT99A01.AttachSpace degree) :=
    fun i => dMap i '' Set.univ
  let L : Set (APMT99A01.AttachSpace degree) :=
    dMap (Fin.last r) '' {z : APMT99A01.Disk | (z : ℂ) ≠ 0}
  have hcMap : Continuous cMap := continuous_coinduced_rng.comp continuous_inl
  have hdMap (i : Fin (r + 1)) : Continuous (dMap i) :=
    continuous_coinduced_rng.comp (continuous_inr.comp
      (continuous_const.prodMk continuous_id))
  have hC : IsPathConnected C := by
    exact t99A01_piOne_attach_succ_cover_aux_connectivity_aux_circle_path.image hcMap
  have hD (i : Fin (r + 1)) : IsPathConnected (D i) := by
    have hball : IsPathConnected (Set.univ : Set APMT99A01.Disk) := by
      letI : PathConnectedSpace APMT99A01.Disk :=
        isPathConnected_iff_pathConnectedSpace.mp
          (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
      exact isPathConnected_univ
    exact hball.image (hdMap i)
  have hL : IsPathConnected L := by
    let P : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ ≤ 1}
    let e : P → APMT99A01.Disk := fun z => ⟨z.1, by
      simpa [Metric.mem_closedBall, dist_zero_right] using z.2.2⟩
    have he : Continuous e := Continuous.subtype_mk continuous_subtype_val _
    have him : e '' Set.univ = {z : APMT99A01.Disk | (z : ℂ) ≠ 0} := by
      ext z
      constructor
      · rintro ⟨w, -, rfl⟩
        exact fun hz => (ne_of_gt w.2.1) (norm_eq_zero.mpr hz)
      · intro hz
        have hp : 0 < ‖(z : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _)
          (fun h => hz (norm_eq_zero.mp h.symm))
        refine ⟨⟨z, hp, ?_⟩, Set.mem_univ _, rfl⟩
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    have hP : IsPathConnected (Set.univ : Set P) := by
      letI : PathConnectedSpace P := isPathConnected_iff_pathConnectedSpace.mp (by
        simpa [P] using
          t99A01_piOne_attach_succ_cover_aux_connectivity_aux_polar_closed)
      exact isPathConnected_univ
    change IsPathConnected (dMap (Fin.last r) '' {z : APMT99A01.Disk | (z : ℂ) ≠ 0})
    rw [← him]
    exact (hP.image he).image (hdMap (Fin.last r))
  have hCsub : C ⊆ APMT99A01.succCircleSide degree := by
    rintro q ⟨z, -, rfl⟩ heq
    have hr := Quotient.exact heq.symm
    have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
    cases hx
  have hDsub (i : Fin (r + 1)) (hi : i ≠ Fin.last r) :
      D i ⊆ APMT99A01.succCircleSide degree := by
    rintro q ⟨z, -, rfl⟩ heq
    have hr := Quotient.exact heq.symm
    have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
    exact hi (Prod.mk.inj (Sum.inr.inj hx)).1
  have hLsub : L ⊆ APMT99A01.succCircleSide degree := by
    rintro q ⟨z, hz, rfl⟩ heq
    have hr := Quotient.exact heq.symm
    have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
    exact hz (congrArg (fun w : APMT99A01.Disk => (w : ℂ))
      (Prod.mk.inj (Sum.inr.inj hx)).2)
  let b := cMap (1 : Circle)
  refine ⟨b, hCsub ⟨_, Set.mem_univ _, rfl⟩, ?_⟩
  intro q hq
  induction q using Quotient.ind with
  | _ x =>
    cases x with
    | inl z =>
        exact (hC.joinedIn b ⟨_, Set.mem_univ _, rfl⟩ _
          ⟨z, Set.mem_univ _, rfl⟩).mono hCsub
    | inr p =>
      rcases p with ⟨i, z⟩
      by_cases hi : i = Fin.last r
      · subst i
        have hz : (z : ℂ) ≠ 0 := by
          intro hz
          apply hq
          apply Quotient.sound
          have he : z = (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk) :=
            Subtype.ext hz
          rw [he]
        have hbL : b ∈ L := by
          let u : APMT99A01.Disk := APMT99A01.circleInDisk (1 : Circle)
          refine ⟨u, ?_, ?_⟩
          · exact one_ne_zero
          · apply Quotient.sound
            simpa [u] using (Relation.EqvGen.rel _ _
              (APMT99A01.AttachRel.boundary (degree := degree) (Fin.last r) 1)).symm
        exact (hL.joinedIn b hbL _ ⟨z, hz, rfl⟩).mono hLsub
      · have hbD : b ∈ D i := by
          let u : APMT99A01.Disk := APMT99A01.circleInDisk (1 : Circle)
          refine ⟨u, Set.mem_univ _, ?_⟩
          apply Quotient.sound
          simpa [u] using (Relation.EqvGen.rel _ _
            (APMT99A01.AttachRel.boundary (degree := degree) i 1)).symm
        exact (hD i).joinedIn b hbD _ ⟨z, Set.mem_univ _, rfl⟩ |>.mono (hDsub i hi)
lemma t99A01_piOne_attach_succ_cover {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    IsOpen (APMT99A01.succCircleSide degree) ∧
      IsOpen (APMT99A01.succDiskSide degree) ∧
      APMT99A01.succCircleSide degree ∪ APMT99A01.succDiskSide degree = Set.univ ∧
      Set.Nonempty (APMT99A01.succCircleSide degree ∩ APMT99A01.succDiskSide degree) ∧
      IsPathConnected (APMT99A01.succCircleSide degree ∩ APMT99A01.succDiskSide degree) ∧
      IsPathConnected (APMT99A01.succCircleSide degree) ∧
      IsPathConnected (APMT99A01.succDiskSide degree) ∧
      IsSimplyConnected (APMT99A01.succDiskSide degree) := by
  rcases t99A01_piOne_attach_succ_cover_aux_basic degree with
    ⟨hU, hV, hcover, hne⟩
  rcases t99A01_piOne_attach_succ_cover_aux_connectivity degree with
    ⟨hUV, hUc, hVc, hVs⟩
  exact ⟨hU, hV, hcover, hne, hUV, hUc, hVc, hVs⟩
/-- **Leaf (last-disk radial retraction, 90--150 lines).**  The circle is
fixed, and the inverse is the explicit `attachCastSucc` inclusion. -/
lemma t99A01_piOne_attach_succ_retract_aux_circle_mem {r : ℕ}
    (degree : Fin (r + 1) → ℕ) (z : Circle) :
    (Quotient.mk _ (Sum.inl z) : APMT99A01.AttachSpace degree) ∈
      APMT99A01.succCircleSide degree := by
  intro h
  have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
      (Sum.inr (Fin.last r,
        (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk)))
      (Sum.inl z) := Quotient.exact h.symm
  have he := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
  cases he

lemma t99A01_piOne_attach_succ_retract_aux_ne_zero {r : ℕ}
    (degree : Fin (r + 1) → ℕ) (z : APMT99A01.Disk)
    (h : (Quotient.mk _ (Sum.inr (Fin.last r, z)) :
      APMT99A01.AttachSpace degree) ∈ APMT99A01.succCircleSide degree) :
    (z : ℂ) ≠ 0 := by
  intro hz
  apply h
  have he : z = (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk) :=
    Subtype.ext hz
  rw [he]
  rfl

def t99A01_piOne_attach_succ_retract_aux_scale
    (t : unitInterval) (z : ℂ) : ℝ :=
  t.1 + (1 - t.1) / ‖z‖

lemma t99A01_piOne_attach_succ_retract_aux_scale_norm
    (t : unitInterval) (z : ℂ) (hz0 : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖(t99A01_piOne_attach_succ_retract_aux_scale t z : ℂ) * z‖ ≤ 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hs0 : 0 ≤ (t : ℝ) + (1 - t.1) / ‖z‖ :=
    add_nonneg ht0 (div_nonneg (sub_nonneg.mpr ht1) hn.le)
  rw [norm_mul]
  change ‖(((t : ℝ) + (1 - t.1) / ‖z‖ : ℝ) : ℂ)‖ * ‖z‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  field_simp
  nlinarith

lemma t99A01_piOne_attach_succ_retract_aux_scale_ne
    (t : unitInterval) (z : ℂ) (hz0 : z ≠ 0) :
    (t99A01_piOne_attach_succ_retract_aux_scale t z : ℂ) * z ≠ 0 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  apply mul_ne_zero
  · rw [t99A01_piOne_attach_succ_retract_aux_scale]
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hp : 0 < (t : ℝ) + (1 - t.1) / ‖z‖ := by
      by_cases ht : (t : ℝ) = 0
      · rw [ht]
        positivity
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ht0 (Ne.symm ht))
          (div_nonneg (sub_nonneg.mpr ht1) hn.le)
    exact_mod_cast hp.ne'
  · exact hz0

def t99A01_piOne_attach_succ_retract_aux_radial (z : ℂ) : Circle :=
  if h : z = 0 then 1 else
    ⟨z / (‖z‖ : ℂ), by
      simp [Submonoid.unitSphere, div_self (norm_ne_zero_iff.mpr h)]⟩

def t99A01_piOne_attach_succ_retract_aux_raw {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    Sum Circle (Fin (r + 1) × APMT99A01.Disk) →
      APMT99A01.AttachSpace (degree ∘ Fin.castSucc)
  | Sum.inl z => Quotient.mk _ (Sum.inl z)
  | Sum.inr (i, z) =>
      if h : i = Fin.last r then
        Quotient.mk _ (Sum.inl
          ((t99A01_piOne_attach_succ_retract_aux_radial (z : ℂ)) ^ degree i))
      else
        Quotient.mk _ (Sum.inr (i.castPred h, z))

lemma t99A01_piOne_attach_succ_retract_aux_raw_boundary {r : ℕ}
    (degree : Fin (r + 1) → ℕ) (i : Fin (r + 1)) (z : Circle) :
    t99A01_piOne_attach_succ_retract_aux_raw degree (Sum.inl (z ^ degree i)) =
      t99A01_piOne_attach_succ_retract_aux_raw degree
        (Sum.inr (i, APMT99A01.circleInDisk z)) := by
  by_cases hi : i = Fin.last r
  · subst i
    simp only [t99A01_piOne_attach_succ_retract_aux_raw, dif_pos rfl]
    congr 2
    have hz : (z : ℂ) ≠ 0 := by
      intro h
      have hn := Circle.norm_coe z
      rw [h, norm_zero] at hn
      norm_num at hn
    apply congrArg (fun u : Circle => u ^ degree (Fin.last r))
    apply Subtype.ext
    simp [t99A01_piOne_attach_succ_retract_aux_radial,
      APMT99A01.circleInDisk, hz, Circle.norm_coe]
  · simp only [t99A01_piOne_attach_succ_retract_aux_raw, dif_neg hi]
    apply Quotient.sound
    have hb := Relation.EqvGen.rel _ _
      (APMT99A01.AttachRel.boundary
        (degree := degree ∘ Fin.castSucc) (i.castPred hi) z)
    simpa [Fin.castSucc_castPred i hi] using hb

lemma t99A01_piOne_attach_succ_retract_aux_raw_respects {r : ℕ}
    (degree : Fin (r + 1) → ℕ)
    {x y : Sum Circle (Fin (r + 1) × APMT99A01.Disk)}
    (h : Relation.EqvGen (APMT99A01.AttachRel degree) x y) :
    t99A01_piOne_attach_succ_retract_aux_raw degree x =
      t99A01_piOne_attach_succ_retract_aux_raw degree y := by
  induction h with
  | rel a b h =>
      cases h with
      | boundary i z =>
          exact t99A01_piOne_attach_succ_retract_aux_raw_boundary degree i z
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma t99A01_piOne_attach_succ_retract_aux_raw_half {r : ℕ}
    (degree : Fin (r + 1) → ℕ) (w : Circle) :
    t99A01_piOne_attach_succ_retract_aux_raw degree
        (Sum.inr (Fin.last r,
          (⟨(w : ℂ) / 2, by
            rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]
            norm_num⟩ : APMT99A01.Disk))) =
      Quotient.mk _ (Sum.inl (w ^ degree (Fin.last r))) := by
  change (if h : Fin.last r = Fin.last r then
      Quotient.mk _ (Sum.inl
        (t99A01_piOne_attach_succ_retract_aux_radial ((w : ℂ) / 2) ^
          degree (Fin.last r)))
    else Quotient.mk _ (Sum.inr ((Fin.last r).castPred h,
      (⟨(w : ℂ) / 2, by
        rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]
        norm_num⟩ : APMT99A01.Disk)))) = _
  rw [dif_pos rfl]
  congr 2
  apply congrArg (fun u : Circle => u ^ degree (Fin.last r))
  apply Subtype.ext
  simp [t99A01_piOne_attach_succ_retract_aux_radial, Circle.norm_coe,
    norm_div]

abbrev t99A01_piOne_attach_succ_retract_aux_Pre {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :=
  ↥((fun x : Sum Circle (Fin (r + 1) × APMT99A01.Disk) =>
    (Quotient.mk _ x : APMT99A01.AttachSpace degree)) ⁻¹'
      APMT99A01.succCircleSide degree)

def t99A01_piOne_attach_succ_retract_aux_q {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    t99A01_piOne_attach_succ_retract_aux_Pre degree →
      APMT99A01.succCircleSide degree :=
  fun x => ⟨Quotient.mk _ x.1, x.2⟩

lemma t99A01_piOne_attach_succ_retract_aux_q_quotient {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    Topology.IsQuotientMap (t99A01_piOne_attach_succ_retract_aux_q degree) := by
  exact isQuotientMap_quotient_mk'.restrictPreimage_isOpen
    (t99A01_piOne_attach_succ_cover degree).1

lemma t99A01_piOne_attach_succ_retract_aux_raw_continuous {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    Continuous (fun x : t99A01_piOne_attach_succ_retract_aux_Pre degree =>
      t99A01_piOne_attach_succ_retract_aux_raw degree x.1) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases x with ⟨x, hx⟩
  cases x with
  | inl z =>
      let g : Sum Circle (Fin (r + 1) × APMT99A01.Disk) →
          APMT99A01.AttachSpace (degree ∘ Fin.castSucc) :=
        Sum.elim (fun w => Quotient.mk _ (Sum.inl w)) (fun _ => Quotient.mk _ (Sum.inl 1))
      have hg : Continuous g := continuous_sum_dom.mpr
        ⟨by
          change Continuous (fun w : Circle =>
            (Quotient.mk _ (Sum.inl w) :
              APMT99A01.AttachSpace (degree ∘ Fin.castSucc)))
          exact continuous_coinduced_rng.comp continuous_inl,
        continuous_const⟩
      apply (hg.continuousAt.comp continuousAt_subtype_val).congr_of_eventuallyEq
      filter_upwards [(isOpen_range_inl.preimage continuous_subtype_val).mem_nhds ⟨z, rfl⟩]
        with y hy
      rcases hy with ⟨w, hw⟩
      change t99A01_piOne_attach_succ_retract_aux_raw degree y.1 = g y.1
      rw [← hw]
      rfl
  | inr p =>
      rcases p with ⟨i, z⟩
      by_cases hi : i = Fin.last r
      · subst i
        have hz : (z : ℂ) ≠ 0 :=
          t99A01_piOne_attach_succ_retract_aux_ne_zero degree z hx
        have hopen : IsOpen {w : APMT99A01.Disk | (w : ℂ) ≠ 0} :=
          isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
        have hrad : Continuous (fun w : {w : APMT99A01.Disk | (w : ℂ) ≠ 0} =>
            t99A01_piOne_attach_succ_retract_aux_radial (w.1 : ℂ)) := by
          apply Continuous.subtype_mk
          change Continuous (fun w : {w : APMT99A01.Disk | (w : ℂ) ≠ 0} =>
            ((t99A01_piOne_attach_succ_retract_aux_radial (w.1 : ℂ) : Circle) : ℂ))
          rw [show (fun w : {w : APMT99A01.Disk | (w : ℂ) ≠ 0} =>
              ((t99A01_piOne_attach_succ_retract_aux_radial (w.1 : ℂ) : Circle) : ℂ)) =
              fun w => (w.1 : ℂ) / (‖(w.1 : ℂ)‖ : ℂ) by
            funext w
            rw [t99A01_piOne_attach_succ_retract_aux_radial, dif_neg w.2]]
          exact (continuous_subtype_val.comp continuous_subtype_val).div₀
            (Complex.continuous_ofReal.comp
              (continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val)))
            (fun w => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr w.2))
        have hc : ContinuousAt (fun w : APMT99A01.Disk =>
            (Quotient.mk _ (Sum.inl
              ((t99A01_piOne_attach_succ_retract_aux_radial (w : ℂ)) ^
                degree (Fin.last r))) :
              APMT99A01.AttachSpace (degree ∘ Fin.castSucc))) z := by
          refine (hopen.isOpenEmbedding_subtypeVal.continuousAt_iff
            (x := ⟨z, hz⟩)).mp ?_
          exact continuous_coinduced_rng.continuousAt.comp
            (continuous_inl.continuousAt.comp
              (hrad.continuousAt.pow (degree (Fin.last r))))
        let g : Sum Circle (Fin (r + 1) × APMT99A01.Disk) →
            APMT99A01.AttachSpace (degree ∘ Fin.castSucc) :=
          Sum.elim (fun _ => Quotient.mk _ (Sum.inl 1)) (fun p =>
            Quotient.mk _ (Sum.inl
              ((t99A01_piOne_attach_succ_retract_aux_radial (p.2 : ℂ)) ^
                degree (Fin.last r))))
        have hg : ContinuousAt g (Sum.inr (Fin.last r, z)) :=
          (Topology.IsOpenEmbedding.inr.continuousAt_iff (g := g)).mp (by
            change ContinuousAt (fun p : Fin (r + 1) × APMT99A01.Disk =>
              (Quotient.mk _ (Sum.inl
                ((t99A01_piOne_attach_succ_retract_aux_radial (p.2 : ℂ)) ^
                  degree (Fin.last r))) :
                APMT99A01.AttachSpace (degree ∘ Fin.castSucc))) (Fin.last r, z)
            exact hc.comp (f := Prod.snd) (x := (Fin.last r, z)) continuousAt_snd)
        apply (hg.comp (x := ⟨Sum.inr (Fin.last r, z), hx⟩)
          continuousAt_subtype_val).congr_of_eventuallyEq
        have hop : IsOpen (Sum.inr '' (({Fin.last r} : Set (Fin (r + 1))) ×ˢ
            {w : APMT99A01.Disk | (w : ℂ) ≠ 0})) :=
          (isOpenMap_inr (X := Circle)) _
            ((isOpen_discrete _).prod hopen)
        filter_upwards [(hop.preimage continuous_subtype_val).mem_nhds
          ⟨(Fin.last r, z), by
            refine ⟨(Set.mem_singleton_iff).2 rfl, hz⟩, rfl⟩] with y hy
        obtain ⟨⟨j, w⟩, hjw, he⟩ := hy
        have hj : j = Fin.last r := by simpa using hjw.1
        subst j
        change t99A01_piOne_attach_succ_retract_aux_raw degree y.1 = g y.1
        rw [← he]
        simp [t99A01_piOne_attach_succ_retract_aux_raw, g]
      · let g : Sum Circle (Fin (r + 1) × APMT99A01.Disk) →
            APMT99A01.AttachSpace (degree ∘ Fin.castSucc) :=
          Sum.elim (fun _ => Quotient.mk _ (Sum.inl 1)) (fun p =>
            Quotient.mk _ (Sum.inr (i.castPred hi, p.2)))
        have hg : ContinuousAt g (Sum.inr (i, z)) :=
          (Topology.IsOpenEmbedding.inr.continuousAt_iff (g := g)).mp (by
            change ContinuousAt (fun p : Fin (r + 1) × APMT99A01.Disk =>
              Quotient.mk _ (Sum.inr (i.castPred hi, p.2))) (i, z)
            exact continuous_coinduced_rng.continuousAt.comp
              (continuous_inr.continuousAt.comp
                (continuous_const.prodMk continuous_snd).continuousAt))
        apply (hg.comp (x := ⟨Sum.inr (i, z), hx⟩)
          continuousAt_subtype_val).congr_of_eventuallyEq
        have hop : IsOpen (Sum.inr '' (({i} : Set (Fin (r + 1))) ×ˢ
            (Set.univ : Set APMT99A01.Disk))) :=
          (isOpenMap_inr (X := Circle)) _ ((isOpen_discrete _).prod isOpen_univ)
        filter_upwards [(hop.preimage continuous_subtype_val).mem_nhds
          ⟨(i, z), by simp⟩] with y hy
        obtain ⟨⟨j, w⟩, hjw, he⟩ := hy
        have hj : j = i := by simpa using hjw.1
        subst j
        change t99A01_piOne_attach_succ_retract_aux_raw degree y.1 = g y.1
        rw [← he]
        simp [t99A01_piOne_attach_succ_retract_aux_raw, g, hi]

lemma t99A01_piOne_attach_succ_retract_aux_retraction {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    ∃ ρ : C(APMT99A01.succCircleSide degree,
        APMT99A01.AttachSpace (degree ∘ Fin.castSucc)),
      (∀ z : Circle, ρ ⟨Quotient.mk _ (Sum.inl z),
          t99A01_piOne_attach_succ_retract_aux_circle_mem degree z⟩ =
        Quotient.mk _ (Sum.inl z)) ∧
      ∀ (w : Circle) (h : (Quotient.mk _ (Sum.inr (Fin.last r,
          (⟨(w : ℂ) / 2, by
            rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]
            norm_num⟩ : APMT99A01.Disk))) : APMT99A01.AttachSpace degree) ∈
            APMT99A01.succCircleSide degree),
        ρ ⟨Quotient.mk _ (Sum.inr (Fin.last r,
          (⟨(w : ℂ) / 2, by
            rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]
            norm_num⟩ : APMT99A01.Disk))), h⟩ =
          Quotient.mk _ (Sum.inl (w ^ degree (Fin.last r))) := by
  let f : APMT99A01.AttachSpace degree →
      APMT99A01.AttachSpace (degree ∘ Fin.castSucc) :=
    Quotient.lift (t99A01_piOne_attach_succ_retract_aux_raw degree)
      (fun _ _ h => t99A01_piOne_attach_succ_retract_aux_raw_respects degree h)
  let ρ : C(APMT99A01.succCircleSide degree,
      APMT99A01.AttachSpace (degree ∘ Fin.castSucc)) :=
    ⟨fun x => f x.1,
      (t99A01_piOne_attach_succ_retract_aux_q_quotient degree).continuous_iff.mpr
        (by simpa [t99A01_piOne_attach_succ_retract_aux_q, f, Function.comp_def] using
          t99A01_piOne_attach_succ_retract_aux_raw_continuous degree)⟩
  refine ⟨ρ, ?_, ?_⟩
  · intro z
    rfl
  · intro w h
    exact t99A01_piOne_attach_succ_retract_aux_raw_half degree w

/-- The last-disk radial retraction, as a definition (same construction as
`t99A01_piOne_attach_succ_retract_aux_retraction`). -/
noncomputable def t99A01_succRho {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    C(APMT99A01.succCircleSide degree, APMT99A01.AttachSpace (degree ∘ Fin.castSucc)) :=
  ⟨fun x => Quotient.lift (t99A01_piOne_attach_succ_retract_aux_raw degree)
      (fun _ _ h => t99A01_piOne_attach_succ_retract_aux_raw_respects degree h) x.1,
    (t99A01_piOne_attach_succ_retract_aux_q_quotient degree).continuous_iff.mpr
      (by simpa [t99A01_piOne_attach_succ_retract_aux_q, Function.comp_def] using
        t99A01_piOne_attach_succ_retract_aux_raw_continuous degree)⟩

/-- **Leaf.** `attachCastSucc` is continuous and lands in `succCircleSide` (the image avoids
the last disk entirely; continuity through the quotient: `continuous_coinduced_rng`). -/
lemma t99A01_piOne_attach_succ_iota {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    ∃ ι : C(APMT99A01.AttachSpace (degree ∘ Fin.castSucc), APMT99A01.succCircleSide degree),
      ∀ y, (ι y).1 = APMT99A01.attachCastSucc degree y := by
  have hraw : Continuous (APMT99A01.attachCastSuccRaw degree) := by
    apply continuous_sum_dom.mpr
    constructor
    · exact continuous_inl
    · exact continuous_inr.comp
        ((continuous_of_discreteTopology.comp continuous_fst).prodMk continuous_snd)
  have hcast : Continuous (APMT99A01.attachCastSucc degree) := by
    apply continuous_coinduced_dom.mpr
    exact continuous_coinduced_rng.comp hraw
  have havoid : ∀ y, APMT99A01.attachCastSucc degree y ∈
      APMT99A01.succCircleSide degree := by
    intro y
    induction y using Quotient.ind with
    | _ x =>
      intro he
      have hr := Quotient.exact he.symm
      have hx := (t99A01_piOne_attach_succ_cover_aux_centre degree
        (APMT99A01.attachCastSuccRaw degree x)).mp hr
      cases x with
      | inl z => cases hx
      | inr p =>
        have hi : Fin.castSucc p.1 = Fin.last r :=
          (Prod.mk.inj (Sum.inr.inj hx)).1
        exact (Fin.castSucc_ne_last p.1) hi
  let ι : C(APMT99A01.AttachSpace (degree ∘ Fin.castSucc),
      APMT99A01.succCircleSide degree) :=
    ⟨fun y => ⟨APMT99A01.attachCastSucc degree y, havoid y⟩,
      Continuous.subtype_mk hcast havoid⟩
  exact ⟨ι, fun _ => rfl⟩

/-- **Leaf.** `ρ ∘ ι = id`: on representatives, `raw (attachCastSuccRaw x) = x`
(circle and non-last disks are untouched). -/
lemma t99A01_piOne_attach_succ_rho_iota {r : ℕ} (degree : Fin (r + 1) → ℕ)
    (ι : C(APMT99A01.AttachSpace (degree ∘ Fin.castSucc), APMT99A01.succCircleSide degree))
    (hι : ∀ y, (ι y).1 = APMT99A01.attachCastSucc degree y) :
    (t99A01_succRho degree).comp ι = ContinuousMap.id _ := by
  ext y
  change (t99A01_succRho degree (ι y)) = y
  change Quotient.lift _ _ (ι y).1 = y
  rw [hι]
  induction y using Quotient.ind with
  | _ x =>
      cases x with
      | inl z => rfl
      | inr p =>
          rcases p with ⟨i, z⟩
          simp [APMT99A01.attachCastSucc,
            APMT99A01.attachCastSuccRaw,
            t99A01_piOne_attach_succ_retract_aux_raw,
            Fin.castSucc_ne_last]

/-- **Leaf.** `ι ∘ ρ ≃ id`: push the last disk radially to its boundary, fixing everything
else (pattern: `t99A01_attach_circleSide_aux_deformation_aux_continuous` / `_aux_respects` /
`_aux_descend`, restricted to the last disk; reuse `_aux_scale`, `_aux_q_quotient`). -/
def t99A01_piOne_attach_succ_deform_aux_scale
    (t : unitInterval) (z : ℂ) : ℝ :=
  t.1 + (1 - t.1) / ‖z‖

lemma t99A01_piOne_attach_succ_deform_aux_scale_norm
    (t : unitInterval) (z : ℂ) (hz0 : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖(t99A01_piOne_attach_succ_deform_aux_scale t z : ℂ) * z‖ ≤ 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hs0 : 0 ≤ (t : ℝ) + (1 - t.1) / ‖z‖ :=
    add_nonneg ht0 (div_nonneg (sub_nonneg.mpr ht1) hn.le)
  rw [norm_mul]
  change ‖(((t : ℝ) + (1 - t.1) / ‖z‖ : ℝ) : ℂ)‖ * ‖z‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  field_simp
  nlinarith

lemma t99A01_piOne_attach_succ_deform_aux_scale_ne
    (t : unitInterval) (z : ℂ) (hz0 : z ≠ 0) :
    (t99A01_piOne_attach_succ_deform_aux_scale t z : ℂ) * z ≠ 0 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  apply mul_ne_zero
  · rw [t99A01_piOne_attach_succ_deform_aux_scale]
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hp : 0 < (t : ℝ) + (1 - t.1) / ‖z‖ := by
      by_cases ht : (t : ℝ) = 0
      · rw [ht]
        positivity
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ht0 (Ne.symm ht))
          (div_nonneg (sub_nonneg.mpr ht1) hn.le)
    exact_mod_cast hp.ne'
  · exact hz0

lemma t99A01_piOne_attach_succ_deform_aux_last_ne {r : ℕ}
    (degree : Fin (r + 1) → ℕ)
    (x : t99A01_piOne_attach_succ_retract_aux_Pre degree)
    (z : APMT99A01.Disk) (hx : x.1 = Sum.inr (Fin.last r, z)) :
    (z : ℂ) ≠ 0 := by
  apply t99A01_piOne_attach_succ_retract_aux_ne_zero degree z
  simpa [hx] using x.2

def t99A01_piOne_attach_succ_deform_aux_raw {r : ℕ}
    (degree : Fin (r + 1) → ℕ)
    (p : unitInterval × t99A01_piOne_attach_succ_retract_aux_Pre degree) :
    Sum Circle (Fin (r + 1) × APMT99A01.Disk) :=
  match hx : p.2.1 with
  | Sum.inl z => Sum.inl z
  | Sum.inr q =>
      if h : q.1 = Fin.last r then
        Sum.inr (q.1, ⟨
          (t99A01_piOne_attach_succ_deform_aux_scale p.1 (q.2 : ℂ) : ℂ) * q.2,
          by
            rw [Metric.mem_closedBall, dist_zero_right]
            apply t99A01_piOne_attach_succ_deform_aux_scale_norm p.1 _
              (t99A01_piOne_attach_succ_deform_aux_last_ne degree p.2 q.2
                (hx.trans (congrArg Sum.inr (Prod.ext h rfl))))
            have hq := q.2.property
            rw [Metric.mem_closedBall, dist_zero_right] at hq
            exact hq⟩)
      else Sum.inr q

lemma t99A01_piOne_attach_succ_deform_aux_raw_mem {r : ℕ}
    (degree : Fin (r + 1) → ℕ)
    (p : unitInterval × t99A01_piOne_attach_succ_retract_aux_Pre degree) :
    Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree p) ∈
      APMT99A01.succCircleSide degree := by
  rcases p with ⟨t, x⟩
  rcases x with ⟨x, hx⟩
  cases x with
  | inl z => simpa [t99A01_piOne_attach_succ_deform_aux_raw] using
      t99A01_piOne_attach_succ_retract_aux_circle_mem degree z
  | inr q =>
      rcases q with ⟨i, z⟩
      by_cases hi : i = Fin.last r
      · subst i
        intro he
        have hr := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp
          (Quotient.exact he.symm)
        simp only [t99A01_piOne_attach_succ_deform_aux_raw, dif_pos rfl] at hr
        have hp := Sum.inr.inj hr
        have hz := congrArg (fun w : APMT99A01.Disk => (w : ℂ)) (Prod.mk.inj hp).2
        simp only [t99A01_piOne_attach_succ_deform_aux_raw, dif_pos rfl] at hz
        exact (t99A01_piOne_attach_succ_deform_aux_scale_ne t _
          (t99A01_piOne_attach_succ_retract_aux_ne_zero degree z hx)) hz
      · simpa [t99A01_piOne_attach_succ_deform_aux_raw, hi] using hx

lemma t99A01_piOne_attach_succ_deform_aux_continuous {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    Continuous (t99A01_piOne_attach_succ_deform_aux_raw degree) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  rcases x with ⟨x, hx⟩
  cases x with
  | inl z =>
      let getZ : t99A01_piOne_attach_succ_retract_aux_Pre degree → Circle :=
        fun y => Sum.elim id (fun _ => z) y.1
      have hgetZ : Continuous getZ :=
        (continuous_sumElim.2 ⟨continuous_id, continuous_const⟩).comp continuous_subtype_val
      apply (continuous_inl.comp (hgetZ.comp continuous_snd)).continuousAt.congr_of_eventuallyEq
      have hopen := (isOpen_range_inl.preimage
        (continuous_subtype_val.comp continuous_snd)).mem_nhds
          (show (t, ⟨Sum.inl z, hx⟩) ∈
            (Subtype.val ∘ Prod.snd) ⁻¹' Set.range Sum.inl from ⟨z, rfl⟩)
      filter_upwards [hopen] with y hy
      rcases hy with ⟨w, hw⟩
      rcases y with ⟨s, ⟨u, hu⟩⟩
      dsimp at hw ⊢
      cases u <;> simp_all [t99A01_piOne_attach_succ_deform_aux_raw, getZ]
  | inr q =>
      rcases q with ⟨i, z⟩
      by_cases hi : i = Fin.last r
      · subst i
        let getZ : t99A01_piOne_attach_succ_retract_aux_Pre degree →
            APMT99A01.Disk := fun y => Sum.elim (fun _ => z)
              (fun p => if p.1 = Fin.last r then p.2 else z) y.1
        have hgetZ : Continuous getZ :=
          (continuous_sumElim.2 ⟨continuous_const,
            (continuous_prod_of_discrete_left.mpr (by
              intro j
              by_cases hj : j = Fin.last r
              · simpa [hj] using (continuous_id : Continuous (fun z : APMT99A01.Disk => z))
              · simpa [hj] using (continuous_const : Continuous (fun _ : APMT99A01.Disk => z))))⟩).comp
            continuous_subtype_val
        have hne : ∀ y, ((getZ y : APMT99A01.Disk) : ℂ) ≠ 0 := by
          intro y
          cases hy : y.1 with
          | inl w =>
              simpa [getZ, hy] using
                (t99A01_piOne_attach_succ_deform_aux_last_ne degree
                  ⟨Sum.inr (Fin.last r, z), hx⟩ z rfl)
          | inr p =>
              by_cases hp : p.1 = Fin.last r
              · simpa [getZ, hy, hp] using
                  (t99A01_piOne_attach_succ_deform_aux_last_ne degree y p.2
                    (hy.trans (congrArg Sum.inr (Prod.ext hp rfl))))
              · simpa [getZ, hy, hp] using
                  (t99A01_piOne_attach_succ_deform_aux_last_ne degree
                    ⟨Sum.inr (Fin.last r, z), hx⟩ z rfl)
        let diskMap : unitInterval × t99A01_piOne_attach_succ_retract_aux_Pre degree →
            APMT99A01.Disk := fun y => ⟨
          (t99A01_piOne_attach_succ_deform_aux_scale y.1 (getZ y.2 : ℂ) : ℂ) * getZ y.2,
          by
            rw [Metric.mem_closedBall, dist_zero_right]
            apply t99A01_piOne_attach_succ_deform_aux_scale_norm y.1 _ (hne y.2)
            have hz := (getZ y.2).property
            rw [Metric.mem_closedBall, dist_zero_right] at hz
            exact hz⟩
        have hdisk : Continuous diskMap := by
          apply Continuous.subtype_mk
          dsimp [diskMap, t99A01_piOne_attach_succ_deform_aux_scale]
          have hv : Continuous (fun y : unitInterval ×
              t99A01_piOne_attach_succ_retract_aux_Pre degree =>
              ((getZ y.2 : APMT99A01.Disk) : ℂ)) :=
            continuous_subtype_val.comp (hgetZ.comp continuous_snd)
          have hn := hv.norm
          have hn0 : ∀ y : unitInterval ×
              t99A01_piOne_attach_succ_retract_aux_Pre degree,
              ‖((getZ y.2 : APMT99A01.Disk) : ℂ)‖ ≠ 0 :=
            fun y => norm_ne_zero_iff.mpr (hne y.2)
          exact (Complex.continuous_ofReal.comp
            ((continuous_subtype_val.comp continuous_fst).add
              ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
                hn hn0))).mul hv
        have hc : Continuous (fun y =>
            (Sum.inr (Fin.last r, diskMap y) :
              Sum Circle (Fin (r + 1) × APMT99A01.Disk))) :=
          continuous_inr.comp (continuous_const.prodMk hdisk)
        apply hc.continuousAt.congr_of_eventuallyEq
        have hop : IsOpen (Sum.inr '' (({Fin.last r} : Set (Fin (r + 1))) ×ˢ
            (Set.univ : Set APMT99A01.Disk))) :=
          (isOpenMap_inr (X := Circle)) _ ((isOpen_discrete _).prod isOpen_univ)
        filter_upwards [((hop.preimage
          (continuous_subtype_val.comp continuous_snd)).mem_nhds (by simp))] with y hy
        obtain ⟨⟨j, w⟩, hjw, he⟩ := hy
        have hj : j = Fin.last r := by simpa using hjw.1
        subst j
        rcases y with ⟨s, ⟨u, hu⟩⟩
        dsimp at he ⊢
        cases u with
        | inl a => cases he
        | inr p =>
          rcases p with ⟨j, v⟩
          have hp : (Fin.last r, w) = (j, v) := Sum.inr.inj he
          have hj' : Fin.last r = j := congrArg Prod.fst hp
          have hv' : w = v := congrArg Prod.snd hp
          subst j
          subst v
          simp [t99A01_piOne_attach_succ_deform_aux_raw, diskMap, getZ]
      · let getQ : t99A01_piOne_attach_succ_retract_aux_Pre degree →
            Fin (r + 1) × APMT99A01.Disk :=
          fun y => Sum.elim (fun _ => (i, z)) id y.1
        have hgetQ : Continuous getQ :=
          (continuous_sumElim.2 ⟨continuous_const, continuous_id⟩).comp continuous_subtype_val
        let g : unitInterval × t99A01_piOne_attach_succ_retract_aux_Pre degree →
            Sum Circle (Fin (r + 1) × APMT99A01.Disk) :=
          fun y => Sum.inr (i, (getQ y.2).2)
        have hg : Continuous g := continuous_inr.comp
          (continuous_const.prodMk (hgetQ.snd.comp continuous_snd))
        apply hg.continuousAt.congr_of_eventuallyEq
        have hop : IsOpen (Sum.inr '' (({i} : Set (Fin (r + 1))) ×ˢ
            (Set.univ : Set APMT99A01.Disk))) :=
          (isOpenMap_inr (X := Circle)) _ ((isOpen_discrete _).prod isOpen_univ)
        filter_upwards [((hop.preimage
          (continuous_subtype_val.comp continuous_snd)).mem_nhds (by simp))] with y hy
        obtain ⟨⟨j, w⟩, hjw, he⟩ := hy
        have hj : j = i := by simpa using hjw.1
        subst j
        rcases y with ⟨s, ⟨u, hu⟩⟩
        dsimp at he ⊢
        cases u with
        | inl a => cases he
        | inr p =>
          rcases p with ⟨j, v⟩
          have hp : (i, w) = (j, v) := Sum.inr.inj he
          have hj' : i = j := congrArg Prod.fst hp
          have hv' : w = v := congrArg Prod.snd hp
          subst j
          subst v
          simp [t99A01_piOne_attach_succ_deform_aux_raw, g, getQ, hi]

lemma t99A01_piOne_attach_succ_deform_aux_respects {r : ℕ}
    (degree : Fin (r + 1) → ℕ) (t : unitInterval)
    (x y : t99A01_piOne_attach_succ_retract_aux_Pre degree)
    (hxy : t99A01_piOne_attach_succ_retract_aux_q degree x =
      t99A01_piOne_attach_succ_retract_aux_q degree y) :
    (Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree (t, x)) :
        APMT99A01.AttachSpace degree) =
      Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree (t, y)) := by
  have hxy' : Relation.EqvGen (APMT99A01.AttachRel degree) x.1 y.1 :=
    Quotient.exact (congrArg Subtype.val hxy)
  have hgen : ∀ a b, Relation.EqvGen (APMT99A01.AttachRel degree) a b →
      ∀ (ha : Quotient.mk _ a ∈ APMT99A01.succCircleSide degree)
        (hb : Quotient.mk _ b ∈ APMT99A01.succCircleSide degree),
      (Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree (t, ⟨a, ha⟩)) :
          APMT99A01.AttachSpace degree) =
        Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree (t, ⟨b, hb⟩)) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        intro ha hb
        cases hab with
        | boundary i z =>
          have hn : ‖(APMT99A01.circleInDisk z : ℂ)‖ = 1 := Circle.norm_coe z
          by_cases hi : i = Fin.last r
          · have hs : t99A01_piOne_attach_succ_deform_aux_scale t
                (APMT99A01.circleInDisk z : ℂ) = 1 := by
              simp [t99A01_piOne_attach_succ_deform_aux_scale, hn]
            apply Quotient.sound
            simpa [t99A01_piOne_attach_succ_deform_aux_raw, hi, hs] using
              (Relation.EqvGen.rel _ _
                (APMT99A01.AttachRel.boundary (degree := degree) i z))
          · apply Quotient.sound
            simpa [t99A01_piOne_attach_succ_deform_aux_raw, hi] using
              (Relation.EqvGen.rel _ _
                (APMT99A01.AttachRel.boundary (degree := degree) i z))
    | refl a => intro ha hb; rfl
    | symm a b hab ih => intro ha hb; exact (ih hb ha).symm
    | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hb : Quotient.mk _ b ∈ APMT99A01.succCircleSide degree := by
          rw [← Quotient.sound hab]
          exact ha
        exact (ih₁ ha hb).trans (ih₂ hb hc)
  exact hgen x.1 y.1 hxy' x.2 y.2

lemma t99A01_piOne_attach_succ_deform {r : ℕ} (degree : Fin (r + 1) → ℕ)
    (ι : C(APMT99A01.AttachSpace (degree ∘ Fin.castSucc), APMT99A01.succCircleSide degree))
    (hι : ∀ y, (ι y).1 = APMT99A01.attachCastSucc degree y) :
    ContinuousMap.Homotopic (ι.comp (t99A01_succRho degree)) (ContinuousMap.id _) := by
  let q := t99A01_piOne_attach_succ_retract_aux_q degree
  have hq := t99A01_piOne_attach_succ_retract_aux_q_quotient degree
  let s : APMT99A01.succCircleSide degree →
      t99A01_piOne_attach_succ_retract_aux_Pre degree :=
    fun x => Classical.choose (hq.surjective x)
  have hs (x : APMT99A01.succCircleSide degree) : q (s x) = x :=
    Classical.choose_spec (hq.surjective x)
  let F : unitInterval × APMT99A01.succCircleSide degree →
      APMT99A01.succCircleSide degree := fun p =>
    ⟨Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree (p.1, s p.2)),
      t99A01_piOne_attach_succ_deform_aux_raw_mem degree (p.1, s p.2)⟩
  have hFq (p : unitInterval × t99A01_piOne_attach_succ_retract_aux_Pre degree) :
      F (p.1, q p.2) =
        ⟨Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree p),
          t99A01_piOne_attach_succ_deform_aux_raw_mem degree p⟩ := by
    apply Subtype.ext
    exact t99A01_piOne_attach_succ_deform_aux_respects degree p.1
      (s (q p.2)) p.2 (hs (q p.2))
  have hF : Continuous F := by
    apply hq.continuous_lift_prod_right
    have hc : Continuous (fun p : unitInterval ×
        t99A01_piOne_attach_succ_retract_aux_Pre degree =>
        (⟨Quotient.mk _ (t99A01_piOne_attach_succ_deform_aux_raw degree p),
          t99A01_piOne_attach_succ_deform_aux_raw_mem degree p⟩ :
          APMT99A01.succCircleSide degree)) :=
      Continuous.subtype_mk (continuous_coinduced_rng.comp
        (t99A01_piOne_attach_succ_deform_aux_continuous degree)) _
    convert hc using 1
    funext p
    exact hFq p
  refine ⟨ContinuousMap.Homotopy.mk (f₀ := ι.comp (t99A01_succRho degree))
    (f₁ := ContinuousMap.id _) ⟨F, hF⟩ ?_ ?_⟩
  · intro x
    apply Subtype.ext
    change (F (0, x)).1 = _
    rw [show F (0, x) = F (0, q (s x)) by rw [hs x]]
    rw [congrArg Subtype.val (hFq (0, s x))]
    generalize hy : s x = y
    rcases y with ⟨y, hymem⟩
    cases y with
    | inl z =>
      simp only [t99A01_piOne_attach_succ_deform_aux_raw]
      change Quotient.mk _ (Sum.inl z) = (ι (t99A01_succRho degree x)).1
      rw [hι]
      have hx : x = ⟨Quotient.mk _ (Sum.inl z), hymem⟩ := (hy ▸ hs x).symm
      rw [hx]
      rfl
    | inr p =>
      rcases p with ⟨i, z⟩
      by_cases hi : i = Fin.last r
      · subst i
        have hval : (s x).1 = Sum.inr (Fin.last r, z) := congrArg Subtype.val hy
        have hz := t99A01_piOne_attach_succ_deform_aux_last_ne degree (s x) z hval
        have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz
        let w : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
          simp [Submonoid.unitSphere, div_self hn.ne']⟩
        have hs0 : t99A01_piOne_attach_succ_deform_aux_scale (0 : unitInterval)
            (z : ℂ) = 1 / ‖(z : ℂ)‖ := by
          simp [t99A01_piOne_attach_succ_deform_aux_scale]
        simp only [t99A01_piOne_attach_succ_deform_aux_raw, dif_pos rfl]
        have hx : x = ⟨Quotient.mk _ (Sum.inr (Fin.last r, z)), hymem⟩ :=
          (hy ▸ hs x).symm
        rw [hx]
        change Quotient.mk _ _ = (ι _).1
        rw [hι]
        dsimp [t99A01_succRho]
        simp only [Quotient.lift_mk,
          t99A01_piOne_attach_succ_retract_aux_raw, dif_pos rfl]
        change Quotient.mk _ _ = APMT99A01.attachCastSucc degree
          (Quotient.mk _ (Sum.inl
            (t99A01_piOne_attach_succ_retract_aux_radial (z : ℂ) ^
              degree (Fin.last r))))
        change Quotient.mk _ _ = Quotient.mk _ (Sum.inl
          (t99A01_piOne_attach_succ_retract_aux_radial (z : ℂ) ^
            degree (Fin.last r)))
        apply Quotient.sound
        have hb := (Relation.EqvGen.rel _ _
          (APMT99A01.AttachRel.boundary (degree := degree) (Fin.last r) w)).symm
        convert hb using 1
        apply congrArg (fun u => Sum.inr (Fin.last r, u))
        apply Subtype.ext
        simp [APMT99A01.circleInDisk, w, hs0, div_eq_mul_inv, mul_comm]
        apply congrArg Sum.inl
        apply congrArg (fun u : Circle => u ^ degree (Fin.last r))
        apply Subtype.ext
        simp [w, t99A01_piOne_attach_succ_retract_aux_radial, hz]
      · simp only [t99A01_piOne_attach_succ_deform_aux_raw, dif_neg hi]
        have hx : x = ⟨Quotient.mk _ (Sum.inr (i, z)), hymem⟩ := (hy ▸ hs x).symm
        rw [hx]
        change Quotient.mk _ (Sum.inr (i, z)) = (ι _).1
        rw [hι]
        dsimp [t99A01_succRho]
        simp only [Quotient.lift_mk,
          t99A01_piOne_attach_succ_retract_aux_raw, dif_neg hi]
        change Quotient.mk _ (Sum.inr (i, z)) = APMT99A01.attachCastSucc degree
          (Quotient.mk _ (Sum.inr (i.castPred hi, z)))
        simp [APMT99A01.attachCastSucc, APMT99A01.attachCastSuccRaw]
  · intro x
    apply Subtype.ext
    change (F (1, x)).1 = _
    rw [show F (1, x) = F (1, q (s x)) by rw [hs x]]
    rw [congrArg Subtype.val (hFq (1, s x))]
    have hone : t99A01_piOne_attach_succ_deform_aux_raw degree (1, s x) =
        (s x).1 := by
      generalize hy : s x = y
      rcases y with ⟨y, hm⟩
      cases y with
      | inl z => simp [t99A01_piOne_attach_succ_deform_aux_raw]
      | inr p =>
        rcases p with ⟨i, z⟩
        by_cases hi : i = Fin.last r
        · simp [t99A01_piOne_attach_succ_deform_aux_raw, hi,
            t99A01_piOne_attach_succ_deform_aux_scale]
        · simp [t99A01_piOne_attach_succ_deform_aux_raw, hi]
    exact (congrArg (Quotient.mk _) hone).trans (congrArg Subtype.val (hs x))

lemma t99A01_piOne_attach_succ_retract {r : ℕ} (degree : Fin (r + 1) → ℕ)
    :
    ∃ e : ContinuousMap.HomotopyEquiv (APMT99A01.succCircleSide degree)
        (APMT99A01.AttachSpace (degree ∘ Fin.castSucc)),
      (∀ z : Circle,
        (e.symm (Quotient.mk _ (Sum.inl z))).1 =
          APMT99A01.attachCastSucc degree (Quotient.mk _ (Sum.inl z))) ∧
      ∀ (w : Circle) (h : (Quotient.mk _ (Sum.inr (Fin.last r, (⟨(w : ℂ) / 2, by rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]; norm_num⟩ : APMT99A01.Disk))) : APMT99A01.AttachSpace degree) ∈ APMT99A01.succCircleSide degree),
        e ⟨(Quotient.mk _ (Sum.inr (Fin.last r, (⟨(w : ℂ) / 2, by rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]; norm_num⟩ : APMT99A01.Disk))) : APMT99A01.AttachSpace degree), h⟩ =
          Quotient.mk _ (Sum.inl (w ^ degree (Fin.last r))) := by
  obtain ⟨ι, hι⟩ := t99A01_piOne_attach_succ_iota degree
  refine ⟨{ toFun := t99A01_succRho degree, invFun := ι,
            left_inv := t99A01_piOne_attach_succ_deform degree ι hι,
            right_inv := by
              rw [t99A01_piOne_attach_succ_rho_iota degree ι hι] }, ?_, ?_⟩
  · intro z
    exact hι _
  · intro w h
    exact t99A01_piOne_attach_succ_retract_aux_raw_half degree w
/-- **Leaf (overlap winding, 60--120 lines).**  After the preceding radial
identification, the positive overlap generator is the `degree last` power of
the fixed base-circle class.  The hypotheses make this leaf independent of
the cover and retraction proofs. -/
lemma t99A01_piOne_attach_succ_loop {r : ℕ} (degree : Fin (r + 1) → ℕ)
    (G : Type*) [Group G]
    (overlapGenerator : G)
    (overlapToSmall : G →* FundamentalGroup
      (APMT99A01.AttachSpace (degree ∘ Fin.castSucc))
      (APMT99A01.basepoint (degree ∘ Fin.castSucc)))
    (hcyclic : ∀ x : G, ∃ n : ℤ, overlapGenerator ^ n = x)
    (hwinding : overlapToSmall overlapGenerator =
      APMT99A01.baseCircleClass (degree ∘ Fin.castSucc) ^
        (degree (Fin.last r) : ℤ)) :
    Subgroup.normalClosure (overlapToSmall.range : Set _) =
      Subgroup.normalClosure
        ({APMT99A01.baseCircleClass (degree ∘ Fin.castSucc) ^
          (degree (Fin.last r) : ℤ)} : Set _) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro y ⟨x, rfl⟩
    rcases hcyclic x with ⟨n, hn⟩
    rw [← hn, map_zpow, hwinding]
    exact (Subgroup.normalClosure
      ({APMT99A01.baseCircleClass (degree ∘ Fin.castSucc) ^
        (degree (Fin.last r) : ℤ)} : Set _)).zpow_mem
          (Subgroup.subset_normalClosure (Set.mem_singleton _)) n
  · apply Subgroup.normalClosure_mono
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [← hwinding]
    exact ⟨overlapGenerator, rfl⟩

/-- **Leaf (cyclic quotient algebra, 50--100 lines).**  Killing `d` times the
chosen generator changes modulus `g` to `gcd g d`, and preserves the class of
one. -/
lemma t99A01_piOne_attach_succ_algebra_aux_normalClosure
    {A : Type*} [CommGroup A] (a : A) :
    Subgroup.normalClosure ({a} : Set A) = Subgroup.closure {a} := by
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal Subgroup.subset_closure
  · exact (Subgroup.closure_le _).2 Subgroup.subset_normalClosure

lemma t99A01_piOne_attach_succ_algebra (g d : ℕ) :
    ∃ e : (Multiplicative (ZMod g) ⧸
        Subgroup.normalClosure ({Multiplicative.ofAdd (d : ZMod g)} :
          Set (Multiplicative (ZMod g)))) ≃*
        Multiplicative (ZMod (Nat.gcd g d)),
      e (QuotientGroup.mk' _ (Multiplicative.ofAdd 1)) =
        Multiplicative.ofAdd 1 := by
  let q := Nat.gcd g d
  have hqg : q ∣ g := Nat.gcd_dvd_left g d
  let fAdd : ZMod g →+ ZMod q := (ZMod.castHom hqg (ZMod q)).toAddMonoidHom
  let f : Multiplicative (ZMod g) →* Multiplicative (ZMod q) :=
    AddMonoidHom.toMultiplicative fAdd
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y.toAdd
    exact ⟨Multiplicative.ofAdd (n : ZMod g), by
      change fAdd (n : ZMod g) = (n : ZMod q)
      simp [fAdd]⟩
  have hker : MonoidHom.ker f =
      Subgroup.normalClosure ({Multiplicative.ofAdd (d : ZMod g)} : Set _) := by
    rw [t99A01_piOne_attach_succ_algebra_aux_normalClosure]
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective x.toAdd
      have hzero : (n : ZMod q) = 0 := by
        have := hx
        change f x = 1 at this
        have hrepr : Multiplicative.ofAdd x.toAdd = x := rfl
        rw [← hrepr, ← hn] at this
        exact congrArg Multiplicative.toAdd (by simpa [f, fAdd] using this)
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd n q).mp hzero
      rw [Subgroup.mem_closure_singleton]
      refine ⟨k * Nat.gcdB g d, ?_⟩
      have hadd : (k * Nat.gcdB g d) • (d : ZMod g) = x.toAdd := by
        rw [← hn]
        rw [hk]
        simp only [zsmul_eq_mul]
        push_cast
        have hb := Nat.gcd_eq_gcd_ab g d
        push_cast at hb
        change (q : ℤ) = (g : ℤ) * Nat.gcdA g d +
          (d : ℤ) * Nat.gcdB g d at hb
        have hb' := congrArg (fun z : ℤ => (z : ZMod g)) hb
        norm_num at hb'
        rw [hb']
        simp [add_mul, mul_assoc, mul_comm, mul_left_comm]
      change Multiplicative.ofAdd (((k * Nat.gcdB g d) : ℤ) • (d : ZMod g)) = x
      simpa [mul_comm] using congrArg Multiplicative.ofAdd hadd
    · intro hx
      rw [Subgroup.mem_closure_singleton] at hx
      rcases hx with ⟨n, rfl⟩
      change f (Multiplicative.ofAdd (d : ZMod g) ^ n) = 1
      rw [map_zpow]
      suffices f (Multiplicative.ofAdd (d : ZMod g)) = 1 by simp [this]
      apply congrArg Multiplicative.toAdd
      change fAdd (d : ZMod g) = 0
      simpa [fAdd] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) q).2
          (Int.ofNat_dvd.2 (Nat.gcd_dvd_right g d))
  let E := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  refine ⟨E, ?_⟩
  change E (QuotientGroup.mk' _ (Multiplicative.ofAdd 1)) = _
  change f (Multiplicative.ofAdd 1) = Multiplicative.ofAdd 1
  apply congrArg Multiplicative.toAdd
  change fAdd (1 : ZMod g) = (1 : ZMod q)
  exact ZMod.cast_one hqg

/-- The one-cell step is the sorry-free assembly of the four leaves above. -/
lemma t99A01_piOne_attach_succ_aux_gcd {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    APMT99A01.degreeGCD degree =
      Nat.gcd (APMT99A01.degreeGCD (degree ∘ Fin.castSucc))
        (degree (Fin.last r)) := by
  simp only [APMT99A01.degreeGCD]
  rw [Fin.univ_castSuccEmb, Finset.gcd_cons]
  simp [Finset.gcd_def, Function.comp_def, Nat.gcd_comm]
  rfl

/-- The remaining geometric bridge: van Kampen, the radial equivalence, and
basepoint transport identify the newly killed overlap class with `d` times
the normalized generator supplied by the induction hypothesis. -/
noncomputable def t99A01_piOne_attach_succ_aux_vankampen_aux_point {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    (APMT99A01.succCircleSide degree ∩ APMT99A01.succDiskSide degree :
      Set (APMT99A01.AttachSpace degree)) := by
  let z : APMT99A01.Disk :=
    ⟨(1 : ℂ) / 2, by
      rw [Metric.mem_closedBall, dist_zero_right, norm_div]
      norm_num⟩
  let q : APMT99A01.AttachSpace degree :=
    Quotient.mk _ (Sum.inr (Fin.last r, z))
  refine ⟨q, ?_, ?_⟩
  · intro hq
    have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
        (Sum.inr (Fin.last r,
          (⟨0, by simp [Metric.mem_closedBall]⟩ : APMT99A01.Disk)))
        (Sum.inr (Fin.last r, z)) := Quotient.exact hq.symm
    have he := (t99A01_piOne_attach_succ_cover_aux_centre degree _).mp hr
    have hp := Sum.inr.inj he.symm
    have hz : (0 : ℂ) = 1 / 2 :=
      congrArg (fun x : Fin (r + 1) × APMT99A01.Disk ↦ (x.2 : ℂ)) hp
    norm_num at hz
  · exact ⟨z, by norm_num [z], rfl⟩

lemma t99A01_piOne_attach_succ_aux_vankampen_aux_apply {r : ℕ}
    (degree : Fin (r + 1) → ℕ) :
    Nonempty
      (FundamentalGroup (APMT99A01.AttachSpace degree)
          (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree).1 ≃*
        (FundamentalGroup (APMT99A01.succCircleSide degree)
            (apm_t92J05_twoOpen_overlapToLeft
              (APMT99A01.succCircleSide degree) (APMT99A01.succDiskSide degree)
              (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree))) ⧸
          Subgroup.normalClosure
            ((FundamentalGroup.map
              (apm_t92J05_twoOpen_overlapToLeft
                (APMT99A01.succCircleSide degree) (APMT99A01.succDiskSide degree))
              (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree)).range : Set _)) := by
  obtain ⟨hU, hV, hcover, _, hUV, hUc, hVc, hVs⟩ :=
    t99A01_piOne_attach_succ_cover degree
  letI : PathConnectedSpace (APMT99A01.succCircleSide degree) :=
    isPathConnected_iff_pathConnectedSpace.mp hUc
  letI : PathConnectedSpace (APMT99A01.succDiskSide degree) :=
    isPathConnected_iff_pathConnectedSpace.mp hVc
  letI : PathConnectedSpace
      (APMT99A01.succCircleSide degree ∩ APMT99A01.succDiskSide degree : Set _) :=
    isPathConnected_iff_pathConnectedSpace.mp hUV
  letI : SimplyConnectedSpace (APMT99A01.succDiskSide degree) := hVs
  exact apm_t92J05_twoOpen_attach_one_cell
    (APMT99A01.succCircleSide degree) (APMT99A01.succDiskSide degree)
    hU hV hcover (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree)

lemma t99A01_piOne_attach_succ_aux_vankampen_aux_piOneOfHomotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y (h x)) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv h
  let ff := E.fullyFaithfulFunctor
  let m := FundamentalGroup.map h.toFun x
  exact ⟨
    { toFun := m
      invFun := fun g ↦ ff.preimage g
      left_inv := fun g ↦ ff.preimage_map g
      right_inv := fun g ↦ ff.map_preimage g
      map_mul' := m.map_mul }⟩

/-- **Leaf (overlap generator + winding).** The overlap (the punctured last disk) has
cyclic π₁ generated by the half-radius loop `w ↦ [last, w/2]`, and the radial retraction
sends it to the base circle loop to the power `degree last` (pointwise `w ↦ [inl (w^d)]`;
the basepoint `pt = [last, 1/2]` goes to `[inl 1]`).  Punctured disk ≃ₕ circle: radial
projection, as in `t99A01_pball_circle`; winding of `z ↦ z^d`: `t99A01_circlePower_hOne_row`'s
sources (`T97A04Closure.circleZPow`) or `CircleUniversalCover`. -/
def t99A01_succ_overlap_generator_aux_pball : Set ℂ :=
  {z | 0 < ‖z‖ ∧ ‖z‖ < 1}

theorem t99A01_succ_overlap_generator_aux_pball_circle :
    ∃ e : ContinuousMap.HomotopyEquiv
        ↥t99A01_succ_overlap_generator_aux_pball Circle,
      ∀ w : Circle,
        ((e.invFun w : ↥t99A01_succ_overlap_generator_aux_pball) : ℂ) =
          (w : ℂ) / 2 := by
  let radial : C(↥t99A01_succ_overlap_generator_aux_pball, Circle) :=
    ⟨fun z => ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
        simp [Submonoid.unitSphere, div_self (ne_of_gt z.2.1)]⟩, by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.div₀
        (Complex.continuous_ofReal.comp
          (continuous_norm.comp continuous_subtype_val))
        (fun z => by exact_mod_cast ne_of_gt z.2.1)⟩
  let half : C(Circle, ↥t99A01_succ_overlap_generator_aux_pball) :=
    ⟨fun w => ⟨(w : ℂ) / 2, by
        change 0 < ‖(w : ℂ) / 2‖ ∧ ‖(w : ℂ) / 2‖ < 1
        rw [norm_div, Circle.norm_coe]
        norm_num⟩, by
      exact Continuous.subtype_mk (continuous_subtype_val.div_const 2) _⟩
  have hradial_half : radial.comp half = ContinuousMap.id Circle := by
    apply ContinuousMap.ext
    intro w
    apply Subtype.ext
    change ((w : ℂ) / 2) / (‖(w : ℂ) / 2‖ : ℂ) = (w : ℂ)
    rw [norm_div, Circle.norm_coe]
    norm_num [div_div]
  let H : ContinuousMap.Homotopy (half.comp radial)
      (ContinuousMap.id ↥t99A01_succ_overlap_generator_aux_pball) := {
    toFun := fun (tx : unitInterval ×
        ↥t99A01_succ_overlap_generator_aux_pball) => by
      let t : ℝ := tx.1
      let x : ℂ := tx.2
      let a : ℝ := (1 - t) * (1 / (2 * ‖x‖)) + t
      refine ⟨(a : ℂ) * x, ?_⟩
      have ht0 : 0 ≤ t := tx.1.2.1
      have ht1 : t ≤ 1 := tx.1.2.2
      have hx0 : 0 < ‖x‖ := tx.2.2.1
      have hx1 : ‖x‖ < 1 := tx.2.2.2
      have ha0 : 0 ≤ a := by
        dsimp [a]
        have hden : 0 ≤ 1 / (2 * ‖x‖) :=
          (one_div_pos.mpr (mul_pos (by norm_num) hx0)).le
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hden) ht0
      have hamul : a * ‖x‖ = (1 - t) / 2 + t * ‖x‖ := by
        dsimp [a]
        field_simp
      change 0 < ‖(a : ℂ) * x‖ ∧ ‖(a : ℂ) * x‖ < 1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0,
        hamul]
      constructor <;> nlinarith
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hnorm : Continuous (fun tx : unitInterval ×
          ↥t99A01_succ_overlap_generator_aux_pball => ‖(tx.2 : ℂ)‖) :=
        continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
      have hne : ∀ tx : unitInterval ×
          ↥t99A01_succ_overlap_generator_aux_pball,
          2 * ‖(tx.2 : ℂ)‖ ≠ 0 := by
        intro tx
        exact mul_ne_zero (by norm_num) (ne_of_gt tx.2.2.1)
      have ht : Continuous (fun tx : unitInterval ×
          ↥t99A01_succ_overlap_generator_aux_pball => (tx.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hx : Continuous (fun tx : unitInterval ×
          ↥t99A01_succ_overlap_generator_aux_pball => (tx.2 : ℂ)) :=
        continuous_subtype_val.comp continuous_snd
      exact (Complex.continuous_ofReal.comp
        (((continuous_const.sub ht).mul
          (continuous_const.div (continuous_const.mul hnorm) hne)).add ht)).mul hx
    map_zero_left x := by
      apply Subtype.ext
      dsimp [half, radial]
      simp only [sub_zero, one_mul, add_zero]
      change (((1 : ℝ) / (2 * ‖(x : ℂ)‖) : ℝ) : ℂ) * (x : ℂ) =
        (x : ℂ) / (‖(x : ℂ)‖ : ℂ) / 2
      push_cast
      field_simp
    map_one_left x := by
      apply Subtype.ext
      simp }
  refine ⟨⟨radial, half, ⟨H⟩, ?_⟩, ?_⟩
  · rw [hradial_half]
  · intro w
    rfl

lemma t99A01_succ_overlap_generator {r : ℕ} (degree : Fin (r + 1) → ℕ) :
    ∃ (γ : FundamentalGroup ↥((APMT99A01.succCircleSide degree) ∩ (APMT99A01.succDiskSide degree)) (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree))
      (h : ((t99A01_succRho degree).comp (apm_t92J05_twoOpen_overlapToLeft (APMT99A01.succCircleSide degree) (APMT99A01.succDiskSide degree))) (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree) =
        APMT99A01.basepoint (degree ∘ Fin.castSucc)),
      (∀ y, ∃ n : ℤ, γ ^ n = y) ∧
      FundamentalGroup.mapOfEq ((t99A01_succRho degree).comp (apm_t92J05_twoOpen_overlapToLeft (APMT99A01.succCircleSide degree) (APMT99A01.succDiskSide degree))) h γ =
        APMT99A01.baseCircleClass (degree ∘ Fin.castSucc) ^ (degree (Fin.last r) : ℤ) := by
  sorry
lemma t99A01_piOne_attach_succ_aux_vankampen {r : ℕ}
    (degree : Fin (r + 1) → ℕ)
    (hgen : ∃ (γ : FundamentalGroup ↥((APMT99A01.succCircleSide degree) ∩ (APMT99A01.succDiskSide degree)) (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree))
      (h : ((t99A01_succRho degree).comp (apm_t92J05_twoOpen_overlapToLeft (APMT99A01.succCircleSide degree) (APMT99A01.succDiskSide degree))) (t99A01_piOne_attach_succ_aux_vankampen_aux_point degree) =
        APMT99A01.basepoint (degree ∘ Fin.castSucc)),
      (∀ y, ∃ n : ℤ, γ ^ n = y) ∧
      FundamentalGroup.mapOfEq ((t99A01_succRho degree).comp (apm_t92J05_twoOpen_overlapToLeft (APMT99A01.succCircleSide degree) (APMT99A01.succDiskSide degree))) h γ =
        APMT99A01.baseCircleClass (degree ∘ Fin.castSucc) ^ (degree (Fin.last r) : ℤ))
    (ih : APMT99A01.PiOneCoordinate (degree ∘ Fin.castSucc)) :
    ∃ e : FundamentalGroup (APMT99A01.AttachSpace degree)
          (APMT99A01.basepoint degree) ≃*
        (Multiplicative
            (ZMod (APMT99A01.degreeGCD (degree ∘ Fin.castSucc))) ⧸
          Subgroup.normalClosure
            ({Multiplicative.ofAdd
                (degree (Fin.last r) :
                  ZMod (APMT99A01.degreeGCD (degree ∘ Fin.castSucc)))} :
              Set (Multiplicative
                (ZMod (APMT99A01.degreeGCD (degree ∘ Fin.castSucc)))))),
      e (APMT99A01.baseCircleClass degree) =
        QuotientGroup.mk' _ (Multiplicative.ofAdd 1) := by
  sorry
lemma t99A01_piOne_attach_succ {r : ℕ} (degree : Fin (r + 1) → ℕ)
    (_hpos : ∀ i, 0 < degree i)
    (ih : APMT99A01.PiOneCoordinate (degree ∘ Fin.castSucc)) :
    APMT99A01.PiOneCoordinate degree := by
  obtain ⟨eVK, heVK⟩ :=
    t99A01_piOne_attach_succ_aux_vankampen degree (t99A01_succ_overlap_generator degree) ih
  obtain ⟨eAlg, heAlg⟩ := t99A01_piOne_attach_succ_algebra
    (APMT99A01.degreeGCD (degree ∘ Fin.castSucc))
    (degree (Fin.last r))
  unfold APMT99A01.PiOneCoordinate
  rw [t99A01_piOne_attach_succ_aux_gcd degree]
  refine ⟨eVK.trans eAlg, ?_⟩
  change eAlg (eVK (APMT99A01.baseCircleClass degree)) = _
  rw [heVK, heAlg]
/-- Fundamental group of a circle with finitely many positive-degree disks
attached.  This is a sorry-free induction assembling the two geometric leaves
above; in particular it also covers `r = 0`. -/
theorem t99A01_piOne_attach {r : ℕ} (degree : Fin r → ℕ)
    (hpos : ∀ i, 0 < degree i) :
    APMT99A01.PiOneCoordinate degree := by
  induction r with
  | zero => exact t99A01_piOne_attach_empty degree
  | succ r ih =>
      apply t99A01_piOne_attach_succ degree hpos
      apply ih (degree ∘ Fin.castSucc)
      intro i
      exact hpos (Fin.castSucc i)

/-- Algebraic specialization of the generic attaching-space theorem. -/
theorem t99A01_piOne_X :
    Nonempty (FundamentalGroup APMT99A01.X
      (APMT99A01.basepoint APMT99A01.degreeX) ≃*
        Multiplicative (ZMod 2)) := by
  rcases t99A01_piOne_attach APMT99A01.degreeX (by simp [APMT99A01.degreeX]) with
    ⟨e, _⟩
  exact ⟨by simpa [APMT99A01.X, APMT99A01.degreeX, APMT99A01.degreeGCD] using e⟩

/-- **LIBRARY boundary.** Van Kampen for the quotient with degree-two and
degree-four cells. -/
theorem t99A01_piOne_Y :
    Nonempty (FundamentalGroup APMT99A01.Y
      (APMT99A01.basepoint APMT99A01.degreeY) ≃*
        Multiplicative (ZMod 2)) := by
  rcases t99A01_piOne_attach APMT99A01.degreeY (by simp [APMT99A01.degreeY]) with
    ⟨e, _⟩
  exact ⟨by simpa [APMT99A01.Y, APMT99A01.degreeY, APMT99A01.degreeGCD] using e⟩

/-- **LIBRARY boundary.** Van Kampen for the quotient with cells of degrees
two, four, and five. -/
theorem t99A01_piOne_Z :
    Subsingleton (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ)) := by
  have h : Nonempty (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ) ≃*
        Multiplicative (ZMod 1)) := by
    rcases t99A01_piOne_attach APMT99A01.degreeZ (by
      intro i
      fin_cases i <;> norm_num [APMT99A01.degreeZ]) with ⟨e, _⟩
    exact ⟨by simpa [APMT99A01.Z, APMT99A01.degreeZ,
      APMT99A01.degreeGCD] using e⟩
  rcases h with ⟨e⟩
  constructor
  intro a b
  apply e.injective
  haveI : Subsingleton (Multiplicative (ZMod 1)) := inferInstance
  exact Subsingleton.elim _ _

/-! ### Generic integral homology calculation

The geometry is factored through one coordinate-level Mayer--Vietoris record.
In particular, none of the four diagram chases below has to reconstruct the
quotient cover or calculate the winding number of an attaching map. -/

namespace APMT99A01

/-- The integral Mayer--Vietoris data needed for the attaching-space
calculation.  The names `i₁`, `j₁`, `δ₁`, ... follow the consecutive arrows
in the long exact sequence.  Coordinates identify `H₁(A ∩ B)` with `ℤ^r`,
`H₁(A) ⊕ H₁(B)` with `ℤ`, and `H₀(A ∩ B)` with `ℤ^r`. -/
structure AttachMVData {r : ℕ} (degree : Fin r → ℕ) where
  i₁ : (Fin r → ℤ) →ₗ[ℤ] ℤ
  j₁ : ℤ →ₗ[ℤ] (H 1 (AttachSpace degree))
  δ₁ : (H 1 (AttachSpace degree)) →ₗ[ℤ] (Fin r → ℤ)
  i₀ : (Fin r → ℤ) →ₗ[ℤ] (ℤ × (Fin r → ℤ))
  j₀ : (ℤ × (Fin r → ℤ)) →ₗ[ℤ] (H 0 (AttachSpace degree))
  δ₂ : (H 2 (AttachSpace degree)) →ₗ[ℤ] (Fin r → ℤ)
  i₁_eq_degreeMap : i₁ = degreeMap degree
  i₀_injective : Function.Injective i₀
  /-- Each overlap component maps to the (connected) circle side and to its own disk. -/
  i₀_eq : ∀ x, i₀ x = (∑ i, x i, x)
  exact_i₁_j₁ : LinearMap.range i₁ = LinearMap.ker j₁
  exact_j₁_δ₁ : LinearMap.range j₁ = LinearMap.ker δ₁
  exact_δ₁_i₀ : LinearMap.range δ₁ = LinearMap.ker i₀
  exact_i₀_j₀ : LinearMap.range i₀ = LinearMap.ker j₀
  j₀_surjective : Function.Surjective j₀
  δ₂_injective : Function.Injective δ₂
  exact_δ₂_i₁ : LinearMap.range δ₂ = LinearMap.ker i₁
  higher : ∀ k : ℕ, 3 ≤ k → Limits.IsZero (H k (AttachSpace degree))

/-- The low-degree part of `AttachMVData`.  It is separated from higher
vanishing so that the Mayer--Vietoris diagram chase and the dimension argument
can be proved independently. -/
structure AttachMVLowData {r : ℕ} (degree : Fin r → ℕ) where
  i₁ : (Fin r → ℤ) →ₗ[ℤ] ℤ
  j₁ : ℤ →ₗ[ℤ] (H 1 (AttachSpace degree))
  δ₁ : (H 1 (AttachSpace degree)) →ₗ[ℤ] (Fin r → ℤ)
  i₀ : (Fin r → ℤ) →ₗ[ℤ] (ℤ × (Fin r → ℤ))
  j₀ : (ℤ × (Fin r → ℤ)) →ₗ[ℤ] (H 0 (AttachSpace degree))
  δ₂ : (H 2 (AttachSpace degree)) →ₗ[ℤ] (Fin r → ℤ)
  i₁_eq_degreeMap : i₁ = degreeMap degree
  i₀_injective : Function.Injective i₀
  i₀_eq : ∀ x, i₀ x = (∑ i, x i, x)
  exact_i₁_j₁ : LinearMap.range i₁ = LinearMap.ker j₁
  exact_j₁_δ₁ : LinearMap.range j₁ = LinearMap.ker δ₁
  exact_δ₁_i₀ : LinearMap.range δ₁ = LinearMap.ker i₀
  exact_i₀_j₀ : LinearMap.range i₀ = LinearMap.ker j₀
  j₀_surjective : Function.Surjective j₀
  δ₂_injective : Function.Injective δ₂
  exact_δ₂_i₁ : LinearMap.range δ₂ = LinearMap.ker i₁

end APMT99A01

namespace APMT99A01

variable {r : ℕ} (degree : Fin r → ℕ)

/-- The quotient map of the attaching space. -/
def attachMk (x : Sum Circle (Fin r × Disk)) : AttachSpace degree :=
  Quotient.mk _ x

lemma continuous_attachMk : Continuous (attachMk degree) :=
  continuous_coinduced_rng

/-- The centre of the unit disk. -/
def diskCentre : Disk := ⟨0, by simp⟩

/-- The point `w / 2` of the unit disk. -/
def halfPoint (w : Circle) : Disk :=
  ⟨(w : ℂ) / 2, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]
    norm_num⟩

lemma continuous_halfPoint : Continuous halfPoint :=
  Continuous.subtype_mk (continuous_subtype_val.div_const 2) _

/-- Circle side of the standard cover: everything except the disk centres. -/
def sideA : Set (AttachSpace degree) :=
  {q | ∀ i, q ≠ attachMk degree (Sum.inr (i, diskCentre))}

/-- Disk side of the standard cover: the open disk interiors. -/
def sideB : Set (AttachSpace degree) :=
  {q | ∃ (i : Fin r) (z : Disk), ‖(z : ℂ)‖ < 1 ∧ q = attachMk degree (Sum.inr (i, z))}

/-- The base circle in the attaching space. -/
def circleIncl : C(Circle, AttachSpace degree) :=
  ⟨fun z ↦ attachMk degree (Sum.inl z), (continuous_attachMk degree).comp continuous_inl⟩

/-- The circle of radius `1/2` in the `i`-th disk. -/
def halfLoop (i : Fin r) : C(Circle, AttachSpace degree) :=
  ⟨fun w ↦ attachMk degree (Sum.inr (i, halfPoint w)),
    (continuous_attachMk degree).comp
      (continuous_inr.comp (continuous_const.prodMk continuous_halfPoint))⟩

/-! Integral Mayer–Vietoris maps (ℤ analogues of `RP3Homology.mvI`/`mvJ`). -/

/-- Homology map of a subset inclusion. -/
def zIncl {X : Type} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    H n S ⟶ H n T :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
      ⟨Set.inclusion h, continuous_inclusion h⟩) n

/-- Homology map of a subset into the whole space. -/
def zToX {X : Type} [TopologicalSpace X] (S : Set X) (n : ℕ) : H n S ⟶ H n X :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
      ⟨Subtype.val, continuous_subtype_val⟩) n

def zI {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    H n ↥(U ∩ V) ⟶ H n U ⊞ H n V :=
  Limits.biprod.lift (zIncl Set.inter_subset_left n) (zIncl Set.inter_subset_right n)

def zJ {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    H n U ⊞ H n V ⟶ H n X :=
  Limits.biprod.desc (zToX U n) (-(zToX V n))

end APMT99A01

/-- **Leaf (quotient topology, 60--120 lines).** The standard cover is an open
cover.  `sideA` is the complement of finitely many closed points (each centre's
class is a singleton, so its preimage is one point); `sideB`'s preimage is the
union of the open disk interiors, because only boundary points of a disk are
identified with circle points.  Use `isOpen_coinduced`, `Relation.EqvGen`
induction on `AttachRel`. -/
lemma t99A01_attach_openCover_aux_centre {r : ℕ} (degree : Fin r → ℕ)
    (i : Fin r) (x : Sum Circle (Fin r × APMT99A01.Disk)) :
    Relation.EqvGen (APMT99A01.AttachRel degree)
        (Sum.inr (i, APMT99A01.diskCentre)) x ↔
      x = Sum.inr (i, APMT99A01.diskCentre) := by
  let P := fun x : Sum Circle (Fin r × APMT99A01.Disk) =>
    x = Sum.inr (i, APMT99A01.diskCentre)
  have hrel : ∀ a b, APMT99A01.AttachRel degree a b → (P a ↔ P b) := by
    intro a b h
    cases h with
    | boundary j z =>
      constructor
      · intro h
        cases h
      · intro h
        have hz : APMT99A01.circleInDisk z ≠ APMT99A01.diskCentre := by
          intro he
          have hv := congrArg (fun w : APMT99A01.Disk => (w : ℂ)) he
          change (z : ℂ) = 0 at hv
          have := Circle.norm_coe z
          rw [hv, norm_zero] at this
          norm_num at this
        have hp : (j, APMT99A01.circleInDisk z) =
            (i, APMT99A01.diskCentre) := Sum.inr.inj h
        exact False.elim (hz (Prod.mk.inj hp).2)
  constructor
  · intro h
    have hinv : ∀ a b, Relation.EqvGen (APMT99A01.AttachRel degree) a b →
        (P a ↔ P b) := by
      intro a b hab
      induction hab with
      | rel a b hab => exact hrel a b hab
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (hinv _ _ h).mp rfl
  · rintro rfl
    exact Relation.EqvGen.refl _

lemma t99A01_attach_openCover_aux_interior {r : ℕ} (degree : Fin r → ℕ)
    (x y : Sum Circle (Fin r × APMT99A01.Disk))
    (h : Relation.EqvGen (APMT99A01.AttachRel degree) x y) :
    (∃ (i : Fin r) (z : APMT99A01.Disk), ‖(z : ℂ)‖ < 1 ∧ x = Sum.inr (i, z)) ↔
      ∃ (i : Fin r) (z : APMT99A01.Disk), ‖(z : ℂ)‖ < 1 ∧ y = Sum.inr (i, z) := by
  let P := fun x : Sum Circle (Fin r × APMT99A01.Disk) =>
    ∃ (i : Fin r) (z : APMT99A01.Disk), ‖(z : ℂ)‖ < 1 ∧ x = Sum.inr (i, z)
  have hrel : ∀ a b, APMT99A01.AttachRel degree a b → (P a ↔ P b) := by
    intro a b hab
    cases hab with
    | boundary i z =>
      constructor
      · rintro ⟨j, w, hw, hbad⟩
        cases hbad
      · rintro ⟨j, w, hw, he⟩
        have hp : (i, APMT99A01.circleInDisk z) = (j, w) := Sum.inr.inj he
        have hij : i = j := (Prod.mk.inj hp).1
        subst j
        have hw' : w = APMT99A01.circleInDisk z := (Prod.mk.inj hp).2.symm
        subst w
        simp [APMT99A01.circleInDisk, Circle.norm_coe] at hw
  induction h with
  | rel a b hab => exact hrel a b hab
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem t99A01_attach_openCover {r : ℕ} (degree : Fin r → ℕ) :
    IsOpen (APMT99A01.sideA degree) ∧ IsOpen (APMT99A01.sideB degree) ∧
      APMT99A01.sideA degree ∪ APMT99A01.sideB degree = Set.univ := by
  have hApre : (APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideA degree =
      {x | ∀ i : Fin r, x ≠ Sum.inr (i, APMT99A01.diskCentre)} := by
    ext x
    simp only [Set.mem_preimage, APMT99A01.sideA, Set.mem_setOf_eq]
    constructor
    · intro h i he
      apply h i
      apply Quotient.sound
      rw [he]
    · intro h i he
      apply h i
      have heq : Relation.EqvGen (APMT99A01.AttachRel degree)
          (Sum.inr (i, APMT99A01.diskCentre)) x := (Quotient.exact he.symm)
      exact (t99A01_attach_openCover_aux_centre degree i x).mp heq
  have hBpre : (APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideB degree =
      {x | ∃ (i : Fin r) (z : APMT99A01.Disk),
        ‖(z : ℂ)‖ < 1 ∧ x = Sum.inr (i, z)} := by
    ext x
    simp only [Set.mem_preimage, APMT99A01.sideB, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, z, hz, he⟩
      have hr : Relation.EqvGen (APMT99A01.AttachRel degree) x (Sum.inr (i, z)) :=
        Quotient.exact he
      exact (t99A01_attach_openCover_aux_interior degree x _ hr).mpr ⟨i, z, hz, rfl⟩
    · rintro ⟨i, z, hz, rfl⟩
      exact ⟨i, z, hz, rfl⟩
  have hA : IsOpen (APMT99A01.sideA degree) := by
    rw [isOpen_coinduced]
    change IsOpen ((APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideA degree)
    rw [hApre]
    have heq : {x : Sum Circle (Fin r × APMT99A01.Disk) |
        ∀ i : Fin r, x ≠ Sum.inr (i, APMT99A01.diskCentre)} =
        ⋂ i : Fin r, ({Sum.inr (i, APMT99A01.diskCentre)}ᶜ :
          Set (Sum Circle (Fin r × APMT99A01.Disk))) := by
      ext x
      simp
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_compl_singleton
  have hB : IsOpen (APMT99A01.sideB degree) := by
    rw [isOpen_coinduced]
    change IsOpen ((APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideB degree)
    rw [hBpre, isOpen_sum_iff]
    constructor
    · simp
    · have heq : Sum.inr ⁻¹' {x : Sum Circle (Fin r × APMT99A01.Disk) |
          ∃ (i : Fin r) (z : APMT99A01.Disk), ‖(z : ℂ)‖ < 1 ∧ x = Sum.inr (i, z)} =
          {p : Fin r × APMT99A01.Disk | ‖(p.2 : ℂ)‖ < 1} := by
          ext p
          constructor
          · rintro ⟨i, z, hz, he⟩
            have hp : p = (i, z) := Sum.inr.inj he
            subst p
            exact hz
          · intro hp
            exact ⟨p.1, p.2, hp, rfl⟩
      rw [heq]
      exact isOpen_lt
        (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)) continuous_const
  refine ⟨hA, hB, Set.eq_univ_of_forall ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  cases x with
  | inl z =>
      left
      intro i he
      have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
          (Sum.inr (i, APMT99A01.diskCentre)) (Sum.inl z) := Quotient.exact he.symm
      have := (t99A01_attach_openCover_aux_centre degree i (Sum.inl z)).mp hr
      cases this
  | inr p =>
      rcases p with ⟨i, z⟩
      by_cases hz : ‖(z : ℂ)‖ < 1
      · right
        exact ⟨i, z, hz, rfl⟩
      · left
        intro j he
        have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
            (Sum.inr (j, APMT99A01.diskCentre)) (Sum.inr (i, z)) := Quotient.exact he.symm
        have hx := (t99A01_attach_openCover_aux_centre degree j (Sum.inr (i, z))).mp hr
        have hp : (i, z) = (j, APMT99A01.diskCentre) := Sum.inr.inj hx
        have hz0 : z = APMT99A01.diskCentre := (Prod.mk.inj hp).2
        subst z
        simp [APMT99A01.diskCentre] at hz

/-- **Leaf (radial deformation, 100--150 lines).** `sideA` deformation retracts
onto the base circle.  `ρ` is the radial retraction: a point `s·w` (`0 < s ≤ 1`) of
disk `i` goes to the boundary point `w`, which is identified with `w ^ degree i` on
the circle; circle points are fixed.  The homotopy is `(t, s·w) ↦ ((1-t)s + t)·w`,
descended through the quotient (as in `CP2RationalHomology`'s
`cpU_homology_aux_cpU_hequiv_CP1_aux_deformation`). -/
lemma t99A01_attach_circleSide_aux_circle_mem {r : ℕ} (degree : Fin r → ℕ)
    (z : Circle) :
    APMT99A01.circleIncl degree z ∈ APMT99A01.sideA degree := by
  intro i h
  have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
      (Sum.inr (i, APMT99A01.diskCentre)) (Sum.inl z) :=
    Quotient.exact h.symm
  have he := (t99A01_attach_openCover_aux_centre degree i (Sum.inl z)).mp hr
  cases he

lemma t99A01_attach_circleSide_aux_half_mem {r : ℕ} (degree : Fin r → ℕ)
    (i : Fin r) (w : Circle) :
    APMT99A01.halfLoop degree i w ∈ APMT99A01.sideA degree := by
  intro j h
  have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
      (Sum.inr (j, APMT99A01.diskCentre))
      (Sum.inr (i, APMT99A01.halfPoint w)) := Quotient.exact h.symm
  have he := (t99A01_attach_openCover_aux_centre degree j
    (Sum.inr (i, APMT99A01.halfPoint w))).mp hr
  have hp : (i, APMT99A01.halfPoint w) =
      (j, APMT99A01.diskCentre) := Sum.inr.inj he
  have hz := congrArg (fun z : APMT99A01.Disk => (z : ℂ)) (Prod.mk.inj hp).2
  change (w : ℂ) / 2 = 0 at hz
  have hw : (w : ℂ) ≠ 0 := by
    intro hw
    have hn := Circle.norm_coe w
    rw [hw, norm_zero] at hn
    norm_num at hn
  rcases div_eq_zero_iff.mp hz with hw0 | htwo
  · exact hw hw0
  · norm_num at htwo

lemma t99A01_attach_circleSide_aux_ne_zero {r : ℕ} (degree : Fin r → ℕ)
    (i : Fin r) (z : APMT99A01.Disk)
    (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideA degree) :
    (z : ℂ) ≠ 0 := by
  intro hz
  apply h i
  have hzc : z = APMT99A01.diskCentre := by
    apply Subtype.ext
    simpa [APMT99A01.diskCentre] using hz
  rw [hzc]

/-- **Leaf (radial retraction).** `ρ` fixes the base circle and sends a point `z ≠ 0`
of disk `i` to `(z/‖z‖)^{degree i}`.  Define it on the preimage of `sideA` in
`Sum Circle (Fin r × Disk)` (`inl z ↦ z`, `inr (i, z) ↦ (z/‖z‖)^{dᵢ}`); it respects
`AttachRel` (boundary `w ↦ w^{dᵢ}`), and descends because the quotient map restricted
to the open saturated preimage of `sideA` is a quotient map
(`Topology.IsQuotientMap.restrictPreimage_isOpen`). -/
theorem t99A01_attach_circleSide_aux_retraction {r : ℕ} (degree : Fin r → ℕ) :
    ∃ ρ : C(APMT99A01.sideA degree, Circle),
      (∀ z (h : APMT99A01.circleIncl degree z ∈ APMT99A01.sideA degree),
        ρ ⟨APMT99A01.circleIncl degree z, h⟩ = z) ∧
      ∀ (i : Fin r) (z : APMT99A01.Disk)
        (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideA degree),
        ((ρ ⟨_, h⟩ : Circle) : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ degree i := by
  let radial : (z : APMT99A01.Disk) → (z : ℂ) ≠ 0 → Circle :=
    fun z hz => ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
      simp [Submonoid.unitSphere, div_self (norm_ne_zero_iff.mpr hz)]⟩
  let raw : Sum Circle (Fin r × APMT99A01.Disk) → Circle
    | Sum.inl z => z
    | Sum.inr p => if h : (p.2 : ℂ) = 0 then 1 else (radial p.2 h) ^ degree p.1
  have hraw_rel : ∀ a b, APMT99A01.AttachRel degree a b → raw a = raw b := by
    intro a b hab
    cases hab with
    | boundary i z =>
      simp only [raw]
      have hz : ((APMT99A01.circleInDisk z : APMT99A01.Disk) : ℂ) ≠ 0 := by
        intro h
        have hn := Circle.norm_coe z
        change (z : ℂ) = 0 at h
        rw [h, norm_zero] at hn
        norm_num at hn
      simp only [dif_neg hz]
      apply Subtype.ext
      change (z : ℂ) ^ degree i =
        (((APMT99A01.circleInDisk z : APMT99A01.Disk) : ℂ) /
          (‖((APMT99A01.circleInDisk z : APMT99A01.Disk) : ℂ)‖ : ℂ)) ^ degree i
      simp [APMT99A01.circleInDisk, Circle.norm_coe]
  have hraw_eqv : ∀ a b, Relation.EqvGen (APMT99A01.AttachRel degree) a b →
      raw a = raw b := by
    intro a b hab
    induction hab with
    | rel a b h => exact hraw_rel a b h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let f : APMT99A01.AttachSpace degree → Circle := Quotient.lift raw hraw_eqv
  have hf_comp : ∀ x, f (APMT99A01.attachMk degree x) = raw x := by
    intro x
    rfl
  let q : (APMT99A01.attachMk degree ⁻¹' APMT99A01.sideA degree) →
      APMT99A01.sideA degree :=
    (APMT99A01.sideA degree).restrictPreimage (APMT99A01.attachMk degree)
  have hq : Topology.IsQuotientMap q :=
    (isQuotientMap_quotient_mk'.restrictPreimage_isOpen
      (t99A01_attach_openCover degree).1)
  have hraw_cont : Continuous (fun x :
      (APMT99A01.attachMk degree ⁻¹' APMT99A01.sideA degree) => raw x.1) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | inl z =>
      let g : Sum Circle (Fin r × APMT99A01.Disk) → Circle :=
        Sum.elim id (fun _ => 1)
      have hg : Continuous g := continuous_sum_dom.mpr ⟨continuous_id, continuous_const⟩
      apply (hg.continuousAt.comp continuousAt_subtype_val).congr_of_eventuallyEq
      filter_upwards [(isOpen_range_inl.preimage continuous_subtype_val).mem_nhds ⟨z, rfl⟩]
        with y hy
      rcases hy with ⟨w, hw⟩
      change raw y.1 = g y.1
      rw [← hw]
      rfl
    | inr p =>
      rcases p with ⟨i, z⟩
      have hz : (z : ℂ) ≠ 0 :=
        t99A01_attach_circleSide_aux_ne_zero degree i z hx
      have hopen : IsOpen {w : APMT99A01.Disk | (w : ℂ) ≠ 0} :=
        isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
      have hnorm : Continuous (fun w : {w : APMT99A01.Disk | (w : ℂ) ≠ 0} =>
          radial w.1 w.2) := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_subtype_val).div₀
          (Complex.continuous_ofReal.comp
            (continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val)))
          (fun w => by exact_mod_cast norm_ne_zero_iff.mpr w.2)
      have hc : ContinuousAt (fun w : APMT99A01.Disk =>
          if h : (w : ℂ) = 0 then (1 : Circle) else (radial w h) ^ degree i) z := by
        refine (hopen.isOpenEmbedding_subtypeVal.continuousAt_iff
          (g := fun w : APMT99A01.Disk =>
            if h : (w : ℂ) = 0 then (1 : Circle) else (radial w h) ^ degree i)
          (x := ⟨z, hz⟩)).mp ?_
        have heq : (fun w : APMT99A01.Disk =>
            if h : (w : ℂ) = 0 then (1 : Circle) else (radial w h) ^ degree i) ∘
              (fun w : {w : APMT99A01.Disk | (w : ℂ) ≠ 0} => w.1) =
            fun w => (radial w.1 w.2) ^ degree i := by
          funext w
          simp only [Function.comp_apply]
          rw [dif_neg w.2]
        rw [heq]
        exact hnorm.continuousAt.pow (degree i)
      let g : Sum Circle (Fin r × APMT99A01.Disk) → Circle :=
        Sum.elim (fun _ => 1) (fun p =>
          if h : (p.2 : ℂ) = 0 then 1 else (radial p.2 h) ^ degree i)
      have hg : ContinuousAt g (Sum.inr (i, z)) :=
        (Topology.IsOpenEmbedding.inr.continuousAt_iff
          (g := g) (x := (i, z))).mp
          (by
            change ContinuousAt (fun p : Fin r × APMT99A01.Disk =>
              if h : (p.2 : ℂ) = 0 then (1 : Circle)
              else (radial p.2 h) ^ degree i) (i, z)
            exact hc.comp (x := (i, z)) continuousAt_snd)
      apply (hg.comp (x := ⟨Sum.inr (i, z), hx⟩) continuousAt_subtype_val).congr_of_eventuallyEq
      have hopprod : IsOpen (({i} : Set (Fin r)) ×ˢ
          (Set.univ : Set APMT99A01.Disk)) :=
        (isOpen_discrete _).prod isOpen_univ
      have hop : IsOpen (Sum.inr '' (({i} : Set (Fin r)) ×ˢ
          (Set.univ : Set APMT99A01.Disk))) :=
        (isOpenMap_inr (X := Circle)) _ hopprod
      filter_upwards [(hop.preimage continuous_subtype_val).mem_nhds
        ⟨(i, z), by simp⟩] with y hy
      obtain ⟨⟨j, w⟩, hp_mem, hp⟩ := hy
      have hji : j = i := by simpa using hp_mem.1
      subst j
      change raw y.1 = g y.1
      rw [← hp]
      rfl
  let ρ : C(APMT99A01.sideA degree, Circle) :=
    ⟨fun x => f x.1, hq.continuous_iff.mpr (by simpa [q, Function.comp_def] using hraw_cont)⟩
  refine ⟨ρ, ?_, ?_⟩
  · intro z h
    rfl
  · intro i z h
    have hz : (z : ℂ) ≠ 0 := t99A01_attach_circleSide_aux_ne_zero degree i z h
    change ((f (APMT99A01.attachMk degree (Sum.inr (i, z))) : Circle) : ℂ) = _
    rw [hf_comp]
    simp only [raw, dif_neg hz]
    rfl

/-- **Leaf (radial deformation).** For any `ρ` with the two retraction properties,
`ι ∘ ρ ≃ id` on `sideA`.  Homotopy: `(t, inl z) ↦ inl z`,
`(t, inr (i, z)) ↦ inr (i, ((1 - t) + t / ‖z‖) • z)` (at `t = 1` the boundary point
`z/‖z‖`, identified with `(z/‖z‖)^{dᵢ}` on the circle).  Descend through
`unitInterval × (restricted quotient)`: a product of a quotient map with the identity
of the locally compact `unitInterval` is a quotient map
(`Topology.IsQuotientMap.prodMap` / `IsQuotientMap.continuous_lift_prod_right`). -/
private abbrev t99A01_attach_circleSide_aux_deformation_Pre {r : ℕ}
    (degree : Fin r → ℕ) :=
  ↥((APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideA degree)

private def t99A01_attach_circleSide_aux_deformation_q {r : ℕ}
    (degree : Fin r → ℕ) :
    t99A01_attach_circleSide_aux_deformation_Pre degree → APMT99A01.sideA degree :=
  fun x ↦ ⟨APMT99A01.attachMk degree x.1, x.2⟩

private lemma t99A01_attach_circleSide_aux_deformation_q_quotient {r : ℕ}
    (degree : Fin r → ℕ) :
    Topology.IsQuotientMap (t99A01_attach_circleSide_aux_deformation_q degree) := by
  exact (isQuotientMap_quotient_mk'.restrictPreimage_isOpen
    (t99A01_attach_openCover degree).1)

private lemma t99A01_attach_circleSide_aux_deformation_disk_ne {r : ℕ}
    (degree : Fin r → ℕ)
    (x : t99A01_attach_circleSide_aux_deformation_Pre degree)
    (i : Fin r) (z : APMT99A01.Disk) (hx : x.1 = Sum.inr (i, z)) :
    (z : ℂ) ≠ 0 := by
  apply t99A01_attach_circleSide_aux_ne_zero degree i z
  simpa [t99A01_attach_circleSide_aux_deformation_q, hx] using x.2

private def t99A01_attach_circleSide_aux_deformation_scale (t : unitInterval) (z : ℂ) : ℝ :=
  t.1 + (1 - t.1) / ‖z‖

private lemma t99A01_attach_circleSide_aux_deformation_scale_norm
    (t : unitInterval) (z : ℂ) (hz0 : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖(t99A01_attach_circleSide_aux_deformation_scale t z : ℂ) * z‖ ≤ 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hs0 : 0 ≤ (t : ℝ) + (1 - t.1) / ‖z‖ :=
    add_nonneg ht0 (div_nonneg (sub_nonneg.mpr ht1) hn.le)
  rw [norm_mul]
  change ‖(((t : ℝ) + (1 - t.1) / ‖z‖ : ℝ) : ℂ)‖ * ‖z‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  field_simp
  nlinarith

private lemma t99A01_attach_circleSide_aux_deformation_scale_ne
    (t : unitInterval) (z : ℂ) (hz0 : z ≠ 0) :
    (t99A01_attach_circleSide_aux_deformation_scale t z : ℂ) * z ≠ 0 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  apply mul_ne_zero
  · rw [t99A01_attach_circleSide_aux_deformation_scale]
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have : 0 < (t : ℝ) + (1 - t.1) / ‖z‖ := by
      by_cases ht : (t : ℝ) = 0
      · rw [ht]
        positivity
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ht0 (Ne.symm ht))
          (div_nonneg (sub_nonneg.mpr ht1) hn.le)
    exact_mod_cast this.ne'
  · exact hz0

private def t99A01_attach_circleSide_aux_deformation_raw {r : ℕ}
    (degree : Fin r → ℕ)
    (p : unitInterval × t99A01_attach_circleSide_aux_deformation_Pre degree) :
    Sum Circle (Fin r × APMT99A01.Disk) :=
  match hx : p.2.1 with
  | Sum.inl z => Sum.inl z
  | Sum.inr q => Sum.inr (q.1, ⟨
      (t99A01_attach_circleSide_aux_deformation_scale p.1 (q.2 : ℂ) : ℂ) * q.2,
      by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact t99A01_attach_circleSide_aux_deformation_scale_norm p.1 _
          (t99A01_attach_circleSide_aux_deformation_disk_ne degree p.2 q.1 q.2 hx)
          (by
            have hq := q.2.property
            rw [Metric.mem_closedBall, dist_zero_right] at hq
            exact hq)⟩)

private lemma t99A01_attach_circleSide_aux_deformation_raw_mem {r : ℕ}
    (degree : Fin r → ℕ)
    (p : unitInterval × t99A01_attach_circleSide_aux_deformation_Pre degree) :
    APMT99A01.attachMk degree
      (t99A01_attach_circleSide_aux_deformation_raw degree p) ∈ APMT99A01.sideA degree := by
  rcases p with ⟨t, x⟩
  rcases x with ⟨x, hxmem⟩
  cases x with
  | inl z => simpa [t99A01_attach_circleSide_aux_deformation_raw] using
      t99A01_attach_circleSide_aux_circle_mem degree z
  | inr q =>
      intro j h
      have he := (t99A01_attach_openCover_aux_centre degree j _).mp
        (Quotient.exact h.symm)
      simp only [t99A01_attach_circleSide_aux_deformation_raw] at he
      have hp := Sum.inr.inj he
      have hz := congrArg (fun w : APMT99A01.Disk ↦ (w : ℂ)) (Prod.mk.inj hp).2
      change (t99A01_attach_circleSide_aux_deformation_scale t (q.2 : ℂ) : ℂ) * q.2 = 0 at hz
      exact (t99A01_attach_circleSide_aux_deformation_scale_ne t _
        (t99A01_attach_circleSide_aux_ne_zero degree q.1 q.2 hxmem)) hz

lemma t99A01_attach_circleSide_aux_deformation_aux_continuous {r : ℕ}
    (degree : Fin r → ℕ) :
    Continuous (t99A01_attach_circleSide_aux_deformation_raw degree) := by
  rw [continuous_iff_continuousAt]
  rintro p
  rcases p with ⟨t, x⟩
  rcases x with ⟨x, hx⟩
  cases x with
  | inl z =>
      let getZ : t99A01_attach_circleSide_aux_deformation_Pre degree → Circle :=
        fun y => Sum.elim id (fun _ => z) y.1
      have hgetZ : Continuous getZ :=
        (continuous_sumElim.2 ⟨continuous_id, continuous_const⟩).comp
          continuous_subtype_val
      apply (continuous_inl.comp (hgetZ.comp continuous_snd)).continuousAt.congr_of_eventuallyEq
      have hopen : IsOpen (Sum.inl '' (Set.univ : Set Circle)) :=
        (isOpenMap_inl (X := Circle) (Y := Fin r × APMT99A01.Disk)) _ isOpen_univ
      filter_upwards [((hopen.preimage
        (continuous_subtype_val.comp continuous_snd)).mem_nhds
          (by simp))] with y hy
      obtain ⟨w, -, hw⟩ := hy
      rcases y with ⟨s, ⟨u, hu⟩⟩
      dsimp at hw ⊢
      cases u <;> simp_all [t99A01_attach_circleSide_aux_deformation_raw, getZ]
  | inr q =>
      let getQ : t99A01_attach_circleSide_aux_deformation_Pre degree →
          Fin r × APMT99A01.Disk :=
        fun y => Sum.elim (fun _ => q) id y.1
      have hgetQ : Continuous getQ :=
        (continuous_sumElim.2 ⟨continuous_const, continuous_id⟩).comp
          continuous_subtype_val
      have hne : ∀ y : t99A01_attach_circleSide_aux_deformation_Pre degree,
          ((getQ y).2 : ℂ) ≠ 0 := by
        intro y
        cases hy : y.1 with
        | inl w =>
            simpa [getQ, hy] using
              (t99A01_attach_circleSide_aux_deformation_disk_ne degree
                ⟨Sum.inr q, hx⟩ q.1 q.2 rfl)
        | inr q' =>
            simpa [getQ, hy] using
              (t99A01_attach_circleSide_aux_deformation_disk_ne degree y q'.1 q'.2 hy)
      let diskMap : unitInterval × t99A01_attach_circleSide_aux_deformation_Pre degree →
          Fin r × APMT99A01.Disk := fun y =>
        ((getQ y.2).1, ⟨
          (t99A01_attach_circleSide_aux_deformation_scale y.1 ((getQ y.2).2 : ℂ) : ℂ) *
            (getQ y.2).2,
          by
            rw [Metric.mem_closedBall, dist_zero_right]
            apply t99A01_attach_circleSide_aux_deformation_scale_norm y.1 _ (hne y.2)
            have hz := (getQ y.2).2.property
            simpa only [Metric.mem_closedBall, dist_zero_right] using hz⟩)
      have hdisk : Continuous diskMap := by
        apply Continuous.prodMk (hgetQ.fst.comp continuous_snd)
        apply Continuous.subtype_mk
        dsimp [diskMap, t99A01_attach_circleSide_aux_deformation_scale]
        have hv : Continuous (fun y : unitInterval ×
            t99A01_attach_circleSide_aux_deformation_Pre degree =>
            ((getQ y.2).2 : ℂ)) :=
          (continuous_subtype_val.comp (hgetQ.snd.comp continuous_snd))
        have hn : Continuous (fun y : unitInterval ×
            t99A01_attach_circleSide_aux_deformation_Pre degree =>
            ‖((getQ y.2).2 : ℂ)‖) := hv.norm
        have hn0 : ∀ y : unitInterval ×
            t99A01_attach_circleSide_aux_deformation_Pre degree,
            ‖((getQ y.2).2 : ℂ)‖ ≠ 0 := fun y => norm_ne_zero_iff.mpr (hne y.2)
        have hquot : Continuous (fun y : unitInterval ×
            t99A01_attach_circleSide_aux_deformation_Pre degree =>
            (1 - (y.1 : ℝ)) / ‖((getQ y.2).2 : ℂ)‖) :=
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div hn hn0
        exact (Complex.continuous_ofReal.comp
          ((continuous_subtype_val.comp continuous_fst).add hquot)).mul hv
      apply (continuous_inr.comp hdisk).continuousAt.congr_of_eventuallyEq
      have hopen : IsOpen (Sum.inr ''
          (Set.univ : Set (Fin r × APMT99A01.Disk))) :=
        (isOpenMap_inr (X := Circle) (Y := Fin r × APMT99A01.Disk)) _ isOpen_univ
      filter_upwards [((hopen.preimage
        (continuous_subtype_val.comp continuous_snd)).mem_nhds
          (by simp))] with y hy
      obtain ⟨q', -, hq'⟩ := hy
      rcases y with ⟨s, ⟨u, hu⟩⟩
      dsimp at hq' ⊢
      cases u <;> simp_all [t99A01_attach_circleSide_aux_deformation_raw, diskMap, getQ]

lemma t99A01_attach_circleSide_aux_deformation_aux_respects {r : ℕ}
    (degree : Fin r → ℕ) (t : unitInterval)
    (x y : t99A01_attach_circleSide_aux_deformation_Pre degree)
    (hxy : t99A01_attach_circleSide_aux_deformation_q degree x =
      t99A01_attach_circleSide_aux_deformation_q degree y) :
    APMT99A01.attachMk degree
        (t99A01_attach_circleSide_aux_deformation_raw degree (t, x)) =
      APMT99A01.attachMk degree
        (t99A01_attach_circleSide_aux_deformation_raw degree (t, y)) := by
  have hxy' : Relation.EqvGen (APMT99A01.AttachRel degree) x.1 y.1 := by
    have hh := Quotient.exact (congrArg Subtype.val hxy)
    change Relation.EqvGen (APMT99A01.AttachRel degree) x.1 y.1 at hh
    exact hh
  have hgen : ∀ a b, Relation.EqvGen (APMT99A01.AttachRel degree) a b →
      ∀ (ha : a ∈ (APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideA degree)
        (hb : b ∈ (APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideA degree),
      APMT99A01.attachMk degree
          (t99A01_attach_circleSide_aux_deformation_raw degree
            (t, ⟨a, ha⟩)) =
        APMT99A01.attachMk degree
          (t99A01_attach_circleSide_aux_deformation_raw degree
            (t, ⟨b, hb⟩)) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        intro ha hb
        cases hab with
        | boundary i z =>
          have hn : ‖(APMT99A01.circleInDisk z : ℂ)‖ = 1 := Circle.norm_coe z
          have hs : t99A01_attach_circleSide_aux_deformation_scale t
              (APMT99A01.circleInDisk z : ℂ) = 1 := by
            simp [t99A01_attach_circleSide_aux_deformation_scale, hn]
          apply Quotient.sound
          simpa [t99A01_attach_circleSide_aux_deformation_raw, hs] using
            (Relation.EqvGen.rel
              _ _
              (APMT99A01.AttachRel.boundary (degree := degree) i z))
    | refl a => intro ha hb; rfl
    | symm a b hab ih => intro ha hb; exact (ih hb ha).symm
    | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hb : b ∈ (APMT99A01.attachMk degree) ⁻¹' APMT99A01.sideA degree := by
          have heq : APMT99A01.attachMk degree a = APMT99A01.attachMk degree b :=
            Quotient.sound hab
          change APMT99A01.attachMk degree b ∈ APMT99A01.sideA degree
          change APMT99A01.attachMk degree a ∈ APMT99A01.sideA degree at ha
          rw [← heq]
          exact ha
        exact (ih₁ ha hb).trans (ih₂ hb hc)
  exact hgen x.1 y.1 hxy' x.2 y.2

/-- **Leaf (descent + endpoints).** Descend `raw` through `unitInterval × q`
(`Topology.IsQuotientMap.continuous_lift_prod_left/right`; `q` is a quotient map:
banked `_q_quotient`), landing in `sideA` by `_raw_mem`; endpoints: scale `0` is the
identity, scale `1` sends `s·w` to the boundary point `w`, whose class is that of
`inl (w ^ dᵢ)` (`AttachRel.boundary`), matching `ι ∘ ρ` by `hρ₁`, `hρ₂`, `hι`. -/
lemma t99A01_attach_circleSide_aux_deformation_aux_descend {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle))
    (hρ₁ : ∀ z (h : APMT99A01.circleIncl degree z ∈ APMT99A01.sideA degree),
      ρ ⟨APMT99A01.circleIncl degree z, h⟩ = z)
    (hρ₂ : ∀ (i : Fin r) (z : APMT99A01.Disk)
      (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideA degree),
      ((ρ ⟨_, h⟩ : Circle) : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ degree i)
    (ι : C(Circle, APMT99A01.sideA degree))
    (hι : ∀ z, (ι z).1 = APMT99A01.circleIncl degree z)
    (hcont : Continuous (t99A01_attach_circleSide_aux_deformation_raw degree))
    (hresp : ∀ (t : unitInterval) (x y : t99A01_attach_circleSide_aux_deformation_Pre degree),
      t99A01_attach_circleSide_aux_deformation_q degree x =
        t99A01_attach_circleSide_aux_deformation_q degree y →
      APMT99A01.attachMk degree (t99A01_attach_circleSide_aux_deformation_raw degree (t, x)) =
        APMT99A01.attachMk degree (t99A01_attach_circleSide_aux_deformation_raw degree (t, y))) :
    ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _) := by
  let q := t99A01_attach_circleSide_aux_deformation_q degree
  have hq := t99A01_attach_circleSide_aux_deformation_q_quotient degree
  let s : APMT99A01.sideA degree →
      t99A01_attach_circleSide_aux_deformation_Pre degree :=
    fun x ↦ Classical.choose (hq.surjective x)
  have hs (x : APMT99A01.sideA degree) : q (s x) = x :=
    Classical.choose_spec (hq.surjective x)
  let F : unitInterval × APMT99A01.sideA degree → APMT99A01.sideA degree :=
    fun p ↦ ⟨APMT99A01.attachMk degree
      (t99A01_attach_circleSide_aux_deformation_raw degree (p.1, s p.2)),
      t99A01_attach_circleSide_aux_deformation_raw_mem degree (p.1, s p.2)⟩
  have hFq (p : unitInterval ×
      t99A01_attach_circleSide_aux_deformation_Pre degree) :
      F (p.1, q p.2) =
        ⟨APMT99A01.attachMk degree
          (t99A01_attach_circleSide_aux_deformation_raw degree p),
          t99A01_attach_circleSide_aux_deformation_raw_mem degree p⟩ := by
    apply Subtype.ext
    exact hresp p.1 (s (q p.2)) p.2 (hs (q p.2))
  have hF : Continuous F := by
    apply hq.continuous_lift_prod_right
    have hc : Continuous (fun p : unitInterval ×
        t99A01_attach_circleSide_aux_deformation_Pre degree ↦
          (⟨APMT99A01.attachMk degree
              (t99A01_attach_circleSide_aux_deformation_raw degree p),
            t99A01_attach_circleSide_aux_deformation_raw_mem degree p⟩ :
            APMT99A01.sideA degree)) :=
      Continuous.subtype_mk ((APMT99A01.continuous_attachMk degree).comp hcont) _
    convert hc using 1
    funext p
    exact hFq p
  refine ⟨ContinuousMap.Homotopy.mk (f₀ := ι.comp ρ)
    (f₁ := ContinuousMap.id _) ⟨F, hF⟩ ?_ ?_⟩
  · intro x
    apply Subtype.ext
    change (F (0, x)).1 = _
    rw [show F (0, x) = F (0, q (s x)) by rw [hs x]]
    rw [congrArg Subtype.val (hFq (0, s x))]
    generalize hy : s x = y
    rcases y with ⟨y, hymem⟩
    cases y with
    | inl z =>
      simp only [t99A01_attach_circleSide_aux_deformation_raw]
      change APMT99A01.attachMk degree (Sum.inl z) = (ι (ρ x)).1
      rw [hι]
      change APMT99A01.attachMk degree (Sum.inl z) =
        APMT99A01.attachMk degree (Sum.inl (ρ x))
      congr 2
      have hx : x = ⟨APMT99A01.circleIncl degree z, hymem⟩ := by
        exact (hy ▸ hs x).symm
      rw [hx]
      exact (hρ₁ z hymem).symm
    | inr p =>
      rcases p with ⟨i, z⟩
      have hval : (s x).1 = Sum.inr (i, z) := congrArg Subtype.val hy
      have hz := t99A01_attach_circleSide_aux_deformation_disk_ne degree (s x) i z hval
      have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz
      let w : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
        simp [Submonoid.unitSphere, div_self hn.ne']⟩
      simp only [t99A01_attach_circleSide_aux_deformation_raw]
      have hs0 : t99A01_attach_circleSide_aux_deformation_scale (0 : unitInterval)
          (z : ℂ) = 1 / ‖(z : ℂ)‖ := by
        simp [t99A01_attach_circleSide_aux_deformation_scale]
      change APMT99A01.attachMk degree _ = (ι (ρ x)).1
      rw [hι]
      have hx : x = ⟨APMT99A01.attachMk degree (Sum.inr (i, z)), hymem⟩ := by
        exact (hy ▸ hs x).symm
      have hrho := hρ₂ i z hymem
      rw [show ρ x = w ^ degree i by rw [hx]; apply Subtype.ext; exact hrho]
      apply Quotient.sound
      have hb0 : Relation.EqvGen (APMT99A01.AttachRel degree)
          (Sum.inl (w ^ degree i))
          (Sum.inr (i, APMT99A01.circleInDisk w)) :=
        Relation.EqvGen.rel _ _
          (APMT99A01.AttachRel.boundary (degree := degree) i w)
      have hb : Relation.EqvGen (APMT99A01.AttachRel degree)
          (Sum.inr (i, APMT99A01.circleInDisk w))
          (Sum.inl (w ^ degree i)) := hb0.symm
      let zd : APMT99A01.Disk :=
        ⟨(t99A01_attach_circleSide_aux_deformation_scale 0 (z : ℂ) : ℂ) * z,
          by
            rw [Metric.mem_closedBall, dist_zero_right]
            apply t99A01_attach_circleSide_aux_deformation_scale_norm 0 _ hz
            have hz1 := z.2
            rw [Metric.mem_closedBall, dist_zero_right] at hz1
            exact hz1⟩
      have hd : zd = APMT99A01.circleInDisk w := by
        apply Subtype.ext
        simp [zd, APMT99A01.circleInDisk, w, hs0, div_eq_mul_inv, mul_comm]
      have hzdraw :
          t99A01_attach_circleSide_aux_deformation_raw degree
              (0, ⟨Sum.inr (i, z), hymem⟩) = Sum.inr (i, zd) := by
        simp [t99A01_attach_circleSide_aux_deformation_raw, zd]
      change Relation.EqvGen (APMT99A01.AttachRel degree)
        (t99A01_attach_circleSide_aux_deformation_raw degree
          (0, ⟨Sum.inr (i, z), hymem⟩)) (Sum.inl (w ^ degree i))
      rw [hzdraw, hd]
      exact hb
  · intro x
    apply Subtype.ext
    change (F (1, x)).1 = _
    rw [show F (1, x) = F (1, q (s x)) by rw [hs x]]
    rw [congrArg Subtype.val (hFq (1, s x))]
    have hone : t99A01_attach_circleSide_aux_deformation_raw degree (1, s x) =
        (s x).1 := by
      generalize hy : s x = y
      rcases y with ⟨y, hm⟩
      cases y with
      | inl z => simp [t99A01_attach_circleSide_aux_deformation_raw]
      | inr p =>
        rcases p with ⟨i, z⟩
        simp [t99A01_attach_circleSide_aux_deformation_raw,
          t99A01_attach_circleSide_aux_deformation_scale]
    exact (congrArg (APMT99A01.attachMk degree) hone).trans
      (congrArg Subtype.val (hs x))

theorem t99A01_attach_circleSide_aux_deformation {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle))
    (hρ₁ : ∀ z (h : APMT99A01.circleIncl degree z ∈ APMT99A01.sideA degree),
      ρ ⟨APMT99A01.circleIncl degree z, h⟩ = z)
    (hρ₂ : ∀ (i : Fin r) (z : APMT99A01.Disk)
      (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideA degree),
      ((ρ ⟨_, h⟩ : Circle) : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ degree i)
    (ι : C(Circle, APMT99A01.sideA degree))
    (hι : ∀ z, (ι z).1 = APMT99A01.circleIncl degree z) :
    ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _) :=
  t99A01_attach_circleSide_aux_deformation_aux_descend degree ρ hρ₁ hρ₂ ι hι
    (t99A01_attach_circleSide_aux_deformation_aux_continuous degree)
    (fun t x y h => t99A01_attach_circleSide_aux_deformation_aux_respects degree t x y h)
theorem t99A01_attach_circleSide {r : ℕ} (degree : Fin r → ℕ) :
    ∃ (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree)),
      (∀ z, (ι z).1 = APMT99A01.circleIncl degree z) ∧
      ρ.comp ι = ContinuousMap.id Circle ∧
      ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _) ∧
      ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideA degree),
        ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i := by
  obtain ⟨ρ, hρ₁, hρ₂⟩ := t99A01_attach_circleSide_aux_retraction degree
  let ι : C(Circle, APMT99A01.sideA degree) :=
    ⟨fun z => ⟨APMT99A01.circleIncl degree z, t99A01_attach_circleSide_aux_circle_mem degree z⟩,
      (APMT99A01.circleIncl degree).continuous.subtype_mk _⟩
  have hι : ∀ z, (ι z).1 = APMT99A01.circleIncl degree z := fun _ => rfl
  refine ⟨ρ, ι, hι, ?_, t99A01_attach_circleSide_aux_deformation degree ρ hρ₁ hρ₂ ι hι, ?_⟩
  · ext z
    simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply]
    exact congrArg (fun c : Circle => (c : ℂ)) (hρ₁ z _)
  · intro i w h
    apply Subtype.ext
    have h2 := hρ₂ i (APMT99A01.halfPoint w) h
    have hn : ‖((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ)‖ = 1 / 2 := by
      change ‖(w : ℂ) / 2‖ = 1 / 2
      rw [norm_div, Circle.norm_coe]; norm_num
    have hq : ((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ) /
        (‖((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ)‖ : ℂ) = (w : ℂ) := by
      rw [hn]; change (w : ℂ) / 2 / ((1 / 2 : ℝ) : ℂ) = w; push_cast; ring
    change ((ρ ⟨APMT99A01.attachMk degree (Sum.inr (i, APMT99A01.halfPoint w)), h⟩ : Circle) : ℂ) = _
    rw [h2, hq, Circle.coe_pow]
/-- **Leaf (disk charts, 60--120 lines).** The disk side is the disjoint union of
the open disks, by the identity chart on each disk interior.  Interior points
are identified with nothing else (`EqvGen` induction on `AttachRel`). -/
noncomputable def t99A01_attach_diskSide_aux_decode {r : ℕ} :
    Sum Circle (Fin r × APMT99A01.Disk) → Option (Σ _ : Fin r, Metric.ball (0 : ℂ) 1)
  | Sum.inl _ => none
  | Sum.inr (i, z) => if h : ‖(z : ℂ)‖ < 1 then
      some ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using h⟩⟩ else none

lemma t99A01_attach_diskSide_aux_decode_eqv {r : ℕ} (degree : Fin r → ℕ)
    {x y : Sum Circle (Fin r × APMT99A01.Disk)}
    (h : Relation.EqvGen (APMT99A01.AttachRel degree) x y) :
    t99A01_attach_diskSide_aux_decode x = t99A01_attach_diskSide_aux_decode y := by
  induction h with
  | rel x y hxy =>
      cases hxy
      simp [t99A01_attach_diskSide_aux_decode, APMT99A01.circleInDisk,
        Circle.norm_coe]
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma t99A01_attach_diskSide_aux_eqv {r : ℕ} (degree : Fin r → ℕ)
    {i j : Fin r} {z w : APMT99A01.Disk}
    (hz : ‖(z : ℂ)‖ < 1) (hw : ‖(w : ℂ)‖ < 1)
    (h : Relation.EqvGen (APMT99A01.AttachRel degree)
      (Sum.inr (i, z)) (Sum.inr (j, w))) : i = j ∧ z = w := by
  have hd := t99A01_attach_diskSide_aux_decode_eqv degree h
  simp [t99A01_attach_diskSide_aux_decode, hz, hw] at hd
  exact ⟨hd.1, Subtype.ext hd.2⟩

noncomputable def t99A01_attach_diskSide_aux_diskOfBall
    (z : Metric.ball (0 : ℂ) 1) : APMT99A01.Disk :=
  ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz : ‖(z : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using z.2
    exact hz.le⟩

lemma t99A01_attach_diskSide_aux_diskOfBall_coe
    (z : Metric.ball (0 : ℂ) 1) :
    ((t99A01_attach_diskSide_aux_diskOfBall z : APMT99A01.Disk) : ℂ) = z := rfl

/-- The canonical chart inverse: a point of disk `i`'s interior. -/
noncomputable def t99A01_attach_diskSide_aux_g {r : ℕ} (degree : Fin r → ℕ)
    (p : Σ _ : Fin r, Metric.ball (0 : ℂ) 1) : APMT99A01.sideB degree :=
  ⟨APMT99A01.attachMk degree (Sum.inr (p.1, t99A01_attach_diskSide_aux_diskOfBall p.2)),
    ⟨p.1, t99A01_attach_diskSide_aux_diskOfBall p.2,
      by simpa only [t99A01_attach_diskSide_aux_diskOfBall,
        Metric.mem_ball, dist_zero_right] using p.2.2, rfl⟩⟩

lemma t99A01_attach_diskSide_aux_continuous_bijection {r : ℕ}
    (degree : Fin r → ℕ) :
    Continuous (t99A01_attach_diskSide_aux_g degree) ∧
      Function.Bijective (t99A01_attach_diskSide_aux_g degree) := by
  let d := t99A01_attach_diskSide_aux_diskOfBall
  let g := t99A01_attach_diskSide_aux_g degree
  refine ⟨?_, ?_, ?_⟩
  · apply continuous_sigma
    intro i
    apply Continuous.subtype_mk
    exact (APMT99A01.continuous_attachMk degree).comp
      (continuous_inr.comp (continuous_const.prodMk
        (Continuous.subtype_mk continuous_subtype_val _)))
  · rintro ⟨i, z⟩ ⟨j, w⟩ h
    have he : Relation.EqvGen (APMT99A01.AttachRel degree)
        (Sum.inr (i, d z)) (Sum.inr (j, d w)) :=
      Quotient.exact (congrArg Subtype.val h)
    have hij := t99A01_attach_diskSide_aux_eqv degree
      (by simpa only [d, t99A01_attach_diskSide_aux_diskOfBall,
        Metric.mem_ball, dist_zero_right] using z.2)
      (by simpa only [d, t99A01_attach_diskSide_aux_diskOfBall,
        Metric.mem_ball, dist_zero_right] using w.2) he
    cases hij.1
    congr 1
    apply Subtype.ext
    simpa only [d, t99A01_attach_diskSide_aux_diskOfBall_coe] using
      congrArg (fun x : APMT99A01.Disk => (x : ℂ)) hij.2
  · rintro ⟨q, i, z, hz, rfl⟩
    let zb : Metric.ball (0 : ℂ) 1 :=
      ⟨z, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
    refine ⟨⟨i, zb⟩, ?_⟩
    apply Subtype.ext
    change APMT99A01.attachMk degree (Sum.inr (i, d zb)) =
      APMT99A01.attachMk degree (Sum.inr (i, z))
    congr 3

/-- **Leaf.** The chart inverse is an open map: an open set of disk interiors has
open, saturated preimage under the quotient map (interior points are singleton classes,
banked above), so its image is open in the quotient, hence in `sideB`
(`isOpen_coinduced`, `IsOpen.isOpenMap_subtype_val`/`Topology.IsInducing.isOpen_iff`). -/
lemma t99A01_attach_diskSide_aux_open_diskOfBall :
    IsOpenMap t99A01_attach_diskSide_aux_diskOfBall := by
  intro U hU
  have hball : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hopen : IsOpen ((fun z : Metric.ball (0 : ℂ) 1 => (z : ℂ)) '' U) :=
    hball.isOpenEmbedding_subtypeVal.isOpenMap U hU
  have heq : t99A01_attach_diskSide_aux_diskOfBall '' U =
      Subtype.val ⁻¹' ((fun z : Metric.ball (0 : ℂ) 1 => (z : ℂ)) '' U) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, he⟩
      refine ⟨w, hw, Subtype.ext ?_⟩
      exact he
  rw [heq]
  exact hopen.preimage continuous_subtype_val

lemma t99A01_attach_diskSide_aux_open_raw {r : ℕ} :
    IsOpenMap (fun p : (Σ _ : Fin r, Metric.ball (0 : ℂ) 1) =>
      (Sum.inr (p.1, t99A01_attach_diskSide_aux_diskOfBall p.2) :
        Sum Circle (Fin r × APMT99A01.Disk))) := by
  intro U hU
  rw [isOpen_sum_iff]
  constructor
  · convert (isOpen_empty : IsOpen (∅ : Set Circle)) using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, -, h⟩
    cases h
  · rw [isOpen_prod_iff]
    intro i b hb
    rcases hb with ⟨p, hpU, hp⟩
    rcases p with ⟨j, z⟩
    have hp' : (j, t99A01_attach_diskSide_aux_diskOfBall z) = (i, b) :=
      Sum.inr.inj hp
    have hji : j = i := (Prod.mk.inj hp').1
    subst j
    have hzb : t99A01_attach_diskSide_aux_diskOfBall z = b := (Prod.mk.inj hp').2
    let Ui : Set (Metric.ball (0 : ℂ) 1) := {z | (⟨i, z⟩ :
      Σ _ : Fin r, Metric.ball (0 : ℂ) 1) ∈ U}
    have hUi : IsOpen Ui := by
      simpa only [Ui, Set.mem_setOf_eq] using (isOpen_sigma_iff.mp hU) i
    have hdi : IsOpen (t99A01_attach_diskSide_aux_diskOfBall ''
        Ui) :=
      t99A01_attach_diskSide_aux_open_diskOfBall _ hUi
    refine ⟨{i}, t99A01_attach_diskSide_aux_diskOfBall ''
      Ui, isOpen_discrete _, hdi, rfl, ⟨z, hpU, hzb⟩, ?_⟩
    rintro ⟨k, c⟩ ⟨hk, hc⟩
    simp only [Set.mem_singleton_iff] at hk
    rcases hc with ⟨w, hwU, rfl⟩
    subst k
    exact ⟨⟨i, w⟩, hwU, rfl⟩

lemma t99A01_attach_diskSide_aux_open {r : ℕ} (degree : Fin r → ℕ) :
    IsOpenMap (t99A01_attach_diskSide_aux_g degree) := by
  intro U hU
  let F : (Σ _ : Fin r, Metric.ball (0 : ℂ) 1) →
      Sum Circle (Fin r × APMT99A01.Disk) := fun p =>
    Sum.inr (p.1, t99A01_attach_diskSide_aux_diskOfBall p.2)
  have hFU : IsOpen (F '' U) := t99A01_attach_diskSide_aux_open_raw U hU
  have hsat : (APMT99A01.attachMk degree) ⁻¹'
      ((APMT99A01.attachMk degree) '' (F '' U)) = F '' U := by
    ext x
    constructor
    · rintro ⟨y, ⟨p, hpU, rfl⟩, hxy⟩
      rcases p with ⟨i, z⟩
      have hz : ‖((t99A01_attach_diskSide_aux_diskOfBall z : APMT99A01.Disk) : ℂ)‖ < 1 := by
        simpa only [t99A01_attach_diskSide_aux_diskOfBall_coe,
          Metric.mem_ball, dist_zero_right] using z.2
      have heq := t99A01_attach_diskSide_aux_decode_eqv degree (Quotient.exact hxy)
      cases x with
      | inl w =>
          simp [F, t99A01_attach_diskSide_aux_decode, hz] at heq
      | inr q =>
          rcases q with ⟨j, w⟩
          simp only [F] at hxy ⊢
          have hw : ‖(w : ℂ)‖ < 1 := by
            by_contra hn
            dsimp [F] at heq
            simp [t99A01_attach_diskSide_aux_decode, hz, hn] at heq
          have hij := t99A01_attach_diskSide_aux_eqv degree hz hw
            (Quotient.exact hxy)
          rcases hij with ⟨rfl, hwz⟩
          subst w
          exact ⟨⟨i, z⟩, hpU, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨F p, ⟨p, hp, rfl⟩, rfl⟩
  have hquot : IsOpen ((APMT99A01.attachMk degree) '' (F '' U)) := by
    rw [isOpen_coinduced]
    change IsOpen ((APMT99A01.attachMk degree) ⁻¹'
      ((APMT99A01.attachMk degree) '' (F '' U)))
    rw [hsat]
    exact hFU
  have heq : t99A01_attach_diskSide_aux_g degree '' U =
      Subtype.val ⁻¹' ((APMT99A01.attachMk degree) '' (F '' U)) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨F p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨p, hp, hxp⟩, hxq⟩
      refine ⟨p, hp, Subtype.ext ?_⟩
      exact (congrArg (APMT99A01.attachMk degree) hxp).trans hxq
  rw [heq]
  exact hquot.preimage continuous_subtype_val

theorem t99A01_attach_diskSide {r : ℕ} (degree : Fin r → ℕ) :
    ∃ e : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
        (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
        e ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩ := by
  obtain ⟨hc, hb⟩ := t99A01_attach_diskSide_aux_continuous_bijection degree
  let E := (Equiv.ofBijective _ hb).toHomeomorphOfContinuousOpen hc
    (t99A01_attach_diskSide_aux_open degree)
  refine ⟨E.symm, fun i z hz h => ?_⟩
  apply E.injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rfl
/-- **Leaf (punctured disks, 80--140 lines).** The overlap is the disjoint union
of the punctured open disks, which deformation retracts onto the radius-`1/2`
circles; the inverse of the equivalence is literally `halfLoop`. -/
lemma t99A01_attach_overlap_aux_rel_boundary
    {r : ℕ} {degree : Fin r → ℕ} {i : Fin r} {z : APMT99A01.Disk}
    (hz : ‖(z : ℂ)‖ < 1) {x : Sum Circle (Fin r × APMT99A01.Disk)}
    (h : APMT99A01.AttachRel degree (Sum.inr (i, z)) x) : False := by
  cases h

lemma t99A01_attach_overlap_aux_rel_boundary_rev
    {r : ℕ} {degree : Fin r → ℕ} {i : Fin r} {z : APMT99A01.Disk}
    (hz : ‖(z : ℂ)‖ < 1) {x : Sum Circle (Fin r × APMT99A01.Disk)}
    (h : APMT99A01.AttachRel degree x (Sum.inr (i, z))) : False := by
  cases h with
  | boundary j w =>
      exact (not_lt_of_ge (by
        simpa [APMT99A01.circleInDisk] using Circle.norm_coe w)) hz

lemma t99A01_attach_overlap_aux_eqv_interior_iff
    {r : ℕ} {degree : Fin r → ℕ} {i : Fin r} {z : APMT99A01.Disk}
    (hz : ‖(z : ℂ)‖ < 1) {x y : Sum Circle (Fin r × APMT99A01.Disk)}
    (h : Relation.EqvGen (APMT99A01.AttachRel degree) x y) :
    (x = Sum.inr (i, z) ↔ y = Sum.inr (i, z)) := by
  induction h with
  | rel x y hxy =>
      constructor
      · intro hx
        subst x
        exact (t99A01_attach_overlap_aux_rel_boundary hz hxy).elim
      · intro hy
        subst y
        exact (t99A01_attach_overlap_aux_rel_boundary_rev hz hxy).elim
  | refl => exact Iff.rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

lemma t99A01_attach_overlap_aux_eqv_interior
    {r : ℕ} {degree : Fin r → ℕ} {i : Fin r} {z : APMT99A01.Disk}
    (hz : ‖(z : ℂ)‖ < 1) {x : Sum Circle (Fin r × APMT99A01.Disk)}
    (h : Relation.EqvGen (APMT99A01.AttachRel degree) (Sum.inr (i, z)) x) :
    x = Sum.inr (i, z) :=
  (t99A01_attach_overlap_aux_eqv_interior_iff hz h).mp rfl

/-- The open punctured unit disk. -/
def t99A01_pball : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < 1}

/-- **Leaf (quotient chart).** The overlap is the disjoint union of punctured open
disks, by the identity chart on each disk (interior points are singleton classes:
`t99A01_attach_overlap_aux_eqv_interior`; continuity of the inverse as in
`t99A01_attach_diskSide`). -/
private abbrev t99A01_attach_overlap_aux_chart_Pre {r : ℕ}
    (degree : Fin r → ℕ) :=
  ↥((APMT99A01.attachMk degree) ⁻¹'
    (APMT99A01.sideA degree ∩ APMT99A01.sideB degree))

private def t99A01_attach_overlap_aux_chart_q {r : ℕ} (degree : Fin r → ℕ) :
    t99A01_attach_overlap_aux_chart_Pre degree →
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) :=
  (APMT99A01.sideA degree ∩ APMT99A01.sideB degree).restrictPreimage
    (APMT99A01.attachMk degree)

lemma t99A01_attach_overlap_aux_chart_q_quotient {r : ℕ} (degree : Fin r → ℕ) :
    Topology.IsQuotientMap (t99A01_attach_overlap_aux_chart_q degree) := by
  exact isQuotientMap_quotient_mk'.restrictPreimage_isOpen
    ((t99A01_attach_openCover degree).1.inter (t99A01_attach_openCover degree).2.1)

lemma t99A01_attach_overlap_aux_chart_mem {r : ℕ} (degree : Fin r → ℕ)
    (i : Fin r) (z : APMT99A01.Disk) (h1 : ‖(z : ℂ)‖ < 1) :
    APMT99A01.attachMk degree (Sum.inr (i, z)) ∈
        APMT99A01.sideA degree ∩ APMT99A01.sideB degree ↔
      0 < ‖(z : ℂ)‖ := by
  constructor
  · intro h
    exact norm_pos_iff.mpr (t99A01_attach_circleSide_aux_ne_zero degree i z h.1)
  · intro h0
    constructor
    · intro j he
      have hr : Relation.EqvGen (APMT99A01.AttachRel degree)
          (Sum.inr (i, z)) (Sum.inr (j, APMT99A01.diskCentre)) :=
        Quotient.exact he
      have hx := t99A01_attach_overlap_aux_eqv_interior h1 hr
      have hp : (j, APMT99A01.diskCentre) = (i, z) := Sum.inr.inj hx
      have hz : APMT99A01.diskCentre = z := (Prod.mk.inj hp).2
      have hv := congrArg (fun w : APMT99A01.Disk => (w : ℂ)) hz
      change (0 : ℂ) = (z : ℂ) at hv
      rw [← hv, norm_zero] at h0
      exact (lt_irrefl 0 h0).elim
    · exact ⟨i, z, h1, rfl⟩

private def t99A01_attach_overlap_aux_chart_aux_sigmaProd
    (X : Type*) [TopologicalSpace X] {r : ℕ} :
    (Σ _ : Fin r, X) ≃ₜ Fin r × X where
  toEquiv := Equiv.sigmaEquivProd (Fin r) X
  continuous_toFun := continuous_sigma fun _ =>
    continuous_const.prodMk continuous_id
  continuous_invFun := by
    rw [continuous_prod_of_discrete_left]
    intro i
    exact continuous_sigmaMk (i := i) (σ := fun _ : Fin r => X)

private def t99A01_attach_overlap_aux_chart_aux_prodSubtype {r : ℕ} :
    {p : Fin r × Metric.ball (0 : ℂ) 1 // 0 < ‖(p.2 : ℂ)‖} ≃ₜ
      Fin r × {z : Metric.ball (0 : ℂ) 1 // 0 < ‖(z : ℂ)‖} where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_fst.comp continuous_subtype_val |>.prodMk <|
      Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) _

private def t99A01_attach_overlap_aux_chart_aux_ballSubtype :
    {z : Metric.ball (0 : ℂ) 1 // 0 < ‖(z : ℂ)‖} ≃ₜ ↥t99A01_pball where
  toFun z := ⟨z.1.1, z.2, by
    simpa only [Metric.mem_ball, dist_zero_right] using z.1.2⟩
  invFun z := ⟨⟨z.1, by
    simpa only [Metric.mem_ball, dist_zero_right] using z.2.2⟩, z.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun z => by
      simpa only [Metric.mem_ball, dist_zero_right] using z.2.2)) _

private def t99A01_attach_overlap_aux_chart_aux_regroup {r : ℕ} :
    {p : Σ _ : Fin r, Metric.ball (0 : ℂ) 1 // 0 < ‖(p.2 : ℂ)‖} ≃ₜ
      Σ _ : Fin r, ↥t99A01_pball :=
  ((t99A01_attach_overlap_aux_chart_aux_sigmaProd
      (Metric.ball (0 : ℂ) 1)).subtype (fun _ => Iff.rfl)).trans <|
    t99A01_attach_overlap_aux_chart_aux_prodSubtype.trans <|
      (Homeomorph.prodCongr (Homeomorph.refl _)
        t99A01_attach_overlap_aux_chart_aux_ballSubtype).trans <|
      (t99A01_attach_overlap_aux_chart_aux_sigmaProd
        ↥t99A01_pball).symm

theorem t99A01_attach_overlap_aux_chart {r : ℕ} (degree : Fin r → ℕ) :
    ∃ c : ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) ≃ₜ
        (Σ _ : Fin r, ↥t99A01_pball),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (h0 : 0 < ‖(z : ℂ)‖) (h1 : ‖(z : ℂ)‖ < 1),
        (c.symm ⟨i, ⟨(z : ℂ), h0, h1⟩⟩).1 = APMT99A01.attachMk degree (Sum.inr (i, z)) := by
  obtain ⟨E, hE⟩ := t99A01_attach_diskSide degree
  have hpred : ∀ q : APMT99A01.sideB degree,
      (q.1 ∈ APMT99A01.sideA degree) ↔ 0 < ‖((E q).2 : ℂ)‖ := by
    rintro ⟨q, i, z, hz, rfl⟩
    have he := hE i z hz ⟨i, z, hz, rfl⟩
    rw [he]
    constructor
    · intro ha
      exact (t99A01_attach_overlap_aux_chart_mem degree i z hz).mp
        ⟨ha, i, z, hz, rfl⟩
    · intro h0
      exact ((t99A01_attach_overlap_aux_chart_mem degree i z hz).mpr h0).1
  let R : {q : APMT99A01.sideB degree // q.1 ∈ APMT99A01.sideA degree} ≃ₜ
      {p : Σ _ : Fin r, Metric.ball (0 : ℂ) 1 // 0 < ‖(p.2 : ℂ)‖} :=
    E.subtype hpred
  let F : ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) ≃ₜ
      {q : APMT99A01.sideB degree // q.1 ∈ APMT99A01.sideA degree} :=
    { toFun := fun q => ⟨⟨q.1, q.2.2⟩, q.2.1⟩
      invFun := fun q => ⟨q.1.1, q.2, q.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val _) _
      continuous_invFun := Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) _ }
  let c := F.trans (R.trans t99A01_attach_overlap_aux_chart_aux_regroup)
  refine ⟨c, ?_⟩
  intro i z h0 h1
  have hm : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈
      APMT99A01.sideA degree ∩ APMT99A01.sideB degree :=
    (t99A01_attach_overlap_aux_chart_mem degree i z h1).2 h0
  have he := hE i z h1 hm.2
  let x : ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) :=
    ⟨APMT99A01.attachMk degree (Sum.inr (i, z)), hm⟩
  have hx : c x = ⟨i, ⟨(z : ℂ), h0, h1⟩⟩ := by
    change t99A01_attach_overlap_aux_chart_aux_regroup
      ⟨E ⟨_, hm.2⟩, _⟩ = _
    have hEp : 0 < ‖((E ⟨APMT99A01.attachMk degree
        (Sum.inr (i, z)), hm.2⟩).2 : ℂ)‖ := (hpred _).mp hm.1
    have hp : (⟨E ⟨APMT99A01.attachMk degree (Sum.inr (i, z)), hm.2⟩, hEp⟩ :
        {p : Σ _ : Fin r, Metric.ball (0 : ℂ) 1 // 0 < ‖(p.2 : ℂ)‖}) =
        ⟨⟨i, ⟨(z : ℂ), by
          simpa only [Metric.mem_ball, dist_zero_right] using h1⟩⟩, h0⟩ :=
      Subtype.ext he
    rw [hp]
    rfl
  have hxi : c.symm ⟨i, ⟨(z : ℂ), h0, h1⟩⟩ = x := by
    rw [← hx, c.symm_apply_apply]
  exact congrArg Subtype.val hxi
/-- **Leaf (one punctured disk, 50--100 lines).** `z ↦ z/‖z‖` and `w ↦ w/2` are
homotopy inverse: `(t, z) ↦ ((1-t)‖z‖ + t/2) · z/‖z‖` stays in the punctured disk. -/
theorem t99A01_pball_circle :
    ∃ e : ContinuousMap.HomotopyEquiv ↥t99A01_pball Circle,
      ∀ w : Circle, ((e.invFun w : ↥t99A01_pball) : ℂ) = (w : ℂ) / 2 := by
  let radial : C(↥t99A01_pball, Circle) :=
    ⟨fun z => ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
        simp [Submonoid.unitSphere, div_self (ne_of_gt z.2.1)]⟩, by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.div₀
        (Complex.continuous_ofReal.comp
          (continuous_norm.comp continuous_subtype_val))
        (fun z => by exact_mod_cast ne_of_gt z.2.1)⟩
  let half : C(Circle, ↥t99A01_pball) :=
    ⟨fun w => ⟨(w : ℂ) / 2, by
        change 0 < ‖(w : ℂ) / 2‖ ∧ ‖(w : ℂ) / 2‖ < 1
        rw [norm_div, Circle.norm_coe]
        norm_num⟩, by
      exact Continuous.subtype_mk (continuous_subtype_val.div_const 2) _⟩
  have hradial_half : radial.comp half = ContinuousMap.id Circle := by
    apply ContinuousMap.ext
    intro w
    apply Subtype.ext
    change ((w : ℂ) / 2) / (‖(w : ℂ) / 2‖ : ℂ) = (w : ℂ)
    rw [norm_div, Circle.norm_coe]
    norm_num [div_div]
  let H : ContinuousMap.Homotopy (half.comp radial) (ContinuousMap.id ↥t99A01_pball) := {
    toFun := fun (tx : unitInterval × ↥t99A01_pball) => by
        let t : ℝ := tx.1
        let x : ℂ := tx.2
        let a : ℝ := (1 - t) * (1 / (2 * ‖x‖)) + t
        refine ⟨(a : ℂ) * x, ?_⟩
        have ht0 : 0 ≤ t := tx.1.2.1
        have ht1 : t ≤ 1 := tx.1.2.2
        have hx0 : 0 < ‖x‖ := tx.2.2.1
        have hx1 : ‖x‖ < 1 := tx.2.2.2
        have ha0 : 0 ≤ a := by
          dsimp [a]
          have hden : 0 ≤ 1 / (2 * ‖x‖) := (one_div_pos.mpr (mul_pos (by norm_num) hx0)).le
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hden) ht0
        have hamul : a * ‖x‖ = (1 - t) / 2 + t * ‖x‖ := by
          dsimp [a]
          field_simp
        change 0 < ‖(a : ℂ) * x‖ ∧ ‖(a : ℂ) * x‖ < 1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0,
          hamul]
        constructor <;> nlinarith
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hnorm : Continuous (fun tx : unitInterval × ↥t99A01_pball => ‖(tx.2 : ℂ)‖) :=
        continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
      have hne : ∀ tx : unitInterval × ↥t99A01_pball, 2 * ‖(tx.2 : ℂ)‖ ≠ 0 := by
        intro tx
        exact mul_ne_zero (by norm_num) (ne_of_gt tx.2.2.1)
      have ht : Continuous (fun tx : unitInterval × ↥t99A01_pball => (tx.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hx : Continuous (fun tx : unitInterval × ↥t99A01_pball => (tx.2 : ℂ)) :=
        continuous_subtype_val.comp continuous_snd
      exact (Complex.continuous_ofReal.comp
        (((continuous_const.sub ht).mul
          (continuous_const.div (continuous_const.mul hnorm) hne)).add ht)).mul hx
    map_zero_left x := by
      apply Subtype.ext
      dsimp [half, radial]
      simp only [sub_zero, one_mul, add_zero]
      change (((1 : ℝ) / (2 * ‖(x : ℂ)‖) : ℝ) : ℂ) * (x : ℂ) =
        (x : ℂ) / (‖(x : ℂ)‖ : ℂ) / 2
      push_cast
      field_simp
    map_one_left x := by
      apply Subtype.ext
      simp }
  refine ⟨⟨radial, half, ⟨H⟩, ?_⟩, ?_⟩
  · rw [hradial_half]
  · intro w
    rfl

/-- **Leaf (generic, 40--80 lines).** A homotopy equivalence induces one between
constant-fibre sigma types, index-preserving (`Sigma.map`/`continuous_sigma`; the
homotopies are `(t, ⟨i, x⟩) ↦ ⟨i, H (t, x)⟩`, continuous on each summand). -/
theorem t99A01_sigma_hequiv (r : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    ∃ E : ContinuousMap.HomotopyEquiv (Σ _ : Fin r, X) (Σ _ : Fin r, Y),
      ∀ (i : Fin r) (y : Y), E.invFun ⟨i, y⟩ = ⟨i, e.invFun y⟩ := by
  let F : C((Σ _ : Fin r, X), (Σ _ : Fin r, Y)) :=
    ⟨Sigma.map id (fun _ => e.toFun),
      Continuous.sigma_map (fun _ => e.toFun.continuous)⟩
  let G : C((Σ _ : Fin r, Y), (Σ _ : Fin r, X)) :=
    ⟨Sigma.map id (fun _ => e.invFun),
      Continuous.sigma_map (fun _ => e.invFun.continuous)⟩
  obtain ⟨hleft⟩ := e.left_inv
  obtain ⟨hright⟩ := e.right_inv
  let Hleft : ContinuousMap.Homotopy (G.comp F) (ContinuousMap.id _) := {
    toFun := fun tx => ⟨tx.2.1, hleft (tx.1, tx.2.2)⟩
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      rintro ⟨t, ⟨i, x⟩⟩
      have hc : Continuous (fun tx : unitInterval × (Σ _ : Fin r, X) =>
          (⟨i, hleft (tx.1, tx.2.2)⟩ : Σ _ : Fin r, X)) :=
        continuous_sigmaMk.comp
          (hleft.continuous.comp (continuous_fst.prodMk (by
            exact (continuous_sigma fun _ => continuous_id).comp continuous_snd)))
      apply hc.continuousAt.congr_of_eventuallyEq
      have hsnd : Continuous (fun p : unitInterval × Sigma (fun _ : Fin r => X) => p.2) :=
        continuous_snd
      filter_upwards [((@isOpen_range_sigmaMk (Fin r) (fun _ => X) _ i).preimage
        hsnd).mem_nhds ⟨x, rfl⟩] with tx htx
      rcases tx with ⟨t', ⟨j, z⟩⟩
      have hji : j = i := by
        obtain ⟨w, hw⟩ := htx
        exact (congrArg Sigma.fst hw).symm
      subst j
      rfl
    map_zero_left := by
      rintro ⟨i, x⟩
      change (Sigma.mk i (hleft (0, x)) : Sigma (fun _ : Fin r => X)) =
        Sigma.mk i (e.invFun (e.toFun x))
      exact congrArg (fun z => (Sigma.mk i z : Sigma (fun _ : Fin r => X)))
        (hleft.map_zero_left x)
    map_one_left := by
      rintro ⟨i, x⟩
      change (Sigma.mk i (hleft (1, x)) : Sigma (fun _ : Fin r => X)) = Sigma.mk i x
      exact congrArg (fun z => (Sigma.mk i z : Sigma (fun _ : Fin r => X)))
        (hleft.map_one_left x) }
  let Hright : ContinuousMap.Homotopy (F.comp G) (ContinuousMap.id _) := {
    toFun := fun ty => ⟨ty.2.1, hright (ty.1, ty.2.2)⟩
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      rintro ⟨t, ⟨i, y⟩⟩
      have hc : Continuous (fun ty : unitInterval × (Σ _ : Fin r, Y) =>
          (⟨i, hright (ty.1, ty.2.2)⟩ : Σ _ : Fin r, Y)) :=
        continuous_sigmaMk.comp
          (hright.continuous.comp (continuous_fst.prodMk (by
            exact (continuous_sigma fun _ => continuous_id).comp continuous_snd)))
      apply hc.continuousAt.congr_of_eventuallyEq
      have hsnd : Continuous (fun p : unitInterval × Sigma (fun _ : Fin r => Y) => p.2) :=
        continuous_snd
      filter_upwards [((@isOpen_range_sigmaMk (Fin r) (fun _ => Y) _ i).preimage
        hsnd).mem_nhds ⟨y, rfl⟩] with ty hty
      rcases ty with ⟨t', ⟨j, z⟩⟩
      have hji : j = i := by
        obtain ⟨w, hw⟩ := hty
        exact (congrArg Sigma.fst hw).symm
      subst j
      rfl
    map_zero_left := by
      rintro ⟨i, y⟩
      change (Sigma.mk i (hright (0, y)) : Sigma (fun _ : Fin r => Y)) =
        Sigma.mk i (e.toFun (e.invFun y))
      exact congrArg (fun z => (Sigma.mk i z : Sigma (fun _ : Fin r => Y)))
        (hright.map_zero_left y)
    map_one_left := by
      rintro ⟨i, y⟩
      change (Sigma.mk i (hright (1, y)) : Sigma (fun _ : Fin r => Y)) = Sigma.mk i y
      exact congrArg (fun z => (Sigma.mk i z : Sigma (fun _ : Fin r => Y)))
        (hright.map_one_left y) }
  let E : ContinuousMap.HomotopyEquiv (Σ _ : Fin r, X) (Σ _ : Fin r, Y) :=
    ⟨F, G, ⟨Hleft⟩, ⟨Hright⟩⟩
  refine ⟨E, ?_⟩
  intro i y
  rfl

/-- Punctured disks retract radially onto the radius-`1/2` circles. -/
theorem t99A01_attach_overlap_aux_pball (r : ℕ) :
    ∃ e : ContinuousMap.HomotopyEquiv (Σ _ : Fin r, ↥t99A01_pball) (Σ _ : Fin r, Circle),
      ∀ (i : Fin r) (w : Circle),
        (e.invFun ⟨i, w⟩).1 = i ∧ ((e.invFun ⟨i, w⟩).2 : ℂ) = (w : ℂ) / 2 := by
  obtain ⟨e, he⟩ := t99A01_pball_circle
  obtain ⟨E, hE⟩ := t99A01_sigma_hequiv r e
  exact ⟨E, fun i w => by rw [hE]; exact ⟨rfl, he w⟩⟩
theorem t99A01_attach_overlap {r : ℕ} (degree : Fin r → ℕ) :
    ∃ e : ContinuousMap.HomotopyEquiv
        ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle),
      ∀ (i : Fin r) (w : Circle), (e.invFun ⟨i, w⟩).1 = APMT99A01.halfLoop degree i w := by
  obtain ⟨c, hc⟩ := t99A01_attach_overlap_aux_chart degree
  obtain ⟨e2, he2⟩ := t99A01_attach_overlap_aux_pball r
  refine ⟨c.toHomotopyEquiv.trans e2, fun i w => ?_⟩
  obtain ⟨h1, h2⟩ := he2 i w
  have hw : ‖((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ)‖ = 1 / 2 := by
    change ‖(w : ℂ) / 2‖ = 1 / 2
    rw [norm_div, Circle.norm_coe]; norm_num
  have hpos : 0 < ‖((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ)‖ := by
    rw [hw]; norm_num
  have hlt : ‖((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ)‖ < 1 := by
    rw [hw]; norm_num
  have hp : e2.invFun ⟨i, w⟩ =
      ⟨i, ⟨((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ), hpos, hlt⟩⟩ := by
    rcases hq : e2.invFun ⟨i, w⟩ with ⟨j, q⟩
    rw [hq] at h1 h2
    simp only at h1 h2
    subst h1
    congr 1
    exact Subtype.ext h2
  change (c.symm (e2.invFun ⟨i, w⟩)).1 = _
  rw [hp, hc _ _ hpos hlt]
  rfl
instance t99A01_chainComplex_hasFiniteBiproducts :
    Limits.HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- **Leaf (simplices of a disjoint union, 40--90 lines).** Every singular simplex of
`Σ j, Y j` lies in exactly one summand: the topological simplex is connected
(`isPreconnected_univ`, `Sigma` components: `continuous_sigma_iff`,
`IsPreconnected.subset_...`/`Sigma.isConnected_iff`). -/
theorem t99A01_sigma_simplices {r : ℕ} (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)]
    (n : ℕ) :
    Function.Bijective (fun p : Σ i, (TopCat.toSSet.obj (TopCat.of (Y i))).obj
        (Opposite.op (SimplexCategory.mk n)) ↦
      (TopCat.toSSet.map (TopCat.ofHom (⟨Sigma.mk p.1, continuous_sigmaMk⟩ :
        C(Y p.1, Σ j, Y j)))).app (Opposite.op (SimplexCategory.mk n)) p.2) := by
  let N := Opposite.op (SimplexCategory.mk n)
  let E (X : Type) [TopologicalSpace X] :=
    TopCat.toSSetObjEquiv (TopCat.of X) N
  let F := fun p : Σ i, (TopCat.toSSet.obj (TopCat.of (Y i))).obj N ↦
    (TopCat.toSSet.map (TopCat.ofHom (⟨Sigma.mk p.1, continuous_sigmaMk⟩ :
      C(Y p.1, Σ j, Y j)))).app N p.2
  have hF (p : Σ i, (TopCat.toSSet.obj (TopCat.of (Y i))).obj N) :
      E (Σ j, Y j) (F p) =
        (⟨Sigma.mk p.1 ∘ (E (Y p.1) p.2),
          continuous_sigmaMk.comp (E (Y p.1) p.2).continuous⟩ :
          C(_, Σ j, Y j)) := by
    rfl
  change Function.Bijective F
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ hab
    have hc := congrArg (E (Σ j, Y j)) hab
    rw [hF, hF] at hc
    have hij : i = j := by
      have hp := congrArg (fun f => (f (Classical.arbitrary _)).1) hc
      simpa using hp
    subst j
    congr 1
    apply (E (Y i)).injective
    apply ContinuousMap.ext
    intro x
    have hp := congrArg (fun f => f x) hc
    change Sigma.mk i ((E (Y i) a) x) = Sigma.mk i ((E (Y i) b) x) at hp
    exact eq_of_heq (Sigma.mk.inj_iff.mp hp).2
  · intro q
    let f := E (Σ j, Y j) q
    obtain ⟨i, g, hg, hfg⟩ := f.continuous.exists_lift_sigma
    let a := (E (Y i)).symm ⟨g, hg⟩
    refine ⟨⟨i, a⟩, ?_⟩
    apply (E (Σ j, Y j)).injective
    rw [hF]
    apply ContinuousMap.ext
    intro x
    change Sigma.mk i (g x) = f x
    exact (congrFun hfg x).symm

/-- **Leaf (chains of a disjoint union, 60--120 lines).** Given the simplex
bijection, the singular chain complex of `Σ j, Y j` is the biproduct of the summands'
chain complexes.  Degreewise: free module on a sigma type is the biproduct of free
modules (`ConstructionTargets.CoefficientSigmaConstFinsuppComparison.sigmaConstFinsuppIso`,
`ModuleCat` free/`Finsupp`); a chain map that is degreewise iso is iso
(`HomologicalComplex.Hom.isIso_of_components`). -/
theorem t99A01_sigma_chains {r : ℕ} (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)]
    (hsimp : ∀ n : ℕ, Function.Bijective (fun p : Σ i, (TopCat.toSSet.obj (TopCat.of (Y i))).obj
        (Opposite.op (SimplexCategory.mk n)) ↦
      (TopCat.toSSet.map (TopCat.ofHom (⟨Sigma.mk p.1, continuous_sigmaMk⟩ :
        C(Y p.1, Σ j, Y j)))).app (Opposite.op (SimplexCategory.mk n)) p.2)) :
    IsIso (Limits.biproduct.desc fun i : Fin r ↦
      ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
        (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) := by
  classical
  let m := fun i : Fin r ↦
    ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
      (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))
  let f := Limits.biproduct.desc m
  change IsIso f
  letI : ∀ n, IsIso (f.f n) := fun n ↦ by
    let S := fun i : Fin r ↦
      (TopCat.toSSet.obj (TopCat.of (Y i))).obj
        (Opposite.op (SimplexCategory.mk n))
    let T := (TopCat.toSSet.obj (TopCat.of (Σ j, Y j))).obj
        (Opposite.op (SimplexCategory.mk n))
    let q : (Σ i, S i) → T := fun p ↦
      (TopCat.toSSet.map (TopCat.ofHom (⟨Sigma.mk p.1, continuous_sigmaMk⟩ :
        C(Y p.1, Σ j, Y j)))).app
          (Opposite.op (SimplexCategory.mk n)) p.2
    let e : (Σ i, S i) ≃ T := Equiv.ofBijective q (hsimp n)
    let u : ∀ i : Fin r,
        (∐ fun _ : S i ↦ ModuleCat.of ℤ ℤ) ⟶
          ∐ fun _ : T ↦ ModuleCat.of ℤ ℤ := fun i ↦
      Limits.Sigma.map' (fun x ↦ q ⟨i, x⟩) (fun _ ↦ 𝟙 _)
    let g :=
      (Limits.biproduct.isoCoproduct
        (fun i : Fin r ↦ ∐ fun _ : S i ↦ ModuleCat.of ℤ ℤ)).hom ≫
      (Limits.sigmaSigmaIso S
        (fun i (_ : S i) ↦ ModuleCat.of ℤ ℤ)).hom ≫
      (Limits.Sigma.whiskerEquiv (C := ModuleCat ℤ)
        (f := fun _ : (Σ i, S i) ↦ ModuleCat.of ℤ ℤ)
        (g := fun _ : T ↦ ModuleCat.of ℤ ℤ) e
        (fun _ ↦ Iso.refl (ModuleCat.of ℤ ℤ))).hom
    have hg : Limits.biproduct.desc u = g := by
      apply Limits.biproduct.hom_ext'
      intro i
      rw [Limits.biproduct.ι_desc]
      dsimp only [g]
      rw [← Category.assoc, Limits.biproduct.isoCoproduct_hom]
      simp only [Category.assoc, Limits.biproduct.ι_desc_assoc]
      rw [Limits.sigmaSigmaIso_hom]
      simp only [Category.assoc, Limits.Sigma.ι_desc_assoc]
      apply Limits.Sigma.hom_ext
      intro x
      dsimp only [u, q]
      rw [Limits.Sigma.ι_desc_assoc]
      simp [Limits.Sigma.whiskerEquiv]
      rfl
    let E := HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n
    have hu : Limits.biproduct.desc (fun i : Fin r ↦ E.map (m i)) =
        Limits.biproduct.desc u := by
      apply Limits.biproduct.hom_ext'
      intro i
      dsimp [E, m, u, S, T, q,
        ConstructionTargets.CoefficientH0.singularPostcomposition,
        ConstructionTargets.CoefficientH0.SingularChains,
        AlgebraicTopology.singularChainComplexFunctor,
        AlgebraicTopology.SSet.singularChainComplexFunctor,
        AlgebraicTopology.alternatingFaceMapComplex,
        AlgebraicTopology.AlternatingFaceMapComplex.map,
        ChainComplex.ofHom]
    have hf : f.f n = (E.mapBiproduct fun i : Fin r ↦
        (ConstructionTargets.CoefficientH0.SingularChains ℤ
          (TopCat.of (Y i)))).hom ≫ g := by
      change E.map f = _
      rw [← Limits.biproduct.mapBiproduct_hom_desc]
      exact congrArg (fun z ↦
        (E.mapBiproduct fun i : Fin r ↦
          (ConstructionTargets.CoefficientH0.SingularChains ℤ
            (TopCat.of (Y i)))).hom ≫ z) (hu.trans hg)
    have hg_iso : IsIso g := by
      change IsIso
        ((Limits.biproduct.isoCoproduct
          (fun i : Fin r ↦ ∐ fun _ : S i ↦ ModuleCat.of ℤ ℤ)).hom ≫
        (Limits.sigmaSigmaIso S
          (fun i (_ : S i) ↦ ModuleCat.of ℤ ℤ)).hom ≫
        (Limits.Sigma.whiskerEquiv (C := ModuleCat ℤ)
          (f := fun _ : (Σ i, S i) ↦ ModuleCat.of ℤ ℤ)
          (g := fun _ : T ↦ ModuleCat.of ℤ ℤ) e
          (fun _ ↦ Iso.refl (ModuleCat.of ℤ ℤ))).hom)
      exact IsIso.comp_isIso' inferInstance
        (IsIso.comp_isIso' inferInstance inferInstance)
    have hE_iso : IsIso (E.mapBiproduct fun i : Fin r ↦
        (ConstructionTargets.CoefficientH0.SingularChains ℤ
          (TopCat.of (Y i)))).hom := inferInstance
    rw [hf]
    exact IsIso.comp_isIso' hE_iso hg_iso
  exact HomologicalComplex.Hom.isIso_of_components f

/-- **Leaf (homology is additive, 20--60 lines).** Pure category theory: the
homology functor is additive, so preserves finite biproducts
(`Functor.mapBiproduct`, `HomologicalComplex.homologyFunctor`, `Functor.Additive`). -/
theorem t99A01_homology_biproduct {r : ℕ} (Cs : Fin r → ChainComplex (ModuleCat ℤ) ℕ)
    (D : ChainComplex (ModuleCat ℤ) ℕ) (f : ∀ i, Cs i ⟶ D)
    (hf : IsIso (Limits.biproduct.desc f)) (k : ℕ) :
    IsIso (Limits.biproduct.desc fun i ↦ HomologicalComplex.homologyMap (f i) k) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k
  letI : IsIso (Limits.biproduct.desc f) := hf
  haveI : IsIso (F.map (Limits.biproduct.desc f)) := inferInstance
  haveI : IsIso (F.mapBiproduct Cs).inv := inferInstance
  have hcomp : IsIso ((F.mapBiproduct Cs).inv ≫
      F.map (Limits.biproduct.desc f)) := IsIso.comp_isIso
  change IsIso (Limits.biproduct.desc fun i => F.map (f i))
  rw [← Limits.biproduct.mapBiproduct_inv_map_desc F Cs f]
  exact hcomp

theorem t99A01_sigma_homology {r : ℕ} (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)]
    (k : ℕ) :
    IsIso (Limits.biproduct.desc fun i : Fin r ↦
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)) :=
  t99A01_homology_biproduct _ _ _
    (t99A01_sigma_chains Y (t99A01_sigma_simplices Y)) k
/-- **LIBRARY leaf (circle winding, 60--120 lines).** The oriented `H₁`
coordinate of all attaching maps is the displayed positive degree row. -/
theorem t99A01_circlePower_hOne_row {r : ℕ} (degree : Fin r → ℕ) :
    ∃ e : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ,
      ∀ i : Fin r,
        e.inv ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map
              (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e.hom =
          ModuleCat.ofHom (APMT99A01.intTimesNat (degree i)) := by
  open ConstructionTargets.IntegralSingularHomologyComparison in
    let e : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ :=
      singularHomologyModuleIsoOfGroupIso (TopCat.of Circle) 1
        (ModuleCat.of ℤ ℤ)
        ConstructionTargets.BoundaryTorusMayerVietoris.circleH1GroupIsoInt
    refine ⟨e, ?_⟩
    intro i
    apply forgetIntModules.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    have he_hom : forgetIntModules.map e.hom =
        (singularHomologyComparison (TopCat.of Circle) 1).hom ≫
          ConstructionTargets.BoundaryTorusMayerVietoris.circleH1GroupIsoInt.hom := by
      dsimp [e, singularHomologyModuleIsoOfGroupIso,
        moduleIsoOfUnderlyingIso]
      exact forgetIntModules.map_preimage _
    have he_inv : forgetIntModules.map e.inv =
        ConstructionTargets.BoundaryTorusMayerVietoris.circleH1GroupIsoInt.inv ≫
          (singularHomologyComparison (TopCat.of Circle) 1).inv := by
      apply (cancel_mono (forgetIntModules.map e.hom)).1
      rw [← Functor.map_comp, e.inv_hom_id]
      rw [he_hom]
      rw [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      exact forgetIntModules.map_id _
    rw [he_inv, he_hom]
    have hpower : APMT99A01.circlePower (degree i) =
        ConstructionTargets.T97A04Closure.circleZPow (degree i : ℤ) := by
      ext z
      exact (zpow_natCast (z : ℂ) (degree i)).symm
    rw [hpower]
    simp only [Category.assoc]
    rw [← Category.assoc _
          (singularHomologyComparison (TopCat.of Circle) 1).hom,
      singularHomologyComparison_naturality, Category.assoc,
      Iso.inv_hom_id_assoc]
    change
      ConstructionTargets.BoundaryTorusMayerVietoris.circleH1GroupIsoInt.inv ≫
          HomologicalComplex.homologyMap
            (ConstructionTargets.SingularSubdivision.singularPostcomposition
              (ConstructionTargets.T97A04Closure.circleZPow (degree i : ℤ))) 1 ≫
          ConstructionTargets.BoundaryTorusMayerVietoris.circleH1GroupIsoInt.hom = _
    rw [ConstructionTargets.T97A04Closure.circleZPow_H1_coordinate]
    ext x
    simp [APMT99A01.intTimesNat, smul_eq_mul]

/-- **Leaf (integral open-cover Mayer–Vietoris).** The ℤ version of
`RP3Homology.rationalMayerVietoris` (`ConstructionTargets/CP2RationalHomology.lean`).
Its proof is coefficient-generic: copy it with `ℚ ↦ ℤ` (the `Coefficient*` modules
work over any commutative ring; `ProductionOpenCoverMayerVietoris` is already over ℤ).
Bank the pieces as `_aux` lemmas, as there. -/
theorem t99A01_integralMayerVietoris {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ δ : ∀ n, APMT99A01.H (n + 1) X ⟶ APMT99A01.H n ↥(U ∩ V),
      (∀ n, LinearMap.range (APMT99A01.zI U V n).hom =
        LinearMap.ker (APMT99A01.zJ U V n).hom) ∧
      (∀ n, LinearMap.range (APMT99A01.zJ U V (n + 1)).hom = LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (APMT99A01.zI U V n).hom) := by
  exact IntegralMV.integralMayerVietoris U V hU hV hcov
/-- **Leaf (transport, LIBRARY-sized: expect PARTIAL and bank pieces).** Assemble
`AttachMVData` from the standard cover.  Coordinates: `H_*(sideA) ≅ H_*(Circle)`
(by `ρ`), `H_*(sideB) ≅ ⨁ H_*(ball)` (contractible balls), `H_*(A∩B) ≅ ⨁ H_*(Circle)`.
Under them, `H₁(A∩B) → H₁(A)` is `ρ ∘ halfLoop i = (· ^ degree i)` on summand `i`,
which `hwinding` turns into `degreeMap`; `H₀(A∩B) → H₀(B)` is the identity on `ℤ^r`
(injective; record it as `i₀_eq : i₀ x = (∑ i, x i, x)`).  Higher vanishing: `H_k` of circles and balls vanish for `k ≥ 2`. -/
lemma t99A01_attach_transport_aux_mv {r : ℕ} (degree : Fin r → ℕ)
    (hcover : IsOpen (APMT99A01.sideA degree) ∧ IsOpen (APMT99A01.sideB degree) ∧
      APMT99A01.sideA degree ∪ APMT99A01.sideB degree = Set.univ)
    (hmv : ∀ (U V : Set (APMT99A01.AttachSpace degree)), IsOpen U → IsOpen V →
      U ∪ V = Set.univ →
      ∃ δ : ∀ n, APMT99A01.H (n + 1) (APMT99A01.AttachSpace degree) ⟶
          APMT99A01.H n ↥(U ∩ V),
        (∀ n, LinearMap.range (APMT99A01.zI U V n).hom =
          LinearMap.ker (APMT99A01.zJ U V n).hom) ∧
        (∀ n, LinearMap.range (APMT99A01.zJ U V (n + 1)).hom =
          LinearMap.ker (δ n).hom) ∧
        (∀ n, LinearMap.range (δ n).hom =
          LinearMap.ker (APMT99A01.zI U V n).hom)) :
    ∃ δ : ∀ n, APMT99A01.H (n + 1) (APMT99A01.AttachSpace degree) ⟶
        APMT99A01.H n ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
      (∀ n, LinearMap.range
          (APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom =
        LinearMap.ker
          (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom) ∧
      (∀ n, LinearMap.range
          (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) (n + 1)).hom =
        LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker
        (APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom) := by
  exact hmv _ _ hcover.1 hcover.2.1 hcover.2.2

/-! The following coordinates are definitions, not existential choices.  This
is important: all later map equations therefore refer to literally the same
coordinate. -/

noncomputable def t99A01_sideA_homotopyEquiv {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle))
    (ι : C(Circle, APMT99A01.sideA degree))
    (hρι : ρ.comp ι = ContinuousMap.id Circle)
    (hιρ : ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _)) :
    ContinuousMap.HomotopyEquiv (APMT99A01.sideA degree) Circle where
  toFun := ρ
  invFun := ι
  left_inv := hιρ
  right_inv := by simpa [hρι] using
    (ContinuousMap.Homotopic.refl (ContinuousMap.id Circle))

noncomputable def t99A01_sideA_coordinate {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle))
    (ι : C(Circle, APMT99A01.sideA degree))
    (hρι : ρ.comp ι = ContinuousMap.id Circle)
    (hιρ : ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _)) (n : ℕ) :
    APMT99A01.H n (APMT99A01.sideA degree) ≅ APMT99A01.H n Circle :=
  ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℤ
    (t99A01_sideA_homotopyEquiv degree ρ ι hρι hιρ) n

noncomputable def t99A01_diskSide_sigma_coordinate {r : ℕ} (degree : Fin r → ℕ)
    (e : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1)) (n : ℕ) :
    APMT99A01.H n (APMT99A01.sideB degree) ≅
      APMT99A01.H n (Σ _ : Fin r, Metric.ball (0 : ℂ) 1) :=
  ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℤ
    e.toHomotopyEquiv n

noncomputable def t99A01_overlap_sigma_coordinate {r : ℕ} (degree : Fin r → ℕ)
    (e : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (n : ℕ) :
    APMT99A01.H n ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) ≅
      APMT99A01.H n (Σ _ : Fin r, Circle) :=
  ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv ℤ e n

/-- The canonical splitting of homology of a finite disjoint union, with the
geometric map pointing from the biproduct to the sigma type. -/
noncomputable def t99A01_sigma_coordinate {r : ℕ}
    (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (n : ℕ)
    (hsigma : IsIso (Limits.biproduct.desc fun i : Fin r ↦
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) n :
        (⨁ fun i : Fin r ↦ APMT99A01.H n (Y i)) ⟶ APMT99A01.H n (Σ j, Y j))) :
    APMT99A01.H n (Σ i, Y i) ≅ (⨁ fun i : Fin r ↦ APMT99A01.H n (Y i)) :=
  by
    let f := (Limits.biproduct.desc fun i : Fin r ↦
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) n)
    letI : IsIso f := hsigma
    exact (asIso f).symm

/-- The underlying module of a finite biproduct of copies of `ℤ` is `Fin r → ℤ`. -/
noncomputable def t99A01_biproduct_int_coordinate (r : ℕ) :
    (⨁ fun _ : Fin r ↦ ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ (Fin r → ℤ) :=
  ModuleCat.biproductIsoPi _

/-- The standard degree-zero coordinate of a nonempty path-connected space. -/
noncomputable def t99A01_h0_coordinate (Y : Type) [TopologicalSpace Y]
    [PathConnectedSpace Y] (p : Y) : APMT99A01.H 0 Y ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.CoefficientH0.h0Iso ℤ p

def t99A01_coordinateSum {r : ℕ} : (Fin r → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ i, x i
  map_add' _ _ := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i, c * x i) = c * ∑ i, x i
    rw [Finset.mul_sum]

/-- Pure algebra behind the low-degree Mayer--Vietoris transport.  In
particular this lemma knows nothing about the cover or its topology. -/
lemma t99A01_lowData_of_coordinates_aux_i0_injective {r : ℕ} :
    Function.Injective (fun x : Fin r → ℤ => (t99A01_coordinateSum x, x)) := by
  intro x y h
  exact congrArg Prod.snd h

/-- All inputs of the low-degree algebra, bundled. -/
structure t99A01_LowInput {r : ℕ} (degree : Fin r → ℕ) where
  O₀ : ModuleCat ℤ
  O₁ : ModuleCat ℤ
  A₀ : ModuleCat ℤ
  A₁ : ModuleCat ℤ
  A₂ : ModuleCat ℤ
  B₀ : ModuleCat ℤ
  B₁ : ModuleCat ℤ
  B₂ : ModuleCat ℤ
  I₀ : O₀ ⟶ A₀ ⊞ B₀
  I₁ : O₁ ⟶ A₁ ⊞ B₁
  J₀ : A₀ ⊞ B₀ ⟶ APMT99A01.H 0 (APMT99A01.AttachSpace degree)
  J₁ : A₁ ⊞ B₁ ⟶ APMT99A01.H 1 (APMT99A01.AttachSpace degree)
  J₂ : A₂ ⊞ B₂ ⟶ APMT99A01.H 2 (APMT99A01.AttachSpace degree)
  δ₀ : APMT99A01.H 1 (APMT99A01.AttachSpace degree) ⟶ O₀
  δ₁ : APMT99A01.H 2 (APMT99A01.AttachSpace degree) ⟶ O₁
  hI₁J₁ : LinearMap.range I₁.hom = LinearMap.ker J₁.hom
  hJ₁δ₀ : LinearMap.range J₁.hom = LinearMap.ker δ₀.hom
  hδ₀I₀ : LinearMap.range δ₀.hom = LinearMap.ker I₀.hom
  hI₀J₀ : LinearMap.range I₀.hom = LinearMap.ker J₀.hom
  hJ₂δ₁ : LinearMap.range J₂.hom = LinearMap.ker δ₁.hom
  hδ₁I₁ : LinearMap.range δ₁.hom = LinearMap.ker I₁.hom
  hA₂ : Limits.IsZero A₂
  hB₁ : Limits.IsZero B₁
  hB₂ : Limits.IsZero B₂
  hJ₀ : Function.Surjective J₀.hom
  cO₀ : O₀ ≅ ModuleCat.of ℤ (Fin r → ℤ)
  cO₁ : O₁ ≅ ModuleCat.of ℤ (Fin r → ℤ)
  cA₀ : A₀ ≅ ModuleCat.of ℤ ℤ
  cA₁ : A₁ ≅ ModuleCat.of ℤ ℤ
  cB₀ : B₀ ≅ ModuleCat.of ℤ (Fin r → ℤ)
  hdegree : cO₁.inv ≫ I₁ ≫ Limits.biprod.fst ≫ cA₁.hom =
    ModuleCat.ofHom (APMT99A01.degreeMap degree)
  hsum : cO₀.inv ≫ I₀ ≫ Limits.biprod.fst ≫ cA₀.hom = ModuleCat.ofHom t99A01_coordinateSum
  hid : cO₀.inv ≫ I₀ ≫ Limits.biprod.snd ≫ cB₀.hom = 𝟙 _

namespace t99A01_LowInput

variable {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree)

/-- `ℤ → H₁(W)`: the `A`-summand of `J₁` in coordinates. -/
noncomputable def j₁ : ℤ →ₗ[ℤ] APMT99A01.H 1 (APMT99A01.AttachSpace degree) :=
  (D.cA₁.inv ≫ Limits.biprod.inl ≫ D.J₁).hom

/-- `H₁(W) → ℤ^r`: the connecting map in coordinates. -/
noncomputable def δ₁c : APMT99A01.H 1 (APMT99A01.AttachSpace degree) →ₗ[ℤ] (Fin r → ℤ) :=
  (D.δ₀ ≫ D.cO₀.hom).hom

/-- `ℤ^r → ℤ × ℤ^r`, `x ↦ (∑ xᵢ, x)`. -/
def i₀ : (Fin r → ℤ) →ₗ[ℤ] (ℤ × (Fin r → ℤ)) :=
  LinearMap.prod t99A01_coordinateSum LinearMap.id

/-- `ℤ × ℤ^r → H₀(W)`: `J₀` in coordinates. -/
noncomputable def j₀ : (ℤ × (Fin r → ℤ)) →ₗ[ℤ] APMT99A01.H 0 (APMT99A01.AttachSpace degree) :=
  (D.cA₀.inv ≫ Limits.biprod.inl ≫ D.J₀).hom.coprod (D.cB₀.inv ≫ Limits.biprod.inr ≫ D.J₀).hom

/-- `H₂(W) → ℤ^r`: the connecting map in coordinates. -/
noncomputable def δ₂c : APMT99A01.H 2 (APMT99A01.AttachSpace degree) →ₗ[ℤ] (Fin r → ℤ) :=
  (D.δ₁ ≫ D.cO₁.hom).hom

end t99A01_LowInput

/-- **Leaf.** Exactness at `ℤ` in degree one (`B₁ = 0`, `hdegree`). -/
lemma t99A01_low_exact_i₁_j₁ {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree) :
    LinearMap.range (APMT99A01.degreeMap degree) = LinearMap.ker D.j₁ := by
  let inl₁ : D.A₁ ⟶ (D.A₁ ⊞ D.B₁) := Limits.biprod.inl
  let fst₁ : (D.A₁ ⊞ D.B₁) ⟶ D.A₁ := Limits.biprod.fst
  let snd₁ : (D.A₁ ⊞ D.B₁) ⟶ D.B₁ := Limits.biprod.snd
  letI := ModuleCat.subsingleton_of_isZero D.hB₁
  have hfst_inl : ∀ a : D.A₁, fst₁.hom (inl₁.hom a) = a := by
    intro a
    change ((inl₁ ≫ fst₁).hom a) = ModuleCat.Hom.hom (𝟙 D.A₁) a
    rw [show inl₁ ≫ fst₁ = 𝟙 D.A₁ by
      exact Limits.biprod.inl_fst]
  have hI₁_apply : ∀ x : Fin r → ℤ,
      D.I₁.hom (D.cO₁.inv.hom x) =
        inl₁.hom (D.cA₁.inv.hom (APMT99A01.degreeMap degree x)) := by
    intro x
    apply (ModuleCat.biprodIsoProd D.A₁ D.B₁).toLinearEquiv.injective
    apply Prod.ext
    · change fst₁.hom _ = fst₁.hom _
      have h := congrArg (fun f => f x)
        (congrArg CategoryTheory.ConcreteCategory.hom D.hdegree)
      calc
        fst₁.hom (D.I₁.hom (D.cO₁.inv.hom x)) =
            D.cA₁.inv.hom (APMT99A01.degreeMap degree x) := by
          simpa [fst₁] using congrArg D.cA₁.inv.hom h
        _ = fst₁.hom (inl₁.hom (D.cA₁.inv.hom
            (APMT99A01.degreeMap degree x))) := (hfst_inl _).symm
    · change snd₁.hom _ = snd₁.hom _
      exact Subsingleton.elim _ _
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change D.J₁.hom (inl₁.hom (D.cA₁.inv.hom
      (APMT99A01.degreeMap degree x))) = 0
    rw [← hI₁_apply]
    exact LinearMap.mem_ker.mp
      (D.hI₁J₁ ▸ LinearMap.mem_range_self D.I₁.hom (D.cO₁.inv.hom x))
  · intro hy
    have hy' : inl₁.hom (D.cA₁.inv.hom y) ∈ LinearMap.ker D.J₁.hom := by
      exact hy
    rw [← D.hI₁J₁] at hy'
    rcases hy' with ⟨z, hz⟩
    refine ⟨D.cO₁.hom.hom z, ?_⟩
    have hi := hI₁_apply (D.cO₁.hom.hom z)
    have hi' : D.I₁.hom z = inl₁.hom (D.cA₁.inv.hom
        (APMT99A01.degreeMap degree (D.cO₁.hom.hom z))) := by
      simpa using hi
    have hz' := congrArg (fun w => fst₁.hom w) (hi'.symm.trans hz)
    simpa only [hfst_inl, D.cA₁.inv_hom_id_apply] using
      congrArg D.cA₁.hom.hom hz'

/-- **Leaf.** Exactness at `H₁(W)` (`B₁ = 0`). -/
lemma t99A01_low_exact_j₁_δ₁ {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree) :
    LinearMap.range D.j₁ = LinearMap.ker D.δ₁c := by
  let fst₁ : D.A₁ ⊞ D.B₁ ⟶ D.A₁ := Limits.biprod.fst
  let snd₁ : D.A₁ ⊞ D.B₁ ⟶ D.B₁ := Limits.biprod.snd
  let inl₁ : D.A₁ ⟶ D.A₁ ⊞ D.B₁ := Limits.biprod.inl
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hh := LinearMap.mem_ker.mp
      (D.hJ₁δ₀ ▸ LinearMap.mem_range_self D.J₁.hom
        (inl₁.hom (D.cA₁.inv.hom x)))
    simpa [t99A01_LowInput.δ₁c] using congrArg D.cO₀.hom.hom hh
  · intro hy
    have hy' : y ∈ LinearMap.ker D.δ₀.hom := by
      rw [LinearMap.mem_ker] at hy ⊢
      have hh := congrArg D.cO₀.inv.hom hy
      simpa [t99A01_LowInput.δ₁c] using hh
    rw [← D.hJ₁δ₀] at hy'
    rcases hy' with ⟨z, hz⟩
    refine ⟨D.cA₁.hom.hom (fst₁.hom z), ?_⟩
    have hz0 : z = inl₁.hom (D.cA₁.inv.hom
        (D.cA₁.hom.hom (fst₁.hom z))) := by
      apply (ModuleCat.biprodIsoProd D.A₁ D.B₁).toLinearEquiv.injective
      apply Prod.ext
      · change fst₁.hom z = fst₁.hom (inl₁.hom _)
        have hcat : inl₁ ≫ fst₁ = 𝟙 D.A₁ := by simp [fst₁, inl₁]
        have happ := congrArg (fun f => f (fst₁.hom z))
          (congrArg CategoryTheory.ConcreteCategory.hom hcat)
        simpa using happ.symm
      · change snd₁.hom z = snd₁.hom (inl₁.hom _)
        exact (ModuleCat.subsingleton_of_isZero D.hB₁).elim _ _
    change D.J₁.hom (inl₁.hom (D.cA₁.inv.hom
      (D.cA₁.hom.hom (fst₁.hom z)))) = y
    rw [← hz0]
    exact hz

/-- **Leaf.** Exactness at `ℤ^r` in degree zero (`hsum`, `hid`). -/
lemma t99A01_low_exact_δ₁_i₀_aux_I₀_injective {r : ℕ} {degree : Fin r → ℕ}
    (D : t99A01_LowInput degree) : Function.Injective D.I₀.hom := by
  intro x y hxy
  have key : ∀ z : D.O₀, D.cO₀.hom.hom z =
      (D.cO₀.inv ≫ D.I₀ ≫ Limits.biprod.snd ≫ D.cB₀.hom).hom (D.cO₀.hom.hom z) := by
    intro z; rw [D.hid]; rfl
  have hx := key x
  have hy := key y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Iso.hom_inv_id_apply] at hx hy
  have hcoord : D.cO₀.hom.hom x = D.cO₀.hom.hom y := by
    rw [hx, hy, hxy]
  have hback := congrArg D.cO₀.inv.hom hcoord
  simpa using hback

lemma t99A01_low_exact_δ₁_i₀ {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree) :
    LinearMap.range D.δ₁c = LinearMap.ker t99A01_LowInput.i₀ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have hy : D.δ₀.hom y = 0 := by
      apply t99A01_low_exact_δ₁_i₀_aux_I₀_injective D
      rw [map_zero]
      exact LinearMap.mem_ker.mp
        (D.hδ₀I₀ ▸ LinearMap.mem_range_self D.δ₀.hom y)
    simp [t99A01_LowInput.δ₁c, hy]
  · intro hx
    have hx0 : x = 0 := by
      have := congrArg Prod.snd (LinearMap.mem_ker.mp hx)
      simpa [t99A01_LowInput.i₀] using this
    subst x
    exact ⟨0, map_zero _⟩

/-- **Leaf.** Exactness at `ℤ × ℤ^r` (`hsum`, `hid`). -/
lemma t99A01_low_exact_i₀_j₀ {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree) :
    LinearMap.range t99A01_LowInput.i₀ = LinearMap.ker D.j₀ := by
  let fst₀ : D.A₀ ⊞ D.B₀ ⟶ D.A₀ := Limits.biprod.fst
  let snd₀ : D.A₀ ⊞ D.B₀ ⟶ D.B₀ := Limits.biprod.snd
  let inl₀ : D.A₀ ⟶ D.A₀ ⊞ D.B₀ := Limits.biprod.inl
  let inr₀ : D.B₀ ⟶ D.A₀ ⊞ D.B₀ := Limits.biprod.inr
  have hfi : ∀ a : D.A₀, fst₀.hom (inl₀.hom a) = a := by
    intro a
    change (inl₀ ≫ fst₀).hom a = ModuleCat.Hom.hom (𝟙 D.A₀) a
    rw [Limits.biprod.inl_fst]
  have hfr : ∀ b : D.B₀, fst₀.hom (inr₀.hom b) = 0 := by
    intro b
    change (inr₀ ≫ fst₀).hom b = 0
    rw [Limits.biprod.inr_fst]
    rfl
  have hsi : ∀ a : D.A₀, snd₀.hom (inl₀.hom a) = 0 := by
    intro a
    change (inl₀ ≫ snd₀).hom a = 0
    rw [Limits.biprod.inl_snd]
    rfl
  have hsr : ∀ b : D.B₀, snd₀.hom (inr₀.hom b) = b := by
    intro b
    change (inr₀ ≫ snd₀).hom b = ModuleCat.Hom.hom (𝟙 D.B₀) b
    rw [Limits.biprod.inr_snd]
  have hI₀_apply : ∀ x : Fin r → ℤ,
      D.I₀.hom (D.cO₀.inv.hom x) =
        inl₀.hom (D.cA₀.inv.hom (t99A01_coordinateSum x)) +
          inr₀.hom (D.cB₀.inv.hom x) := by
    intro x
    apply (ModuleCat.biprodIsoProd D.A₀ D.B₀).toLinearEquiv.injective
    apply Prod.ext
    · change fst₀.hom _ = fst₀.hom _
      have h := congrArg (fun f => f x)
        (congrArg CategoryTheory.ConcreteCategory.hom D.hsum)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
        D.cA₀.hom_inv_id_apply, map_add, hfi, hfr, add_zero] using
        congrArg D.cA₀.inv.hom h
    · change snd₀.hom _ = snd₀.hom _
      have h := congrArg (fun f => f x)
        (congrArg CategoryTheory.ConcreteCategory.hom D.hid)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
        D.cB₀.hom_inv_id_apply, map_add, hsi, hsr, zero_add,
        CategoryTheory.ConcreteCategory.id_apply] using congrArg D.cB₀.inv.hom h
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hj : D.j₀ (t99A01_LowInput.i₀ x) =
        D.J₀.hom (D.I₀.hom (D.cO₀.inv.hom x)) := by
      rw [hI₀_apply]
      simp only [t99A01_LowInput.j₀, LinearMap.coprod_apply,
        t99A01_LowInput.i₀, LinearMap.prod_apply, LinearMap.id_coe,
        id_eq, ModuleCat.hom_comp, LinearMap.comp_apply, map_add]
      dsimp [inl₀, inr₀]
    rw [hj]
    exact LinearMap.mem_ker.mp
      (D.hI₀J₀ ▸ LinearMap.mem_range_self D.I₀.hom (D.cO₀.inv.hom x))
  · intro hy
    rcases y with ⟨a, b⟩
    have hy' :
        inl₀.hom (D.cA₀.inv.hom a) + inr₀.hom (D.cB₀.inv.hom b) ∈
          LinearMap.ker D.J₀.hom := by
      rw [LinearMap.mem_ker] at hy ⊢
      simpa only [t99A01_LowInput.j₀, LinearMap.coprod_apply,
        ModuleCat.hom_comp, LinearMap.comp_apply, map_add] using hy
    rw [← D.hI₀J₀] at hy'
    rcases hy' with ⟨z, hz⟩
    refine ⟨D.cO₀.hom.hom z, ?_⟩
    have hi : D.I₀.hom z =
        inl₀.hom (D.cA₀.inv.hom
          (t99A01_coordinateSum (D.cO₀.hom.hom z))) +
        inr₀.hom (D.cB₀.inv.hom (D.cO₀.hom.hom z)) := by
      convert hI₀_apply (D.cO₀.hom.hom z) using 1 <;>
        simp only [D.cO₀.hom_inv_id_apply]
    have hz' := hi.symm.trans hz
    apply Prod.ext
    · have h := congrArg (fun w => fst₀.hom w) hz'
      change t99A01_coordinateSum (D.cO₀.hom.hom z) = a
      have h' := congrArg D.cA₀.hom.hom h
      simp only [map_add, hfi, hfr, add_zero] at h'
      rw [D.cA₀.inv_hom_id_apply, D.cA₀.inv_hom_id_apply] at h'
      exact h'
    · have h := congrArg (fun w => snd₀.hom w) hz'
      change D.cO₀.hom.hom z = b
      have h' := congrArg D.cB₀.hom.hom h
      simp only [map_add, hsi, hsr, zero_add] at h'
      rw [D.cB₀.inv_hom_id_apply, D.cB₀.inv_hom_id_apply] at h'
      exact h'

/-- **Leaf.** `j₀` is onto (`hJ₀`, biproduct decomposition). -/
lemma t99A01_low_j₀_surjective {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree) :
    Function.Surjective D.j₀ := by
  intro y
  rcases D.hJ₀ y with ⟨z, rfl⟩
  let fst₀ : D.A₀ ⊞ D.B₀ ⟶ D.A₀ := Limits.biprod.fst
  let snd₀ : D.A₀ ⊞ D.B₀ ⟶ D.B₀ := Limits.biprod.snd
  let inl₀ : D.A₀ ⟶ D.A₀ ⊞ D.B₀ := Limits.biprod.inl
  let inr₀ : D.B₀ ⟶ D.A₀ ⊞ D.B₀ := Limits.biprod.inr
  refine ⟨(D.cA₀.hom.hom (fst₀.hom z), D.cB₀.hom.hom (snd₀.hom z)), ?_⟩
  simp only [t99A01_LowInput.j₀, LinearMap.coprod_apply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [D.cA₀.hom_inv_id_apply, D.cB₀.hom_inv_id_apply]
  rw [← map_add]
  congr 1
  have hcat : (fst₀ ≫ inl₀) + (snd₀ ≫ inr₀) = 𝟙 (D.A₀ ⊞ D.B₀) := by
    apply Limits.biprod.hom_ext <;> simp [fst₀, snd₀, inl₀, inr₀]
  exact congrArg (fun f : D.A₀ ⊞ D.B₀ ⟶ D.A₀ ⊞ D.B₀ => f.hom z) hcat

/-- **Leaf.** `δ₂` is injective (`A₂ = B₂ = 0` kill the range of `J₂`). -/
lemma t99A01_low_δ₂_injective {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree) :
    Function.Injective D.δ₂c := by
  intro x y hxy
  have hinj : Function.Injective D.δ₁.hom := by
    intro a b hab
    have hk : a - b ∈ LinearMap.ker D.δ₁.hom := by
      rw [LinearMap.mem_ker, map_sub, hab, sub_self]
    rw [← D.hJ₂δ₁] at hk
    rcases hk with ⟨z, hz⟩
    have hzeroA : ∀ u : D.A₂, u = 0 := by
      intro u
      have h := congrArg (fun f ↦ f u)
        (congrArg ModuleCat.Hom.hom (D.hA₂.eq_zero_of_src (𝟙 D.A₂)))
      simpa using h
    have hzeroB : ∀ u : D.B₂, u = 0 := by
      intro u
      have h := congrArg (fun f ↦ f u)
        (congrArg ModuleCat.Hom.hom (D.hB₂.eq_zero_of_src (𝟙 D.B₂)))
      simpa using h
    have hz0 : z = 0 := by
      apply (ModuleCat.biprodIsoProd D.A₂ D.B₂).toLinearEquiv.injective
      apply Prod.ext
      · exact (hzeroA _).trans (hzeroA _).symm
      · exact (hzeroB _).trans (hzeroB _).symm
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  have hh := congrArg D.cO₁.inv.hom hxy
  apply hinj
  simpa [t99A01_LowInput.δ₂c] using hh

/-- **Leaf.** Exactness at `ℤ^r` in degree one (`B₁ = 0`, `hdegree`). -/
lemma t99A01_low_exact_δ₂_i₁ {r : ℕ} {degree : Fin r → ℕ} (D : t99A01_LowInput degree) :
    LinearMap.range D.δ₂c = LinearMap.ker (APMT99A01.degreeMap degree) := by
  let fst₁ : (D.A₁ ⊞ D.B₁) ⟶ D.A₁ := Limits.biprod.fst
  let snd₁ : (D.A₁ ⊞ D.B₁) ⟶ D.B₁ := Limits.biprod.snd
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have hker : D.δ₁.hom y ∈ LinearMap.ker D.I₁.hom := by
      rw [← D.hδ₁I₁]
      exact LinearMap.mem_range_self D.δ₁.hom y
    have hzero : D.I₁.hom (D.δ₁.hom y) = 0 := LinearMap.mem_ker.mp hker
    have hdegree := congrArg (fun f => f (D.cO₁.hom.hom (D.δ₁.hom y)))
      (congrArg CategoryTheory.ConcreteCategory.hom D.hdegree)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hdegree
    rw [D.cO₁.hom_inv_id_apply] at hdegree
    rw [hzero, map_zero, map_zero] at hdegree
    simpa [t99A01_LowInput.δ₂c, fst₁] using hdegree.symm
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hker : D.cO₁.inv.hom x ∈ LinearMap.ker D.I₁.hom := by
      rw [LinearMap.mem_ker]
      apply (ModuleCat.biprodIsoProd D.A₁ D.B₁).toLinearEquiv.injective
      apply Prod.ext
      · change fst₁.hom (D.I₁.hom (D.cO₁.inv.hom x)) = fst₁.hom 0
        have hdegree := congrArg (fun f => f x)
          (congrArg CategoryTheory.ConcreteCategory.hom D.hdegree)
        simpa [fst₁, hx] using congrArg D.cA₁.inv.hom hdegree
      · change snd₁.hom (D.I₁.hom (D.cO₁.inv.hom x)) = snd₁.hom 0
        exact (ModuleCat.subsingleton_of_isZero D.hB₁).elim _ _
    rw [← D.hδ₁I₁] at hker
    rcases hker with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change D.cO₁.hom.hom (D.δ₁.hom y) = x
    rw [hy]
    exact D.cO₁.inv_hom_id_apply x

lemma t99A01_lowData_of_coordinates {r : ℕ} (degree : Fin r → ℕ)
    (O₀ O₁ A₀ A₁ A₂ B₀ B₁ B₂ : ModuleCat ℤ)
    (I₀ : O₀ ⟶ A₀ ⊞ B₀) (I₁ : O₁ ⟶ A₁ ⊞ B₁)
    (J₀ : A₀ ⊞ B₀ ⟶ APMT99A01.H 0 (APMT99A01.AttachSpace degree))
    (J₁ : A₁ ⊞ B₁ ⟶ APMT99A01.H 1 (APMT99A01.AttachSpace degree))
    (J₂ : A₂ ⊞ B₂ ⟶ APMT99A01.H 2 (APMT99A01.AttachSpace degree))
    (δ₀ : APMT99A01.H 1 (APMT99A01.AttachSpace degree) ⟶ O₀)
    (δ₁ : APMT99A01.H 2 (APMT99A01.AttachSpace degree) ⟶ O₁)
    (hI₁J₁ : LinearMap.range I₁.hom = LinearMap.ker J₁.hom)
    (hJ₁δ₀ : LinearMap.range J₁.hom = LinearMap.ker δ₀.hom)
    (hδ₀I₀ : LinearMap.range δ₀.hom = LinearMap.ker I₀.hom)
    (hI₀J₀ : LinearMap.range I₀.hom = LinearMap.ker J₀.hom)
    (hJ₂δ₁ : LinearMap.range J₂.hom = LinearMap.ker δ₁.hom)
    (hδ₁I₁ : LinearMap.range δ₁.hom = LinearMap.ker I₁.hom)
    (hA₂ : Limits.IsZero A₂) (hB₁ : Limits.IsZero B₁) (hB₂ : Limits.IsZero B₂)
    (hJ₀ : Function.Surjective J₀.hom)
    (cO₀ : O₀ ≅ ModuleCat.of ℤ (Fin r → ℤ))
    (cO₁ : O₁ ≅ ModuleCat.of ℤ (Fin r → ℤ))
    (cA₀ : A₀ ≅ ModuleCat.of ℤ ℤ) (cA₁ : A₁ ≅ ModuleCat.of ℤ ℤ)
    (cB₀ : B₀ ≅ ModuleCat.of ℤ (Fin r → ℤ))
    (hdegree : cO₁.inv ≫ I₁ ≫ Limits.biprod.fst ≫ cA₁.hom =
      ModuleCat.ofHom (APMT99A01.degreeMap degree))
    (hsum : cO₀.inv ≫ I₀ ≫ Limits.biprod.fst ≫ cA₀.hom =
      ModuleCat.ofHom t99A01_coordinateSum)
    (hid : cO₀.inv ≫ I₀ ≫ Limits.biprod.snd ≫ cB₀.hom = 𝟙 _) :
    Nonempty (APMT99A01.AttachMVLowData degree) := by
  let D : t99A01_LowInput degree :=
    ⟨O₀, O₁, A₀, A₁, A₂, B₀, B₁, B₂, I₀, I₁, J₀, J₁, J₂, δ₀, δ₁, hI₁J₁, hJ₁δ₀, hδ₀I₀, hI₀J₀,
      hJ₂δ₁, hδ₁I₁, hA₂, hB₁, hB₂, hJ₀, cO₀, cO₁, cA₀, cA₁, cB₀, hdegree, hsum, hid⟩
  exact ⟨{
    i₁ := APMT99A01.degreeMap degree
    j₁ := D.j₁
    δ₁ := D.δ₁c
    i₀ := t99A01_LowInput.i₀
    j₀ := D.j₀
    δ₂ := D.δ₂c
    i₁_eq_degreeMap := rfl
    i₀_injective := t99A01_lowData_of_coordinates_aux_i0_injective
    i₀_eq := fun _ => rfl
    exact_i₁_j₁ := t99A01_low_exact_i₁_j₁ D
    exact_j₁_δ₁ := t99A01_low_exact_j₁_δ₁ D
    exact_δ₁_i₀ := t99A01_low_exact_δ₁_i₀ D
    exact_i₀_j₀ := t99A01_low_exact_i₀_j₀ D
    j₀_surjective := t99A01_low_j₀_surjective D
    δ₂_injective := t99A01_low_δ₂_injective D
    exact_δ₂_i₁ := t99A01_low_exact_δ₂_i₁ D }⟩
/-- Concrete positive-degree vanishings required by the algebra leaf. -/
lemma t99A01_low_coordinates_vanishing {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree))
    (hρι : ρ.comp ι = ContinuousMap.id Circle)
    (hιρ : ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _))
    (eB : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1)) :
    Limits.IsZero (APMT99A01.H 2 (APMT99A01.sideA degree)) ∧
      Limits.IsZero (APMT99A01.H 1 (APMT99A01.sideB degree)) ∧
      Limits.IsZero (APMT99A01.H 2 (APMT99A01.sideB degree)) := by
  have hA₂ : Limits.IsZero (APMT99A01.H 2 (APMT99A01.sideA degree)) :=
    (ConstructionTargets.SolidTorusHomotopyAndHomology.circleModuleHomology_isZero_of_one_lt
      2 (by omega)).of_iso
        (t99A01_sideA_coordinate degree ρ ι hρι hιρ 2)
  have hsigma_zero : ∀ k : ℕ, k ≠ 0 →
      Limits.IsZero (APMT99A01.H k (Σ _ : Fin r, Metric.ball (0 : ℂ) 1)) := by
    intro k hk
    let Y : Fin r → Type := fun _ ↦ Metric.ball (0 : ℂ) 1
    let f := Limits.biproduct.desc fun i : Fin r ↦
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k
    letI : IsIso f := t99A01_sigma_homology Y k
    have hpiece : ∀ i : Fin r,
        Limits.IsZero (APMT99A01.H k (Metric.ball (0 : ℂ) 1)) := by
      intro i
      letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
        Metric.contractibleSpace_ball (by norm_num)
      exact ConstructionTargets.CoefficientContractiblePair.higher_zero ℤ _ k hk
    have hbip : Limits.IsZero
        (⨁ fun _ : Fin r ↦ APMT99A01.H k (Metric.ball (0 : ℂ) 1)) := by
      rw [Limits.IsZero.iff_id_eq_zero]
      apply Limits.biproduct.hom_ext'
      intro i
      exact (hpiece i).eq_of_src _ _
    exact hbip.of_iso (asIso f).symm
  refine ⟨hA₂, ?_, ?_⟩
  · exact (hsigma_zero 1 (by omega)).of_iso
      (t99A01_diskSide_sigma_coordinate degree eB 1)
  · exact (hsigma_zero 2 (by omega)).of_iso
      (t99A01_diskSide_sigma_coordinate degree eB 2)

/-- The degree-one row in the fixed sigma, circle, and winding coordinates. -/
lemma t99A01_low_coordinates_degree_one_aux_inv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
      ℤ e n).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.invFun) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  apply (cancel_epi
    (ConstructionTargets.CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv
      ℤ e n).hom).1
  rw [Iso.hom_inv_id]
  symm
  rw [ConstructionTargets.CoefficientRadialPair.homotopyIso_hom]
  change F.map (TopCat.ofHom e.toFun) ≫ F.map (TopCat.ofHom e.invFun) = 𝟙 _
  have he : F.map (TopCat.ofHom (e.invFun.comp e.toFun)) = F.map (𝟙 _) :=
    ConstructionTargets.CoefficientContractiblePair.singularHomology_map_eq_of_topCatHomotopy
    ℤ (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder (Classical.choice e.left_inv))
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_zero (Classical.choice e.left_inv))
      (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_one (Classical.choice e.left_inv)) n
  change F.map (TopCat.ofHom e.toFun) ≫ F.map (TopCat.ofHom e.invFun) = 𝟙 _
  calc
    _ = F.map (TopCat.ofHom (e.invFun.comp e.toFun)) := by
      rw [← F.map_comp]
      rfl
    _ = F.map (𝟙 _) := he
    _ = 𝟙 _ := F.map_id _

lemma t99A01_low_coordinates_degree_one_aux_circle
    {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle))
    (eO : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (heO : ∀ (i : Fin r) (w : Circle), (eO.invFun ⟨i, w⟩).1 =
      APMT99A01.halfLoop degree i w)
    (hρ : ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈
      APMT99A01.sideA degree), ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i)
    (i : Fin r) :
    ρ.comp
      ((⟨Set.inclusion Set.inter_subset_left,
          continuous_inclusion Set.inter_subset_left⟩ :
        C(↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
          APMT99A01.sideA degree)).comp
        (eO.invFun.comp
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
              @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle)))) =
      APMT99A01.circlePower (degree i) := by
  ext w
  have hm : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideA degree := by
    rw [← heO i w]
    exact (eO.invFun ⟨i, w⟩).property.1
  have hin :
      (⟨Set.inclusion Set.inter_subset_left,
          continuous_inclusion Set.inter_subset_left⟩ :
        C(↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
          APMT99A01.sideA degree))
          (eO.invFun
            ((⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
                @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
              C(Circle, Σ _ : Fin r, Circle)) w)) =
        ⟨APMT99A01.halfLoop degree i w, hm⟩ := by
    apply Subtype.ext
    exact heO i w
  simp only [ContinuousMap.comp_apply]
  rw [hin, hρ]
  rfl

/-
  rw [hp]
  unfold APMT99A01.zI
  simp only [← Category.assoc]
  rw [Limits.biprod.lift_fst]
  simp only [Category.assoc]
  rw [t99A01_low_coordinates_degree_one_aux_inv]
  rw [ConstructionTargets.CoefficientRadialPair.homotopyIso_hom]
  trace_state
-/

lemma t99A01_low_coordinates_degree_one_aux_summand_seat
    {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree))
    (hρι : ρ.comp ι = ContinuousMap.id Circle)
    (hιρ : ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _))
    (eO : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (heO : ∀ (i : Fin r) (w : Circle), (eO.invFun ⟨i, w⟩).1 =
      APMT99A01.halfLoop degree i w)
    (hρ : ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈
      APMT99A01.sideA degree), ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)))
    (e₁ : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ)
    (hw : ∀ i : Fin r, e₁.inv ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e₁.hom =
      ModuleCat.ofHom (APMT99A01.intTimesNat (degree i))) (i : Fin r) :
    e₁.inv ≫ Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 1 Circle) i ≫
      (t99A01_overlap_sigma_coordinate degree eO 1 ≪≫
        t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 1 (hsigma _ 1)).inv ≫
      APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) 1 ≫
      Limits.biprod.fst ≫ (t99A01_sideA_coordinate degree ρ ι hρι hιρ 1 ≪≫ e₁).hom =
      ModuleCat.ofHom (APMT99A01.intTimesNat (degree i)) := by
  rw [Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc, Limits.biproduct.ι_desc_assoc,
    Limits.biprod.lift_fst_assoc]
  dsimp [t99A01_sigma_coordinate, t99A01_overlap_sigma_coordinate,
    t99A01_sideA_coordinate]
  unfold APMT99A01.zI
  simp only [Category.assoc, Limits.biproduct.ι_desc_assoc,
    Limits.biprod.lift_fst_assoc]
  rw [t99A01_low_coordinates_degree_one_aux_inv]
  rw [ConstructionTargets.CoefficientRadialPair.homotopyIso_hom]
  have hp : Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 1 Circle) i ≫
      (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
              C(Circle, Σ j : Fin r, Circle))) 1) =
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
              C(Circle, Σ j : Fin r, Circle))) 1 := by
    rw [Limits.biproduct.ι_desc]
  slice_lhs 2 3 => exact hp
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  change e₁.inv ≫ F.map (TopCat.ofHom
      (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
        @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
          C(Circle, Σ j : Fin r, Circle))) ≫
      F.map (TopCat.ofHom eO.invFun) ≫
      F.map (TopCat.ofHom
        (⟨Set.inclusion Set.inter_subset_left,
          continuous_inclusion Set.inter_subset_left⟩ :
          C(↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
            APMT99A01.sideA degree))) ≫
      F.map (TopCat.ofHom ρ) ≫ e₁.hom = _
  slice_lhs 2 5 => rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
  rw [show TopCat.ofHom
        (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
          @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
          C(Circle, Σ j : Fin r, Circle)) ≫
      TopCat.ofHom eO.invFun ≫
      (TopCat.ofHom
        (⟨Set.inclusion Set.inter_subset_left,
          continuous_inclusion Set.inter_subset_left⟩ :
          C(↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
            APMT99A01.sideA degree))) ≫
      TopCat.ofHom ρ =
      TopCat.ofHom (APMT99A01.circlePower (degree i)) by
        exact congrArg TopCat.ofHom
          (t99A01_low_coordinates_degree_one_aux_circle degree ρ eO heO hρ i)]
  exact hw i

lemma t99A01_low_coordinates_degree_one {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree))
    (hρι : ρ.comp ι = ContinuousMap.id Circle)
    (hιρ : ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _))
    (eO : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (heO : ∀ (i : Fin r) (w : Circle), (eO.invFun ⟨i, w⟩).1 =
      APMT99A01.halfLoop degree i w)
    (hρ : ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈
      APMT99A01.sideA degree), ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)))
    (e₁ : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ)
    (hw : ∀ i : Fin r, e₁.inv ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e₁.hom =
      ModuleCat.ofHom (APMT99A01.intTimesNat (degree i))) :
    let cO₁ := t99A01_overlap_sigma_coordinate degree eO 1 ≪≫
      t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 1 (hsigma _ 1) ≪≫
      Limits.biproduct.mapIso (fun _ : Fin r ↦ e₁) ≪≫
      t99A01_biproduct_int_coordinate r
    let cA₁ := t99A01_sideA_coordinate degree ρ ι hρι hιρ 1 ≪≫ e₁
    cO₁.inv ≫ APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) 1 ≫
      Limits.biprod.fst ≫ cA₁.hom = ModuleCat.ofHom (APMT99A01.degreeMap degree) := by
  dsimp only
  apply ModuleCat.hom_ext
  apply LinearMap.pi_ext
  intro i x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  have hsingle : ModuleCat.ofHom
      (LinearMap.single ℤ (fun _ : Fin r => ℤ) i) ≫
      (ModuleCat.biproductIsoPi (fun _ : Fin r => ModuleCat.of ℤ ℤ)).inv =
      Limits.biproduct.ι (fun _ : Fin r => ModuleCat.of ℤ ℤ) i := by
    apply Limits.biproduct.hom_ext
    intro j
    rw [Category.assoc, ModuleCat.biproductIsoPi_inv_comp_π]
    apply ModuleCat.hom_ext
    ext y
    by_cases h : i = j
    · subst j
      simp
    · simp [Pi.single_apply, h]
  have hsingle_apply := congrArg
    (fun f : ModuleCat.of ℤ ℤ ⟶ (⨁ fun _ : Fin r => ModuleCat.of ℤ ℤ) => f.hom x)
    hsingle
  have hsingle_apply' :
      (ModuleCat.biproductIsoPi (fun _ : Fin r => ModuleCat.of ℤ ℤ)).inv.hom
        (Pi.single i x) =
      (Limits.biproduct.ι (fun _ : Fin r => ModuleCat.of ℤ ℤ) i).hom x := by
    simpa [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.single_apply] using hsingle_apply
  have hmap_apply := congrArg
    (fun f : ModuleCat.of ℤ ℤ ⟶
      (⨁ fun _ : Fin r => APMT99A01.H 1 Circle) => f.hom x)
    (Limits.biproduct.ι_map (fun _ : Fin r => e₁.inv) i)
  change
      (Limits.biproduct.map (fun _ : Fin r => e₁.inv)).hom
        ((Limits.biproduct.ι (fun _ : Fin r => ModuleCat.of ℤ ℤ) i).hom x) =
      (Limits.biproduct.ι (fun _ : Fin r => APMT99A01.H 1 Circle) i).hom
        (e₁.inv.hom x) at hmap_apply
  simp only [Iso.trans_inv, t99A01_biproduct_int_coordinate,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [hsingle_apply']
  dsimp [Limits.biproduct.mapIso]
  rw [hmap_apply]
  have hs := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f.hom x)
    (t99A01_low_coordinates_degree_one_aux_summand_seat degree ρ ι hρι hιρ
      eO heO hρ hsigma e₁ hw i)
  simpa [Iso.trans_inv, t99A01_biproduct_int_coordinate,
    APMT99A01.degreeMap, APMT99A01.intTimesNat, hsingle_apply,
    hmap_apply, Pi.single_apply] using hs
instance t99A01_circle_pathConnected : PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using h)

instance t99A01_ball_pathConnected : PathConnectedSpace (Metric.ball (0 : ℂ) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (Metric.isPathConnected_ball (x := (0 : ℂ)) (r := 1) (by norm_num))

/-- Canonical `H₀` coordinate of the circle: every point class ↦ 1. -/
noncomputable def t99A01_eC : APMT99A01.H 0 Circle ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.CoefficientH0.h0Iso ℤ (1 : Circle)

/-- Canonical `H₀` coordinate of the open unit disk: every point class ↦ 1. -/
noncomputable def t99A01_eD : APMT99A01.H 0 (Metric.ball (0 : ℂ) 1) ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.CoefficientH0.h0Iso ℤ ⟨0, by simp [Metric.mem_ball]⟩

/-- The two degree-zero coordinate rows, including the sign convention of
`zI = lift(incl,incl)`; the minus sign belongs to `zJ`, not this map. -/
lemma t99A01_low_coordinates_degree_zero_aux_left
    {r : ℕ} (degree : Fin r → ℕ)
    (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree))
    (hρι : ρ.comp ι = ContinuousMap.id Circle)
    (hιρ : ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _))
    (eO : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)))
    (i : Fin r) :
    t99A01_eC.inv ≫ Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫
      (t99A01_overlap_sigma_coordinate degree eO 0 ≪≫
        t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 0 (hsigma _ 0)).inv ≫
      APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) 0 ≫
      Limits.biprod.fst ≫ (t99A01_sideA_coordinate degree ρ ι hρι hιρ 0 ≪≫
        t99A01_eC).hom = 𝟙 _ := by
  rw [Iso.trans_inv, Iso.trans_hom]
  unfold APMT99A01.zI
  simp only [Category.assoc, Limits.biproduct.ι_desc_assoc,
    Limits.biprod.lift_fst_assoc]
  dsimp [t99A01_sigma_coordinate, t99A01_overlap_sigma_coordinate,
    t99A01_sideA_coordinate]
  rw [t99A01_low_coordinates_degree_one_aux_inv]
  rw [ConstructionTargets.CoefficientRadialPair.homotopyIso_hom]
  have hp : Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫
      (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0) =
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0 := by
    rw [Limits.biproduct.ι_desc]
  slice_lhs 2 3 => exact hp
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
    (ModuleCat.of ℤ ℤ)
  let s : C(Circle, Σ _ : Fin r, Circle) :=
    ⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
      @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩
  let inc : C(↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
      APMT99A01.sideA degree) :=
    ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion Set.inter_subset_left⟩
  let f : C(Circle, Circle) := ρ.comp (inc.comp (eO.invFun.comp s))
  change t99A01_eC.inv ≫ F.map (TopCat.ofHom s) ≫
    F.map (TopCat.ofHom eO.invFun) ≫ F.map (TopCat.ofHom inc) ≫
    F.map (TopCat.ofHom ρ) ≫ t99A01_eC.hom = 𝟙 _
  slice_lhs 2 5 => rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
  change ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ (1 : Circle) ≫
    (F.map (TopCat.ofHom f) ≫ ConstructionTargets.CoefficientH0.h0Augmentation ℤ) = 𝟙 _
  exact (congrArg (fun g =>
    ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ (1 : Circle) ≫ g)
      (ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℤ f)).trans
    (ConstructionTargets.CoefficientH0.singularVertexH0Class_comp_h0Augmentation ℤ _)

lemma t99A01_low_coordinates_degree_zero_aux_right
    {r : ℕ} (degree : Fin r → ℕ)
    (eB : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1))
    (eO : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (heB : ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
      (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
      eB ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩)
    (heO : ∀ (i : Fin r) (w : Circle), (eO.invFun ⟨i, w⟩).1 =
      APMT99A01.halfLoop degree i w)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j))) :
    let eD : ∀ _ : Fin r, APMT99A01.H 0 (Metric.ball (0 : ℂ) 1) ≅ ModuleCat.of ℤ ℤ :=
      fun _ ↦ t99A01_eD
    let cO₀ := t99A01_overlap_sigma_coordinate degree eO 0 ≪≫
      t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso (fun _ : Fin r ↦ t99A01_eC) ≪≫
      t99A01_biproduct_int_coordinate r
    let cB₀ := t99A01_diskSide_sigma_coordinate degree eB 0 ≪≫
      t99A01_sigma_coordinate (fun _ : Fin r ↦ Metric.ball (0 : ℂ) 1) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso eD ≪≫ t99A01_biproduct_int_coordinate r
    cO₀.inv ≫ APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) 0 ≫
      Limits.biprod.snd ≫ cB₀.hom = 𝟙 _ := by
  dsimp only
  rw [Iso.trans_inv, Iso.trans_hom]
  unfold APMT99A01.zI
  simp only [Category.assoc, Limits.biproduct.ι_desc_assoc,
    Limits.biprod.lift_snd_assoc]
  apply (cancel_epi
    (t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso (fun _ : Fin r ↦ t99A01_eC) ≪≫
      t99A01_biproduct_int_coordinate r).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]
  apply (cancel_mono
    (t99A01_sigma_coordinate (fun _ : Fin r ↦ Metric.ball (0 : ℂ) 1) 0
      (hsigma _ 0) ≪≫ Limits.biproduct.mapIso (fun _ : Fin r ↦ t99A01_eD) ≪≫
      t99A01_biproduct_int_coordinate r).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp [t99A01_sigma_coordinate, t99A01_overlap_sigma_coordinate,
    t99A01_diskSide_sigma_coordinate]
  rw [t99A01_low_coordinates_degree_one_aux_inv]
  rw [ConstructionTargets.CoefficientRadialPair.homotopyIso_hom]
  let f := (Limits.biproduct.desc fun i : Fin r ↦
    HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
        (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
          @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
          C(Circle, Σ _ : Fin r, Circle))) 0)
  letI : IsIso f := hsigma (fun _ : Fin r ↦ Circle) 0
  apply (cancel_epi f).1
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  apply Limits.biproduct.hom_ext'
  intro i
  dsimp [f]
  simp only [Category.assoc, Limits.biproduct.ι_desc_assoc,
    Limits.biproduct.ι_map_assoc, Iso.hom_inv_id_assoc]
  have hp : Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫ f =
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0 := by
    change Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫
      (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0) = _
    rw [Limits.biproduct.ι_desc]
  have hc : HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0 ≫ inv f =
      Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i := by
    rw [← hp]
    simp
    rfl
  change _ = _ ≫ inv f ≫ _
  conv_rhs => rw [← Category.assoc, hc]
  have hm : Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫
        (Limits.biproduct.map fun _ : Fin r ↦ t99A01_eC.hom) ≫
        (Limits.biproduct.map fun _ : Fin r ↦ t99A01_eD.inv) ≫
        (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
            (⟨@Sigma.mk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) i,
              @continuous_sigmaMk (Fin r)
                (fun _ ↦ Metric.ball (0 : ℂ) 1) _ i⟩ :
              C(Metric.ball (0 : ℂ) 1, Σ _ : Fin r, Metric.ball (0 : ℂ) 1))) 0) =
      t99A01_eC.hom ≫ t99A01_eD.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
            (⟨@Sigma.mk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) i,
              @continuous_sigmaMk (Fin r)
                (fun _ ↦ Metric.ball (0 : ℂ) 1) _ i⟩ :
              C(Metric.ball (0 : ℂ) 1, Σ _ : Fin r, Metric.ball (0 : ℂ) 1))) 0 := by
    simp only [Category.assoc, Limits.biproduct.ι_map_assoc,
      Limits.biproduct.ι_desc_assoc]
    slice_lhs 3 4 => rw [Limits.biproduct.ι_desc]
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
    (ModuleCat.of ℤ ℤ)
  let s : C(Circle, Σ _ : Fin r, Circle) :=
    ⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
      @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩
  let inc : C(↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
      APMT99A01.sideB degree) :=
    ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion Set.inter_subset_right⟩
  let b : C(APMT99A01.sideB degree,
      Σ _ : Fin r, Metric.ball (0 : ℂ) 1) := eB.toHomotopyEquiv.toFun
  let g : C(Circle, Metric.ball (0 : ℂ) 1) :=
    ⟨fun w ↦ ⟨w / 2, by
        rw [Metric.mem_ball, dist_zero_right, norm_div, Circle.norm_coe]
        norm_num⟩,
      Continuous.subtype_mk (continuous_subtype_val.div_const 2) (by
        intro w
        rw [Metric.mem_ball, dist_zero_right, norm_div, Circle.norm_coe]
        norm_num)⟩
  let t : C(Metric.ball (0 : ℂ) 1,
      Σ _ : Fin r, Metric.ball (0 : ℂ) 1) :=
    ⟨@Sigma.mk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) i,
      @continuous_sigmaMk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) _ i⟩
  apply Eq.trans (b := t99A01_eC.hom ≫ t99A01_eD.inv ≫
    F.map (TopCat.ofHom t))
  swap
  exact hm.symm
  change F.map (TopCat.ofHom s) ≫ F.map (TopCat.ofHom eO.invFun) ≫
      F.map (TopCat.ofHom inc) ≫ F.map (TopCat.ofHom b) =
    t99A01_eC.hom ≫ t99A01_eD.inv ≫ F.map (TopCat.ofHom t)
  have hcomp : b.comp (inc.comp (eO.invFun.comp s)) = t.comp g := by
    apply ContinuousMap.ext
    intro w
    have hmem : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideB degree := by
      rw [← heO i w]
      exact (eO.invFun ⟨i, w⟩).property.2
    have hb := heB i (APMT99A01.halfPoint w) (by
      rw [show ‖((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ)‖ = 1 / 2 by
        simp [APMT99A01.halfPoint, norm_div, Circle.norm_coe]]
      norm_num) hmem
    have hx : inc (eO.invFun (s w)) =
        ⟨APMT99A01.halfLoop degree i w, hmem⟩ := by
      apply Subtype.ext
      exact heO i w
    rw [show (b.comp (inc.comp (eO.invFun.comp s))) w =
      b ⟨APMT99A01.halfLoop degree i w, hmem⟩ by exact congrArg b hx]
    simpa [b, t, g, APMT99A01.halfLoop, APMT99A01.halfPoint] using hb
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
  change F.map (TopCat.ofHom (b.comp (inc.comp (eO.invFun.comp s)))) = _
  rw [hcomp]
  change F.map (TopCat.ofHom g ≫ TopCat.ofHom t) = _
  rw [F.map_comp]
  have hg : t99A01_eC.hom ≫ t99A01_eD.inv = F.map (TopCat.ofHom g) := by
    apply (cancel_mono t99A01_eD.hom).1
    change (ConstructionTargets.CoefficientH0.h0Augmentation ℤ ≫
        ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ
          (⟨0, by simp [Metric.mem_ball]⟩ : Metric.ball (0 : ℂ) 1)) ≫
        ConstructionTargets.CoefficientH0.h0Augmentation ℤ = _
    rw [Category.assoc,
      ConstructionTargets.CoefficientH0.singularVertexH0Class_comp_h0Augmentation,
      Category.comp_id]
    exact (ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℤ g).symm
  exact (congrArg (fun q => q ≫ F.map (TopCat.ofHom t)) hg).symm

lemma t99A01_low_coordinates_degree_zero_aux_right_aux_right
    {r : ℕ} (degree : Fin r → ℕ)
    (eB : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1))
    (eO : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (heB : ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
      (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
      eB ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩)
    (heO : ∀ (i : Fin r) (w : Circle), (eO.invFun ⟨i, w⟩).1 =
      APMT99A01.halfLoop degree i w)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j))) :
    let eD : ∀ _ : Fin r, APMT99A01.H 0 (Metric.ball (0 : ℂ) 1) ≅ ModuleCat.of ℤ ℤ :=
      fun _ ↦ t99A01_eD
    let cO₀ := t99A01_overlap_sigma_coordinate degree eO 0 ≪≫
      t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso (fun _ : Fin r ↦ t99A01_eC) ≪≫
      t99A01_biproduct_int_coordinate r
    let cB₀ := t99A01_diskSide_sigma_coordinate degree eB 0 ≪≫
      t99A01_sigma_coordinate (fun _ : Fin r ↦ Metric.ball (0 : ℂ) 1) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso eD ≪≫ t99A01_biproduct_int_coordinate r
    cO₀.inv ≫ APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) 0 ≫
      Limits.biprod.snd ≫ cB₀.hom = 𝟙 _ := by
  dsimp only
  rw [Iso.trans_inv, Iso.trans_hom]
  unfold APMT99A01.zI
  simp only [Category.assoc, Limits.biproduct.ι_desc_assoc,
    Limits.biprod.lift_snd_assoc]
  apply (cancel_epi
    (t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso (fun _ : Fin r ↦ t99A01_eC) ≪≫
      t99A01_biproduct_int_coordinate r).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]
  apply (cancel_mono
    (t99A01_sigma_coordinate (fun _ : Fin r ↦ Metric.ball (0 : ℂ) 1) 0
      (hsigma _ 0) ≪≫ Limits.biproduct.mapIso (fun _ : Fin r ↦ t99A01_eD) ≪≫
      t99A01_biproduct_int_coordinate r).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp [t99A01_sigma_coordinate, t99A01_overlap_sigma_coordinate,
    t99A01_diskSide_sigma_coordinate]
  rw [t99A01_low_coordinates_degree_one_aux_inv]
  rw [ConstructionTargets.CoefficientRadialPair.homotopyIso_hom]
  let f := (Limits.biproduct.desc fun i : Fin r ↦
    HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
        (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
          @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
          C(Circle, Σ _ : Fin r, Circle))) 0)
  letI : IsIso f := hsigma (fun _ : Fin r ↦ Circle) 0
  apply (cancel_epi f).1
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  apply Limits.biproduct.hom_ext'
  intro i
  dsimp [f]
  simp only [Category.assoc, Limits.biproduct.ι_desc_assoc,
    Limits.biproduct.ι_map_assoc, Iso.hom_inv_id_assoc]
  have hp : Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫ f =
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0 := by
    change Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫
      (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0) = _
    rw [Limits.biproduct.ι_desc]
  have hc : HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
            @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩ :
            C(Circle, Σ _ : Fin r, Circle))) 0 ≫ inv f =
      Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i := by
    rw [← hp]
    simp
    rfl
  change _ = _ ≫ inv f ≫ _
  conv_rhs => rw [← Category.assoc, hc]
  have hm : Limits.biproduct.ι (fun _ : Fin r ↦ APMT99A01.H 0 Circle) i ≫
        (Limits.biproduct.map fun _ : Fin r ↦ t99A01_eC.hom) ≫
        (Limits.biproduct.map fun _ : Fin r ↦ t99A01_eD.inv) ≫
        (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
            (⟨@Sigma.mk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) i,
              @continuous_sigmaMk (Fin r)
                (fun _ ↦ Metric.ball (0 : ℂ) 1) _ i⟩ :
              C(Metric.ball (0 : ℂ) 1, Σ _ : Fin r, Metric.ball (0 : ℂ) 1))) 0) =
      t99A01_eC.hom ≫ t99A01_eD.inv ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
            (⟨@Sigma.mk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) i,
              @continuous_sigmaMk (Fin r)
                (fun _ ↦ Metric.ball (0 : ℂ) 1) _ i⟩ :
              C(Metric.ball (0 : ℂ) 1, Σ _ : Fin r, Metric.ball (0 : ℂ) 1))) 0 := by
    simp only [Category.assoc, Limits.biproduct.ι_map_assoc,
      Limits.biproduct.ι_desc_assoc]
    slice_lhs 3 4 => rw [Limits.biproduct.ι_desc]
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
    (ModuleCat.of ℤ ℤ)
  let s : C(Circle, Σ _ : Fin r, Circle) :=
    ⟨@Sigma.mk (Fin r) (fun _ ↦ Circle) i,
      @continuous_sigmaMk (Fin r) (fun _ ↦ Circle) _ i⟩
  let inc : C(↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
      APMT99A01.sideB degree) :=
    ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion Set.inter_subset_right⟩
  let b : C(APMT99A01.sideB degree,
      Σ _ : Fin r, Metric.ball (0 : ℂ) 1) := eB.toHomotopyEquiv.toFun
  let g : C(Circle, Metric.ball (0 : ℂ) 1) :=
    ⟨fun w ↦ ⟨w / 2, by
        rw [Metric.mem_ball, dist_zero_right, norm_div, Circle.norm_coe]
        norm_num⟩,
      Continuous.subtype_mk (continuous_subtype_val.div_const 2) (by
        intro w
        rw [Metric.mem_ball, dist_zero_right, norm_div, Circle.norm_coe]
        norm_num)⟩
  let t : C(Metric.ball (0 : ℂ) 1,
      Σ _ : Fin r, Metric.ball (0 : ℂ) 1) :=
    ⟨@Sigma.mk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) i,
      @continuous_sigmaMk (Fin r) (fun _ ↦ Metric.ball (0 : ℂ) 1) _ i⟩
  apply Eq.trans (b := t99A01_eC.hom ≫ t99A01_eD.inv ≫
    F.map (TopCat.ofHom t))
  swap
  exact hm.symm
  change F.map (TopCat.ofHom s) ≫ F.map (TopCat.ofHom eO.invFun) ≫
      F.map (TopCat.ofHom inc) ≫ F.map (TopCat.ofHom b) =
    t99A01_eC.hom ≫ t99A01_eD.inv ≫ F.map (TopCat.ofHom t)
  have hcomp : b.comp (inc.comp (eO.invFun.comp s)) = t.comp g := by
    apply ContinuousMap.ext
    intro w
    have hmem : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideB degree := by
      rw [← heO i w]
      exact (eO.invFun ⟨i, w⟩).property.2
    have hb := heB i (APMT99A01.halfPoint w) (by
      rw [show ‖((APMT99A01.halfPoint w : APMT99A01.Disk) : ℂ)‖ = 1 / 2 by
        simp [APMT99A01.halfPoint, norm_div, Circle.norm_coe]]
      norm_num) hmem
    have hx : inc (eO.invFun (s w)) =
        ⟨APMT99A01.halfLoop degree i w, hmem⟩ := by
      apply Subtype.ext
      exact heO i w
    rw [show (b.comp (inc.comp (eO.invFun.comp s))) w =
      b ⟨APMT99A01.halfLoop degree i w, hmem⟩ by exact congrArg b hx]
    simpa [b, t, g, APMT99A01.halfLoop, APMT99A01.halfPoint] using hb
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
  change F.map (TopCat.ofHom (b.comp (inc.comp (eO.invFun.comp s)))) = _
  rw [hcomp]
  change F.map (TopCat.ofHom g ≫ TopCat.ofHom t) = _
  rw [F.map_comp]
  have hg : t99A01_eC.hom ≫ t99A01_eD.inv = F.map (TopCat.ofHom g) := by
    apply (cancel_mono t99A01_eD.hom).1
    change (ConstructionTargets.CoefficientH0.h0Augmentation ℤ ≫
        ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ
          (⟨0, by simp [Metric.mem_ball]⟩ : Metric.ball (0 : ℂ) 1)) ≫
        ConstructionTargets.CoefficientH0.h0Augmentation ℤ = _
    rw [Category.assoc,
      ConstructionTargets.CoefficientH0.singularVertexH0Class_comp_h0Augmentation,
      Category.comp_id]
    exact (ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℤ g).symm
  exact (congrArg (fun q => q ≫ F.map (TopCat.ofHom t)) hg).symm
lemma t99A01_low_coordinates_degree_zero {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r)
    (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree))
    (hρι : ρ.comp ι = ContinuousMap.id Circle)
    (hιρ : ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _))
    (eB : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1))
    (eO : ContinuousMap.HomotopyEquiv
      ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle))
    (heB : ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
      (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
      eB ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩)
    (heO : ∀ (i : Fin r) (w : Circle), (eO.invFun ⟨i, w⟩).1 =
      APMT99A01.halfLoop degree i w)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
          (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j))) :
    let eC := t99A01_eC
    let eD : ∀ _ : Fin r, APMT99A01.H 0 (Metric.ball (0 : ℂ) 1) ≅ ModuleCat.of ℤ ℤ :=
      fun _ ↦ t99A01_eD
    let cO₀ := t99A01_overlap_sigma_coordinate degree eO 0 ≪≫
      t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso (fun _ : Fin r ↦ eC) ≪≫ t99A01_biproduct_int_coordinate r
    let cA₀ := t99A01_sideA_coordinate degree ρ ι hρι hιρ 0 ≪≫ eC
    let cB₀ := t99A01_diskSide_sigma_coordinate degree eB 0 ≪≫
      t99A01_sigma_coordinate (fun _ : Fin r ↦ Metric.ball (0 : ℂ) 1) 0 (hsigma _ 0) ≪≫
      Limits.biproduct.mapIso eD ≪≫ t99A01_biproduct_int_coordinate r
    (cO₀.inv ≫ APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) 0 ≫
      Limits.biprod.fst ≫ cA₀.hom = ModuleCat.ofHom t99A01_coordinateSum) ∧
    (cO₀.inv ≫ APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) 0 ≫
      Limits.biprod.snd ≫ cB₀.hom = 𝟙 _) := by
  dsimp only
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.pi_ext
    intro i x
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    have hsingle : ModuleCat.ofHom
        (LinearMap.single ℤ (fun _ : Fin r => ℤ) i) ≫
        (ModuleCat.biproductIsoPi (fun _ : Fin r => ModuleCat.of ℤ ℤ)).inv =
        Limits.biproduct.ι (fun _ : Fin r => ModuleCat.of ℤ ℤ) i := by
      apply Limits.biproduct.hom_ext
      intro j
      rw [Category.assoc, ModuleCat.biproductIsoPi_inv_comp_π]
      apply ModuleCat.hom_ext
      ext y
      by_cases h : i = j
      · subst j
        simp
      · simp [Pi.single_apply, h]
    have hsingle_apply := congrArg
      (fun f : ModuleCat.of ℤ ℤ ⟶ (⨁ fun _ : Fin r => ModuleCat.of ℤ ℤ) => f.hom x)
      hsingle
    have hsingle_apply' :
        (ModuleCat.biproductIsoPi (fun _ : Fin r => ModuleCat.of ℤ ℤ)).inv.hom
          (Pi.single i x) =
        (Limits.biproduct.ι (fun _ : Fin r => ModuleCat.of ℤ ℤ) i).hom x := by
      simpa [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.single_apply] using hsingle_apply
    have hmap_apply := congrArg
      (fun f : ModuleCat.of ℤ ℤ ⟶
        (⨁ fun _ : Fin r => APMT99A01.H 0 Circle) => f.hom x)
      (Limits.biproduct.ι_map (fun _ : Fin r => t99A01_eC.inv) i)
    change
        (Limits.biproduct.map (fun _ : Fin r => t99A01_eC.inv)).hom
          ((Limits.biproduct.ι (fun _ : Fin r => ModuleCat.of ℤ ℤ) i).hom x) =
        (Limits.biproduct.ι (fun _ : Fin r => APMT99A01.H 0 Circle) i).hom
          (t99A01_eC.inv.hom x) at hmap_apply
    simp only [Iso.trans_inv, t99A01_biproduct_int_coordinate,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    rw [hsingle_apply']
    dsimp [Limits.biproduct.mapIso]
    rw [hmap_apply]
    have hs := congrArg
      (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f.hom x)
      (t99A01_low_coordinates_degree_zero_aux_left degree ρ ι hρι hιρ
        eO hsigma i)
    simpa [Iso.trans_inv, t99A01_biproduct_int_coordinate,
      t99A01_coordinateSum, hsingle_apply, hmap_apply, Pi.single_apply] using hs
  · exact t99A01_low_coordinates_degree_zero_aux_right_aux_right
      degree eB eO heB heO hsigma
/-- Standard `H₀` coordinates for the circle and the open disk components. -/
lemma t99A01_low_h0_coordinates {r : ℕ} :
    ∃ (eC : APMT99A01.H 0 Circle ≅ ModuleCat.of ℤ ℤ)
      (eD : ∀ _ : Fin r,
        APMT99A01.H 0 (Metric.ball (0 : ℂ) 1) ≅ ModuleCat.of ℤ ℤ), True := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
          isPathConnected_univ
      simpa using h)
  letI : PathConnectedSpace (Metric.ball (0 : ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_ball (x := (0 : ℂ)) (r := 1) (by norm_num))
  exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℤ (1 : Circle),
    fun _ ↦ ConstructionTargets.CoefficientH0.h0Iso ℤ
      ⟨0, by simp [Metric.mem_ball]⟩, trivial⟩

lemma t99A01_low_j0_surjective_aux_vertex_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ x ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ f) 0 =
      ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ (f x) := by
  let s := ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
    (TopCat.of X) 0 (ConstructionTargets.T02A06SphereH0.singularVertexAt x)
  have hpoint : ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint s = x := by
    change ((TopCat.toSSetObjEquiv (TopCat.of X)
        (Opposite.op (SimplexCategory.mk 0)))
      ((TopCat.toSSetObjEquiv (TopCat.of X)
        (Opposite.op (SimplexCategory.mk 0))).symm
        (ContinuousMap.const _ x)))
          (ConstructionTargets.SingularSubdivision.standardSimplexVertices 0 0) = x
    rw [Equiv.apply_symm_apply]
    rfl
  rw [← hpoint, ← ConstructionTargets.CoefficientH0.singularGenerator_zeroChainH0Class
    ℤ s, Category.assoc,
    ConstructionTargets.CoefficientH0.zeroChainH0Class_naturality ℤ]
  let sf := ConstructionTargets.SingularSubdivision.singularSimplexOfContinuousMap
    (TopCat.of Y) 0 (f.comp (ConstructionTargets.T02A06SphereH0.singularVertexAt x))
  have hm : ConstructionTargets.CoefficientH0.singularGenerator ℤ (TopCat.of X) 0 s ≫
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ f).f 0 =
      ConstructionTargets.CoefficientH0.singularGenerator ℤ (TopCat.of Y) 0 sf := by
    exact ConstructionTargets.CoefficientH0.singularGenerator_singularPostcomposition ℤ _
      (ConstructionTargets.T02A06SphereH0.singularVertexAt x) f
  calc
    _ = ConstructionTargets.CoefficientH0.singularGenerator ℤ (TopCat.of Y) 0 sf ≫
        ConstructionTargets.CoefficientH0.zeroChainH0Class ℤ := by
          simpa only [Category.assoc] using congrArg
            (fun q => q ≫ ConstructionTargets.CoefficientH0.zeroChainH0Class ℤ) hm
    _ = ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ
        (ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint sf) :=
      ConstructionTargets.CoefficientH0.singularGenerator_zeroChainH0Class ℤ sf
    _ = _ := by rfl

lemma t99A01_low_j0_surjective {r : ℕ} (degree : Fin r → ℕ) (hr : 0 < r) :
    Function.Surjective
      (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) 0).hom := by
  classical
  let K := ConstructionTargets.CoefficientH0.SingularChains ℤ
    (TopCat.of (APMT99A01.AttachSpace degree))
  let point := fun s : ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of (APMT99A01.AttachSpace degree)) 0 =>
    ConstructionTargets.T02A06SphereH0.singularZeroSimplexPoint s
  let liftVertex := fun s : ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of (APMT99A01.AttachSpace degree)) 0 =>
    if hs : point s ∈ APMT99A01.sideA degree then
      ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ
          (⟨point s, hs⟩ : APMT99A01.sideA degree) ≫ Limits.biprod.inl
    else
      -ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ
          (⟨point s, by
            have hc : point s ∈ APMT99A01.sideA degree ∨
                point s ∈ APMT99A01.sideB degree := by
              rw [← Set.mem_union, (t99A01_attach_openCover degree).2.2]
              trivial
            exact hc.resolve_left hs⟩ : APMT99A01.sideB degree) ≫ Limits.biprod.inr
  let L : K.X 0 ⟶
      APMT99A01.H 0 (APMT99A01.sideA degree) ⊞
        APMT99A01.H 0 (APMT99A01.sideB degree) := by
    change (∐ fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
      (TopCat.of (APMT99A01.AttachSpace degree)) 0 ↦ ModuleCat.of ℤ ℤ) ⟶ _
    exact Limits.Sigma.desc liftVertex
  have hfactor : L ≫ APMT99A01.zJ (APMT99A01.sideA degree)
      (APMT99A01.sideB degree) 0 =
      ConstructionTargets.CoefficientH0.zeroChainH0Class ℤ := by
    apply Limits.Sigma.hom_ext
    intro s
    change (Limits.Sigma.ι (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of (APMT99A01.AttachSpace degree)) 0 ↦ ModuleCat.of ℤ ℤ) s ≫
        L) ≫ APMT99A01.zJ (APMT99A01.sideA degree)
          (APMT99A01.sideB degree) 0 = _
    have hL : Limits.Sigma.ι (fun _ : ConstructionTargets.SingularSubdivision.SingularSimplex
        (TopCat.of (APMT99A01.AttachSpace degree)) 0 ↦ ModuleCat.of ℤ ℤ) s ≫ L =
        liftVertex s := by
      dsimp [L]
      exact Limits.Sigma.ι_desc _ _
    rw [hL]
    change liftVertex s ≫ APMT99A01.zJ (APMT99A01.sideA degree)
      (APMT99A01.sideB degree) 0 =
        ConstructionTargets.CoefficientH0.singularGenerator ℤ
          (TopCat.of (APMT99A01.AttachSpace degree)) 0 s ≫
            ConstructionTargets.CoefficientH0.zeroChainH0Class ℤ
    rw [ConstructionTargets.CoefficientH0.singularGenerator_zeroChainH0Class ℤ s]
    change liftVertex s ≫ APMT99A01.zJ (APMT99A01.sideA degree)
      (APMT99A01.sideB degree) 0 =
        ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ (point s)
    dsimp only [liftVertex]
    split_ifs with hs
    · rw [APMT99A01.zJ, Category.assoc, Limits.biprod.inl_desc]
      exact t99A01_low_j0_surjective_aux_vertex_naturality
        (⟨Subtype.val, continuous_subtype_val⟩ : C(APMT99A01.sideA degree, _)) _
    · rw [APMT99A01.zJ, Preadditive.neg_comp, Category.assoc,
        Limits.biprod.inr_desc, Preadditive.comp_neg, neg_neg]
      exact t99A01_low_j0_surjective_aux_vertex_naturality
        (⟨Subtype.val, continuous_subtype_val⟩ : C(APMT99A01.sideB degree, _)) _
  intro y
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (ConstructionTargets.CoefficientH0.zeroChainH0Class ℤ
      (X := APMT99A01.AttachSpace degree))).mp inferInstance y
  refine ⟨L.hom x, ?_⟩
  change (L ≫ APMT99A01.zJ (APMT99A01.sideA degree)
    (APMT99A01.sideB degree) 0).hom x =
      (ConstructionTargets.CoefficientH0.zeroChainH0Class ℤ).hom x
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hfactor) x

lemma t99A01_attach_transport_aux_low_degree {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i)
    (hcover : IsOpen (APMT99A01.sideA degree) ∧ IsOpen (APMT99A01.sideB degree) ∧
      APMT99A01.sideA degree ∪ APMT99A01.sideB degree = Set.univ)
    (hcircle : ∃ (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree)),
      (∀ z, (ι z).1 = APMT99A01.circleIncl degree z) ∧
      ρ.comp ι = ContinuousMap.id Circle ∧
      ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _) ∧
      ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideA degree),
        ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i)
    (hdisk : ∃ e : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
        (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
        e ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩)
    (hoverlap : ∃ e : ContinuousMap.HomotopyEquiv
        ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle),
      ∀ (i : Fin r) (w : Circle), (e.invFun ⟨i, w⟩).1 = APMT99A01.halfLoop degree i w)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
            (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
          (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)))
    (hwinding : ∃ e : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ,
      ∀ i : Fin r, e.inv ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map
            (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e.hom =
        ModuleCat.ofHom (APMT99A01.intTimesNat (degree i)))
    (hexact : ∃ δ : ∀ n, APMT99A01.H (n + 1) (APMT99A01.AttachSpace degree) ⟶
        APMT99A01.H n ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
      (∀ n, LinearMap.range
          (APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom =
        LinearMap.ker
          (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom) ∧
      (∀ n, LinearMap.range
          (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) (n + 1)).hom =
        LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker
        (APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom)) :
    Nonempty (APMT99A01.AttachMVLowData degree) := by
  obtain ⟨ρ, ι, -, hρι, hιρ, hρ⟩ := hcircle
  obtain ⟨eB, heB⟩ := hdisk
  obtain ⟨eO, heO⟩ := hoverlap
  obtain ⟨e₁, hw⟩ := hwinding
  let eC := t99A01_eC
  let eD : ∀ _ : Fin r, APMT99A01.H 0 (Metric.ball (0 : ℂ) 1) ≅ ModuleCat.of ℤ ℤ :=
    fun _ ↦ t99A01_eD
  obtain ⟨δ, hIJ, hJδ, hδI⟩ := hexact
  let cO₁ := t99A01_overlap_sigma_coordinate degree eO 1 ≪≫
    t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 1 (hsigma _ 1) ≪≫
    Limits.biproduct.mapIso (fun _ : Fin r ↦ e₁) ≪≫ t99A01_biproduct_int_coordinate r
  let cA₁ := t99A01_sideA_coordinate degree ρ ι hρι hιρ 1 ≪≫ e₁
  let cO₀ := t99A01_overlap_sigma_coordinate degree eO 0 ≪≫
    t99A01_sigma_coordinate (fun _ : Fin r ↦ Circle) 0 (hsigma _ 0) ≪≫
    Limits.biproduct.mapIso (fun _ : Fin r ↦ eC) ≪≫ t99A01_biproduct_int_coordinate r
  let cA₀ := t99A01_sideA_coordinate degree ρ ι hρι hιρ 0 ≪≫ eC
  let cB₀ := t99A01_diskSide_sigma_coordinate degree eB 0 ≪≫
    t99A01_sigma_coordinate (fun _ : Fin r ↦ Metric.ball (0 : ℂ) 1) 0 (hsigma _ 0) ≪≫
    Limits.biproduct.mapIso eD ≪≫ t99A01_biproduct_int_coordinate r
  obtain ⟨hA₂, hB₁, hB₂⟩ := t99A01_low_coordinates_vanishing degree ρ ι hρι hιρ eB
  have hdeg := t99A01_low_coordinates_degree_one degree ρ ι hρι hιρ eO heO hρ hsigma e₁ hw
  obtain ⟨hsum, hid⟩ := t99A01_low_coordinates_degree_zero degree hr ρ ι hρι hιρ
    eB eO heB heO hsigma
  exact t99A01_lowData_of_coordinates degree _ _ _ _ _ _ _ _
    (APMT99A01.zI _ _ 0) (APMT99A01.zI _ _ 1) (APMT99A01.zJ _ _ 0)
    (APMT99A01.zJ _ _ 1) (APMT99A01.zJ _ _ 2) (δ 0) (δ 1)
    (hIJ 1) (hJδ 0) (hδI 0) (hIJ 0) (hJδ 1) (hδI 1)
    hA₂ hB₁ hB₂ (t99A01_low_j0_surjective degree hr) cO₀ cO₁ cA₀ cA₁ cB₀
    hdeg hsum hid
/-- **Leaf (higher degrees, 50--100 lines, independent).** An attaching space made
from a circle and finitely many two-disks has no integral homology in degrees
at least three.  Prove this from the same MV cover using circle and contractible
ball vanishing; it is deliberately independent of all low-degree coordinates. -/
lemma t99A01_attach_transport_aux_higher_aux_exact_zero
    {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hA : Limits.IsZero A) (hC : Limits.IsZero C)
    (hex : LinearMap.range f.hom = LinearMap.ker g.hom) : Limits.IsZero B := by
  letI : Subsingleton B := ⟨by
    intro x y
    suffices hz : ∀ z : B, z = 0 by exact (hz x).trans (hz y).symm
    intro z
    have hg : g.hom z = 0 := by
      letI := ModuleCat.subsingleton_of_isZero hC
      exact Subsingleton.elim _ _
    have hz : z ∈ LinearMap.ker g.hom := hg
    rw [← hex] at hz
    obtain ⟨a, ha⟩ := hz
    letI := ModuleCat.subsingleton_of_isZero hA
    rw [← ha, Subsingleton.elim a 0, map_zero]⟩
  exact ModuleCat.isZero_of_subsingleton _

lemma t99A01_attach_transport_aux_higher_aux_sigma_zero {r k : ℕ}
    (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)]
    (hY : ∀ i, Limits.IsZero (APMT99A01.H k (Y i))) :
    Limits.IsZero (APMT99A01.H k (Σ i, Y i)) := by
  let f := Limits.biproduct.desc fun i : Fin r ↦
    HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
        (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k
  letI : IsIso f := t99A01_sigma_homology Y k
  have hs : Limits.IsZero (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    apply Limits.biproduct.hom_ext'
    intro i
    exact (hY i).eq_of_src _ _
  exact hs.of_iso (asIso f).symm

lemma t99A01_attach_transport_aux_higher {r : ℕ} (degree : Fin r → ℕ) :
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (APMT99A01.H k (APMT99A01.AttachSpace degree)) := by
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := by
    exact ⟨k - 3, by omega⟩
  obtain ⟨ρ, ι, -, hρι, hιρ, -⟩ := t99A01_attach_circleSide degree
  obtain ⟨eB, -⟩ := t99A01_attach_diskSide degree
  obtain ⟨eI, -⟩ := t99A01_attach_overlap degree
  have hcircle (q : ℕ) (hq : 1 < q) :
      Limits.IsZero (APMT99A01.H q Circle) :=
    ConstructionTargets.SolidTorusHomotopyAndHomology.circleModuleHomology_isZero_of_one_lt
      q hq
  have hA : Limits.IsZero
      (APMT99A01.H (n + 3) (APMT99A01.sideA degree)) :=
    (hcircle (n + 3) (by omega)).of_iso
      (t99A01_sideA_coordinate degree ρ ι hρι hιρ (n + 3))
  have hBσ : Limits.IsZero
      (APMT99A01.H (n + 3) (Σ _ : Fin r, Metric.ball (0 : ℂ) 1)) := by
    apply t99A01_attach_transport_aux_higher_aux_sigma_zero
    intro i
    letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
      Metric.contractibleSpace_ball (by norm_num)
    exact ConstructionTargets.CoefficientContractiblePair.higher_zero ℤ
      (Metric.ball (0 : ℂ) 1) (n + 3) (by omega)
  have hB : Limits.IsZero
      (APMT99A01.H (n + 3) (APMT99A01.sideB degree)) :=
    hBσ.of_iso (t99A01_diskSide_sigma_coordinate degree eB (n + 3))
  have hpieces : Limits.IsZero
      (APMT99A01.H (n + 3) (APMT99A01.sideA degree) ⊞
        APMT99A01.H (n + 3) (APMT99A01.sideB degree)) :=
    (Limits.biprod_isZero_iff _ _).2 ⟨hA, hB⟩
  have hIσ : Limits.IsZero
      (APMT99A01.H (n + 2) (Σ _ : Fin r, Circle)) := by
    apply t99A01_attach_transport_aux_higher_aux_sigma_zero
    intro i
    exact hcircle (n + 2) (by omega)
  have hI : Limits.IsZero
      (APMT99A01.H (n + 2)
        ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree)) :=
    hIσ.of_iso (t99A01_overlap_sigma_coordinate degree eI (n + 2))
  obtain ⟨δ, -, hex, -⟩ := t99A01_integralMayerVietoris
    (APMT99A01.sideA degree) (APMT99A01.sideB degree)
    (t99A01_attach_openCover degree).1
    (t99A01_attach_openCover degree).2.1
    (t99A01_attach_openCover degree).2.2
  apply t99A01_attach_transport_aux_higher_aux_exact_zero
    (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) (n + 3))
    (δ (n + 2)) hpieces hI
  simpa only [Nat.add_assoc, Nat.reduceAdd] using hex (n + 2)

lemma t99A01_attach_transport_aux_coordinates {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i)
    (hcover : IsOpen (APMT99A01.sideA degree) ∧ IsOpen (APMT99A01.sideB degree) ∧
      APMT99A01.sideA degree ∪ APMT99A01.sideB degree = Set.univ)
    (hcircle : ∃ (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree)),
      (∀ z, (ι z).1 = APMT99A01.circleIncl degree z) ∧
      ρ.comp ι = ContinuousMap.id Circle ∧
      ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _) ∧
      ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideA degree),
        ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i)
    (hdisk : ∃ e : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
        (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
        e ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩)
    (hoverlap : ∃ e : ContinuousMap.HomotopyEquiv
        ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle),
      ∀ (i : Fin r) (w : Circle), (e.invFun ⟨i, w⟩).1 = APMT99A01.halfLoop degree i w)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
            (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
          (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)))
    (hwinding : ∃ e : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ,
      ∀ i : Fin r, e.inv ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map
            (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e.hom =
        ModuleCat.ofHom (APMT99A01.intTimesNat (degree i)))
    (hexact : ∃ δ : ∀ n, APMT99A01.H (n + 1) (APMT99A01.AttachSpace degree) ⟶
        APMT99A01.H n ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree),
      (∀ n, LinearMap.range
          (APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom =
        LinearMap.ker
          (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom) ∧
      (∀ n, LinearMap.range
          (APMT99A01.zJ (APMT99A01.sideA degree) (APMT99A01.sideB degree) (n + 1)).hom =
        LinearMap.ker (δ n).hom) ∧
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker
        (APMT99A01.zI (APMT99A01.sideA degree) (APMT99A01.sideB degree) n).hom)) :
    Nonempty (APMT99A01.AttachMVData degree) := by
  obtain ⟨D⟩ := t99A01_attach_transport_aux_low_degree degree hr hdegree hcover hcircle
    hdisk hoverlap hsigma hwinding hexact
  refine ⟨{
    i₁ := D.i₁
    j₁ := D.j₁
    δ₁ := D.δ₁
    i₀ := D.i₀
    j₀ := D.j₀
    δ₂ := D.δ₂
    i₁_eq_degreeMap := D.i₁_eq_degreeMap
    i₀_injective := D.i₀_injective
    i₀_eq := D.i₀_eq
    exact_i₁_j₁ := D.exact_i₁_j₁
    exact_j₁_δ₁ := D.exact_j₁_δ₁
    exact_δ₁_i₀ := D.exact_δ₁_i₀
    exact_i₀_j₀ := D.exact_i₀_j₀
    j₀_surjective := D.j₀_surjective
    δ₂_injective := D.δ₂_injective
    exact_δ₂_i₁ := D.exact_δ₂_i₁
    higher := t99A01_attach_transport_aux_higher degree }⟩

theorem t99A01_attach_transport {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i)
    (hcover : IsOpen (APMT99A01.sideA degree) ∧ IsOpen (APMT99A01.sideB degree) ∧
      APMT99A01.sideA degree ∪ APMT99A01.sideB degree = Set.univ)
    (hcircle : ∃ (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree)),
      (∀ z, (ι z).1 = APMT99A01.circleIncl degree z) ∧
      ρ.comp ι = ContinuousMap.id Circle ∧
      ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _) ∧
      ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideA degree),
        ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i)
    (hdisk : ∃ e : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
        (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
        e ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩)
    (hoverlap : ∃ e : ContinuousMap.HomotopyEquiv
        ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) (Σ _ : Fin r, Circle),
      ∀ (i : Fin r) (w : Circle), (e.invFun ⟨i, w⟩).1 = APMT99A01.halfLoop degree i w)
    (hsigma : ∀ (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)] (k : ℕ),
      IsIso (Limits.biproduct.desc fun i : Fin r ↦
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientH0.singularPostcomposition ℤ
            (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) k :
          (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)))
    (hwinding : ∃ e : APMT99A01.H 1 Circle ≅ ModuleCat.of ℤ ℤ,
      ∀ i : Fin r, e.inv ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map
            (TopCat.ofHom (APMT99A01.circlePower (degree i))) ≫ e.hom =
        ModuleCat.ofHom (APMT99A01.intTimesNat (degree i)))
    (hmv : ∀ (U V : Set (APMT99A01.AttachSpace degree)), IsOpen U → IsOpen V →
      U ∪ V = Set.univ →
      ∃ δ : ∀ n, APMT99A01.H (n + 1) (APMT99A01.AttachSpace degree) ⟶ APMT99A01.H n ↥(U ∩ V),
        (∀ n, LinearMap.range (APMT99A01.zI U V n).hom =
          LinearMap.ker (APMT99A01.zJ U V n).hom) ∧
        (∀ n, LinearMap.range (APMT99A01.zJ U V (n + 1)).hom = LinearMap.ker (δ n).hom) ∧
        (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (APMT99A01.zI U V n).hom)) :
    Nonempty (APMT99A01.AttachMVData degree) := by
  apply t99A01_attach_transport_aux_coordinates degree hr hdegree hcover hcircle hdisk
    hoverlap hsigma hwinding
  exact t99A01_attach_transport_aux_mv degree hcover hmv
theorem t99A01_attachSpace_MVData {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.AttachMVData degree) :=
  t99A01_attach_transport degree hr hdegree
    (t99A01_attach_openCover degree)
    (t99A01_attach_circleSide degree)
    (t99A01_attach_diskSide degree)
    (t99A01_attach_overlap degree)
    (fun Y _ k ↦ t99A01_sigma_homology Y k)
    (t99A01_circlePower_hOne_row degree)
    (fun U V hU hV hc ↦ t99A01_integralMayerVietoris U V hU hV hc)
/-! The next four leaves are independent pure algebra/diagram chases.  Their
only common input is an arbitrary `AttachMVData`; hence they can be proved in
parallel and cannot acquire the MV leaf's `sorryAx`. -/

def t99A01_attachMVData_hZero_aux_map {r : ℕ} :
    (ℤ × (Fin r → ℤ)) →ₗ[ℤ] ℤ where
  toFun p := p.1 - ∑ i, p.2 i
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
    rw [← Finset.mul_sum]
    simp only [RingHom.id_apply]
    ring

theorem t99A01_attachMVData_hZero {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) :
    Nonempty (APMT99A01.H 0 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ ℤ) := by
  let f : (ℤ × (Fin r → ℤ)) →ₗ[ℤ] ℤ :=
    t99A01_attachMVData_hZero_aux_map
  have hfker : LinearMap.ker f = LinearMap.range D.i₀ := by
    ext p
    constructor
    · intro hp
      rw [LinearMap.mem_ker] at hp
      refine ⟨p.2, ?_⟩
      rw [D.i₀_eq]
      apply Prod.ext
      · change (∑ i, p.2 i) = p.1
        change p.1 - ∑ i, p.2 i = 0 at hp
        omega
      · rfl
    · rintro ⟨x, rfl⟩
      rw [LinearMap.mem_ker, D.i₀_eq]
      simp [f, t99A01_attachMVData_hZero_aux_map]
  have hexact_f : Function.Exact D.i₀ f := by
    rw [LinearMap.exact_iff]
    exact hfker
  have hf_surj : Function.Surjective f := by
    intro z
    refine ⟨(z, 0), ?_⟩
    simp [f, t99A01_attachMVData_hZero_aux_map]
  have hexact_j : Function.Exact D.i₀ D.j₀ := by
    rw [LinearMap.exact_iff]
    exact D.exact_i₀_j₀.symm
  let ej := hexact_j.linearEquivOfSurjective D.j₀_surjective
  let ef := hexact_f.linearEquivOfSurjective hf_surj
  exact ⟨LinearEquiv.toModuleIso (ej.symm.trans ef)⟩

theorem t99A01_attachMVData_hOne {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) :
    Nonempty (APMT99A01.H 1 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeCokernel degree)) := by
  have hdelta : D.δ₁ = 0 := by
    apply LinearMap.ext
    intro x
    apply D.i₀_injective
    have hx : D.δ₁ x ∈ LinearMap.range D.δ₁ := ⟨x, rfl⟩
    rw [D.exact_δ₁_i₀] at hx
    simpa using hx
  have hj : Function.Surjective D.j₁ := by
    rw [← LinearMap.range_eq_top, D.exact_j₁_δ₁, hdelta,
      LinearMap.ker_zero]
  have hexact : Function.Exact (APMT99A01.degreeMap degree) D.j₁ := by
    rw [LinearMap.exact_iff]
    rw [← D.i₁_eq_degreeMap]
    exact D.exact_i₁_j₁.symm
  exact ⟨LinearEquiv.toModuleIso (hexact.linearEquivOfSurjective hj).symm⟩

theorem t99A01_attachMVData_hTwo {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) :
    Nonempty (APMT99A01.H 2 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeKernel degree)) := by
  have hrange : LinearMap.range D.δ₂ =
      LinearMap.ker (APMT99A01.degreeMap degree) := by
    rw [← D.i₁_eq_degreeMap]
    exact D.exact_δ₂_i₁
  exact ⟨LinearEquiv.toModuleIso
    ((LinearEquiv.ofInjective D.δ₂ D.δ₂_injective).trans
      (LinearEquiv.ofEq _ _ hrange))⟩

theorem t99A01_attachMVData_hHigher {r : ℕ} (degree : Fin r → ℕ)
    (D : APMT99A01.AttachMVData degree) (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k (APMT99A01.AttachSpace degree)) := by
  exact D.higher k hk

/-- **LIBRARY leaf (MV, degree zero).** A nonempty positive family of cells
attached to the circle is connected. -/
theorem t99A01_attachSpace_hZero {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 0 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ ℤ) := by
  exact t99A01_attachMVData_hZero degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree))

/-- **LIBRARY leaf (MV, degree one).** The first homology is the cokernel of
the row of attaching degrees. -/
theorem t99A01_attachSpace_hOne {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 1 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeCokernel degree)) := by
  exact t99A01_attachMVData_hOne degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree))

/-- **LIBRARY leaf (MV, degree two).** The second homology is the kernel of
the row of attaching degrees. -/
theorem t99A01_attachSpace_hTwo {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 2 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeKernel degree)) := by
  exact t99A01_attachMVData_hTwo degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree))

/-- **LIBRARY leaf (MV, high degrees).** The homology vanishes above the
two-dimensional cover calculation. -/
theorem t99A01_attachSpace_hHigher {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k (APMT99A01.AttachSpace degree)) := by
  exact t99A01_attachMVData_hHigher degree
    (Classical.choice (t99A01_attachSpace_MVData degree hr hdegree)) k hk

/-- Admission-free packaging of the generic positive-degree calculation. -/
theorem t99A01_attachSpace_homology {r : ℕ} (degree : Fin r → ℕ)
    (hr : 0 < r) (hdegree : ∀ i, 0 < degree i) :
    Nonempty (APMT99A01.H 0 (APMT99A01.AttachSpace degree) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeCokernel degree)) ∧
    Nonempty (APMT99A01.H 2 (APMT99A01.AttachSpace degree) ≅
      ModuleCat.of ℤ (APMT99A01.DegreeKernel degree)) ∧
    ∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (APMT99A01.H k (APMT99A01.AttachSpace degree)) := by
  exact ⟨t99A01_attachSpace_hZero degree hr hdegree,
    t99A01_attachSpace_hOne degree hr hdegree,
    t99A01_attachSpace_hTwo degree hr hdegree,
    t99A01_attachSpace_hHigher degree hr hdegree⟩

/-! The remaining admitted leaves are finite integer linear algebra.  They
do not depend on any topology leaf and can therefore be proved in parallel. -/

def t99A01_cokernel_X_aux_mod : ℤ →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap

lemma t99A01_cokernel_X_aux_exact : Function.Exact
    (APMT99A01.degreeMap APMT99A01.degreeX) t99A01_cokernel_X_aux_mod := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change (x : ZMod 2) = 0 at hx
    have hdvd : (2 : ℤ) ∣ x := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨fun _ ↦ k, ?_⟩
    change (∑ i, (APMT99A01.degreeX i : ℤ) * k) = x
    calc
      _ = 2 * k := by rw [Fin.sum_univ_one]; simp [APMT99A01.degreeX]
      _ = x := hk.symm
  · rintro ⟨v, rfl⟩
    change (((∑ i, (APMT99A01.degreeX i : ℤ) * v i) : ℤ) : ZMod 2) = 0
    rw [Fin.sum_univ_one]
    rw [show APMT99A01.degreeX 0 = 2 by rfl, Int.cast_mul]
    change (2 : ZMod 2) * (v 0 : ZMod 2) = 0
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [htwo]
    simp

theorem t99A01_cokernel_X : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeCokernel APMT99A01.degreeX) ≅
      ModuleCat.of ℤ (ZMod 2)) := by
  refine ⟨LinearEquiv.toModuleIso
    (t99A01_cokernel_X_aux_exact.linearEquivOfSurjective ?_)⟩
  exact ZMod.intCast_surjective

theorem t99A01_kernel_X : Limits.IsZero
    (ModuleCat.of ℤ (APMT99A01.DegreeKernel APMT99A01.degreeX)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro x y
  apply Subtype.ext
  funext i
  fin_cases i
  have hx : APMT99A01.degreeMap APMT99A01.degreeX
      (x : Fin 1 → ℤ) = 0 := x.2
  have hy : APMT99A01.degreeMap APMT99A01.degreeX
      (y : Fin 1 → ℤ) = 0 := y.2
  simp [APMT99A01.degreeMap, APMT99A01.degreeX] at hx hy
  simpa using hx.trans hy.symm

def t99A01_cokernel_Y_aux_mod : ℤ →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap

lemma t99A01_cokernel_Y_aux_exact : Function.Exact
    (APMT99A01.degreeMap APMT99A01.degreeY) t99A01_cokernel_Y_aux_mod := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change (x : ZMod 2) = 0 at hx
    have hdvd : (2 : ℤ) ∣ x := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨![k, 0], ?_⟩
    change (∑ i, (APMT99A01.degreeY i : ℤ) * (![k, 0] i)) = x
    simpa [APMT99A01.degreeY, Fin.sum_univ_two] using hk.symm
  · rintro ⟨v, rfl⟩
    change (((∑ i, (APMT99A01.degreeY i : ℤ) * v i) : ℤ) : ZMod 2) = 0
    rw [Fin.sum_univ_two]
    simp only [APMT99A01.degreeY, Matrix.cons_val_zero, Nat.cast_ofNat,
      Matrix.cons_val_one, Int.cast_add, Int.cast_mul]
    have h2 : ((2 : ℤ) : ZMod 2) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) 2).2 (dvd_refl 2)
    have h4 : ((4 : ℤ) : ZMod 2) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (4 : ℤ) 2).2 ⟨2, rfl⟩
    rw [h2, h4]
    simp

theorem t99A01_cokernel_Y : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeCokernel APMT99A01.degreeY) ≅
      ModuleCat.of ℤ (ZMod 2)) := by
  refine ⟨LinearEquiv.toModuleIso
    (t99A01_cokernel_Y_aux_exact.linearEquivOfSurjective ?_)⟩
  exact ZMod.intCast_surjective

def t99A01_kernel_Y_aux_coordinate :
    APMT99A01.DegreeKernel APMT99A01.degreeY →ₗ[ℤ] ℤ where
  toFun x := x.1 1
  map_add' x y := by simp
  map_smul' c x := by simp

lemma t99A01_kernel_Y_aux_bijective :
    Function.Bijective t99A01_kernel_Y_aux_coordinate := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext i
    fin_cases i
    · have hx : APMT99A01.degreeMap APMT99A01.degreeY x.1 = 0 :=
        LinearMap.mem_ker.mp x.2
      have hy : APMT99A01.degreeMap APMT99A01.degreeY y.1 = 0 :=
        LinearMap.mem_ker.mp y.2
      simp [APMT99A01.degreeMap, APMT99A01.degreeY] at hx hy
      change x.1 1 = y.1 1 at hxy
      have hx' : x.1 0 + 2 * x.1 1 = 0 := by omega
      have hy' : y.1 0 + 2 * y.1 1 = 0 := by omega
      change x.1 0 = y.1 0
      omega
    · exact hxy
  · intro n
    let x : Fin 2 → ℤ := ![-2 * n, n]
    have hx : APMT99A01.degreeMap APMT99A01.degreeY x = 0 := by
      simp [APMT99A01.degreeMap, APMT99A01.degreeY, x]
      ring
    refine ⟨⟨x, hx⟩, ?_⟩
    rfl

theorem t99A01_kernel_Y : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeKernel APMT99A01.degreeY) ≅
      ModuleCat.of ℤ ℤ) := by
  exact ⟨LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective t99A01_kernel_Y_aux_coordinate
      t99A01_kernel_Y_aux_bijective)⟩

theorem t99A01_cokernel_Z : Limits.IsZero
    (ModuleCat.of ℤ (APMT99A01.DegreeCokernel APMT99A01.degreeZ)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hsurj : Function.Surjective
      (APMT99A01.degreeMap APMT99A01.degreeZ) := by
    intro x
    refine ⟨![-2 * x, 0, x], ?_⟩
    simp [APMT99A01.degreeMap, APMT99A01.degreeZ, Fin.sum_univ_three]
    ring
  have hrange : LinearMap.range
      (APMT99A01.degreeMap APMT99A01.degreeZ) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  apply Quotient.sound
  apply (Submodule.quotientRel_def (p := LinearMap.range
    (APMT99A01.degreeMap APMT99A01.degreeZ))).2
  rw [hrange]
  trivial

def t99A01_kernel_Z_aux_parametrize :
    (Fin 2 → ℤ) →ₗ[ℤ] APMT99A01.DegreeKernel APMT99A01.degreeZ where
  toFun v := ⟨![-2 * v 0 - 5 * v 1, v 0, 2 * v 1], by
    simp [APMT99A01.degreeMap, APMT99A01.degreeZ, Fin.sum_univ_three]
    ring⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> ring

lemma t99A01_kernel_Z_aux_bijective :
    Function.Bijective t99A01_kernel_Z_aux_parametrize := by
  constructor
  · intro x y hxy
    have h := congr_arg Subtype.val hxy
    funext i
    fin_cases i
    · exact congr_fun h 1
    · have h2 := congr_fun h 2
      change 2 * x 1 = 2 * y 1 at h2
      simpa using (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2)
  · intro x
    have hx : APMT99A01.degreeMap APMT99A01.degreeZ x.1 = 0 :=
      LinearMap.mem_ker.mp x.2
    have hx' : 2 * x.1 0 + 4 * x.1 1 + 5 * x.1 2 = 0 := by
      simpa [APMT99A01.degreeMap, APMT99A01.degreeZ, Fin.sum_univ_three] using hx
    have heven : ∃ b : ℤ, x.1 2 = 2 * b := by
      refine ⟨-x.1 0 - 2 * x.1 1 - 2 * x.1 2, ?_⟩
      omega
    obtain ⟨b, hb⟩ := heven
    refine ⟨![x.1 1, b], ?_⟩
    apply Subtype.ext
    funext i
    fin_cases i
    · change -2 * x.1 1 - 5 * b = x.1 0
      omega
    · rfl
    · change 2 * b = x.1 2
      omega

theorem t99A01_kernel_Z : Nonempty
    (ModuleCat.of ℤ (APMT99A01.DegreeKernel APMT99A01.degreeZ) ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  exact ⟨LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective t99A01_kernel_Z_aux_parametrize
      t99A01_kernel_Z_aux_bijective).symm⟩

/-- **LIBRARY boundary.** The degree-zero integral homology of `X`. -/
theorem t99A01_hZero_X :
    Nonempty (APMT99A01.H 0 APMT99A01.X ≅ ModuleCat.of ℤ ℤ) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeX (by decide) (by decide)).1

/-- **LIBRARY boundary.** The degree-one integral homology of `X`. -/
theorem t99A01_hOne_X :
    Nonempty (APMT99A01.H 1 APMT99A01.X ≅ ModuleCat.of ℤ (ZMod 2)) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeX (by decide) (by decide)).2.1 ≪≫
      Classical.choice t99A01_cokernel_X⟩

/-- **LIBRARY boundary.** The degree-two integral homology of `X`. -/
theorem t99A01_hTwo_X :
    Limits.IsZero (APMT99A01.H 2 APMT99A01.X) := by
  exact t99A01_kernel_X.of_iso (Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeX (by decide) (by decide)).2.2.1)

/-- **LIBRARY boundary.** The degree-zero integral homology of `Y`. -/
theorem t99A01_hZero_Y :
    Nonempty (APMT99A01.H 0 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeY (by decide) (by decide)).1

/-- **LIBRARY boundary.** The degree-one integral homology of `Y`. -/
theorem t99A01_hOne_Y :
    Nonempty (APMT99A01.H 1 APMT99A01.Y ≅ ModuleCat.of ℤ (ZMod 2)) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeY (by decide) (by decide)).2.1 ≪≫
      Classical.choice t99A01_cokernel_Y⟩

/-- **LIBRARY boundary.** The degree-two integral homology of `Y`. -/
theorem t99A01_hTwo_Y :
    Nonempty (APMT99A01.H 2 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeY (by decide) (by decide)).2.2.1 ≪≫
      Classical.choice t99A01_kernel_Y⟩

/-- **LIBRARY boundary.** The degree-zero integral homology of `Z`. -/
theorem t99A01_hZero_Z :
    Nonempty (APMT99A01.H 0 APMT99A01.Z ≅ ModuleCat.of ℤ ℤ) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeZ (by decide) (by decide)).1

/-- **LIBRARY boundary.** The degree-one integral homology of `Z`. -/
theorem t99A01_hOne_Z :
    Limits.IsZero (APMT99A01.H 1 APMT99A01.Z) := by
  exact t99A01_cokernel_Z.of_iso (Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeZ (by decide) (by decide)).2.1)

/-- **LIBRARY boundary.** The degree-two integral homology of `Z`. -/
theorem t99A01_hTwo_Z :
    Nonempty (APMT99A01.H 2 APMT99A01.Z ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  exact ⟨Classical.choice
    (t99A01_attachSpace_homology APMT99A01.degreeZ (by decide) (by decide)).2.2.1 ≪≫
      Classical.choice t99A01_kernel_Z⟩

/-- **LIBRARY boundary.** Integral homology of `X` vanishes above its CW
dimension. -/
theorem t99A01_hHigher_X (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k APMT99A01.X) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeX
    (by decide) (by decide)).2.2.2 k hk

/-- **LIBRARY boundary.** Integral homology of `Y` vanishes above its CW
dimension. -/
theorem t99A01_hHigher_Y (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k APMT99A01.Y) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeY
    (by decide) (by decide)).2.2.2 k hk

/-- **LIBRARY boundary.** Integral homology of `Z` vanishes above its CW
dimension. -/
theorem t99A01_hHigher_Z (k : ℕ) (hk : 3 ≤ k) :
    Limits.IsZero (APMT99A01.H k APMT99A01.Z) := by
  exact (t99A01_attachSpace_homology APMT99A01.degreeZ
    (by decide) (by decide)).2.2.2 k hk

/-- Assembly of the independent van Kampen and homology computations. -/
theorem t99A01_attached_cells_computation :
    Nonempty (FundamentalGroup APMT99A01.X
      (APMT99A01.basepoint APMT99A01.degreeX) ≃*
        Multiplicative (ZMod 2)) ∧
    Nonempty (FundamentalGroup APMT99A01.Y
      (APMT99A01.basepoint APMT99A01.degreeY) ≃*
        Multiplicative (ZMod 2)) ∧
    Subsingleton (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ)) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.X ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Limits.IsZero (APMT99A01.H 2 APMT99A01.X) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.Y ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Z ≅ ModuleCat.of ℤ ℤ) ∧
    Limits.IsZero (APMT99A01.H 1 APMT99A01.Z) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Z ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (APMT99A01.H k APMT99A01.X) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Y) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Z)) := by
  exact ⟨t99A01_piOne_X, t99A01_piOne_Y, t99A01_piOne_Z,
    t99A01_hZero_X, t99A01_hOne_X, t99A01_hTwo_X,
    t99A01_hZero_Y, t99A01_hOne_Y, t99A01_hTwo_Y,
    t99A01_hZero_Z, t99A01_hOne_Z, t99A01_hTwo_Z,
    fun k hk ↦ ⟨t99A01_hHigher_X k hk, t99A01_hHigher_Y k hk,
      t99A01_hHigher_Z k hk⟩⟩

theorem apm_t99a01 :
    Nonempty (FundamentalGroup APMT99A01.X
      (APMT99A01.basepoint APMT99A01.degreeX) ≃*
        Multiplicative (ZMod 2)) ∧
    Nonempty (FundamentalGroup APMT99A01.Y
      (APMT99A01.basepoint APMT99A01.degreeY) ≃*
        Multiplicative (ZMod 2)) ∧
    Subsingleton (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ)) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.X ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Limits.IsZero (APMT99A01.H 2 APMT99A01.X) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 1 APMT99A01.Y ≅ ModuleCat.of ℤ (ZMod 2)) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Y ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (APMT99A01.H 0 APMT99A01.Z ≅ ModuleCat.of ℤ ℤ) ∧
    Limits.IsZero (APMT99A01.H 1 APMT99A01.Z) ∧
    Nonempty (APMT99A01.H 2 APMT99A01.Z ≅
      ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ k : ℕ, 3 ≤ k →
      Limits.IsZero (APMT99A01.H k APMT99A01.X) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Y) ∧
      Limits.IsZero (APMT99A01.H k APMT99A01.Z)) := by
  exact t99A01_attached_cells_computation

#print axioms apm_t99a01
