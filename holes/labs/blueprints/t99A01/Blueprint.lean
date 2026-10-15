import Mathlib
import ConstructionTargets.t97A04Closure
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.IntegralOpenCoverMayerVietoris

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

/-- **LIBRARY boundary.** Van Kampen for the quotient with one degree-two cell. -/
theorem t99A01_piOne_X :
    Nonempty (FundamentalGroup APMT99A01.X
      (APMT99A01.basepoint APMT99A01.degreeX) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/-- **LIBRARY boundary.** Van Kampen for the quotient with degree-two and
degree-four cells. -/
theorem t99A01_piOne_Y :
    Nonempty (FundamentalGroup APMT99A01.Y
      (APMT99A01.basepoint APMT99A01.degreeY) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/-- **LIBRARY boundary.** Van Kampen for the quotient with cells of degrees
two, four, and five. -/
theorem t99A01_piOne_Z :
    Subsingleton (FundamentalGroup APMT99A01.Z
      (APMT99A01.basepoint APMT99A01.degreeZ)) := by
  sorry

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
  sorry

lemma t99A01_attach_circleSide_aux_deformation_aux_respects {r : ℕ}
    (degree : Fin r → ℕ) (t : unitInterval)
    (x y : t99A01_attach_circleSide_aux_deformation_Pre degree)
    (hxy : t99A01_attach_circleSide_aux_deformation_q degree x =
      t99A01_attach_circleSide_aux_deformation_q degree y) :
    APMT99A01.attachMk degree
        (t99A01_attach_circleSide_aux_deformation_raw degree (t, x)) =
      APMT99A01.attachMk degree
        (t99A01_attach_circleSide_aux_deformation_raw degree (t, y)) := by
  sorry

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
  sorry

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

theorem t99A01_attach_overlap_aux_chart {r : ℕ} (degree : Fin r → ℕ) :
    ∃ c : ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) ≃ₜ
        (Σ _ : Fin r, ↥t99A01_pball),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (h0 : 0 < ‖(z : ℂ)‖) (h1 : ‖(z : ℂ)‖ < 1),
        (c.symm ⟨i, ⟨(z : ℂ), h0, h1⟩⟩).1 = APMT99A01.attachMk degree (Sum.inr (i, z)) := by
  sorry
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
  sorry

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
  sorry

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
