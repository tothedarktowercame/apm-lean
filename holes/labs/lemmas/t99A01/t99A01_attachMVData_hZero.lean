import Mathlib
import ConstructionTargets.t97A04Closure
import ConstructionTargets.IntegralSingularHomologyComparison

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
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩)

/-- Homology map of a subset into the whole space. -/
def zToX {X : Type} [TopologicalSpace X] (S : Set X) (n : ℕ) : H n S ⟶ H n X :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

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
theorem t99A01_attach_circleSide {r : ℕ} (degree : Fin r → ℕ) :
    ∃ (ρ : C(APMT99A01.sideA degree, Circle)) (ι : C(Circle, APMT99A01.sideA degree)),
      (∀ z, (ι z).1 = APMT99A01.circleIncl degree z) ∧
      ρ.comp ι = ContinuousMap.id Circle ∧
      ContinuousMap.Homotopic (ι.comp ρ) (ContinuousMap.id _) ∧
      ∀ (i : Fin r) (w : Circle) (h : APMT99A01.halfLoop degree i w ∈ APMT99A01.sideA degree),
        ρ ⟨APMT99A01.halfLoop degree i w, h⟩ = w ^ degree i := by
  sorry

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

theorem t99A01_attach_diskSide {r : ℕ} (degree : Fin r → ℕ) :
    ∃ e : APMT99A01.sideB degree ≃ₜ (Σ _ : Fin r, Metric.ball (0 : ℂ) 1),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (hz : ‖(z : ℂ)‖ < 1)
        (h : APMT99A01.attachMk degree (Sum.inr (i, z)) ∈ APMT99A01.sideB degree),
        e ⟨_, h⟩ = ⟨i, ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩⟩ := by
  sorry
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
theorem t99A01_attach_overlap_aux_chart {r : ℕ} (degree : Fin r → ℕ) :
    ∃ c : ↥(APMT99A01.sideA degree ∩ APMT99A01.sideB degree) ≃ₜ
        (Σ _ : Fin r, ↥t99A01_pball),
      ∀ (i : Fin r) (z : APMT99A01.Disk) (h0 : 0 < ‖(z : ℂ)‖) (h1 : ‖(z : ℂ)‖ < 1),
        (c.symm ⟨i, ⟨(z : ℂ), h0, h1⟩⟩).1 = APMT99A01.attachMk degree (Sum.inr (i, z)) := by
  sorry

/-- **Leaf (pure, no quotient).** Punctured disks retract radially onto the
radius-`1/2` circles: `z ↦ z/‖z‖` one way, `w ↦ w/2` back, homotopy
`(t, z) ↦ ((1-t)‖z‖ + t/2) · z/‖z‖`. -/
theorem t99A01_attach_overlap_aux_pball (r : ℕ) :
    ∃ e : ContinuousMap.HomotopyEquiv (Σ _ : Fin r, ↥t99A01_pball) (Σ _ : Fin r, Circle),
      ∀ (i : Fin r) (w : Circle),
        (e.invFun ⟨i, w⟩).1 = i ∧ ((e.invFun ⟨i, w⟩).2 : ℂ) = (w : ℂ) / 2 := by
  sorry

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
/-- **Leaf (finite additivity, 40--100 lines).** Integral singular homology of a
finite disjoint union is the biproduct, via the summand inclusions.  Check
`ConstructionTargets/CoefficientSigmaConstFinsuppComparison.lean` first (simplices
of a sigma type land in one summand: `IsPreconnected` of the simplex). -/
theorem t99A01_sigma_homology {r : ℕ} (Y : Fin r → Type) [∀ i, TopologicalSpace (Y i)]
    (k : ℕ) :
    IsIso (Limits.biproduct.desc fun i : Fin r ↦
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) :
        (⨁ fun i : Fin r ↦ APMT99A01.H k (Y i)) ⟶ APMT99A01.H k (Σ j, Y j)) := by
  sorry

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
  sorry

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
  sorry

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
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
          (ModuleCat.of ℤ ℤ)).map
            (TopCat.ofHom (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(Y i, Σ j, Y j))) :
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

-- BEGIN SEAT AREA
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
-- END SEAT AREA

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
