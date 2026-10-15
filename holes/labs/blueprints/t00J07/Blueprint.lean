import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.AttachTwoCell
import ConstructionTargets.DeckGroupQuotientFundamentalGroup
import ConstructionTargets.SimplyConnectedSphereProducts
import ConstructionTargets.BoundaryTorusHurewiczIsomorphism
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.DegreeOneHurewiczSurjective
import ConstructionTargets.CircleHomology
import ConstructionTargets.CoefficientH0

/-!
# APM t00J07

## Statement repairs

The former conclusion used opaque adjunction and homology types, together with
axioms merely to inhabit them.  The disk adjunction is now the actual quotient
of `RP² ⊕ D²` by its attaching relation, and all homology groups are Mathlib's
integral singular homology.  No source claim is changed.
-/

open CategoryTheory Set
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t00j07_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t00j07_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

abbrev apm_t00j07_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t00j07_circleToDisk (z : Circle) : apm_t00j07_Disk :=
  ⟨(z : ℂ), by simpa [mem_closedBall_zero_iff] using (Circle.norm_coe z).le⟩

lemma apm_t00j07_circleToDisk_injective :
    Function.Injective apm_t00j07_circleToDisk := by
  intro z w h
  apply Subtype.ext
  exact congrArg (fun x : apm_t00j07_Disk => (x : ℂ)) h

@[simp] lemma apm_t00j07_norm_circleToDisk (z : Circle) :
    ‖(apm_t00j07_circleToDisk z : ℂ)‖ = 1 :=
  Circle.norm_coe z

inductive apm_t00j07_attachRel (f : C(Circle, apm_t00j07_RP2)) :
    Sum apm_t00j07_RP2 apm_t00j07_Disk →
      Sum apm_t00j07_RP2 apm_t00j07_Disk → Prop
  | glue (z : Circle) :
      apm_t00j07_attachRel f (.inl (f z)) (.inr (apm_t00j07_circleToDisk z))

def apm_t00j07_attachDisk (f : C(Circle, apm_t00j07_RP2)) :=
  Quotient (Relation.EqvGen.setoid (apm_t00j07_attachRel f))

noncomputable instance (f : C(Circle, apm_t00j07_RP2)) :
    TopologicalSpace (apm_t00j07_attachDisk f) :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t00j07_RP2 apm_t00j07_Disk =>
      Quotient.mk (Relation.EqvGen.setoid (apm_t00j07_attachRel f)) x)
    inferInstance

def apm_t00j07_diskCenter : apm_t00j07_Disk :=
  ⟨0, by simp⟩

lemma apm_t00j07_diskCenter_ne_boundary (z : Circle) :
    apm_t00j07_diskCenter ≠ apm_t00j07_circleToDisk z := by
  intro h
  have := congrArg (fun x : apm_t00j07_Disk => ‖(x : ℂ)‖) h
  simp [apm_t00j07_diskCenter] at this

def apm_t00j07_basepoint (f : C(Circle, apm_t00j07_RP2)) :
    apm_t00j07_attachDisk f :=
  Quotient.mk _ (.inr apm_t00j07_diskCenter)

/-- The quotient construction identifies every attaching-circle point with
its prescribed image in `RP²`. -/
lemma apm_t00j07_attach_glue (f : C(Circle, apm_t00j07_RP2)) (z : Circle) :
    (Quotient.mk _ (.inl (f z)) : apm_t00j07_attachDisk f) =
      Quotient.mk _ (.inr (apm_t00j07_circleToDisk z)) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (apm_t00j07_attachRel.glue z))

/-- The generated attaching relation never moves the interior disk center. -/
lemma apm_t00j07_center_eqvGen_iff
    (f : C(Circle, apm_t00j07_RP2))
    (s : Sum apm_t00j07_RP2 apm_t00j07_Disk) :
    Relation.EqvGen (apm_t00j07_attachRel f)
        (.inr apm_t00j07_diskCenter) s ↔
      s = .inr apm_t00j07_diskCenter := by
  constructor
  · intro h
    have preserve : ∀ a b,
        apm_t00j07_attachRel f a b →
        (a = .inr apm_t00j07_diskCenter ↔
          b = .inr apm_t00j07_diskCenter) := by
      intro a b hab
      cases hab with
      | glue z =>
          constructor
          · intro h
            cases h
          · intro h
            exact False.elim
              (apm_t00j07_diskCenter_ne_boundary z (Sum.inr.inj h.symm))
    have invariant : ∀ a b,
        Relation.EqvGen (apm_t00j07_attachRel f) a b →
        (a = .inr apm_t00j07_diskCenter ↔
          b = .inr apm_t00j07_diskCenter) := by
      intro a b hab
      induction hab with
      | rel a b hab => exact preserve a b hab
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (invariant _ _ h).mp rfl
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- Consequently the quotient basepoint is not a point of the attached
`RP²` summand. -/
lemma apm_t00j07_basepoint_ne_left
    (f : C(Circle, apm_t00j07_RP2)) (p : apm_t00j07_RP2) :
    apm_t00j07_basepoint f ≠
      (Quotient.mk _ (.inl p) : apm_t00j07_attachDisk f) := by
  intro h
  have heq := Quotient.exact h
  have hs := (apm_t00j07_center_eqvGen_iff f (.inl p)).mp heq
  simp at hs

abbrev apm_t00j07_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t00j07_invariants
    (f : C(Circle, apm_t00j07_RP2))
    (piOne : Type) [Group piOne] (hOne : ModuleCat ℤ) : Prop :=
  Nonempty
      (FundamentalGroup (apm_t00j07_attachDisk f)
        (apm_t00j07_basepoint f) ≃* piOne) ∧
    Nonempty
      (apm_t00j07_H 0 (apm_t00j07_attachDisk f) ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t00j07_H 1 (apm_t00j07_attachDisk f) ≅ hOne) ∧
    Nonempty
      (apm_t00j07_H 2 (apm_t00j07_attachDisk f) ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k, 3 ≤ k → Limits.IsZero (apm_t00j07_H k (apm_t00j07_attachDisk f))

/-! # Blueprint (revision 2026-10-15)

`apm_t00j07_attachDisk f` is literally `AttachTwoCell.Cell f` (same sum, same
generating relation up to constructor names), so no Schoenflies step is
needed: `cell_piOne`, `cell_H1`, `cell_H2_of_zero`, `cell_H_high` apply to
the loop `f` directly.  `π₁(RP²) = Z/2` is copied from the closed t92J05;
`H_*(RP²)` comes from the one-crosscap polygon `Surface false 1`
(`PolygonSurfaceHomology`) via the upper-hemisphere chart.  The class of `f`
is `1` (null case: Hurewicz is injective on RP²) or the generator (essential
case: free/based loop comparison).
-/

abbrev apm_t00J07_S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-! ## Part A. `π₁(RP²) ≅ Z/2`

Copied verbatim (renamed `apm_t92J05_` ↦ `apm_t00J07_rp2_`) from the closed
`problems/t92J05/lean/Main.lean` (sorry-free). -/

abbrev apm_t00J07_rp2_antipodalGroup := Multiplicative (ZMod 2)

def apm_t00J07_rp2_antipodalSMul
    (g : apm_t00J07_rp2_antipodalGroup) (x : apm_t00J07_S2) : apm_t00J07_S2 :=
  if g.toAdd = 0 then x else -x

instance : MulAction apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 where
  smul := apm_t00J07_rp2_antipodalSMul
  one_smul x := by
    change apm_t00J07_rp2_antipodalSMul (.ofAdd 0) x = x
    simp [apm_t00J07_rp2_antipodalSMul]
  mul_smul g h x := by
    change apm_t00J07_rp2_antipodalSMul (g * h) x =
      apm_t00J07_rp2_antipodalSMul g (apm_t00J07_rp2_antipodalSMul h x)
    fin_cases g <;> fin_cases h
    · change apm_t00J07_rp2_antipodalSMul (.ofAdd 0) x =
        apm_t00J07_rp2_antipodalSMul (.ofAdd 0)
          (apm_t00J07_rp2_antipodalSMul (.ofAdd 0) x)
      simp [apm_t00J07_rp2_antipodalSMul]
    · change apm_t00J07_rp2_antipodalSMul (.ofAdd 1) x =
        apm_t00J07_rp2_antipodalSMul (.ofAdd 0)
          (apm_t00J07_rp2_antipodalSMul (.ofAdd 1) x)
      simp [apm_t00J07_rp2_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t00J07_rp2_antipodalSMul (.ofAdd 1) x =
        apm_t00J07_rp2_antipodalSMul (.ofAdd 1)
          (apm_t00J07_rp2_antipodalSMul (.ofAdd 0) x)
      simp [apm_t00J07_rp2_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]
    · change apm_t00J07_rp2_antipodalSMul (.ofAdd 0) x =
        apm_t00J07_rp2_antipodalSMul (.ofAdd 1)
          (apm_t00J07_rp2_antipodalSMul (.ofAdd 1) x)
      simp [apm_t00J07_rp2_antipodalSMul, show (1 : ZMod 2) ≠ 0 by decide]

instance : ContinuousConstSMul apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 where
  continuous_const_smul g := by
    fin_cases g
    · simpa [apm_t00J07_rp2_antipodalSMul] using
        (continuous_id : Continuous (id : apm_t00J07_S2 → apm_t00J07_S2))
    · exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

/-- **LIBRARY.** The antipodal `ZMod 2` action on the unit two-sphere is free. -/
lemma apm_t00J07_rp2_antipodalAction_free :
    ∀ g : apm_t00J07_rp2_antipodalGroup, ∀ x : apm_t00J07_S2,
      g • x = x → g = 1 := by
  intro g x hx
  fin_cases g
  · rfl
  · exfalso
    have hneg : -(x : EuclideanSpace ℝ (Fin 3)) = x := by
      exact congrArg Subtype.val hx
    have hx0 : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
        calc
          (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 3)) = x + x := by
            exact two_smul ℝ (x : EuclideanSpace ℝ (Fin 3))
          _ = -(x : EuclideanSpace ℝ (Fin 3)) + x :=
            congrArg (fun y => y + (x : EuclideanSpace ℝ (Fin 3))) hneg.symm
          _ = 0 := neg_add_cancel (x : EuclideanSpace ℝ (Fin 3))
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    rw [hx0, norm_zero] at hnorm
    norm_num at hnorm

/-- **LIBRARY.** The finite antipodal action is properly discontinuous. -/
lemma apm_t00J07_rp2_antipodalAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 := by
  infer_instance

/-- **LIBRARY.** Real projective two-space is the orbit quotient of the unit
two-sphere by the antipodal action. -/
def apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP
    (x : apm_t00J07_S2) : apm_t00j07_RP2 :=
  Projectivization.mk ℝ x.1.ofLp (by
    intro hx
    have := x.property
    have hx' : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      apply WithLp.ofLp_injective 2
      simpa using hx
    rw [Metric.mem_sphere, dist_zero_right, hx', norm_zero] at this
    norm_num at this)

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP_continuous :
    Continuous apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP := by
  apply continuous_quotient_mk'.comp
  exact Continuous.subtype_mk
    (EuclideanSpace.equiv (Fin 3) ℝ |>.continuous.comp continuous_subtype_val) _

def apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0
    (v : {v : Fin 3 → ℝ // v ≠ 0}) :
    MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 :=
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (v : Fin 3 → ℝ)
  Quotient.mk'' ⟨(‖w‖⁻¹ : ℝ) • w, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (by
      change WithLp.toLp 2 (v : Fin 3 → ℝ) ≠ 0
      exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective.ne v.property)⟩

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_continuous :
    Continuous apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 := by
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  · let e : (Fin 3 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
    exact ((continuous_norm.comp (e.continuous.comp continuous_subtype_val)).inv₀
      (fun (v : {v : Fin 3 → ℝ // v ≠ 0}) hv => v.property (by
        have := congrArg WithLp.ofLp (norm_eq_zero.mp hv)
        simpa using this))).smul
        (e.continuous.comp continuous_subtype_val)

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_scale
    (a b : {v : Fin 3 → ℝ // v ≠ 0}) (t : ℝ)
    (h : (a : Fin 3 → ℝ) = t • b) :
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 a =
      apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0 b := by
  have ht : t ≠ 0 := by
    intro ht
    apply a.property
    simpa [ht] using h
  apply Quotient.sound
  by_cases hpos : 0 < t
  · refine ⟨Multiplicative.ofAdd 0, ?_⟩
    apply Subtype.ext
    change (‖WithLp.toLp 2 (b : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (b : Fin 3 → ℝ) =
      (‖WithLp.toLp 2 (a : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (a : Fin 3 → ℝ)
    rw [h, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    rw [mul_inv_rev, smul_smul]
    congr 1
    field_simp
  · refine ⟨Multiplicative.ofAdd 1, ?_⟩
    apply Subtype.ext
    change -_ = _
    have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ht
    change -((‖WithLp.toLp 2 (b : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (b : Fin 3 → ℝ)) =
      (‖WithLp.toLp 2 (a : Fin 3 → ℝ)‖⁻¹ : ℝ) • WithLp.toLp 2 (a : Fin 3 → ℝ)
    rw [h, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_neg htneg]
    rw [mul_inv_rev]
    simp only [one_div, neg_smul, smul_smul]
    congr 1
    field_simp
    simp

def apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
    (p : apm_t00j07_RP2) :
    MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 :=
  Projectivization.lift
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_scale p

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ_continuous :
    Continuous apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ := by
  apply isQuotientMap_quot_mk.continuous_iff.mpr
  exact apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ0_continuous

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP_invariant
    (x y : apm_t00J07_S2)
    (h : MulAction.orbitRel apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 x y) :
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP x =
      apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP y := by
  rcases h with ⟨g, rfl⟩
  fin_cases g
  · rfl
  · apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨-1, ?_⟩
    change (-1 : ℝ) • y.1.ofLp =
      (apm_t00J07_rp2_antipodalSMul (Multiplicative.ofAdd 1) y).1.ofLp
    ext i
    simp [apm_t00J07_rp2_antipodalSMul]

def apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ :
    MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 →
      apm_t00j07_RP2 :=
  Quotient.lift
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP_invariant

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ_continuous :
    Continuous apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ := by
  apply isQuotientMap_quot_mk.continuous_iff.mpr
  exact apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toP_continuous

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_left
    (q : MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2) :
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
      (apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ q) = q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    apply Quotient.sound
    refine ⟨Multiplicative.ofAdd 0, ?_⟩
    apply Subtype.ext
    change (x : EuclideanSpace ℝ (Fin 3)) =
      (‖WithLp.toLp 2 x.1.ofLp‖⁻¹ : ℝ) • WithLp.toLp 2 x.1.ofLp
    have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      simpa [Metric.mem_sphere] using x.property
    simp [hx]

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_right
    (p : apm_t00j07_RP2) :
    apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ
      (apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
    refine ⟨‖WithLp.toLp 2 v‖⁻¹, ?_⟩
    ext i
    rfl

lemma apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient :
    Nonempty
      (MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 ≃ₜ
        apm_t00j07_RP2) := by
  exact ⟨{
    toFun := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ
    invFun := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ
    left_inv := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_left
    right_inv := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_right
    continuous_toFun := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toPQ_continuous
    continuous_invFun := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient_aux_toQ_continuous }⟩

/-- **LIBRARY.** Specialization of the deck-group quotient theorem to the
antipodal action, with the two action obligations supplied explicitly. -/
lemma apm_t00J07_rp2_antipodalQuotient_fundamentalGroup
    (hfree : ∀ g : apm_t00J07_rp2_antipodalGroup, ∀ x : apm_t00J07_S2,
      g • x = x → g = 1)
    (hproper : ProperlyDiscontinuousSMul
      apm_t00J07_rp2_antipodalGroup apm_t00J07_S2)
    (x : apm_t00J07_S2) :
    Nonempty
      (FundamentalGroup
          (MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2)
          (Quotient.mk _ x) ≃*
        apm_t00J07_rp2_antipodalGroup) := by
  letI : ProperlyDiscontinuousSMul
      apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 := hproper
  letI : SimplyConnectedSpace apm_t00J07_S2 :=
    ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
      2 (by norm_num)
  letI : LocPathConnectedSpace apm_t00J07_S2 :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) apm_t00J07_S2
  exact
    ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv
      hfree x

/-- **LIBRARY.** A quotient/projectivization homeomorphism transports the deck
calculation to at least one concrete projective-plane basepoint. -/
lemma apm_t00J07_rp2_projectivePlane_fundamentalGroup_at_one_point
    (e : MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2 ≃ₜ
      apm_t00j07_RP2)
    (hdeck : ∀ x : apm_t00J07_S2,
      Nonempty
        (FundamentalGroup
            (MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2)
            (Quotient.mk _ x) ≃*
          apm_t00J07_rp2_antipodalGroup)) :
    ∃ x : apm_t00j07_RP2,
      Nonempty (FundamentalGroup apm_t00j07_RP2 x ≃* Multiplicative (ZMod 2)) := by
  let x : apm_t00J07_S2 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  refine ⟨e (Quotient.mk _ x), ?_⟩
  obtain ⟨d⟩ := hdeck x
  exact
    ⟨(ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
        e (Quotient.mk _ x)).symm.trans d⟩

/-- **LIBRARY.** The concrete real projective plane is path connected. -/
lemma apm_t00J07_rp2_projectivePlane_pathConnected :
    PathConnectedSpace apm_t00j07_RP2 := by
  let V := Fin 3 → ℝ
  have hrank : 1 < Module.rank ℝ V := by
    rw [← Module.finrank_eq_rank]
    norm_num [V]
  have hnonzero : IsPathConnected ({0}ᶜ : Set V) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  letI : PathConnectedSpace {v : V // v ≠ 0} := by
    change PathConnectedSpace {v : V // v ∈ ({0}ᶜ : Set V)}
    exact isPathConnected_iff_pathConnectedSpace.mp hnonzero
  exact (Quotient.mk'_surjective (s := projectivizationSetoid ℝ V)).pathConnectedSpace
    continuous_quotient_mk'

/-- **LIBRARY.** On a path-connected space, one computed fundamental group
determines it at every basepoint. -/
lemma apm_t00J07_rp2_fundamentalGroup_all_basepoints
    {X G : Type} [TopologicalSpace X] [Group G]
    (hpath : PathConnectedSpace X)
    (hone : ∃ x₀ : X, Nonempty (FundamentalGroup X x₀ ≃* G)) :
    ∀ x : X, Nonempty (FundamentalGroup X x ≃* G) := by
  letI : PathConnectedSpace X := hpath
  obtain ⟨x₀, e⟩ := hone
  intro x
  exact
    ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀).trans e.some⟩

/-- The antipodal two-sphere cover computes the fundamental group of the
concrete real projective plane at every basepoint. -/
theorem apm_t00J07_rp2_bridge_projectivePlane_fundamentalGroup :
    ∀ x : apm_t00j07_RP2,
      Nonempty
        (FundamentalGroup apm_t00j07_RP2 x ≃*
          Multiplicative (ZMod 2)) := by
  letI := apm_t00J07_rp2_antipodalAction_properlyDiscontinuous
  have hdeck := apm_t00J07_rp2_antipodalQuotient_fundamentalGroup
    apm_t00J07_rp2_antipodalAction_free
    apm_t00J07_rp2_antipodalAction_properlyDiscontinuous
  obtain ⟨e⟩ := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient
  exact apm_t00J07_rp2_fundamentalGroup_all_basepoints
    apm_t00J07_rp2_projectivePlane_pathConnected
    (apm_t00J07_rp2_projectivePlane_fundamentalGroup_at_one_point e hdeck)

namespace APMT00J07

open scoped ContinuousMap
open ConstructionTargets
open ConstructionTargets.Surfaces
open ConstructionTargets.AttachTwoCell
open ConstructionTargets.PolygonSurfacePiOne

/-! ## Part B. The problem's space is `Cell f` -/

lemma cellHomeo_aux_fwd (f : C(Circle, apm_t00j07_RP2))
    (a b : apm_t00j07_RP2 ⊕ apm_t00j07_Disk)
    (h : Relation.EqvGen (apm_t00j07_attachRel f) a b) :
    Relation.EqvGen (CellRel f) a b :=
  Relation.EqvGen.mono (fun _ _ h => by cases h with | glue z => exact CellRel.boundary z) h

lemma cellHomeo_aux_bwd (f : C(Circle, apm_t00j07_RP2))
    (a b : apm_t00j07_RP2 ⊕ apm_t00j07_Disk)
    (h : Relation.EqvGen (CellRel f) a b) :
    Relation.EqvGen (apm_t00j07_attachRel f) a b :=
  Relation.EqvGen.mono
    (fun _ _ h => by cases h with | boundary z => exact apm_t00j07_attachRel.glue z) h

/-- The identity on `RP² ⊕ D²` descends to a homeomorphism of the problem's
quotient with `RP² ∪_f D²`. -/
def cellHomeo (f : C(Circle, apm_t00j07_RP2)) : apm_t00j07_attachDisk f ≃ₜ Cell f where
  toFun := Quotient.lift (fun x => cellMk f x)
    (fun a b h => Quotient.sound (cellHomeo_aux_fwd f a b h))
  invFun := Quotient.lift (s := Relation.EqvGen.setoid (CellRel f))
    (fun x => (Quotient.mk _ x : apm_t00j07_attachDisk f))
    (fun a b h => Quotient.sound (cellHomeo_aux_bwd f a b h))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn
    rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn (s := Relation.EqvGen.setoid (CellRel f))
    rfl
  continuous_toFun := continuous_coinduced_dom.mpr (continuous_cellMk f)
  continuous_invFun := continuous_coinduced_dom.mpr continuous_coinduced_rng

/-! ## Part C. `RP² ≅ Surface false 1` (upper-hemisphere chart) -/

/-- `z ↦ (Re z, Im z, √(1 - |z|²))`, a unit vector in the closed upper
hemisphere. -/
def hemiVec (z : Surfaces.Disk) : Fin 3 → ℝ :=
  ![(z : ℂ).re, (z : ℂ).im, Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)]

lemma hemiVec_ne_zero (z : Surfaces.Disk) : hemiVec z ≠ 0 := by
  intro h
  have h0 : (z : ℂ).re = 0 := congrFun h 0
  have h1 : (z : ℂ).im = 0 := congrFun h 1
  have h2 : Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) = 0 := congrFun h 2
  have hz : (z : ℂ) = 0 := Complex.ext h0 h1
  rw [hz, norm_zero] at h2
  norm_num at h2

/-- The hemisphere chart `D² → RP²`. -/
def hemi (z : Surfaces.Disk) : apm_t00j07_RP2 :=
  Projectivization.mk ℝ (hemiVec z) (hemiVec_ne_zero z)

lemma continuous_hemi : Continuous hemi := by
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [hemiVec] <;> fun_prop

/-- Every line through the origin meets the closed upper unit hemisphere. -/
lemma hemi_surjective : Function.Surjective hemi := by
  intro p
  let v : Fin 3 → ℝ := Projectivization.rep p
  have hv : v ≠ 0 := Projectivization.rep_nonzero p
  let w : Fin 3 → ℝ := if 0 ≤ v 2 then v else -v
  have hw : w ≠ 0 := by
    dsimp [w]
    split <;> simp_all
  have hw2 : 0 ≤ w 2 := by
    dsimp [w]
    split
    · assumption
    · simp only [Pi.neg_apply]
      exact neg_nonneg.mpr (le_of_not_ge ‹¬ 0 ≤ v 2›)
  let S : ℝ := (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2
  have hS : 0 < S := by
    by_contra h
    have hle : S ≤ 0 := le_of_not_gt h
    have h0 : w 0 = 0 := by
      dsimp [S] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    have h1 : w 1 = 0 := by
      dsimp [S] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    have h2 : w 2 = 0 := by
      dsimp [S] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    apply hw
    funext i
    fin_cases i <;> assumption
  let n : ℝ := Real.sqrt S
  have hn : 0 < n := Real.sqrt_pos.2 hS
  have hn_sq : n ^ 2 = S := by
    dsimp [n]
    rw [Real.sq_sqrt hS.le]
  let zc : ℂ := ⟨w 0 / n, w 1 / n⟩
  have hzc_sq : ‖zc‖ ^ 2 = ((w 0) ^ 2 + (w 1) ^ 2) / n ^ 2 := by
    rw [Complex.sq_norm]
    dsimp [zc]
    ring
  have hzc_le : ‖zc‖ ≤ 1 := by
    have hn0 : 0 ≤ ‖zc‖ := norm_nonneg _
    have hden : 0 < n ^ 2 := sq_pos_of_pos hn
    have hs : ‖zc‖ ^ 2 ≤ 1 := by
      rw [hzc_sq, div_le_one hden]
      dsimp [S] at hn_sq
      nlinarith [sq_nonneg (w 2)]
    nlinarith [sq_nonneg (‖zc‖ - 1)]
  let z : Surfaces.Disk := ⟨zc, by simpa [Metric.mem_closedBall, dist_zero_right]⟩
  have hsqrt : Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) = w 2 / n := by
    have hden : 0 < n ^ 2 := sq_pos_of_pos hn
    have hsq : 1 - ‖(z : ℂ)‖ ^ 2 = (w 2 / n) ^ 2 := by
      change 1 - ‖zc‖ ^ 2 = _
      rw [hzc_sq]
      field_simp
      dsimp [S] at hn_sq
      nlinarith
    rw [hsq, Real.sqrt_sq (div_nonneg hw2 hn.le)]
  have hvec : hemiVec z = fun i => w i / n := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hsqrt
  refine ⟨z, ?_⟩
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ (hemiVec_ne_zero z) hv).mpr
  by_cases h : 0 ≤ v 2
  · refine ⟨n⁻¹, ?_⟩
    rw [hvec]
    funext i
    simp [w, h, div_eq_inv_mul]
  · refine ⟨-n⁻¹, ?_⟩
    rw [hvec]
    funext i
    simp [w, h, div_eq_inv_mul]

/-- The chart identifies the two edges of the one-crosscap polygon. -/
lemma hemi_respects {x y : Surfaces.Disk} (h : SurfaceRel false 1 x y) : hemi x = hemi y := by
  simp only [SurfaceRel, Bool.false_eq_true, if_false] at h
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  have hj0 : j = 0 := by omega
  subst j
  have hedge :
      ((Surfaces.edgePoint 2 1 t : Surfaces.Disk) : ℂ) =
        -((Surfaces.edgePoint 2 0 t : Surfaces.Disk) : ℂ) := by
    simp only [Surfaces.edgePoint, Subtype.coe_mk]
    norm_num
    change Complex.exp (Complex.I * (2 * (Real.pi : ℂ) *
      (1 + (t.1 : ℂ)) / 2)) =
      -Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (t.1 : ℂ) / 2))
    calc
      _ = Complex.exp (Real.pi * Complex.I) *
          Complex.exp (Complex.I * (Real.pi * t.1)) := by
            rw [← Complex.exp_add]
            congr 1
            ring
      _ = _ := by rw [Complex.exp_pi_mul_I]; ring
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _
    (hemiVec_ne_zero (Surfaces.edgePoint (2 * 1) (2 * 0) t))
    (hemiVec_ne_zero (Surfaces.edgePoint (2 * 1) (2 * 0 + 1) t))).2
  refine ⟨-1, ?_⟩
  funext i
  fin_cases i <;> simp [hemiVec, hedge, norm_edgePoint]

/-- Fibres of the chart: equal images are equal points or antipodal points of
the boundary circle. -/
lemma hemi_eq_cases {x y : Surfaces.Disk} (h : hemi x = hemi y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ (y : ℂ) = -(x : ℂ)) := by
  have hsqrt_sq (z : Surfaces.Disk) :
      (Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)) ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2 := by
    rw [Real.sq_sqrt]
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      have hz' : dist (z : ℂ) 0 ≤ 1 := z.property
      simpa [dist_zero_right] using hz'
    nlinarith [norm_nonneg (z : ℂ)]
  have hunit (z : Surfaces.Disk) :
      (hemiVec z 0) ^ 2 + (hemiVec z 1) ^ 2 + (hemiVec z 2) ^ 2 = 1 := by
    change (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 +
      (Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)) ^ 2 = 1
    rw [hsqrt_sq z, Complex.sq_norm, Complex.normSq_apply]
    ring
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ _ _ (hemiVec_ne_zero x)
      (hemiVec_ne_zero y)).mp h
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have ha2 := congrFun ha 2
  change a * (y : ℂ).re = (x : ℂ).re at ha0
  change a * (y : ℂ).im = (x : ℂ).im at ha1
  change a * Real.sqrt (1 - ‖(y : ℂ)‖ ^ 2) =
    Real.sqrt (1 - ‖(x : ℂ)‖ ^ 2) at ha2
  have ha_sq : a ^ 2 = 1 := by
    have hxunit := hunit x
    have hyunit := hunit y
    change (x : ℂ).re ^ 2 + (x : ℂ).im ^ 2 +
      (Real.sqrt (1 - ‖(x : ℂ)‖ ^ 2)) ^ 2 = 1 at hxunit
    change (y : ℂ).re ^ 2 + (y : ℂ).im ^ 2 +
      (Real.sqrt (1 - ‖(y : ℂ)‖ ^ 2)) ^ 2 = 1 at hyunit
    rw [← ha0, ← ha1, ← ha2] at hxunit
    nlinarith
  rcases (sq_eq_one_iff.mp ha_sq) with ha_one | ha_neg
  · left
    rw [ha_one, one_mul] at ha0 ha1
    apply Subtype.ext
    apply Complex.ext
    · exact ha0.symm
    · exact ha1.symm
  · right
    have hsx : Real.sqrt (1 - ‖(x : ℂ)‖ ^ 2) = 0 := by
      have hxnonneg := Real.sqrt_nonneg (1 - ‖(x : ℂ)‖ ^ 2)
      have hynonneg := Real.sqrt_nonneg (1 - ‖(y : ℂ)‖ ^ 2)
      rw [ha_neg] at ha2
      nlinarith
    have hxnorm_sq : ‖(x : ℂ)‖ ^ 2 = 1 := by
      have := hsqrt_sq x
      rw [hsx] at this
      nlinarith
    constructor
    · nlinarith [norm_nonneg (x : ℂ)]
    · apply Complex.ext
      · simp only [map_neg, Complex.neg_re]
        rw [ha_neg] at ha0
        nlinarith
      · simp only [map_neg, Complex.neg_im]
        rw [ha_neg] at ha1
        nlinarith

/-- Antipodal boundary points are identified in `Surface false 1`. -/
lemma surfaceRel_one_antipodal_aux_edge (t : Set.Icc (0 : ℝ) 1) :
    ((Surfaces.edgePoint 2 1 t : Surfaces.Disk) : ℂ) =
      -((Surfaces.edgePoint 2 0 t : Surfaces.Disk) : ℂ) := by
  simp only [Surfaces.edgePoint, Subtype.coe_mk]
  norm_num
  change Complex.exp (Complex.I * (2 * (Real.pi : ℂ) *
    (1 + (t.1 : ℂ)) / 2)) =
    -Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (t.1 : ℂ) / 2))
  calc
    _ = Complex.exp (Real.pi * Complex.I) *
        Complex.exp (Complex.I * (Real.pi * t.1)) := by
          rw [← Complex.exp_add]
          congr 1
          ring
    _ = _ := by rw [Complex.exp_pi_mul_I]; ring

lemma surfaceRel_one_antipodal {x y : Surfaces.Disk} (hx : ‖(x : ℂ)‖ = 1)
    (hy : (y : ℂ) = -(x : ℂ)) : Relation.EqvGen (SurfaceRel false 1) x y := by
  obtain ⟨i, t, hi⟩ := edgePoint_surjective_boundary 2 (by omega) x hx
  fin_cases i
  · have hy' : y = Surfaces.edgePoint 2 1 t := by
      apply Subtype.ext
      rw [hy, ← hi]
      exact (surfaceRel_one_antipodal_aux_edge t).symm
    apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, Bool.false_eq_true, if_false]
    exact ⟨0, by omega, t, hi.symm, hy'⟩
  · have hy' : y = Surfaces.edgePoint 2 0 t := by
      apply Subtype.ext
      rw [hy, ← hi]
      have h := surfaceRel_one_antipodal_aux_edge t
      rw [h, neg_neg]
    apply Relation.EqvGen.symm _ _
    apply Relation.EqvGen.rel _ _
    simp only [SurfaceRel, Bool.false_eq_true, if_false]
    exact ⟨0, by omega, t, hy', hi.symm⟩

def surfaceToRP2 : Surface false 1 → apm_t00j07_RP2 :=
  Quotient.lift hemi (fun a b h => by
    induction h with
    | rel x y h => exact hemi_respects h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma surfaceToRP2_continuous : Continuous surfaceToRP2 :=
  continuous_coinduced_dom.mpr continuous_hemi

lemma surfaceToRP2_bijective : Function.Bijective surfaceToRP2 := by
  constructor
  · intro p q hpq
    induction p using Quotient.inductionOn
    induction q using Quotient.inductionOn
    rcases hemi_eq_cases hpq with h | ⟨hx, hy⟩
    · rw [h]
    · exact Quotient.sound (surfaceRel_one_antipodal hx hy)
  · intro p
    obtain ⟨z, hz⟩ := hemi_surjective p
    exact ⟨Quotient.mk _ z, hz⟩

instance rp2_t2 : T2Space apm_t00j07_RP2 := by
  obtain ⟨e⟩ := apm_t00J07_rp2_projectivePlane_homeomorph_antipodalQuotient
  letI := apm_t00J07_rp2_antipodalAction_properlyDiscontinuous
  haveI : T2Space
      (MulAction.orbitRel.Quotient apm_t00J07_rp2_antipodalGroup apm_t00J07_S2) :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
  exact e.symm.isEmbedding.t2Space

instance surface_one_compact : CompactSpace (Surface false 1) := by
  haveI : CompactSpace Surfaces.Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  refine ⟨?_⟩
  rw [← (surjective_surfaceQuotient false 1).range_eq]
  exact isCompact_range (continuous_surfaceQuotient false 1)

def rp2Homeo : Surface false 1 ≃ₜ apm_t00j07_RP2 :=
  surfaceToRP2_continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ surfaceToRP2_bijective)

/-! ## Part D. Homology of `RP²` -/

/-- B11 of t97J04. -/
lemma H_of_homeomorph {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (h : S ≃ₜ T) (k : ℕ) : Nonempty (H k S ≅ H k T) := by
  exact ⟨((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo h)⟩

/-- B10 of t97J04. -/
lemma H0_of_pathConnected (S : Type) [TopologicalSpace S] [PathConnectedSpace S] :
    Nonempty (H 0 S ≅ ModuleCat.of ℤ ℤ) := by
  exact ⟨ConstructionTargets.CoefficientH0.h0Iso ℤ
    (Classical.choice (inferInstance : Nonempty S))⟩

/-- The one-crosscap polygon `aa` has `H₁ = Z/2`, `H₂ = 0`. -/
abbrev rp2Polygon_homology_aux_P := standardPairingData false 1 Nat.one_pos

def rp2Polygon_homology_aux_coord :
    (PairingOrbit rp2Polygon_homology_aux_P.pair → ℤ) ≃ₗ[ℤ] ℤ :=
  { toFun := fun f => f ((nonorientableOrbitEquiv 1).symm 0)
    invFun := fun n q => n
    left_inv := by
      intro f
      funext q
      have hq : q = (nonorientableOrbitEquiv 1).symm 0 := by
        apply (nonorientableOrbitEquiv 1).injective
        exact Subsingleton.elim _ _
      simp [hq]
    right_inv := by intro n; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

lemma rp2Polygon_homology_aux_degree :
    PolygonSurfaceHomology.attachingDegree rp2Polygon_homology_aux_P
      ((nonorientableOrbitEquiv 1).symm 0) = -2 := by
  rw [PolygonSurfaceHomology.attachingDegree_apply]
  simp_rw [PolygonSurfaceHomology.edgeOrbitContribution]
  have horbit (i : Fin 2) :
      rp2Polygon_homology_aux_P.orbit i = (nonorientableOrbitEquiv 1).symm 0 := by
    apply (nonorientableOrbitEquiv 1).injective
    exact Subsingleton.elim _ _
  simp_rw [horbit]
  simp [standardPairingData,
    nonorientableStandardPairingData, standardPairingDataOfOneVertex,
    standardPair, standardSign, nonorientableOrbitLabel, nonorientableCoord,
    PolygonSurfaceHomology.edgeAttachingDegree, standardEdgeCount]
  change (2 : ℤ) = 2
  rfl

lemma rp2Polygon_homology_aux_coord_boundary (m : ℤ) :
    rp2Polygon_homology_aux_coord
        (PolygonSurfaceHomology.attachingBoundary rp2Polygon_homology_aux_P m) =
      m * (-2) := by
  change m * PolygonSurfaceHomology.attachingDegree rp2Polygon_homology_aux_P
      ((nonorientableOrbitEquiv 1).symm 0) = m * (-2)
  rw [rp2Polygon_homology_aux_degree]

def rp2Polygon_homology_aux_parity : ℤ →ₗ[ℤ] ZMod 2 where
  toFun n := n
  map_add' := by intros; simp
  map_smul' := by intros; simp

lemma rp2Polygon_homology_aux_range_eq_ker :
    Submodule.map rp2Polygon_homology_aux_coord.toLinearMap
        (LinearMap.range
          (PolygonSurfaceHomology.attachingBoundary rp2Polygon_homology_aux_P)) =
      LinearMap.ker rp2Polygon_homology_aux_parity := by
  ext n
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    rw [LinearMap.mem_ker]
    change ((rp2Polygon_homology_aux_coord
      (PolygonSurfaceHomology.attachingBoundary rp2Polygon_homology_aux_P m) : ℤ) :
        ZMod 2) = 0
    rw [rp2Polygon_homology_aux_coord_boundary]
    change ((m * (-2) : ℤ) : ZMod 2) = 0
    rw [Int.cast_mul]
    change (m : ZMod 2) * (-2 : ZMod 2) = 0
    have htwo : (-2 : ZMod 2) = 0 := by decide
    rw [htwo, mul_zero]
  · intro hn
    rw [LinearMap.mem_ker] at hn
    change ((n : ℤ) : ZMod 2) = 0 at hn
    have hd : (2 : ℤ) ∣ n := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hn
    rcases hd with ⟨m, rfl⟩
    refine ⟨fun _ => 2 * m, ?_, ?_⟩
    · refine ⟨-m, ?_⟩
      funext q
      have hq : q = (nonorientableOrbitEquiv 1).symm 0 := by
        apply (nonorientableOrbitEquiv 1).injective
        exact Subsingleton.elim _ _
      subst q
      simp only [PolygonSurfaceHomology.attachingBoundary_apply_apply]
      rw [rp2Polygon_homology_aux_degree]
      simp [mul_comm]
    · simp [rp2Polygon_homology_aux_coord]

lemma rp2Polygon_homology_aux_boundary_injective :
    Function.Injective
      (PolygonSurfaceHomology.attachingBoundary rp2Polygon_homology_aux_P) := by
  intro m n h
  have h' := congrArg rp2Polygon_homology_aux_coord h
  rw [rp2Polygon_homology_aux_coord_boundary,
    rp2Polygon_homology_aux_coord_boundary] at h'
  omega

noncomputable def rp2Polygon_homology_aux_quotientEquiv
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) (p : Submodule ℤ M) (q : Submodule ℤ N)
    (h : Submodule.map e.toLinearMap p = q) : (M ⧸ p) ≃ₗ[ℤ] (N ⧸ q) := by
  let f := p.mapQ q e.toLinearMap (by
    intro x hx; rw [← h]; exact ⟨x, hx, rfl⟩)
  let g := q.mapQ p e.symm.toLinearMap (by
    intro y hy
    rw [← h] at hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa using hx)
  exact LinearEquiv.ofLinear f g
    (by apply LinearMap.ext; intro x; refine Quotient.inductionOn x ?_; intro x
        change Quotient.mk _ (e (e.symm x)) = Quotient.mk _ x
        rw [e.apply_symm_apply])
    (by apply LinearMap.ext; intro x; refine Quotient.inductionOn x ?_; intro x
        change Quotient.mk _ (e.symm (e x)) = Quotient.mk _ x
        rw [e.symm_apply_apply])

lemma rp2Polygon_homology :
    Nonempty (PolygonSurfaceHomology.H (standardPairingData false 1 Nat.one_pos) 1 ≅
        ModuleCat.of ℤ (ZMod 2)) ∧
      Limits.IsZero (PolygonSurfaceHomology.H (standardPairingData false 1 Nat.one_pos) 2) := by
  obtain ⟨_, ⟨h1⟩, ⟨h2⟩, _⟩ :=
    PolygonSurfaceHomology.polygonQuotient_homology rp2Polygon_homology_aux_P
  change PolygonSurfaceHomology.H (standardPairingData false 1 Nat.one_pos) 1 ≅
    ModuleCat.of ℤ (PolygonSurfaceHomology.BoundaryCokernel
      (standardPairingData false 1 Nat.one_pos)) at h1
  change PolygonSurfaceHomology.H (standardPairingData false 1 Nat.one_pos) 2 ≅
    ModuleCat.of ℤ (PolygonSurfaceHomology.BoundaryKernel
      (standardPairingData false 1 Nat.one_pos)) at h2
  have hcok : PolygonSurfaceHomology.BoundaryCokernel rp2Polygon_homology_aux_P
      ≃ₗ[ℤ] ZMod 2 :=
    (rp2Polygon_homology_aux_quotientEquiv
      rp2Polygon_homology_aux_coord _ _
      rp2Polygon_homology_aux_range_eq_ker).trans
      (rp2Polygon_homology_aux_parity.quotKerEquivOfSurjective (by
        intro z
        refine ⟨z.val, ?_⟩
        simp [rp2Polygon_homology_aux_parity]))
  change PolygonSurfaceHomology.BoundaryCokernel
      (standardPairingData false 1 Nat.one_pos) ≃ₗ[ℤ] ZMod 2 at hcok
  constructor
  · exact ⟨Iso.trans h1 hcok.toModuleIso⟩
  · apply Limits.IsZero.of_iso _ h2
    rw [show PolygonSurfaceHomology.BoundaryKernel rp2Polygon_homology_aux_P = ⊥ from
      LinearMap.ker_eq_bot.mpr rp2Polygon_homology_aux_boundary_injective]
    exact ModuleCat.isZero_of_subsingleton _

def rp2PolyHomeo : apm_t00j07_RP2 ≃ₜ (standardPairingData false 1 Nat.one_pos).Space :=
  rp2Homeo.symm.trans (standardPairingData_space_homeomorph false 1 Nat.one_pos).symm

theorem rp2_homology :
    Nonempty (H 1 apm_t00j07_RP2 ≅ ModuleCat.of ℤ (ZMod 2)) ∧
      Limits.IsZero (H 2 apm_t00j07_RP2) ∧
      ∀ k, 3 ≤ k → Limits.IsZero (H k apm_t00j07_RP2) := by
  obtain ⟨⟨e1⟩, h2⟩ := rp2Polygon_homology
  have hk := (PolygonSurfaceHomology.polygonQuotient_homology
    (standardPairingData false 1 Nat.one_pos)).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i⟩ := H_of_homeomorph rp2PolyHomeo 1
    exact ⟨i ≪≫ e1⟩
  · obtain ⟨i⟩ := H_of_homeomorph rp2PolyHomeo 2
    exact h2.of_iso i
  · intro k hk3
    obtain ⟨i⟩ := H_of_homeomorph rp2PolyHomeo k
    exact (hk k hk3).of_iso i

instance rp2_pc : PathConnectedSpace apm_t00j07_RP2 :=
  apm_t00J07_rp2_projectivePlane_pathConnected

/-! ## Part E. Loops, Hurewicz, and `f_*` on `H₁` -/

/-- The Hurewicz image of `[γ]` is `γ_*` of the circle class. -/
lemma hurewicz_loopClass_mem_range {Y : Type} [TopologicalSpace Y] (γ : C(Circle, Y)) :
    ∃ c, (Hmap γ 1).hom c =
      PolygonSurfaceHomology.moduleHurewicz (γ 1) (loopClassAt γ (γ 1) rfl) := by
  refine ⟨PolygonSurfaceHomology.moduleHurewicz (1 : Circle)
    PolygonSurfaceHomology.circleIntegerLoopOneClass, ?_⟩
  rw [show loopClassAt γ (γ 1) rfl = FundamentalGroup.map γ 1
    PolygonSurfaceHomology.circleIntegerLoopOneClass from rfl,
    PolygonSurfaceHomology.moduleHurewicz_naturality]
  rfl

/-- Hurewicz is injective when `π₁ ≅ Z/2 ≅ H₁` (it is always onto). -/
lemma hurewicz_injective_of_zmod2_aux_surjective
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Function.Surjective (PolygonSurfaceHomology.moduleHurewicz x) := by
  intro y
  let e :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of X) 1
  obtain ⟨g, hg⟩ :=
    ConstructionTargets.DegreeOneHurewiczSurjective.fundamentalGroupH1Hom_surjective
      x (Multiplicative.ofAdd (e.hom y))
  refine ⟨g, ?_⟩
  change e.inv
      (Multiplicative.toAdd
        (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom x g)) = y
  rw [hg]
  exact e.hom_inv_id_apply y

lemma hurewicz_injective_of_zmod2 {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) (hπ : Nonempty (FundamentalGroup X x ≃* Multiplicative (ZMod 2)))
    (hH : Nonempty (H 1 X ≅ ModuleCat.of ℤ (ZMod 2))) :
    Function.Injective (PolygonSurfaceHomology.moduleHurewicz x) := by
  let eπ := hπ.some
  let eH := hH.some.toLinearEquiv
  letI : Fintype (FundamentalGroup X x) :=
    Fintype.ofEquiv (Multiplicative (ZMod 2)) eπ.symm.toEquiv
  letI : Fintype (H 1 X) :=
    Fintype.ofEquiv (ZMod 2) eH.symm.toEquiv
  apply ((Fintype.bijective_iff_surjective_and_card
    (PolygonSurfaceHomology.moduleHurewicz x)).2 ⟨
      hurewicz_injective_of_zmod2_aux_surjective x, ?_⟩).injective
  calc
    Fintype.card (FundamentalGroup X x) = Fintype.card (Multiplicative (ZMod 2)) :=
      Fintype.card_congr eπ.toEquiv
    _ = Fintype.card (ZMod 2) := by simp
    _ = Fintype.card (H 1 X) := (Fintype.card_congr eH.toEquiv).symm

/-- A loop whose based class is trivial is freely null-homotopic. -/
lemma nullhomotopic_of_loopClassAt_eq_one {Y : Type} [TopologicalSpace Y]
    (γ : C(Circle, Y)) (h : loopClassAt γ (γ 1) rfl = 1) :
    ∃ p : Y, ContinuousMap.Homotopic γ (ContinuousMap.const Circle p) := by
  let a := ConstructionTargets.CircleUniversalCover.integerLoop 1
  have hq : Path.Homotopic.Quotient.mk (a.map γ.continuous) =
      Path.Homotopic.Quotient.mk (Path.refl (γ 1)) := by
    simpa [loopClassAt, PolygonSurfaceHomology.circleIntegerLoopOneClass,
      FundamentalGroup.map_apply] using h
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hq
  let c : C(Set.Icc (0 : ℝ) 1, Circle) :=
    ⟨PolygonSurfacePiOne.circleArc, by
      exact AddCircle.continuous_toCircle.comp
        ((AddCircle.continuous_mk' 1).comp continuous_subtype_val)⟩
  have hc_surj : Function.Surjective c :=
    PolygonSurfacePiOne.surjective_circleArc
  have hc_quot : Topology.IsQuotientMap c :=
    IsQuotientMap.of_surjective_continuous hc_surj c.continuous
  let G : C(unitInterval × Set.Icc (0 : ℝ) 1, Y) :=
    ⟨fun ts ↦ H (ts.1, ts.2), H.continuous⟩
  have hfac : Function.FactorsThrough G
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval) c) := by
    rintro ⟨t, x⟩ ⟨u, y⟩ hxy
    change (t, c x) = (u, c y) at hxy
    have ht : t = u := congrArg (fun q : unitInterval × Circle ↦ q.1) hxy
    have hs : c x = c y := congrArg (fun q : unitInterval × Circle ↦ q.2) hxy
    subst u
    rcases (PolygonSurfacePiOne.circleArc_eq_iff x y).mp hs with
      hxy | hends | hends
    · subst hxy
      rfl
    · rcases hends with ⟨rfl, rfl⟩
      exact (H.source t).trans (H.target t).symm
    · rcases hends with ⟨rfl, rfl⟩
      exact (H.target t).trans (H.source t).symm
  let Kfun : unitInterval × Circle → Y := fun tz ↦
    G (tz.1, Function.surjInv hc_surj tz.2)
  have hKcomp : ∀ ts : unitInterval × Set.Icc (0 : ℝ) 1,
      Kfun (ts.1, c ts.2) = G ts := by
    intro ts
    exact hfac (by
      apply Prod.ext
      · rfl
      · exact Function.rightInverse_surjInv hc_surj (c ts.2))
  have hKcont : Continuous Kfun := by
    apply hc_quot.continuous_lift_prod_right
    simpa only [hKcomp] using G.continuous
  let K : C(unitInterval × Circle, Y) := ⟨Kfun, hKcont⟩
  refine ⟨γ 1, ⟨{
    toContinuousMap := K
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro z
    let s := Function.surjInv hc_surj z
    have hs : c s = z := Function.rightInverse_surjInv hc_surj z
    rw [← hs]
    change Kfun (0, c s) = γ (c s)
    rw [hKcomp (0, s)]
    change H (0, s) = γ (c s)
    rw [H.apply_zero]
    change γ (a s) = γ (c s)
    congr 1
    exact (PolygonSurfaceHomology.circleArc_eq_integerLoop_one s).symm
  · intro z
    let s := Function.surjInv hc_surj z
    have hs : c s = z := Function.rightInverse_surjInv hc_surj z
    rw [← hs]
    change Kfun (1, c s) = γ 1
    rw [hKcomp (1, s)]
    change H (1, s) = γ 1
    rw [H.apply_one]
    rfl

/-! ## Part F. `H₂` of a cell attached to a space with `H₂ = 0` -/

/-- Generic companion of `cell_H2_of_zero`: `H₂(Y ∪_γ D²) ≅ ker γ_*`. -/
lemma cell_H2_ker {Y : Type} [TopologicalSpace Y] (γ : C(Circle, Y))
    (hA1 : IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ)
    (hA2 : ContractibleSpace (cellInner γ))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA5 : ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ))
    (hY2 : Limits.IsZero (H 2 Y)) :
    Nonempty (H 2 (Cell γ) ≅ ModuleCat.of ℤ (LinearMap.ker (Hmap γ 1).hom)) := by
  sorry

/-- The kernel of a map from an infinite cyclic group to a group of
exponent two is infinite cyclic. -/
lemma ker_int_of_two_torsion {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    (eM : M ≃ₗ[ℤ] ℤ) (φ : M →ₗ[ℤ] N) (h2 : ∀ n : N, n + n = 0) :
    Nonempty (LinearMap.ker φ ≃ₗ[ℤ] ℤ) := by
  letI : Module.Free ℤ M := Module.Free.of_equiv eM.symm
  letI : Module.Finite ℤ M := Module.Finite.equiv eM.symm
  have hker_ne : LinearMap.ker φ ≠ ⊥ := by
    intro hker
    let x : M := eM.symm 1
    have hx : x + x ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, map_add, h2]
    have hx0 : x + x = 0 := by
      have : x + x ∈ (⊥ : Submodule ℤ M) := hker ▸ hx
      simpa using this
    have := congrArg eM hx0
    simp [x] at this
  let bM := Module.Free.chooseBasis ℤ M
  let bd := (LinearMap.ker φ).basisOfPid bM
  let bker := bd.2
  letI : Module ℤ (LinearMap.ker φ) := Submodule.module (LinearMap.ker φ)
  letI : Module.Free ℤ (LinearMap.ker φ) := Module.Free.of_basis bker
  letI : Module.Finite ℤ (LinearMap.ker φ) := Module.Finite.of_basis bker
  have hfinrank_pos : 0 < Module.finrank ℤ (LinearMap.ker φ) := by
    rw [Module.finrank_pos_iff]
    exact (LinearMap.ker φ).nontrivial_iff_ne_bot.mpr hker_ne
  have hfinrank_le : Module.finrank ℤ (LinearMap.ker φ) ≤ 1 := by
    calc
      Module.finrank ℤ (LinearMap.ker φ) ≤ Module.finrank ℤ M :=
        Submodule.finrank_le _
      _ = Module.finrank ℤ ℤ := eM.finrank_eq
      _ = 1 := by simp
  obtain ⟨ek⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℤ (LinearMap.ker φ) = Module.finrank ℤ ℤ by
      rw [show Module.finrank ℤ ℤ = 1 by simp]
      omega)
  exact ⟨ek.toAddEquiv.toIntLinearEquiv⟩

/-! ## Part G. Two-element algebra (proved) -/

lemma zmod2_cases (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  revert a; decide

lemma two_elem_mul {G : Type} [Group G] (e : G ≃* Multiplicative (ZMod 2)) {g : G}
    (hg : g ≠ 1) (h : G) : h = 1 ∨ h = g := by
  have hg' : e g = Multiplicative.ofAdd 1 :=
    (zmod2_cases (e g)).resolve_left (fun h1 => hg (e.injective (by rw [h1, map_one])))
  rcases zmod2_cases (e h) with h1 | h1
  · exact Or.inl (e.injective (by rw [h1, map_one]))
  · exact Or.inr (e.injective (by rw [h1, hg']))

lemma normalClosure_eq_top_of_zmod2 {G : Type} [Group G] (e : G ≃* Multiplicative (ZMod 2))
    {g : G} (hg : g ≠ 1) : Subgroup.normalClosure ({g} : Set G) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro h
  rcases two_elem_mul e hg h with rfl | rfl
  · exact one_mem _
  · exact Subgroup.subset_normalClosure rfl

lemma two_elem_add {N : Type} [AddCommGroup N] [Module ℤ N] (e : N ≃ₗ[ℤ] ZMod 2) {g : N}
    (hg : g ≠ 0) (h : N) : h = 0 ∨ h = g := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hg' : e g = 1 :=
    (hc (e g)).resolve_left (fun h1 => hg (e.injective (by rw [h1, map_zero])))
  rcases hc (e h) with h1 | h1
  · exact Or.inl (e.injective (by rw [h1, map_zero]))
  · exact Or.inr (e.injective (by rw [h1, hg']))

lemma zmod1_mulEquiv {G : Type} [Group G] (h : ∀ g : G, g = 1) :
    Nonempty (G ≃* Multiplicative (ZMod 1)) :=
  ⟨{ toFun := fun _ => 1
     invFun := fun _ => 1
     left_inv := fun g => (h g).symm
     right_inv := fun a => Subsingleton.elim (α := ZMod 1) _ _
     map_mul' := fun _ _ => (mul_one 1).symm }⟩

/-! ## Part H. Assembly -/

/-- π₁ of the problem space, transported to the cell picture at `f 1`. -/
def piOneTransport (f : C(Circle, apm_t00j07_RP2)) :
    FundamentalGroup (apm_t00j07_attachDisk f) (apm_t00j07_basepoint f) ≃*
      FundamentalGroup (Cell f) (cellIncl f (f 1)) :=
  letI : PathConnectedSpace (Cell f) := cell_pc f
  (ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
    (cellHomeo f) (apm_t00j07_basepoint f)).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected _ _)

/-- Common part: `H₀` and `H_{≥3}`. -/
theorem common_invariants (f : C(Circle, apm_t00j07_RP2)) :
    Nonempty (apm_t00j07_H 0 (apm_t00j07_attachDisk f) ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k, 3 ≤ k → Limits.IsZero (apm_t00j07_H k (apm_t00j07_attachDisk f)) := by
  letI : PathConnectedSpace (Cell f) := cell_pc f
  obtain ⟨hA1, hA2, hA3, hA4, -⟩ := cell_facts f
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := H_of_homeomorph (cellHomeo f) 0
    obtain ⟨g⟩ := H0_of_pathConnected (Cell f)
    exact ⟨e ≪≫ g⟩
  · intro k hk
    obtain ⟨e⟩ := H_of_homeomorph (cellHomeo f) k
    have hc := cell_H_high f hA1 hA2 hA3 hA4 k hk
    refine Limits.IsZero.of_iso ?_ e
    exact Limits.IsZero.of_iso (rp2_homology.2.2 k hk) (LinearEquiv.toModuleIso
      (LinearEquiv.ofBijective (Hmap (cellIncl f) k).hom hc)).symm

theorem apm_t00J07_bridge_nullhomotopic_attachment_invariants
    (f : C(Circle, apm_t00j07_RP2))
    (hemb : Topology.IsEmbedding (f : Circle → apm_t00j07_RP2))
    (hnull : ∃ p : apm_t00j07_RP2,
      ContinuousMap.Homotopic f (ContinuousMap.const _ p)) :
    apm_t00j07_invariants f (Multiplicative (ZMod 2))
      (ModuleCat.of ℤ (ZMod 2)) := by
  letI : PathConnectedSpace (Cell f) := cell_pc f
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := cell_facts f
  have hzero : Hmap f 1 = 0 := by
    obtain ⟨p, hp⟩ := hnull
    exact ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_zero_of_nullhomotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero f ⟨p, hp⟩
  have hcls : loopClassAt f (f 1) rfl = 1 := by
    obtain ⟨c, hc⟩ := hurewicz_loopClass_mem_range f
    apply hurewicz_injective_of_zmod2 (f 1)
      (apm_t00J07_rp2_bridge_projectivePlane_fundamentalGroup (f 1)) rp2_homology.1
    rw [PolygonSurfaceHomology.moduleHurewicz_one, ← hc, hzero]
    rfl
  obtain ⟨hps, hpk⟩ := cell_piOne f (f 1) rfl hA1 hA2 hA3 hA4 hA5
    (cell_pathConnected f hA3 hA4) cell_piOne_aux_hequiv_bijective
    cell_piOne_aux_homotopic_conj (cell_piOne_aux_overlap_generator f hA3)
  have hbot : Subgroup.normalClosure
      ({(1 : FundamentalGroup apm_t00j07_RP2 (f 1))} : Set _) = ⊥ :=
    le_bot_iff.mp (Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (one_mem _)))
  rw [hcls, hbot] at hpk
  have h1 := cell_H1 f hA1 hA2 hA3 hA4 hA5
    (cell_H1_aux_inner_zero f hA2) (cell_H1_aux_mv0_injective f hA3 hA4 hA2)
    (cell_H1_aux_transport f hA3 hA4 hA5)
  obtain ⟨h0, hhigh⟩ := common_invariants f
  refine ⟨?_, h0, ?_, ?_, hhigh⟩
  · have hinj : Function.Injective (FundamentalGroup.map (cellIncl f) (f 1)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hpk
    obtain ⟨e⟩ := apm_t00J07_rp2_bridge_projectivePlane_fundamentalGroup (f 1)
    exact ⟨(piOneTransport f).trans
      ((MulEquiv.ofBijective _ ⟨hinj, hps⟩).symm.trans e)⟩
  · obtain ⟨e⟩ := H_of_homeomorph (cellHomeo f) 1
    obtain ⟨g⟩ := rp2_homology.1
    have hinj : Function.Injective (Hmap (cellIncl f) 1).hom := by
      rw [← LinearMap.ker_eq_bot, h1.2, hzero]
      exact LinearMap.range_zero
    exact ⟨e ≪≫ (LinearEquiv.toModuleIso
      (LinearEquiv.ofBijective (Hmap (cellIncl f) 1).hom ⟨hinj, h1.1⟩)).symm ≪≫ g⟩
  · obtain ⟨e⟩ := H_of_homeomorph (cellHomeo f) 2
    obtain ⟨g⟩ := cell_H2_of_zero f hA1 hA2 hA3 hA4 hA5 rp2_homology.2.1 hzero
    exact ⟨e ≪≫ g⟩

theorem apm_t00J07_bridge_essential_attachment_invariants
    (f : C(Circle, apm_t00j07_RP2))
    (hemb : Topology.IsEmbedding (f : Circle → apm_t00j07_RP2))
    (hessential : ¬∃ p : apm_t00j07_RP2,
      ContinuousMap.Homotopic f (ContinuousMap.const _ p)) :
    apm_t00j07_invariants f (Multiplicative (ZMod 1))
      (ModuleCat.of ℤ (ZMod 1)) := by
  letI : PathConnectedSpace (Cell f) := cell_pc f
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := cell_facts f
  obtain ⟨eπ⟩ := apm_t00J07_rp2_bridge_projectivePlane_fundamentalGroup (f 1)
  obtain ⟨eH⟩ := rp2_homology.1
  have hcls : loopClassAt f (f 1) rfl ≠ 1 := fun h =>
    hessential (nullhomotopic_of_loopClassAt_eq_one f h)
  have hhur : PolygonSurfaceHomology.moduleHurewicz (f 1) (loopClassAt f (f 1) rfl) ≠ 0 := by
    intro h
    apply hcls
    apply hurewicz_injective_of_zmod2 (f 1) ⟨eπ⟩ ⟨eH⟩
    rw [h, PolygonSurfaceHomology.moduleHurewicz_one]
  obtain ⟨c, hc⟩ := hurewicz_loopClass_mem_range f
  obtain ⟨hps, hpk⟩ := cell_piOne f (f 1) rfl hA1 hA2 hA3 hA4 hA5
    (cell_pathConnected f hA3 hA4) cell_piOne_aux_hequiv_bijective
    cell_piOne_aux_homotopic_conj (cell_piOne_aux_overlap_generator f hA3)
  rw [normalClosure_eq_top_of_zmod2 eπ hcls] at hpk
  have h1 := cell_H1 f hA1 hA2 hA3 hA4 hA5
    (cell_H1_aux_inner_zero f hA2) (cell_H1_aux_mv0_injective f hA3 hA4 hA2)
    (cell_H1_aux_transport f hA3 hA4 hA5)
  obtain ⟨h0, hhigh⟩ := common_invariants f
  refine ⟨?_, h0, ?_, ?_, hhigh⟩
  · have htriv : ∀ g : FundamentalGroup (Cell f) (cellIncl f (f 1)), g = 1 := by
      intro g
      obtain ⟨w, rfl⟩ := hps g
      have : w ∈ (FundamentalGroup.map (cellIncl f) (f 1)).ker := by rw [hpk]; trivial
      exact this
    obtain ⟨e⟩ := zmod1_mulEquiv htriv
    exact ⟨(piOneTransport f).trans e⟩
  · obtain ⟨e⟩ := H_of_homeomorph (cellHomeo f) 1
    have hrange : LinearMap.range (Hmap f 1).hom = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rcases two_elem_add eH.toLinearEquiv hhur y with rfl | rfl
      · exact zero_mem _
      · exact ⟨c, hc⟩
    have hsub : ∀ z : H 1 (Cell f), z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := h1.1 z
      have hw : w ∈ LinearMap.ker (Hmap (cellIncl f) 1).hom := by
        rw [h1.2, hrange]; trivial
      exact hw
    haveI : Subsingleton (H 1 (Cell f)) := ⟨fun a b => (hsub a).trans (hsub b).symm⟩
    haveI : Subsingleton (ModuleCat.of ℤ (ZMod 1)) := inferInstanceAs (Subsingleton (ZMod 1))
    exact ⟨e ≪≫ (ModuleCat.isZero_of_subsingleton (H 1 (Cell f))).iso
      (ModuleCat.isZero_of_subsingleton _)⟩
  · obtain ⟨e⟩ := H_of_homeomorph (cellHomeo f) 2
    obtain ⟨g⟩ := cell_H2_ker f hA1 hA2 hA3 hA4 hA5 rp2_homology.2.1
    have h2tors : ∀ n : H 1 apm_t00j07_RP2, n + n = 0 := by
      intro n
      have hc : ∀ a : ZMod 2, a + a = 0 := by decide
      apply eH.toLinearEquiv.injective
      rw [map_add, map_zero]
      exact hc _
    obtain ⟨k⟩ := ker_int_of_two_torsion
      ConstructionTargets.CircleHomology.circleH1IsoInt.toLinearEquiv (Hmap f 1).hom h2tors
    exact ⟨e ≪≫ g ≪≫ k.toModuleIso⟩

end APMT00J07

open APMT00J07 in
theorem apm_t00j07 :
    ∀ f : C(Circle, apm_t00j07_RP2),
      Topology.IsEmbedding (f : Circle → apm_t00j07_RP2) →
      ((∃ p : apm_t00j07_RP2,
          ContinuousMap.Homotopic f (ContinuousMap.const _ p)) →
        apm_t00j07_invariants f (Multiplicative (ZMod 2))
          (ModuleCat.of ℤ (ZMod 2))) ∧
      ((¬∃ p : apm_t00j07_RP2,
          ContinuousMap.Homotopic f (ContinuousMap.const _ p)) →
        apm_t00j07_invariants f (Multiplicative (ZMod 1))
          (ModuleCat.of ℤ (ZMod 1))) := by
  intro f hemb
  exact ⟨apm_t00J07_bridge_nullhomotopic_attachment_invariants f hemb,
    apm_t00J07_bridge_essential_attachment_invariants f hemb⟩
