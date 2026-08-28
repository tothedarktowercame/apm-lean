import Mathlib.GroupTheory.PushoutI
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The algebraic pushout underlying the twice-spiral gluing

This target isolates the group-theoretic colimit that a future topological
Seifert--van Kampen theorem must produce.  It does not assert that a
fundamental group is this pushout.
-/

namespace ConstructionTargets.TwiceSpiralFundamentalGroupPushout

abbrev IntGroup := Multiplicative ℤ
abbrev IntPairGroup := Multiplicative (ℤ × ℤ)

def leftBoundaryHom : IntPairGroup →* IntGroup :=
  AddMonoidHom.toMultiplicative
    { toFun := fun p : ℤ × ℤ ↦ p.2
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

def rightBoundaryHom (d : ℤ) : IntPairGroup →* IntGroup :=
  AddMonoidHom.toMultiplicative
    { toFun := fun p : ℤ × ℤ ↦ 2 * p.1 + d * p.2
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add]; ac_rfl }

def twiceSpiralDiagram (d : ℤ) : Bool → IntPairGroup →* IntGroup
  | false => leftBoundaryHom
  | true => rightBoundaryHom d

abbrev TwiceSpiralPushout (d : ℤ) := Monoid.PushoutI (twiceSpiralDiagram d)

def leftToZModTwo (d : ℤ) : IntGroup →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun n : ℤ ↦ (d * n : ℤ)
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }

def rightToZModTwo : IntGroup →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))

def baseToZModTwo (d : ℤ) : IntPairGroup →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun p : ℤ × ℤ ↦ (d * p.2 : ℤ)
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }

theorem branches_comp_boundary (d : ℤ) (i : Bool) :
    (cond i rightToZModTwo (leftToZModTwo d)).comp
        (twiceSpiralDiagram d i) = baseToZModTwo d := by
  cases i
  · ext p
    simp [twiceSpiralDiagram, leftBoundaryHom, leftToZModTwo, baseToZModTwo]
  · ext p
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [twiceSpiralDiagram, rightBoundaryHom, rightToZModTwo, baseToZModTwo,
      Int.cast_add, Int.cast_mul, htwo]

def pushoutToZModTwo (d : ℤ) :
    TwiceSpiralPushout d →* Multiplicative (ZMod 2) :=
  Monoid.PushoutI.lift (fun i ↦ cond i rightToZModTwo (leftToZModTwo d))
    (baseToZModTwo d) (branches_comp_boundary d)

@[simp] theorem pushoutToZModTwo_of_false (d n) :
    pushoutToZModTwo d (Monoid.PushoutI.of false (Multiplicative.ofAdd n)) =
      Multiplicative.ofAdd (d * n : ZMod 2) := by
  simp [pushoutToZModTwo, leftToZModTwo]

@[simp] theorem pushoutToZModTwo_of_true (d n) :
    pushoutToZModTwo d (Monoid.PushoutI.of true (Multiplicative.ofAdd n)) =
      Multiplicative.ofAdd (n : ZMod 2) := by
  simp [pushoutToZModTwo, rightToZModTwo]

theorem right_generator_sq (d : ℤ) :
    (Monoid.PushoutI.of true (Multiplicative.ofAdd (1 : ℤ)) :
      TwiceSpiralPushout d) ^ 2 = 1 := by
  have h := Monoid.PushoutI.of_apply_eq_base (φ := twiceSpiralDiagram d)
    true (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ))
  have h' := Monoid.PushoutI.of_apply_eq_base (φ := twiceSpiralDiagram d)
    false (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ))
  have hrel :
      (Monoid.PushoutI.of true (Multiplicative.ofAdd (2 : ℤ)) :
        TwiceSpiralPushout d) = 1 := by
    calc
      _ = (Monoid.PushoutI.base (twiceSpiralDiagram d))
          (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)) := by
        simpa [twiceSpiralDiagram, rightBoundaryHom] using h
      _ = Monoid.PushoutI.of false (Multiplicative.ofAdd (0 : ℤ)) := h'.symm
      _ = 1 := by simp
  calc
    _ = Monoid.PushoutI.of true (Multiplicative.ofAdd (2 : ℤ)) := by
      rw [← map_pow]
      rfl
    _ = 1 := hrel

/-- The canonical map from the algebraic twice-spiral pushout onto the expected
cyclic group is surjective. -/
theorem pushoutToZModTwo_surjective (d : ℤ) :
    Function.Surjective (pushoutToZModTwo d) := by
  intro x
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨Monoid.PushoutI.of true (Multiplicative.ofAdd n), ?_⟩
  rw [pushoutToZModTwo_of_true]
  exact congrArg Multiplicative.ofAdd hn

#print axioms branches_comp_boundary
#print axioms right_generator_sq
#print axioms pushoutToZModTwo_surjective

end ConstructionTargets.TwiceSpiralFundamentalGroupPushout
