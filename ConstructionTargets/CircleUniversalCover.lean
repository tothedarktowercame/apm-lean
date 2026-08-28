import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting

/-!
# The exponential universal cover of the circle

This file packages the concrete covering geometry behind integer winding
classes.  It deliberately stops before classifying homotopy classes of loops.
-/

noncomputable section

namespace ConstructionTargets.CircleUniversalCover

open Function

/-- The standard real-line covering of the complex unit circle. -/
def circleCover : ℝ → Circle := fun t ↦ Circle.exp t

@[simp] theorem circleCover_apply (t : ℝ) : circleCover t = Circle.exp t := rfl

@[simp] theorem circleCover_zero : circleCover 0 = 1 := by
  simp [circleCover]

/-- The standard exponential map is a covering map. -/
theorem circleCover_isCoveringMap : IsCoveringMap circleCover := by
  have h := (AddCircle.isCoveringMap_coe (2 * Real.pi)).homeomorph_comp
    AddCircle.homeomorphCircle'
  simpa only [circleCover, Function.comp_apply,
    AddCircle.homeomorphCircle'_apply_mk] using h

/-- In particular, the exponential cover is locally a homeomorphism. -/
theorem circleCover_isLocalHomeomorph : IsLocalHomeomorph circleCover :=
  circleCover_isCoveringMap.isLocalHomeomorph

/-- Two real parameters have the same image precisely when their difference
is an integral multiple of `2π`. -/
theorem circleCover_eq_iff (s t : ℝ) :
    circleCover s = circleCover t ↔ ∃ n : ℤ, n • (2 * Real.pi) = s - t := by
  change AddCircle.homeomorphCircle' (s : AddCircle (2 * Real.pi)) =
      AddCircle.homeomorphCircle' (t : AddCircle (2 * Real.pi)) ↔ _
  rw [AddCircle.homeomorphCircle'.injective.eq_iff]
  exact QuotientAddGroup.eq_iff_sub_mem.trans AddSubgroup.mem_zmultiples_iff

/-- A real number has at most one expression as an integral multiple of the
nonzero period `2π`. -/
theorem period_integer_unique {x : ℝ} {m n : ℤ}
    (hm : m • (2 * Real.pi) = x) (hn : n • (2 * Real.pi) = x) : m = n := by
  have h : (m : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
    simpa [zsmul_eq_mul] using hm.trans hn.symm
  have hmn : (m : ℝ) = (n : ℝ) := by
    exact mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h
  exact_mod_cast hmn

/-- The canonical continuous lift of a based circle loop starting at zero. -/
noncomputable def liftBasedLoop (gamma : C(Set.Icc (0 : ℝ) 1, Circle))
    (hgamma : gamma 0 = 1) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  circleCover_isCoveringMap.liftPath gamma 0 (by simpa using hgamma)

@[simp] theorem liftBasedLoop_zero (gamma : C(Set.Icc (0 : ℝ) 1, Circle))
    (hgamma : gamma 0 = 1) : liftBasedLoop gamma hgamma 0 = 0 :=
  circleCover_isCoveringMap.liftPath_zero gamma 0 (by simpa using hgamma)

theorem circleCover_comp_liftBasedLoop (gamma : C(Set.Icc (0 : ℝ) 1, Circle))
    (hgamma : gamma 0 = 1) :
    circleCover ∘ liftBasedLoop gamma hgamma = gamma :=
  circleCover_isCoveringMap.liftPath_lifts gamma 0 (by simpa using hgamma)

/-- The endpoint of the lift of a based loop is an integral multiple of `2π`.
This is the concrete integer-valued datum from which winding is constructed. -/
theorem liftBasedLoop_endpoint_periodic
    (gamma : C(Set.Icc (0 : ℝ) 1, Circle))
    (hzero : gamma 0 = 1) (hone : gamma 1 = 1) :
    ∃ n : ℤ, n • (2 * Real.pi) = liftBasedLoop gamma hzero 1 := by
  have hc : circleCover (liftBasedLoop gamma hzero 1) = circleCover 0 := by
    rw [show circleCover (liftBasedLoop gamma hzero 1) = gamma 1 by
      exact congrFun (circleCover_comp_liftBasedLoop gamma hzero) 1]
    simpa using hone
  simpa using (circleCover_eq_iff (liftBasedLoop gamma hzero 1) 0).mp hc

/-- The lifted endpoint determines a unique integer period. -/
theorem existsUnique_liftBasedLoop_endpoint_integer
    (gamma : C(Set.Icc (0 : ℝ) 1, Circle))
    (hzero : gamma 0 = 1) (hone : gamma 1 = 1) :
    ∃! n : ℤ, n • (2 * Real.pi) = liftBasedLoop gamma hzero 1 := by
  obtain ⟨n, hn⟩ := liftBasedLoop_endpoint_periodic gamma hzero hone
  exact ⟨n, hn, fun m hm ↦ period_integer_unique hm hn⟩

#print axioms circleCover_isCoveringMap
#print axioms circleCover_eq_iff
#print axioms liftBasedLoop_endpoint_periodic
#print axioms existsUnique_liftBasedLoop_endpoint_integer

end ConstructionTargets.CircleUniversalCover
