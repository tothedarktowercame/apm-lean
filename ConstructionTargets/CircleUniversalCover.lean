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

/-- The integer coordinate of the endpoint of the lift of a based loop. -/
noncomputable def liftBasedLoopEndpointInteger
    (gamma : C(Set.Icc (0 : ℝ) 1, Circle))
    (hzero : gamma 0 = 1) (hone : gamma 1 = 1) : ℤ :=
  (existsUnique_liftBasedLoop_endpoint_integer gamma hzero hone).choose

theorem liftBasedLoopEndpointInteger_spec
    (gamma : C(Set.Icc (0 : ℝ) 1, Circle))
    (hzero : gamma 0 = 1) (hone : gamma 1 = 1) :
    liftBasedLoopEndpointInteger gamma hzero hone • (2 * Real.pi) =
      liftBasedLoop gamma hzero 1 :=
  (existsUnique_liftBasedLoop_endpoint_integer gamma hzero hone).choose_spec.1

/-- Based-homotopic loops have lifts from zero with the same endpoint. -/
theorem liftBasedLoop_one_eq_of_homotopicRel
    {gamma₀ gamma₁ : C(Set.Icc (0 : ℝ) 1, Circle)}
    (h : gamma₀.HomotopicRel gamma₁ {0, 1})
    (hzero₀ : gamma₀ 0 = 1) (hzero₁ : gamma₁ 0 = 1) :
    liftBasedLoop gamma₀ hzero₀ 1 = liftBasedLoop gamma₁ hzero₁ 1 := by
  simpa only [liftBasedLoop] using
    circleCover_isCoveringMap.liftPath_apply_one_eq_of_homotopicRel h 0
      (by simpa using hzero₀) (by simpa using hzero₁)

/-- The lifted endpoint integer is invariant under homotopy relative to both
endpoints. -/
theorem liftBasedLoopEndpointInteger_eq_of_homotopicRel
    {gamma₀ gamma₁ : C(Set.Icc (0 : ℝ) 1, Circle)}
    (h : gamma₀.HomotopicRel gamma₁ {0, 1})
    (hzero₀ : gamma₀ 0 = 1) (hone₀ : gamma₀ 1 = 1)
    (hzero₁ : gamma₁ 0 = 1) (hone₁ : gamma₁ 1 = 1) :
    liftBasedLoopEndpointInteger gamma₀ hzero₀ hone₀ =
      liftBasedLoopEndpointInteger gamma₁ hzero₁ hone₁ := by
  apply period_integer_unique
    (liftBasedLoopEndpointInteger_spec gamma₀ hzero₀ hone₀)
  rw [liftBasedLoop_one_eq_of_homotopicRel h hzero₀ hzero₁]
  exact liftBasedLoopEndpointInteger_spec gamma₁ hzero₁ hone₁

/-- The based loop that travels through `n` full turns of the exponential
cover at constant speed. -/
def integerLoop (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := circleCover ((n • (2 * Real.pi)) * (t : ℝ))
  continuous_toFun := circleCover_isCoveringMap.continuous.comp
    (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by
    have h := (circleCover_eq_iff ((n • (2 * Real.pi)) * (1 : ℝ)) 0).2
      ⟨n, by simp⟩
    simpa using h

/-- The evident linear real path is the canonical lift of `integerLoop`. -/
theorem liftBasedLoop_integerLoop (n : ℤ) :
    liftBasedLoop (integerLoop n) (integerLoop n).source =
      ⟨fun t ↦ (n • (2 * Real.pi)) * (t : ℝ),
        continuous_const.mul continuous_subtype_val⟩ := by
  symm
  apply (circleCover_isCoveringMap.eq_liftPath_iff' _).2
  constructor
  · rfl
  · simp

/-- The explicit `n`-turn loop has endpoint integer `n`. -/
@[simp] theorem liftBasedLoopEndpointInteger_integerLoop (n : ℤ) :
    liftBasedLoopEndpointInteger (integerLoop n) (integerLoop n).source
      (integerLoop n).target = n := by
  apply period_integer_unique
    (liftBasedLoopEndpointInteger_spec (integerLoop n) (integerLoop n).source
      (integerLoop n).target)
  rw [liftBasedLoop_integerLoop]
  simp

/-- Starting the lift of a based loop at another point over `1` translates
the canonical lift by that starting point. -/
theorem liftPath_basedLoop_from_period
    (gamma : Path (1 : Circle) 1) (a : ℝ) (ha : circleCover a = 1) :
    circleCover_isCoveringMap.liftPath gamma a (gamma.source.trans ha.symm) =
      ⟨fun t ↦ a + liftBasedLoop gamma gamma.source t,
        continuous_const.add (liftBasedLoop gamma gamma.source).continuous⟩ := by
  symm
  apply (circleCover_isCoveringMap.eq_liftPath_iff' _).2
  constructor
  · funext t
    change Circle.exp (a + liftBasedLoop gamma gamma.source t) = gamma t
    rw [Circle.exp_add, ← circleCover_apply, ha, one_mul]
    exact congrFun (circleCover_comp_liftBasedLoop gamma gamma.source) t
  · simp

/-- The endpoint of the canonical lift of a concatenation is the sum of the
two canonical lifted endpoints. -/
theorem liftBasedLoop_trans_endpoint (gamma delta : Path (1 : Circle) 1) :
    liftBasedLoop (gamma.trans delta) (gamma.trans delta).source 1 =
      liftBasedLoop gamma gamma.source 1 + liftBasedLoop delta delta.source 1 := by
  have htrans := DFunLike.congr_fun
    (circleCover_isCoveringMap.liftPath_trans circleCover_zero.symm gamma delta) 1
  have ha : circleCover (liftBasedLoop gamma gamma.source 1) = 1 := by
    rw [show circleCover (liftBasedLoop gamma gamma.source 1) = gamma 1 by
      exact congrFun (circleCover_comp_liftBasedLoop gamma gamma.source) 1]
    exact gamma.target
  have htrans' :
      liftBasedLoop (gamma.trans delta) (gamma.trans delta).source 1 =
        circleCover_isCoveringMap.liftPath delta
          (liftBasedLoop gamma gamma.source 1) (delta.source.trans ha.symm) 1 := by
    simpa [liftBasedLoop, Path.trans_apply] using htrans
  have hshift := DFunLike.congr_fun
    (liftPath_basedLoop_from_period delta
      (liftBasedLoop gamma gamma.source 1) ha) 1
  exact htrans'.trans (by simpa using hshift)

/-- The endpoint integer is additive under the path concatenation used to
multiply based-loop homotopy classes. -/
theorem liftBasedLoopEndpointInteger_trans (gamma delta : Path (1 : Circle) 1) :
    liftBasedLoopEndpointInteger (gamma.trans delta) (gamma.trans delta).source
        (gamma.trans delta).target =
      liftBasedLoopEndpointInteger gamma gamma.source gamma.target +
        liftBasedLoopEndpointInteger delta delta.source delta.target := by
  apply period_integer_unique
    (liftBasedLoopEndpointInteger_spec (gamma.trans delta) (gamma.trans delta).source
      (gamma.trans delta).target)
  rw [liftBasedLoop_trans_endpoint]
  rw [add_zsmul]
  rw [liftBasedLoopEndpointInteger_spec gamma gamma.source gamma.target]
  rw [liftBasedLoopEndpointInteger_spec delta delta.source delta.target]

/-- In Mathlib's fundamental group, `gamma * delta` is represented by
`delta.trans gamma` (`CategoryTheory.End.mul_def`).  This is the path-level
additivity formula in that exact multiplication order. -/
theorem liftBasedLoopEndpointInteger_mul_order (gamma delta : Path (1 : Circle) 1) :
    liftBasedLoopEndpointInteger (delta.trans gamma) (delta.trans gamma).source
        (delta.trans gamma).target =
      liftBasedLoopEndpointInteger gamma gamma.source gamma.target +
        liftBasedLoopEndpointInteger delta delta.source delta.target := by
  rw [liftBasedLoopEndpointInteger_trans, add_comm]

@[simp] theorem liftBasedLoopEndpointInteger_refl :
    liftBasedLoopEndpointInteger (Path.refl (1 : Circle)) rfl rfl = 0 := by
  apply period_integer_unique
    (liftBasedLoopEndpointInteger_spec (Path.refl (1 : Circle)) rfl rfl)
  rw [show liftBasedLoop (Path.refl (1 : Circle)) rfl =
      ContinuousMap.const _ 0 by
    exact circleCover_isCoveringMap.liftPath_const circleCover_zero.symm]
  simp

/-- The endpoint coordinate descended to the actual based-loop homotopy
quotient. -/
noncomputable def circleWindingHom :
    FundamentalGroup Circle 1 →* Multiplicative ℤ where
  toFun := Quotient.lift
    (fun gamma : Path (1 : Circle) 1 ↦
      Multiplicative.ofAdd
        (liftBasedLoopEndpointInteger gamma gamma.source gamma.target))
    (fun gamma delta h ↦ congrArg Multiplicative.ofAdd
      (liftBasedLoopEndpointInteger_eq_of_homotopicRel h
        gamma.source gamma.target delta.source delta.target))
  map_one' := by
    change Multiplicative.ofAdd
      (liftBasedLoopEndpointInteger (Path.refl (1 : Circle)) rfl rfl) = 1
    simp
  map_mul' p q := by
    induction p, q using Path.Homotopic.Quotient.ind₂ with
    | mk gamma delta =>
        change Multiplicative.ofAdd
            (liftBasedLoopEndpointInteger (delta.trans gamma)
              (delta.trans gamma).source (delta.trans gamma).target) =
          Multiplicative.ofAdd
              (liftBasedLoopEndpointInteger gamma gamma.source gamma.target) *
            Multiplicative.ofAdd
              (liftBasedLoopEndpointInteger delta delta.source delta.target)
        exact congrArg Multiplicative.ofAdd
          (liftBasedLoopEndpointInteger_mul_order gamma delta)

@[simp] theorem circleWindingHom_mk (gamma : Path (1 : Circle) 1) :
    circleWindingHom (Path.Homotopic.Quotient.mk gamma) =
      Multiplicative.ofAdd
        (liftBasedLoopEndpointInteger gamma gamma.source gamma.target) := rfl

theorem circleWindingHom_surjective : Function.Surjective circleWindingHom := by
  intro n
  refine ⟨Path.Homotopic.Quotient.mk (integerLoop n.toAdd), ?_⟩
  simp [circleWindingHom_mk]

/-- Equal endpoint coordinates give a straight-line relative homotopy between
the two canonical lifts in `ℝ`. -/
def liftBasedLoopStraightHomotopy
    (gamma delta : Path (1 : Circle) 1)
    (hend : liftBasedLoop gamma gamma.source 1 =
      liftBasedLoop delta delta.source 1) :
    (liftBasedLoop gamma gamma.source).HomotopyRel
      (liftBasedLoop delta delta.source) {0, 1} where
  toFun ts :=
    (1 - (ts.1 : ℝ)) * liftBasedLoop gamma gamma.source ts.2 +
      (ts.1 : ℝ) * liftBasedLoop delta delta.source ts.2
  continuous_toFun :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((liftBasedLoop gamma gamma.source).continuous.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((liftBasedLoop delta delta.source).continuous.comp continuous_snd))
  map_zero_left s := by simp
  map_one_left s := by simp
  prop' t s hs := by
    rcases hs with (rfl | rfl)
    · simp
    · change (1 - (t : ℝ)) * liftBasedLoop gamma gamma.source 1 +
        (t : ℝ) * liftBasedLoop delta delta.source 1 =
          liftBasedLoop gamma gamma.source 1
      rw [hend]
      ring

/-- Equal endpoint integers imply that two based loops are homotopic relative
to their endpoints: linearly homotope their lifts and project the homotopy
through the exponential cover. -/
theorem basedLoops_homotopic_of_endpointInteger_eq
    (gamma delta : Path (1 : Circle) 1)
    (hcoord : liftBasedLoopEndpointInteger gamma gamma.source gamma.target =
      liftBasedLoopEndpointInteger delta delta.source delta.target) :
    gamma.HomotopicRel delta {0, 1} := by
  have hend : liftBasedLoop gamma gamma.source 1 =
      liftBasedLoop delta delta.source 1 := by
    rw [← liftBasedLoopEndpointInteger_spec gamma gamma.source gamma.target,
      ← liftBasedLoopEndpointInteger_spec delta delta.source delta.target,
      hcoord]
  let F := liftBasedLoopStraightHomotopy gamma delta hend
  let Fc := F.compContinuousMap
    ⟨circleCover, circleCover_isCoveringMap.continuous⟩
  refine ⟨ContinuousMap.HomotopyRel.cast Fc ?_ ?_⟩
  · dsimp [Fc]
    apply ContinuousMap.ext
    intro t
    exact congrFun (circleCover_comp_liftBasedLoop gamma gamma.source) t
  · dsimp [Fc]
    apply ContinuousMap.ext
    intro t
    exact congrFun (circleCover_comp_liftBasedLoop delta delta.source) t

theorem circleWindingHom_injective : Function.Injective circleWindingHom := by
  intro p q hpq
  induction p, q using Path.Homotopic.Quotient.ind₂ with
  | mk gamma delta =>
      apply Path.Homotopic.Quotient.eq.mpr
      apply basedLoops_homotopic_of_endpointInteger_eq gamma delta
      exact Multiplicative.ofAdd.injective hpq

/-- The exponential lift endpoint classifies based loops in the circle. -/
noncomputable def circleFundamentalGroupMulEquivInt :
    FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective circleWindingHom
    ⟨circleWindingHom_injective, circleWindingHom_surjective⟩

#print axioms circleCover_isCoveringMap
#print axioms circleCover_eq_iff
#print axioms liftBasedLoop_endpoint_periodic
#print axioms existsUnique_liftBasedLoop_endpoint_integer
#print axioms liftBasedLoop_one_eq_of_homotopicRel
#print axioms liftBasedLoopEndpointInteger_eq_of_homotopicRel
#print axioms liftBasedLoopEndpointInteger_integerLoop
#print axioms liftBasedLoopEndpointInteger_trans
#print axioms liftBasedLoopEndpointInteger_mul_order
#print axioms circleWindingHom
#print axioms basedLoops_homotopic_of_endpointInteger_eq
#print axioms circleFundamentalGroupMulEquivInt

end ConstructionTargets.CircleUniversalCover
