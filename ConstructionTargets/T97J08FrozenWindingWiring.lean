import ConstructionTargets.T97J08PeriodicWindingAdapter
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Frozen t97J08 winding wiring

This file supplies the topological part of the frozen problem: a smooth,
nonvanishing periodic complex loop has a unique integer for which the frozen
complex-valued norm-one homotopy exists.  No line-integral calculation is used.
-/

open scoped unitInterval

namespace ConstructionTargets.T97J08FrozenWindingWiring

open Set
open ConstructionTargets.CircleWindingUniqueness
open ConstructionTargets.PeriodicCircleHomotopyWinding
open ConstructionTargets.T97J08PeriodicWindingAdapter

noncomputable section

def SmoothPuncturedLoop (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ t, f (t + 2 * Real.pi) = f t) ∧ ∀ t, f t ≠ 0

def normalizedLoop (f : ℝ → ℂ) (t : ℝ) : ℂ := f t / ‖f t‖

def FrozenWindingNumber (f : ℝ → ℂ) (n : ℤ) : Prop :=
  ∃ H : ℝ → ℝ → ℂ,
    Continuous (fun p : ℝ × ℝ ↦ H p.1 p.2) ∧
    (∀ t s, H (t + 2 * Real.pi) s = H t s) ∧
    (∀ t, H t 0 = normalizedLoop f t) ∧
    (∀ t, H t 1 = Complex.exp (Complex.I * (n : ℝ) * t)) ∧
    ∀ t s, s ∈ Icc (0 : ℝ) 1 → ‖H t s‖ = 1

theorem norm_normalizedLoop {f : ℝ → ℂ} (hf : ∀ t, f t ≠ 0) (t : ℝ) :
    ‖normalizedLoop f t‖ = 1 := by
  simp [normalizedLoop, hf t]

noncomputable def circleLoop (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f) : C(ℝ, Circle) :=
  ⟨fun t ↦ ⟨normalizedLoop f t, by
      simpa [Submonoid.unitSphere] using norm_normalizedLoop hf.2.2 t⟩, by
    apply Continuous.subtype_mk
    unfold normalizedLoop
    exact hf.1.continuous.div
      (Complex.ofRealCLM.continuous.comp hf.1.continuous.norm)
      (fun t ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf.2.2 t)))⟩

theorem circleLoop_periodic (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f) :
    IsPeriodic (circleLoop f hf) := by
  intro t
  apply Subtype.ext
  change normalizedLoop f (t + 2 * Real.pi) = normalizedLoop f t
  simp only [normalizedLoop]
  rw [hf.2.1 t]

theorem exists_frozenWindingNumber (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f) :
    FrozenWindingNumber f (winding (circleLoop f hf) (circleLoop_periodic f hf)) := by
  let g := circleLoop f hf
  let hg := circleLoop_periodic f hf
  refine ⟨fun t s ↦ (periodicHomotopy g hg t s : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (continuous_periodicHomotopy g hg)
  · intro t s
    exact congrArg Subtype.val (periodicHomotopy_periodic g hg t s)
  · intro t
    exact congrArg Subtype.val (periodicHomotopy_zero g hg t)
  · intro t
    change ((periodicHomotopy g hg t 1 : Circle) : ℂ) = _
    rw [periodicHomotopy_one]
    rw [Circle.coe_exp]
    congr 1
    dsimp [g, hg]
    push_cast
    ring
  · intro t s hs
    simpa [Submonoid.unitSphere] using (periodicHomotopy g hg t s).property

private noncomputable def squareHomotopy (H : ℝ → ℝ → ℂ)
    (hcont : Continuous (fun p : ℝ × ℝ ↦ H p.1 p.2))
    (hnorm : ∀ t s, s ∈ Icc (0 : ℝ) 1 → ‖H t s‖ = 1) : C(I × I, Circle) :=
  ⟨fun p ↦ ⟨H ((2 * Real.pi) * (p.1 : ℝ)) (p.2 : ℝ), by
      simpa [Submonoid.unitSphere] using hnorm _ _ ⟨p.2.2.1, p.2.2.2⟩⟩, by
    apply Continuous.subtype_mk
    exact hcont.comp (((continuous_const.mul continuous_subtype_val).comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))⟩

theorem frozenWindingNumber_unique (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f)
    {m : ℤ} (hm : FrozenWindingNumber f m) :
    m = winding (circleLoop f hf) (circleLoop_periodic f hf) := by
  rcases hm with ⟨H, hcont, hperiod, hzero, hone, hnorm⟩
  let Q := squareHomotopy H hcont hnorm
  let g := circleLoop f hf
  let hg := circleLoop_periodic f hf
  let a := baseAngle g
  have hQ0 : Q (0, 0) = Circle.exp a := by
    apply Subtype.ext
    simp [Q, squareHomotopy, hzero, g, circleLoop, a, exp_baseAngle]
  have hloop : ∀ s : I, Q (1, s) = Q (0, s) := by
    intro s
    apply Subtype.ext
    simpa [Q, squareHomotopy] using hperiod 0 (s : ℝ)
  let L := liftedSquare Q a hQ0
  have hL0 : L (0, 0) = a := by
    rw [show L (0, 0) = liftedLeftEdge Q a hQ0 0 by
      exact liftedSquare_zero Q a hQ0 0]
    exact Circle.isCoveringMap_exp.liftPath_zero (leftEdge Q) a hQ0
  have hbottom : IsEndpointWinding (L (1, 0)) (L (0, 0)) (winding g hg) := by
    let d : I → ℝ := fun u ↦ L (u, 0) - globalLift g ((2 * Real.pi) * (u : ℝ))
    have hd : (fun u : I ↦ L (u, 0) - globalLift g ((2 * Real.pi) * (u : ℝ))) 1 =
        (fun u : I ↦ L (u, 0) - globalLift g ((2 * Real.pi) * (u : ℝ))) 0 := by
      change d 1 = d 0
      have hdc : Continuous d := by
        dsimp [d]
        fun_prop
      have hde : ∀ u v, Circle.exp (d u) = Circle.exp (d v) := by
        intro u v
        dsimp [d]
        rw [Circle.exp_sub, Circle.exp_sub, exp_liftedSquare, exp_liftedSquare,
          exp_globalLift, exp_globalLift]
        simp [Q, squareHomotopy, hzero, g, circleLoop]
      exact Circle.isCoveringMap_exp.const_of_comp hdc hde 1 0
    unfold IsEndpointWinding
    have hs := winding_spec g hg
    unfold IsEndpointWinding at hs
    simp only [L] at hd ⊢
    rw [globalLift_zero] at hs
    norm_num at hd
    rw [hL0] at hd
    rw [globalLift_zero] at hd
    linarith
  have htop : IsEndpointWinding (L (1, 1)) (L (0, 1)) m := by
    let d : I → ℝ := fun u ↦ L (u, 1) - (m : ℝ) * (2 * Real.pi) * (u : ℝ)
    have hd : (fun u : I ↦ L (u, 1) - (m : ℝ) * (2 * Real.pi) * (u : ℝ)) 1 =
        (fun u : I ↦ L (u, 1) - (m : ℝ) * (2 * Real.pi) * (u : ℝ)) 0 := by
      change d 1 = d 0
      have hdc : Continuous d := by
        dsimp [d]
        fun_prop
      have hde : ∀ u v, Circle.exp (d u) = Circle.exp (d v) := by
        intro u v
        dsimp [d]
        rw [Circle.exp_sub, Circle.exp_sub, exp_liftedSquare, exp_liftedSquare]
        apply Subtype.ext
        simp only [Circle.coe_div]
        change H ((2 * Real.pi) * (u : ℝ)) 1 /
            (Circle.exp ((m : ℝ) * (2 * Real.pi) * (u : ℝ)) : ℂ) =
          H ((2 * Real.pi) * (v : ℝ)) 1 /
            (Circle.exp ((m : ℝ) * (2 * Real.pi) * (v : ℝ)) : ℂ)
        rw [hone, hone]
        simp only [Circle.coe_exp]
        have hu : Complex.I * ((m : ℝ) : ℂ) * (((2 * Real.pi) * (u : ℝ) : ℝ) : ℂ) =
            (((m : ℝ) * (2 * Real.pi) * (u : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        have hv : Complex.I * ((m : ℝ) : ℂ) * (((2 * Real.pi) * (v : ℝ) : ℝ) : ℂ) =
            (((m : ℝ) * (2 * Real.pi) * (v : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hu, hv]
        simp
      exact Circle.isCoveringMap_exp.const_of_comp hdc hde 1 0
    unfold IsEndpointWinding
    simp only [L] at hd ⊢
    norm_num at hd
    linarith
  exact (uniqueEndpointWinding_agrees Q a hQ0 hloop hbottom htop).symm

theorem existsUnique_frozenWindingNumber (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f) :
    ∃! n : ℤ, FrozenWindingNumber f n := by
  refine ⟨winding (circleLoop f hf) (circleLoop_periodic f hf),
    exists_frozenWindingNumber f hf, ?_⟩
  intro m hm
  exact frozenWindingNumber_unique f hf hm

#print axioms exists_frozenWindingNumber
#print axioms frozenWindingNumber_unique
#print axioms existsUnique_frozenWindingNumber

end

end ConstructionTargets.T97J08FrozenWindingWiring
