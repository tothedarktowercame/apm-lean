import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Regularity of continuous lifts through a local inverse

A generic scalar lemma transferring `ContDiffAt` regularity across a smooth
map whose derivative is nonzero at the lifted point.
-/

open Filter

noncomputable section

namespace ConstructionTargets.ContinuousLiftLocalInverseRegularity

/-- A continuous lift through a locally invertible smooth scalar map inherits
the regularity of its composite. -/
theorem contDiffAt_of_continuous_lift
    {n : WithTop ℕ∞} (hn : n ≠ 0)
    {theta u phi : ℝ → ℝ} {x : ℝ}
    (htheta : ContinuousAt theta x)
    (hu : ContDiffAt ℝ n u x)
    (hphi : ContDiffAt ℝ n phi (theta x))
    {d : ℝ} (hphi' : HasDerivAt phi d (theta x)) (hd : d ≠ 0)
    (hcomp : phi ∘ theta = u) :
    ContDiffAt ℝ n theta x := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hd)
  have hfe : HasFDerivAt phi (e : ℝ →L[ℝ] ℝ) (theta x) :=
    hphi'.hasFDerivAt_equiv hd
  let inv : ℝ → ℝ := hphi.localInverse hfe hn
  have hinv : ContDiffAt ℝ n inv (phi (theta x)) := hphi.to_localInverse hfe hn
  have hleft : (fun y ↦ inv (phi (theta y))) =ᶠ[nhds x] theta := by
    have h := (hphi.hasStrictFDerivAt' hfe hn).eventually_left_inverse
    exact (htheta.tendsto.eventually h).mono (fun _ hy ↦ hy)
  have heu : inv ∘ u =ᶠ[nhds x] theta := by
    filter_upwards [hleft] with y hy
    simpa [Function.comp_apply, ← congrFun hcomp y] using hy
  have hux : u x = phi (theta x) := (congrFun hcomp x).symm
  exact ((hux ▸ hinv).comp x hu).congr_of_eventuallyEq heu.symm

#print axioms contDiffAt_of_continuous_lift

end ConstructionTargets.ContinuousLiftLocalInverseRegularity
