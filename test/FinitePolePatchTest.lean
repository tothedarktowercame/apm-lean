import ConstructionTargets.FinitePolePatch

open Filter Set Topology
open ConstructionTargets.FinitePolePatch

noncomputable section

/-- Patching replaces the deliberately wrong value at zero and recovers the
entire polynomial `z²`. -/
example : Differentiable ℂ
    (patchFinite ({0} : Finset ℂ)
      (fun z => if z = 0 then 7 else z ^ 2)
      (fun _ z => z ^ 2)) := by
  apply differentiable_patchFinite
  · intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hev : (fun w : ℂ => if w = 0 then 7 else w ^ 2) =ᶠ[𝓝 z]
        (fun w : ℂ => w ^ 2) := by
      filter_upwards [continuousAt_id.eventually_ne hz0] with w hw
      simp only [id_eq] at hw
      simp [hw]
    exact (hev.differentiableAt_iff).mpr (by fun_prop)
  · intro a ha
    fun_prop
  · intro a ha
    have ha0 : a = 0 := by simpa using ha
    subst a
    change ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (if z = 0 then 7 else z ^ 2) = z ^ 2
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [mem_compl_iff, mem_singleton_iff] at hz
    simp [hz]

#print axioms ConstructionTargets.FinitePolePatch.differentiable_patchFinite
