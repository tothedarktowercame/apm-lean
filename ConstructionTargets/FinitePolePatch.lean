import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Patching finitely many removable singularities

Contour arguments repeatedly subtract principal parts and then fill the
resulting removable singularities.  This module packages that finite patching
step independently of any particular residue computation.
-/

open Filter Set Topology

noncomputable section

namespace ConstructionTargets.FinitePolePatch

/-- Replace a function at each point of a finite set by the value of its
specified local analytic extension. -/
noncomputable def patchFinite (s : Finset ℂ) (r : ℂ → ℂ)
    (extension : ℂ → ℂ → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ s then extension z z else r z

/-- If `r` is differentiable off a finite set and agrees punctured-locally
with an analytic extension at every exceptional point, filling those points
produces an entire function. -/
theorem differentiable_patchFinite
    (s : Finset ℂ) (r : ℂ → ℂ) (extension : ℂ → ℂ → ℂ)
    (hr : ∀ z, z ∉ s → DifferentiableAt ℂ r z)
    (hextAnalytic : ∀ a ∈ s, AnalyticAt ℂ (extension a) a)
    (hext : ∀ a ∈ s, r =ᶠ[𝓝[≠] a] extension a) :
    Differentiable ℂ (patchFinite s r extension) := by
  classical
  intro z
  by_cases hz : z ∈ s
  · have hav : ∀ᶠ w in 𝓝 z, w ∉ s.erase z :=
      (s.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds
        (by simp)
    have hpunc := eventually_nhdsWithin_iff.mp (hext z hz)
    have hlocal : patchFinite s r extension =ᶠ[𝓝 z] extension z := by
      filter_upwards [hav, hpunc] with w hwavoid hwext
      by_cases hwz : w = z
      · subst w
        simp [patchFinite, hz]
      · have hws : w ∉ s := by
          intro hmem
          exact hwavoid (Finset.mem_erase.mpr ⟨hwz, hmem⟩)
        simp [patchFinite, hws, hwext hwz]
    exact (hlocal.differentiableAt_iff).mpr (hextAnalytic z hz).differentiableAt
  · have hav : ∀ᶠ w in 𝓝 z, w ∉ (s : Set ℂ) :=
      s.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
    have hlocal : patchFinite s r extension =ᶠ[𝓝 z] r := by
      filter_upwards [hav] with w hw
      have hw' : w ∉ s := by simpa using hw
      simp [patchFinite, hw']
    exact (hlocal.differentiableAt_iff).mpr (hr z hz)

/-- Away from the patched set, patching does not change the function. -/
theorem patchFinite_eq {s : Finset ℂ} {r : ℂ → ℂ}
    {extension : ℂ → ℂ → ℂ} {z : ℂ} (hz : z ∉ s) :
    patchFinite s r extension z = r z := by
  classical
  simp [patchFinite, hz]

end ConstructionTargets.FinitePolePatch
