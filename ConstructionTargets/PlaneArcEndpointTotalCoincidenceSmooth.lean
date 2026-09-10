import ConstructionTargets.PlaneArcEndpointPairBoundaryFinite

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointTotalCoincidenceSmooth
open PlaneArcEndpointPreservingPerturbation

abbrev Plane := ℝ × ℝ
abbrev TotalParameters := (ℝ × ℝ) × (Plane × Plane)

def totalDifference (a b : ℝ → Plane) (p : TotalParameters) : Plane :=
  perturb a p.2.1 p.1.1 - perturb b p.2.2 p.1.2

theorem totalDifference_contDiffOn (a b : ℝ → Plane) (U V : Set ℝ)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) :
    ContDiffOn ℝ ∞ (totalDifference a b)
      ((U ×ˢ V) ×ˢ (Set.univ : Set (Plane × Plane))) := by
  let S : Set TotalParameters := (U ×ˢ V) ×ˢ (Set.univ : Set (Plane × Plane))
  have hat : ContDiffOn ℝ ∞ (fun p : TotalParameters => a p.1.1) S :=
    ha.comp (contDiff_fst.comp contDiff_fst).contDiffOn (fun p hp => hp.1.1)
  have hbt : ContDiffOn ℝ ∞ (fun p : TotalParameters => b p.1.2) S :=
    hb.comp (contDiff_snd.comp contDiff_fst).contDiffOn (fun p hp => hp.1.2)
  have hwt : ContDiffOn ℝ ∞ (fun p : TotalParameters => endpointWeight p.1.1) S :=
    endpointWeight_contDiff.contDiffOn.comp
      (contDiff_fst.comp contDiff_fst).contDiffOn (fun _ _ => mem_univ _)
  have hws : ContDiffOn ℝ ∞ (fun p : TotalParameters => endpointWeight p.1.2) S :=
    endpointWeight_contDiff.contDiffOn.comp
      (contDiff_snd.comp contDiff_fst).contDiffOn (fun _ _ => mem_univ _)
  have hva : ContDiffOn ℝ ∞ (fun p : TotalParameters => p.2.1) S :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have hvb : ContDiffOn ℝ ∞ (fun p : TotalParameters => p.2.2) S :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  exact hat.add (hwt.smul hva) |>.sub (hbt.add (hws.smul hvb))

#print axioms totalDifference_contDiffOn

end PlaneArcEndpointTotalCoincidenceSmooth
