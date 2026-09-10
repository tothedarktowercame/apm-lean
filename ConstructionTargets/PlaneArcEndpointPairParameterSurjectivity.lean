import ConstructionTargets.PlaneArcEndpointPerturbationInteriorParameter

noncomputable section
open Set

namespace PlaneArcEndpointPairParameterSurjectivity
open PlaneArcEndpointPreservingPerturbation
open PlaneArcEndpointPerturbationInteriorParameter

abbrev Plane := ℝ × ℝ

def pairDifference (a b : ℝ → Plane) (va vb : Plane) (t s : ℝ) : Plane :=
  perturb a va t - perturb b vb s

lemma pairDifference_vary_left_surjective (a b : ℝ → Plane) (vb : Plane)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    Function.Surjective (fun va : Plane => pairDifference a b va vb t s) := by
  intro y
  obtain ⟨va, hva⟩ := perturb_parameter_surjective a ht
    (y + perturb b vb s - a t)
  refine ⟨va, ?_⟩
  unfold pairDifference
  rw [sub_eq_iff_eq_add]
  dsimp at hva
  have h := congrArg (fun z => z + a t) hva
  simpa only [sub_add_cancel] using h

lemma pairDifference_vary_right_surjective (a b : ℝ → Plane) (va : Plane)
    (t : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective (fun vb : Plane => pairDifference a b va vb t s) := by
  intro y
  obtain ⟨vb, hvb⟩ := perturb_parameter_surjective b hs
    (perturb a va t - b s - y)
  refine ⟨vb, ?_⟩
  unfold pairDifference
  rw [sub_eq_iff_eq_add]
  rw [sub_eq_iff_eq_add] at hvb
  rw [hvb]
  abel

#print axioms pairDifference_vary_left_surjective
#print axioms pairDifference_vary_right_surjective

end PlaneArcEndpointPairParameterSurjectivity
