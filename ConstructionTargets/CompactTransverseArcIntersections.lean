import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.DiscreteSubset

/- Conditional finiteness only: no perturbation or transverse triangle cover is constructed. -/
open Set Topology
namespace CompactTransverseArcIntersections
noncomputable section
abbrev Plane := ℝ × ℝ

def difference (a b : ℝ → Plane) (p : Plane) : Plane := a p.1 - b p.2

theorem difference_derivative (a b : ℝ → Plane) (p : Plane)
    (ha : DifferentiableAt ℝ a p.1) (hb : DifferentiableAt ℝ b p.2) :
    HasFDerivAt (difference a b)
      ((fderiv ℝ a p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
       (fderiv ℝ b p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
  (ha.hasFDerivAt.comp p hasFDerivAt_fst).sub
    (hb.hasFDerivAt.comp p hasFDerivAt_snd)

theorem actual_derivative (a b : ℝ → Plane) (p : Plane)
    (ha : DifferentiableAt ℝ a p.1) (hb : DifferentiableAt ℝ b p.2) :
    fderiv ℝ (difference a b) p =
      (fderiv ℝ a p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
      (fderiv ℝ b p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) :=
  (difference_derivative a b p ha hb).fderiv

theorem isolated (f : Plane → Plane) (p : Plane)
    (hf : ContDiffAt ℝ 1 f p)
    (hi : ∃ e : Plane ≃L[ℝ] Plane, (e : Plane →L[ℝ] Plane) = fderiv ℝ f p) :
    ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, f q = f p → q = p := by
  obtain ⟨e, he⟩ := hi
  have hd : HasFDerivAt f (e : Plane →L[ℝ] Plane) p := by
    rw [he]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let h := hf.toOpenPartialHomeomorph f hd (by norm_num)
  have hp : p ∈ h.source := hf.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  exact ⟨h.source, h.open_source, hp, fun q hq heq => h.injOn hq hp heq⟩

theorem compact_fiber_finite (f : Plane → Plane) (K : Set Plane) (v : Plane)
    (hK : IsCompact K) (hf : ∀ p ∈ K, ContDiffAt ℝ 1 f p)
    (hi : ∀ p ∈ K, f p = v →
      ∃ e : Plane ≃L[ℝ] Plane, (e : Plane →L[ℝ] Plane) = fderiv ℝ f p) :
    (K ∩ f ⁻¹' {v}).Finite := by
  have hc : ContinuousOn f K := fun p hp => (hf p hp).continuousAt.continuousWithinAt
  obtain ⟨T, hT, heq⟩ := continuousOn_iff_isClosed.mp hc {v} isClosed_singleton
  have hk : IsCompact (K ∩ f ⁻¹' {v}) := by
    rw [inter_comm, heq, inter_comm]
    exact hK.inter_right hT
  apply hk.finite
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro p hp
  obtain ⟨W, hW, hpW, hinj⟩ := isolated f p (hf p hp.1) (hi p hp.1 hp.2)
  refine ⟨W, hW, ?_⟩
  ext q
  constructor
  · intro hq
    exact mem_singleton_iff.mpr (hinj q hq.1 (hq.2.2.trans hp.2.symm))
  · rintro rfl
    exact ⟨hpW, hp⟩

/-- Open neighborhood extensions include coincidences at all four edges of the square. -/
theorem finite_coincidences (a b : ℝ → Plane) (U V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (hIU : Icc (0 : ℝ) 1 ⊆ U) (hIV : Icc (0 : ℝ) 1 ⊆ V)
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b V)
    (hi : ∀ p ∈ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), a p.1 = b p.2 →
      ∃ e : Plane ≃L[ℝ] Plane,
        (e : Plane →L[ℝ] Plane) = fderiv ℝ (difference a b) p) :
    {p : Plane | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
      a p.1 = b p.2}.Finite := by
  have h := compact_fiber_finite (difference a b)
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) 0 (isCompact_Icc.prod isCompact_Icc)
    (fun p hp => (ha.contDiffAt (hU.mem_nhds (hIU hp.1))).comp p contDiffAt_fst |>.sub
      ((hb.contDiffAt (hV.mem_nhds (hIV hp.2))).comp p contDiffAt_snd))
    (fun p hp he => hi p hp (sub_eq_zero.mp he))
  convert h using 1
  ext p
  simp only [mem_setOf_eq, mem_inter_iff, mem_prod, mem_preimage, mem_singleton_iff,
    difference, sub_eq_zero, and_assoc]

#print axioms difference_derivative
#print axioms actual_derivative
#print axioms isolated
#print axioms compact_fiber_finite
#print axioms finite_coincidences
end
end CompactTransverseArcIntersections
