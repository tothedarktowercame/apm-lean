import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Covering.AddCircle

noncomputable section

namespace UnitAddCircleFiveTorsionCardinality

abbrev fiveKernel := (nsmulAddMonoidHom (α := UnitAddCircle) 5).ker

def finFiveToKernel (m : Fin 5) : fiveKernel :=
  ⟨(((((m : ℕ) : ℝ) / 5 : ℝ) : UnitAddCircle)), by
    change 5 • (((((m : ℕ) : ℝ) / 5 : ℝ) : UnitAddCircle)) = 0
    rw [AddCircle.nsmul_eq_zero_iff (by norm_num : 0 < 5)]
    exact ⟨m, m.isLt, by simp⟩⟩

theorem finFiveToKernel_bijective : Function.Bijective finFiveToKernel := by
  constructor
  · intro m n h
    apply Fin.ext
    have hc : (((((m : ℕ) : ℝ) / 5 : ℝ) : UnitAddCircle)) =
        (((((n : ℕ) : ℝ) / 5 : ℝ) : UnitAddCircle)) :=
      congrArg Subtype.val h
    rw [AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)] at hc
    · exact_mod_cast (div_left_inj' (by norm_num : (5 : ℝ) ≠ 0)).mp hc
    · constructor
      · positivity
      · norm_num only [zero_add]
        apply (div_lt_one (by norm_num : (0 : ℝ) < 5)).2
        exact_mod_cast m.isLt
    · constructor
      · positivity
      · norm_num only [zero_add]
        apply (div_lt_one (by norm_num : (0 : ℝ) < 5)).2
        exact_mod_cast n.isLt
  · rintro ⟨u, hu⟩
    change 5 • u = 0 at hu
    obtain ⟨m, hm, rfl⟩ := (AddCircle.nsmul_eq_zero_iff (by norm_num : 0 < 5)).mp hu
    refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
    simp [finFiveToKernel]

def finFiveEquivKernel : Fin 5 ≃ fiveKernel :=
  Equiv.ofBijective finFiveToKernel finFiveToKernel_bijective

theorem fiveKernel_natCard : Nat.card fiveKernel = 5 := by
  rw [← Nat.card_congr finFiveEquivKernel]
  simp

#print axioms finFiveToKernel_bijective
#print axioms finFiveEquivKernel
#print axioms fiveKernel_natCard

end UnitAddCircleFiveTorsionCardinality
