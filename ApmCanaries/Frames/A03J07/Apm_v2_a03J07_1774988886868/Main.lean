import Mathlib
import ApmCanaries.Frames.A03J07.Apm_v2_a03J07_1774988886868.Scratch

noncomputable section

namespace ApmCanaries.Frames.A03J07.Apm_v2_a03J07_1774988886868.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

lemma abs_cexp_I_mul (ε : ℝ) (z : ℂ) :
    Complex.abs (Complex.exp (Complex.I * ε * z)) =
      Real.exp (-ε * z.im) := by
  have := Complex.abs_exp (Complex.I * ε * z)
  simp [Complex.mul_re, Complex.mul_im, Complex.abs_exp,
    Complex.ofReal_im, Complex.ofReal_re, mul_comm, mul_left_comm,
    mul_assoc] at this
  simpa using this

end ApmCanaries.Frames.A03J07.Apm_v2_a03J07_1774988886868.Main
