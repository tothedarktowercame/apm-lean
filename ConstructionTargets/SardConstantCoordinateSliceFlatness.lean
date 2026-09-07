import Mathlib

namespace SardConstantCoordinateSliceFlatnessProbe

variable {E R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- If a coordinate is constant along a parametrized slice, the derivative of
the slice lands in the kernel of that coordinate derivative. -/
theorem derivative_comp_eq_zero_of_coordinate_constant
    (p : E → R) (s : G → E) (r : R) (z : G)
    (P : E →L[ℝ] R) (J : G →L[ℝ] E)
    (hp : HasFDerivAt p P (s z)) (hs : HasFDerivAt s J z)
    (hconst : p ∘ s = fun _ => r) : P.comp J = 0 := by
  have hc : HasFDerivAt (p ∘ s) (P.comp J) z := hp.comp z hs
  rw [hconst] at hc
  exact hc.unique (hasFDerivAt_const (x := z) (c := r))

/-- A residual map whose derivative vanishes on the coordinate kernel has zero
derivative after restriction to any constant-coordinate slice. -/
theorem hasFDerivAt_zero_on_constantCoordinateSlice
    (h : E → S) (s : G → E) (z : G)
    (H : E →L[ℝ] S) (P : E →L[ℝ] R) (J : G →L[ℝ] E)
    (hh : HasFDerivAt h H (s z)) (hs : HasFDerivAt s J z)
    (hPJ : P.comp J = 0)
    (hflat : ∀ v ∈ P.ker, H v = 0) :
    HasFDerivAt (h ∘ s) (0 : G →L[ℝ] S) z := by
  have hHJ : H.comp J = 0 := by
    ext v
    have hv : J v ∈ P.ker := by
      change P (J v) = 0
      have := congrArg (fun T : G →L[ℝ] R => T v) hPJ
      simpa using this
    simpa using hflat (J v) hv
  have hc : HasFDerivAt (h ∘ s) (H.comp J) z := hh.comp z hs
  simpa [hHJ] using hc

#print axioms derivative_comp_eq_zero_of_coordinate_constant
#print axioms hasFDerivAt_zero_on_constantCoordinateSlice
end SardConstantCoordinateSliceFlatnessProbe
