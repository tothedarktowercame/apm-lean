import ConstructionTargets.Sinc

open MeasureTheory Set Real

noncomputable section

/-! # APM a02J05: ∫_{-∞}^{∞} sin(x)/x dx = π

The reusable proof now lives in `ConstructionTargets.Sinc`.  This solved
problem retains an elaborated use of the promoted headline theorem, so there
is exactly one implementation of the Dirichlet-integral argument.
-/

example :
    Filter.Tendsto (fun R : ℝ => ∫ x in Set.Icc (-R) R, Real.sinc x ∂volume)
      Filter.atTop (nhds π) :=
  dirichlet_integral_improper
