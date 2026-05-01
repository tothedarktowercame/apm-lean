import Mathlib
import ApmCanaries.Frames.B93J02.Apm_v2_b93J02_1775006390328.Scratch

noncomputable section

open scoped Polynomial

namespace ApmCanaries.Frames.B93J02.Apm_v2_b93J02_1775006390328.Main

/-- In any commutative integral domain, the PID property implies
unique factorisation and hence integral closure.  This formalises
part (a) of the problem. -/
lemma pid_isIntegrallyClosed
    (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsIntegrallyClosed R := by
  classical
  -- `IsPrincipalIdealRing` gives us a `UniqueFactorizationMonoid` instance
  -- which in turn supplies integral closedness.
  simpa using (UniqueFactorizationMonoid.isIntegrallyClosed (R := R))

end ApmCanaries.Frames.B93J02.Apm_v2_b93J02_1775006390328.Main
