import Mathlib
import ApmCanaries.Frames.M98J03.Apm_v2_m98J03_1775007499607.Scratch

noncomputable section
open scoped RealInnerProductSpace

namespace ApmCanaries.Frames.M98J03.Apm_v2_m98J03_1775007499607.Main

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

namespace ProjectionFacts

variable (V : ClosedSubmodule Real H)

local notation "P" => V.starProjection
local notation "Vsub" => (V : Submodule Real H)
local notation "Vperp" => Vsubᗮ

lemma starProjection_maps_onto (x : H) (hx : x ∈ (V : Set H)) : P x = x := by
  have hx' : x ∈ Vsub := hx
  simpa [Vsub, P] using
    (Submodule.starProjection_eq_self_iff (K := Vsub) (v := x)).2 hx'

lemma starProjection_kills_perp (x : H) (hx : x ∈ (Vperp : Set H)) : P x = 0 := by
  have hx' : x ∈ Vperp := hx
  have hker := (Submodule.orthogonalProjection_eq_zero_iff (K := Vsub) (v := x)).2 hx'
  simpa [P] using hker

/-- The orthogonal complement of `V` is closed. -/
lemma orthogonal_isClosed : IsClosed (Vperp : Set H) :=
  (Submodule.isClosed_orthogonal (V := Vsub)).trans rfl

/-- If a continuous linear operator commutes with `P`, it preserves `V` and `V_perp`. -/
lemma commute_preserves
    (A : H ->L[Real] H) (hcomm : A.comp P = P.comp A) :
    (forall x ∈ (V : Set H), A x ∈ (V : Set H)) ∧
      (forall x ∈ (Vperp : Set H), A x ∈ (Vperp : Set H)) := by
  constructor
  · intro x hx
    have hxproj := starProjection_maps_onto (V := V) x hx
    have h := congrArg (fun f : H ->L[Real] H => f x) hcomm
    have hmem : P (A x) = A x := by
      simpa [ContinuousLinearMap.comp_apply, hxproj] using h
    have : A x ∈ Vsub :=
      (Submodule.starProjection_eq_self_iff (K := Vsub) (v := A x)).1
        (by simpa [P] using hmem)
    simpa using this
  · intro x hx
    have hxker : P x = 0 := starProjection_kills_perp (V := V) x hx
    have h := congrArg (fun f : H ->L[Real] H => f x) hcomm.symm
    have hzero : P (A x) = 0 := by
      simpa [ContinuousLinearMap.comp_apply, hxker] using h
    have : A x ∈ Vperp :=
      (Submodule.orthogonalProjection_eq_zero_iff (K := Vsub) (v := A x)).1
        (by simpa [P] using hzero)
    simpa using this

-- The Hilbert adjoint of P equals P itself.
lemma adjoint_eq : P.adjoint = P := by
  apply adjoint_eq
  simpa [P] using isSelfAdjoint_starProjection (V := Vsub)

end ProjectionFacts

end ApmCanaries.Frames.M98J03.Apm_v2_m98J03_1775007499607.Main
