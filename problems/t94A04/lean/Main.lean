import Mathlib
import ConstructionTargets.SimplyConnectedOpenCover

/-!
# APM t94A04 — simply connected union without a van Kampen premise

The conclusion is stated for the actual union `U ∪ V`; no fundamental-group
computation is assumed.
-/

theorem apm_t94a04
    (X : Type*) [TopologicalSpace X]
    (U V : Set X)
    (hU_open : IsOpen U) (hV_open : IsOpen V)
    (hU_pc : IsPathConnected U) (hV_pc : IsPathConnected V)
    (hU_sc : SimplyConnectedSpace U) (hV_sc : SimplyConnectedSpace V)
    (hinter_nonempty : (U ∩ V).Nonempty)
    (hinter_pc : IsPathConnected (U ∩ V))
    (hcover : U ∪ V = Set.univ) :
    SimplyConnectedSpace X :=
  simplyConnectedSpace_of_union_eq_univ hU_open hV_open hcover hU_sc hV_sc hinter_pc
