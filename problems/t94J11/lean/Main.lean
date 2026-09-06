import Mathlib

/-! The quotient is equipped explicitly with the coinduced topology, so the
statement is about the quotient topology specified in the source problem. -/

/-- For an open equivalence relation, its graph is closed exactly when the
quotient is Hausdorff. -/
theorem apm_t94j11
    (X : Type*) [TopologicalSpace X] (r : Setoid X) :
    let quotientTopology : TopologicalSpace (Quotient r) :=
      TopologicalSpace.coinduced Quotient.mk' inferInstance
    @IsOpenMap X (Quotient r) inferInstance quotientTopology Quotient.mk' →
      (IsClosed {p : X × X | r.r p.1 p.2} ↔
        @T2Space (Quotient r) quotientTopology) := by
  sorry
