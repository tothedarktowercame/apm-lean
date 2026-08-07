import Mathlib

/-! # APM t93A03: a connected sum with nontrivial fundamental group

## Statement repairs

None.

## Encoding note

Mathlib has no connected-sum construction for smooth three-manifolds. Since
the claim is purely homotopical, we use the standard deformation-retract spine
of `(S¹ × S²) # (S¹ × S²)`: a wedge of two circles. Unlike the former typed
placeholder, this is an actual quotient topological space with an actual
basepoint. Its fundamental group is stated explicitly as the free group on
two generators.
-/

open FundamentalGroupoid

noncomputable section

inductive apm_t93a03_wedgeRel : Sum Circle Circle → Sum Circle Circle → Prop
  | base : apm_t93a03_wedgeRel (Sum.inl 1) (Sum.inr 1)

def apm_t93a03_connectedSumSpine :=
  Quotient (Relation.EqvGen.setoid apm_t93a03_wedgeRel)

noncomputable instance : TopologicalSpace apm_t93a03_connectedSumSpine :=
  TopologicalSpace.coinduced
    (fun z : Sum Circle Circle ↦
      Quotient.mk (Relation.EqvGen.setoid apm_t93a03_wedgeRel) z)
    inferInstance

def apm_t93a03_basepoint : apm_t93a03_connectedSumSpine :=
  Quotient.mk _ (Sum.inl 1)

lemma apm_t93a03_not_simplyConnected_of_piOne_equiv
    (e : FundamentalGroup apm_t93a03_connectedSumSpine apm_t93a03_basepoint ≃*
      FreeGroup (Fin 2)) :
    ¬SimplyConnectedSpace apm_t93a03_connectedSumSpine := by
  intro hsc
  letI : SimplyConnectedSpace apm_t93a03_connectedSumSpine := hsc
  letI : Subsingleton
      (FundamentalGroup apm_t93a03_connectedSumSpine apm_t93a03_basepoint) :=
    inferInstanceAs
      (Subsingleton
        (Path.Homotopic.Quotient apm_t93a03_basepoint apm_t93a03_basepoint))
  have h := congrArg e
    (Subsingleton.elim (e.symm (FreeGroup.of (0 : Fin 2))) (e.symm 1))
  exact FreeGroup.of_ne_one (0 : Fin 2) (by simpa using h)

theorem apm_t93a03 :
    Nonempty
      (FundamentalGroup apm_t93a03_connectedSumSpine apm_t93a03_basepoint ≃*
        FreeGroup (Fin 2)) ∧
    ¬SimplyConnectedSpace apm_t93a03_connectedSumSpine := by
  /-
  CLOSER HOP 1 boundary. The second conjunct is now reduced completely to the
  first by `apm_t93a03_not_simplyConnected_of_piOne_equiv`: simple connectivity
  makes the based path-homotopy quotient subsingleton, whereas the free
  generator `FreeGroup.of 0` is not the identity.

  The remaining bridge is therefore exactly the fundamental-group computation
  for this quotient wedge. The intended proof identifies the fundamental group
  of each circle with `ℤ` and applies Seifert--van Kampen at their common
  basepoint, obtaining `ℤ * ℤ ≅ FreeGroup (Fin 2)`. Mathlib has path/homotopy
  quotients and product preservation for the fundamental groupoid, but no
  topological Seifert--van Kampen theorem, no wedge/free-product theorem, and
  no packaged `FundamentalGroup Circle 1 ≃* Multiplicative ℤ` computation.

  A direct graph route was also checked: Mathlib defines combinatorial
  `Graph.bouquet`, but does not connect graph realization fundamental groups to
  `FreeGroup`, nor identify this raw quotient with such a realization. Building
  explicit loops and a universal inverse would reproduce van Kampen, including
  subdivision and quotient-continuity bookkeeping.

  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, wedge and
  covering siblings (`t01A03`, `t01A04`, `t01J03`, `t92J05`, `t92J06`,
  `t97A03`), Mathlib's FundamentalGroupoid, SimplyConnected, Circle/AddCircle,
  quotient, graph bouquet, FreeGroup, and categorical/topological van Kampen
  sources, and git history. The categorical `IsVanKampenColimit` API is
  unrelated to the missing topological theorem. No reusable wedge π₁ bridge
  was found.
  -/
  sorry
