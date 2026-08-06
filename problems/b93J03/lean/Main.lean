import Mathlib

/-!
# APM b93J03

## Statement repairs

The source omits the necessary assumption that `V` is nonzero. It is added as
`[Nontrivial V]`, since the zero vector space has no eigenvector.

## Encoding questions

None. The ordered basis is indexed by `Fin (finrank k V)`, and upper
triangularity is Mathlib's `Matrix.BlockTriangular id` predicate.
-/

theorem apm_b93j03 :
    ∀ (k V : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V]
        [Module k V] [FiniteDimensional k V] [Nontrivial V]
        (A : Set (V →ₗ[k] V)),
      (∀ a ∈ A, ∀ b ∈ A, a.comp b = b.comp a) →
      (∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, ∃ μ : k, a v = μ • v) ∧
      (∃ basis : Module.Basis (Fin (Module.finrank k V)) k V,
        ∀ a ∈ A, (LinearMap.toMatrix basis basis a).BlockTriangular id) := by
  intro k V _ _ _ _ _ _ A hA
  let f : A → Module.End k V := fun a ↦ a.1
  have hcomm : Pairwise fun i j : A ↦ Commute (f i) (f j) := by
    intro i j hij
    change (i.1.comp j.1) = (j.1.comp i.1)
    exact hA i.1 i.2 j.1 j.2
  have hsimultaneousGeneralized :
      ⨆ χ : A → k, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
    apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hcomm
    intro i
    exact Module.End.iSup_maxGenEigenspace_eq_top (f i)
  have hexistsGeneralized :
      ∃ χ : A → k, (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥ := by
    by_contra h
    push_neg at h
    have hz : (⨆ χ : A → k, ⨅ i, (f i).maxGenEigenspace (χ i)) = ⊥ :=
      iSup_eq_bot.mpr h
    rw [hsimultaneousGeneralized] at hz
    exact top_ne_bot hz
  /- PASS-1 boundary: `hsimultaneousGeneralized` establishes the simultaneous
     generalized-eigenspace decomposition for the family indexed by `A`, using
     `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
     and `Module.End.iSup_maxGenEigenspace_eq_top`; `hcomm` discharges its
     compatibility hypothesis from the frozen commutation assumption.
     `hexistsGeneralized` now extracts a nonzero simultaneous generalized
     eigenspace rather than merely leaving the result as a lattice equality.

     I exhaustively searched `Module.End.exists_eigenvalue`, the eigenspace
     `Pi.lean` API, quotient/restriction linear maps, basis flags, and the
     matrix `BlockTriangular` API.  Mathlib's
     `Eigenspace/Triangularizable.lean` explicitly lists defining
     triangularizability and proving its invariant-flag/basis equivalence as
     a TODO.  The remaining first bridge is a local lemma that a commuting
     family of nilpotent restrictions on the selected generalized eigenspace
     has a nonzero common kernel, yielding an ordinary common eigenvector.
     The second is a dimension induction through the quotient by that common
     eigenline, lifting a quotient basis and proving its matrices satisfy
     `Matrix.BlockTriangular id`.  No closed sibling or construction module
     packages either bridge. -/
  sorry
