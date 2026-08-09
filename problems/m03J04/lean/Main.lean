import Mathlib

/-! # APM m03J04: adjoints, annihilators, and an inf-sup condition

## Statement repairs

The displayed supremum divides by `‖w‖` while quantifying over all `w`, including
zero.  The standard inf-sup expression, and the one used below, ranges over
`w ≠ 0`.
-/

noncomputable section

/-- The adjoint defined by transposing the bilinear pairing. -/
def dualAdjoint {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) : W →L[ℝ] V →L[ℝ] ℝ :=
  B.flip

/-- Functionals vanishing on a subset. -/
def dualAnnihilator {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (U : Set W) :
    Submodule ℝ (W →L[ℝ] ℝ) :=
  ⨅ w : U, ((ContinuousLinearMap.apply ℝ ℝ) w.1).ker

/-- Every element in the range annihilates the kernel of the transposed pairing. -/
lemma apm_m03J04_range_subset_dualAnnihilator
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) :
    (B.range : Set (W →L[ℝ] ℝ)) ⊆
      (dualAnnihilator ((dualAdjoint B).ker : Set W) : Set (W →L[ℝ] ℝ)) := by
  rintro f ⟨v, rfl⟩
  change B v ∈ dualAnnihilator ((dualAdjoint B).ker : Set W)
  rw [dualAnnihilator, Submodule.mem_iInf]
  intro w
  change B v w.1 = 0
  have hw : dualAdjoint B w.1 = 0 := w.2
  exact DFunLike.congr_fun hw v

/-- The range inclusion persists after closure because the annihilator is an
intersection of closed evaluation kernels. -/
lemma apm_m03J04_closure_range_subset_dualAnnihilator
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) :
    closure (B.range : Set (W →L[ℝ] ℝ)) ⊆
      (dualAnnihilator ((dualAdjoint B).ker : Set W) : Set (W →L[ℝ] ℝ)) := by
  have hclosed :
      IsClosed (dualAnnihilator ((dualAdjoint B).ker : Set W) :
        Set (W →L[ℝ] ℝ)) := by
    unfold dualAnnihilator
    convert isClosed_iInter fun w : (dualAdjoint B).ker ↦
      ContinuousLinearMap.isClosed_ker ((ContinuousLinearMap.apply ℝ ℝ) w.1)
    simp
  exact hclosed.closure_subset_iff.2
    (apm_m03J04_range_subset_dualAnnihilator B)

/-- Why this unblocks the closure identity in `apm_m03j04`: this is the
missing Hahn--Banach/Riesz density direction, identifying the custom
intersection of evaluation kernels with the closure of the represented
functionals. The reverse inclusion is already proved above. -/
theorem apm_m03J04_bridge_1
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) :
    (dualAnnihilator ((dualAdjoint B).ker : Set W) :
        Set (W →L[ℝ] ℝ)) ⊆
      closure (B.range : Set (W →L[ℝ] ℝ)) := by
  sorry

/-- Why this unblocks the inf--sup clause of `apm_m03j04`: after rewriting
the signed homogeneous supremum as the operator norm, the lower bound makes
`B` injective with closed range; the density identity then identifies that
range with the annihilator and supplies the bounded inverse. -/
theorem apm_m03J04_bridge_2
    {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] W →L[ℝ] ℝ)
    (hinfsup : ∃ α : ℝ, 0 < α ∧ ∀ v : V,
      sSup {r : ℝ | ∃ w : W, w ≠ 0 ∧ r = B v w / ‖w‖} ≥ α * ‖v‖) :
    ∃ e : V ≃L[ℝ]
        dualAnnihilator ((dualAdjoint B).ker : Set W),
      ∀ v : V, (e v).1 = B v := by
  sorry

/-- All four parts: continuity and involutivity of the adjoint, closedness of
annihilators, the closure-of-range identity, and the inf-sup isomorphism. -/
theorem apm_m03j04
    (V W : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) :
    dualAdjoint (dualAdjoint B) = B ∧
    (∀ U : Set W, IsClosed (dualAnnihilator U : Set (W →L[ℝ] ℝ))) ∧
    closure (B.range : Set (W →L[ℝ] ℝ)) =
      (dualAnnihilator ((dualAdjoint B).ker : Set W) : Set (W →L[ℝ] ℝ)) ∧
    ((∃ α : ℝ, 0 < α ∧ ∀ v : V,
      sSup {r : ℝ | ∃ w : W, w ≠ 0 ∧ r = B v w / ‖w‖} ≥ α * ‖v‖) →
      ∃ e : V ≃L[ℝ]
          dualAnnihilator ((dualAdjoint B).ker : Set W),
        ∀ v : V, (e v).1 = B v) := by
  constructor
  · rfl
  constructor
  · intro U
    unfold dualAnnihilator
    convert isClosed_iInter fun w : U ↦
      ContinuousLinearMap.isClosed_ker ((ContinuousLinearMap.apply ℝ ℝ) w.1)
    simp
  · /-
    Boundary for the closed-range and inf-sup clauses. The definitional
    double-flip identity and closedness of annihilators as intersections of
    evaluation kernels are compiled above.

    The remaining closure identity needs the Hahn–Banach annihilator theorem
    together with the Hilbert reflexivity equivalence identifying continuous
    functionals on `W →L[ℝ] ℝ` with evaluation at points of `W`. The final
    clause then requires rewriting the signed `sSup` as `‖B v‖`, deriving a
    bounded-below estimate, proving `B.range` closed, and packaging the
    restricted map and its bounded inverse as a `ContinuousLinearEquiv` into
    the subtype `dualAnnihilator ...`. Searches found no single compiled
    closed-range theorem with these exact dual/subtype conventions. No sibling
    code was reused, and the frozen statement was left unchanged.

    Closer hop 1 proves `apm_m03J04_range_subset_dualAnnihilator` above, closing
    the algebraic inclusion before taking closure. Searches also found
    `ContinuousLinearMap.orthogonal_ker`,
    `Submodule.orthogonal_orthogonal_eq_closure`, the algebraic
    `Submodule.dualCoannihilator_range_eq_ker_flip`, and the bounded-below
    closed-range API in `Analysis/Normed/Operator/Banach.lean`. The unresolved
    bridge is transporting the first two Hilbert-space theorems across
    `InnerProductSpace.toDual` so that their orthogonal complements coincide
    with this file's intersection-of-evaluation-kernels `dualAnnihilator`.
    After that, the signed `sSup` still must be identified with the operator
    norm to feed the antilipschitz/closed-range machinery.

    Closer hop 2 found `ContinuousLinearMap.sSup_sphere_eq_norm` in
    `Analysis/Normed/Operator/NNNorm.lean`.  It proves exactly that the supremum
    of `‖f w‖` over the unit sphere is `‖f‖`.  The frozen signed homogeneous
    quotient reduces to this theorem by normalizing every `w ≠ 0`; in the
    reverse comparison, replace a unit vector by its negative when `f w < 0`,
    so the absolute value is attained as a signed value.  Thus the norm bridge
    no longer needs to be developed from `csSup` bounds from scratch.

    The closure identity remains open. Inspection of
    `ContinuousLinearMap.orthogonal_ker` confirms its exact output
    `T.kerᗮ = T†.range.topologicalClosure`, but applying it here still requires
    constructing the Riesz-conjugated operator whose adjoint is definitionally
    compatible with `B.flip`, and proving that Riesz transport sends this
    file's evaluation-kernel intersection to the Hilbert orthogonal. Searches
    of all closed artifacts and construction libraries found no such transport
    lemma. Once that identity is available, the sphere-supremum theorem and
    Banach closed-range APIs provide the remaining inf-sup equivalence route.

    Closer hop 3 extracts
    `apm_m03J04_closure_range_subset_dualAnnihilator`: closedness of the
    intersection of evaluation kernels upgrades the earlier algebraic range
    inclusion to the full closure inclusion. Thus only the reverse (density)
    inclusion needs the Riesz/orthogonal transport. Additional searches of the
    Riesz, adjoint, dual-annihilator, and closed-range APIs found no theorem
    identifying this custom evaluation-kernel intersection with the relevant
    Hilbert orthogonal, so that density bridge and the subsequent inf-sup
    equivalence remain open.
    -/
    sorry
