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

/-- The operator represented by the bilinear form under the real Riesz equivalence. -/
def rieszOperator {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) : V →L[ℝ] W :=
  (InnerProductSpace.toDual ℝ W).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

@[simp] lemma inner_rieszOperator {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) (v : V) (w : W) :
    inner ℝ (rieszOperator B v) w = B v w := by
  exact InnerProductSpace.toDual_symm_apply

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
  intro f hf
  let T : V →L[ℝ] W := rieszOperator B
  let x : W := (InnerProductSpace.toDual ℝ W).symm f
  have hxker : x ∈ T.adjoint.kerᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    have hw' : dualAdjoint B w = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      change B v w = 0
      have hw0 : T.adjoint w = 0 := hw
      have hz := congrArg (fun z : V ↦ inner ℝ v z) hw0
      calc
        B v w = inner ℝ (T v) w := (inner_rieszOperator B v w).symm
        _ = inner ℝ w (T v) := real_inner_comm _ _
        _ = inner ℝ (T.adjoint w) v := (T.adjoint_inner_left v w).symm
        _ = inner ℝ v (T.adjoint w) := real_inner_comm _ _
        _ = 0 := by simpa using hz
    have hfw : f w = 0 := by
      change f ∈ dualAnnihilator ((dualAdjoint B).ker : Set W) at hf
      rw [dualAnnihilator, Submodule.mem_iInf] at hf
      exact hf ⟨w, hw'⟩
    simpa [x, InnerProductSpace.toDual_symm_apply] using hfw
  have hxcl : x ∈ closure (T.range : Set W) := by
    rw [ContinuousLinearMap.orthogonal_ker,
      ContinuousLinearMap.adjoint_adjoint] at hxker
    exact hxker
  have himage : (InnerProductSpace.toDual ℝ W) x ∈
      closure ((InnerProductSpace.toDual ℝ W) '' (T.range : Set W)) :=
    image_closure_subset_closure_image
      (InnerProductSpace.toDual ℝ W).continuous ⟨x, hxcl, rfl⟩
  have hrange : (InnerProductSpace.toDual ℝ W) '' (T.range : Set W) =
      (B.range : Set (W →L[ℝ] ℝ)) := by
    ext g
    constructor
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      refine ⟨v, ?_⟩
      apply ContinuousLinearMap.ext
      intro w
      exact (inner_rieszOperator B v w).symm
    · rintro ⟨v, rfl⟩
      refine ⟨T v, ⟨v, rfl⟩, ?_⟩
      apply ContinuousLinearMap.ext
      intro w
      exact inner_rieszOperator B v w
  rw [hrange] at himage
  simpa [x] using himage

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
  obtain ⟨α, hα, hbound⟩ := hinfsup
  have hnorm : ∀ v : V, α * ‖v‖ ≤ ‖B v‖ := by
    intro v
    refine (hbound v).trans ?_
    by_cases hW : Nontrivial W
    · letI : Nontrivial W := hW
      apply csSup_le
      · obtain ⟨w, hw⟩ := exists_ne (0 : W)
        exact ⟨B v w / ‖w‖, w, hw, rfl⟩
      · rintro r ⟨w, hw, rfl⟩
        calc
          B v w / ‖w‖ ≤ |B v w / ‖w‖| := le_abs_self _
          _ = ‖B v w‖ / ‖w‖ := by rw [abs_div, abs_norm, ← Real.norm_eq_abs]
          _ ≤ ‖B v‖ := (div_le_iff₀ (norm_pos_iff.mpr hw)).2 (by
            simpa using (B v).le_opNorm w)
    · haveI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
      have hempty : {r : ℝ | ∃ w : W, w ≠ 0 ∧ r = B v w / ‖w‖} = ∅ := by
        ext r
        constructor
        · rintro ⟨w, hw, -⟩
          exact hw (Subsingleton.elim w 0)
        · intro hr
          contradiction
      rw [hempty, Real.sSup_empty]
      exact norm_nonneg _
  have hinj : Function.Injective B := by
    intro v₁ v₂ hv
    apply sub_eq_zero.mp
    have hzero : B (v₁ - v₂) = 0 := by simpa using sub_eq_zero.mpr hv
    have := hnorm (v₁ - v₂)
    rw [hzero, norm_zero] at this
    have : ‖v₁ - v₂‖ = 0 := by nlinarith [norm_nonneg (v₁ - v₂)]
    exact norm_eq_zero.mp this
  have hanti : ∃ K, AntilipschitzWith K B :=
    antilipschitzWith_iff_exists_mul_le_norm.mpr ⟨α, hα, hnorm⟩
  have hclosed : IsClosed (B.range : Set (W →L[ℝ] ℝ)) :=
    (B.isClosed_range_iff_antilipschitz_of_injective hinj).2 hanti
  have hrange : (B.range : Set (W →L[ℝ] ℝ)) =
      (dualAnnihilator ((dualAdjoint B).ker : Set W) : Set (W →L[ℝ] ℝ)) := by
    rw [← hclosed.closure_eq]
    exact Set.Subset.antisymm (apm_m03J04_closure_range_subset_dualAnnihilator B)
      (apm_m03J04_bridge_1 B)
  have hrangeSubmodule : B.range = dualAnnihilator ((dualAdjoint B).ker : Set W) :=
    SetLike.ext' hrange
  let e : V ≃L[ℝ] dualAnnihilator ((dualAdjoint B).ker : Set W) := by
    exact (B.equivRange hinj hclosed).trans
      (ContinuousLinearEquiv.ofEq B.range
        (dualAnnihilator ((dualAdjoint B).ker : Set W)) hrangeSubmodule)
  refine ⟨e, ?_⟩
  intro v
  rfl

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
  · -- The two analytic bridges above supply the closure and inf--sup clauses.
    constructor
    · exact Set.Subset.antisymm
        (apm_m03J04_closure_range_subset_dualAnnihilator B)
        (apm_m03J04_bridge_1 B)
    · exact apm_m03J04_bridge_2 B
