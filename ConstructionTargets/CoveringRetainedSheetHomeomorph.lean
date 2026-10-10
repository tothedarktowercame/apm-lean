import ConstructionTargets.CoveringRetainedSheetIndices

open Set Bundle

noncomputable section

namespace ConstructionTargets.CoveringRetainedSheetHomeomorph

open ConstructionTargets.CoveringRetainedSheetIndices

universe u v w

variable {E : Type u} {B : Type v} {F : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
variable {p : E → B}

local instance retainedIndexTopologicalSpace
    (t : Trivialization F p) (C : Set E) (b : B) (hb : b ∈ t.baseSet) :
    TopologicalSpace (RetainedIndex t C b hb) :=
  TopologicalSpace.induced Subtype.val inferInstance

abbrev RestrictedSource (t : Trivialization F p) (C : Set E) :=
  {z : C // p z.1 ∈ t.baseSet}

/-- A path-connected trivialization restricts over a clopen source subset to
exactly the sheets whose center points lie in that subset. -/
noncomputable def retainedSheetHomeomorph
    (t : Trivialization F p) (C : Set E) (hC : IsClopen C)
    (hpath : IsPathConnected t.baseSet)
    (b : B) (hb : b ∈ t.baseSet) :
    RestrictedSource t C ≃ₜ t.baseSet × RetainedIndex t C b hb where
  toFun z :=
    (⟨p z.1.1, z.2⟩,
      ⟨(t z.1.1).2, by
        rw [← invFun_mem_iff_retained t C hC hpath b hb]
        · have hinv : t.invFun (p z.1.1, (t z.1.1).2) = z.1.1 := by
            exact t.symm_apply_mk_proj (t.mem_source.mpr z.2)
          rw [hinv]
          exact z.1.2
        · exact z.2⟩)
  invFun yi :=
    ⟨⟨t.invFun (yi.1.1, yi.2.1), by
        rw [invFun_mem_iff_retained t C hC hpath b hb]
        · exact yi.2.2
        · exact yi.1.2⟩,
      by
        change p (t.toPartialEquiv.symm (yi.1.1, yi.2.1)) ∈ t.baseSet
        have hp : p (t.toPartialEquiv.symm (yi.1.1, yi.2.1)) = yi.1.1 :=
          t.proj_symm_apply' (x := yi.2.1) yi.1.2
        exact hp.symm ▸ yi.1.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change t.invFun (p z.1.1, (t z.1.1).2) = z.1.1
    exact t.symm_apply_mk_proj (t.mem_source.mpr z.2)
  right_inv yi := by
    apply Prod.ext
    · apply Subtype.ext
      exact t.proj_symm_apply
        (show (yi.1.1, yi.2.1) ∈ t.target from t.mem_target.mpr yi.1.2)
    · apply Subtype.ext
      exact congrArg Prod.snd (t.right_inv
        (show (yi.1.1, yi.2.1) ∈ t.target from t.mem_target.mpr yi.1.2))
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (continuous_fst.comp
        (t.continuousOn_toFun.comp_continuous (by fun_prop)
          (fun (z : RestrictedSource t C) => t.mem_source.mpr z.2))).congr
        (fun z => t.coe_fst (t.mem_source.mpr z.2))
    · apply Continuous.subtype_mk
      exact continuous_snd.comp
        (t.continuousOn_toFun.comp_continuous (by fun_prop)
          (fun (z : RestrictedSource t C) => t.mem_source.mpr z.2))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact t.continuousOn_invFun.comp_continuous
      (continuous_subtype_val.comp continuous_fst |>.prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun yi => t.mem_target.mpr yi.1.2)

#print axioms retainedSheetHomeomorph

end ConstructionTargets.CoveringRetainedSheetHomeomorph
