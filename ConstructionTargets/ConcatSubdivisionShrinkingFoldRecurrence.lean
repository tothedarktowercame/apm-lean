import ConstructionTargets.ConcatSubdivisionShrinkingFold
import ConstructionTargets.ComposeFinIndexReindex

/-!
# Zero stage and one-step recurrence for shrinking prefix folds
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionShrinkingFoldRecurrence

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionShrinkingPrefix
open ConstructionTargets.ConcatSubdivisionShrinkingFold
open ConstructionTargets.ComposeFinIndexReindex
open ConstructionTargets.ComposeFinAppend

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}
variable {C : Type*} [Category C]

theorem shrinkingVertexEmbedding_zero_stage
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (i : Fin (concatSegmentCount S T + 1)) :
    shrinkingVertexEmbedding S T 0 i = i := by
  apply Fin.ext
  rfl

theorem shrinkingSegmentEmbedding_zero_stage
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (i : Fin (concatSegmentCount S T)) :
    shrinkingSegmentEmbedding S T 0 i = i := by
  apply Fin.ext
  rfl

/-- `composeFin` with one or more arrows is its initial restriction followed
by its terminal arrow.  This wrapper fixes the orientation used below. -/
theorem composeFin_terminal_split {n : ℕ} (A : Fin (n + 2) → C)
    (f : (i : Fin (n + 1)) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin A f =
      TwoOpenDescentDatum.composeFin (A ∘ Fin.castSucc)
          (fun i => f i.castSucc) ≫
        f (Fin.last n) :=
  TwoOpenDescentDatum.composeFin_succ A f

/-- Initial vertex inclusion for the prefix of a positive-length chain. -/
def terminalPrefixVertex {m : ℕ} (hm : 0 < m) :
    Fin (m - 1 + 1) → Fin (m + 1) := fun i => ⟨i, by omega⟩

/-- Initial segment inclusion for the same prefix. -/
def terminalPrefixSegment {m : ℕ} (hm : 0 < m) :
    Fin (m - 1) → Fin m := fun i => ⟨i, by omega⟩

def terminalSegmentIndex {m : ℕ} (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

def terminalStructuralIndex {m : ℕ} (hm : 0 < m) : Fin m :=
  Fin.cast (by omega) (Fin.last (m - 1))

theorem terminalPrefixVertex_zero {m : ℕ} (hm : 0 < m) :
    terminalPrefixVertex hm 0 = (0 : Fin (m + 1)) := by apply Fin.ext; rfl

theorem terminalSegmentIndex_succ {m : ℕ} (hm : 0 < m) :
    (terminalSegmentIndex hm).succ = Fin.last m := by
  apply Fin.ext
  simp [terminalSegmentIndex]
  omega

theorem terminalSegmentIndex_eq_last {m : ℕ} (hm : 0 < m) :
    terminalSegmentIndex hm = terminalStructuralIndex hm := by
  apply Fin.ext
  simp [terminalSegmentIndex]
  simp [terminalStructuralIndex]

/-- A proof-carrying chosen terminal arrow, conjugated to the structural last
index, is exactly the structural last arrow.  Index equality is eliminated
before either dependent arrow is compared. -/
theorem terminalArrow_transport {n : ℕ} (A : Fin (n + 2) → C)
    (f : (i : Fin (n + 1)) → A i.castSucc ⟶ A i.succ)
    (chosen : Fin (n + 1)) (h : chosen = Fin.last n) :
    eqToHom (congrArg A (congrArg Fin.castSucc h)) ≫
        f (Fin.last n) ≫
        eqToHom (congrArg A (congrArg Fin.succ h).symm) =
      f chosen := by
  subst chosen
  simp

theorem terminalPrefixEndpoint_castSucc {m : ℕ} (hm : 0 < m)
    (i : Fin (m - 1)) :
    terminalPrefixVertex hm i.castSucc = (terminalPrefixSegment hm i).castSucc := by
  apply Fin.ext; rfl

theorem terminalPrefixEndpoint_succ {m : ℕ} (hm : 0 < m)
    (i : Fin (m - 1)) :
    terminalPrefixVertex hm i.succ = (terminalPrefixSegment hm i).succ := by
  apply Fin.ext; rfl

def successorChainVertex {m : ℕ} (hm : 0 < m) :
    Fin ((m - 1) + 2) → Fin (m + 1) := fun i => ⟨i, by omega⟩

def successorChainSegment {m : ℕ} (hm : 0 < m) :
    Fin ((m - 1) + 1) → Fin m := fun i => ⟨i, by omega⟩

theorem successorChainEndpoint_castSucc {m : ℕ} (hm : 0 < m)
    (i : Fin ((m - 1) + 1)) :
    successorChainVertex hm i.castSucc =
      (successorChainSegment hm i).castSucc := by
  apply Fin.ext; rfl

theorem successorChainEndpoint_succ {m : ℕ} (hm : 0 < m)
    (i : Fin ((m - 1) + 1)) :
    successorChainVertex hm i.succ =
      (successorChainSegment hm i).succ := by
  apply Fin.ext; rfl

/-- The proof-carrying arrow family of the successor-shaped whole-chain copy.
-/
def successorChainArrow {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ)
    (i : Fin ((m - 1) + 1)) :
    A (successorChainVertex hm i.castSucc) ⟶
      A (successorChainVertex hm i.succ) :=
  eqToHom (congrArg A (successorChainEndpoint_castSucc hm i)) ≫
    f (successorChainSegment hm i) ≫
    eqToHom (congrArg A (successorChainEndpoint_succ hm i)).symm

theorem successorChainArrow_eq {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ)
    (i : Fin ((m - 1) + 1)) :
    successorChainArrow hm A f i =
      eqToHom (congrArg A (successorChainEndpoint_castSucc hm i)) ≫
        f (successorChainSegment hm i) ≫
        eqToHom (congrArg A (successorChainEndpoint_succ hm i)).symm := rfl

theorem successorChainVertex_eq {m : ℕ} (hm : 0 < m)
    (i : Fin ((m - 1) + 2)) :
    successorChainVertex hm i = Fin.cast (by omega) i := by
  apply Fin.ext
  rfl

theorem successorChainSegment_eq {m : ℕ} (hm : 0 < m)
    (i : Fin ((m - 1) + 1)) :
    successorChainSegment hm i = Fin.cast (by omega) i := by
  apply Fin.ext
  rfl

/-- The cast structural last vertex of the successor-shaped presentation is
the literal last vertex of the original chain. -/
theorem successorChainCastLast_eq_last {m : ℕ} (hm : 0 < m) :
    Fin.cast (by omega) (Fin.last (m - 1 + 1)) = Fin.last m := by
  apply Fin.ext
  simp

theorem successorChainCastZero_eq_zero {m : ℕ} (hm : 0 < m) :
    Fin.cast (by omega) (0 : Fin (m - 1 + 2)) = (0 : Fin (m + 1)) := by
  apply Fin.ext
  rfl

def successorChainInitialObjectIso {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C) :
    A (successorChainVertex hm 0) ≅ A 0 :=
  eqToIso (congrArg A
    ((successorChainVertex_eq hm 0).trans
      (successorChainCastZero_eq_zero hm)))

def successorChainLastObjectIso {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C) :
    A (Fin.cast (by omega) (Fin.last (m - 1 + 1))) ≅ A (Fin.last m) :=
  eqToIso (congrArg A (successorChainCastLast_eq_last hm))

def successorChainFinalObjectIso {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C) :
    A (successorChainVertex hm (Fin.last (m - 1 + 1))) ≅ A (Fin.last m) :=
  eqToIso (congrArg A
    ((successorChainVertex_eq hm (Fin.last (m - 1 + 1))).trans
      (successorChainCastLast_eq_last hm)))

theorem eqToHom_inv_comp_trans {ι : Type*} (O : ι → C)
    {a b c : ι} (h : a = b) (k : b = c) :
    eqToHom (congrArg O h).symm ≫ eqToHom (congrArg O (h.trans k)) =
      eqToHom (congrArg O k) := by
  subst b
  subst c
  simp

/-- The final reindex isomorphism from the whole-chain comparison followed by
the cast-last isomorphism is the single composite index transport. -/
theorem successorChain_final_object_transport {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C) :
    (objectIsoOfIndexEq A
        (successorChainVertex_eq hm (Fin.last (m - 1 + 1)))).inv ≫
      (successorChainFinalObjectIso hm A).hom =
    eqToHom (congrArg A (successorChainCastLast_eq_last hm)) := by
  -- Insert the direct successor-vertex-to-last transport; the inverse
  -- reindex transport then cancels its first leg.
  simpa [successorChainFinalObjectIso, objectIsoOfIndexEq] using
    eqToHom_inv_comp_trans A
      (successorChainVertex_eq hm (Fin.last (m - 1 + 1)))
      (successorChainCastLast_eq_last hm)

theorem eqToHom_trans_comp_inv {ι : Type*} (O : ι → C)
    {a b c : ι} (h : a = b) (k : b = c) :
    eqToHom (congrArg O (h.trans k)) ≫ eqToHom (congrArg O k).symm =
      eqToHom (congrArg O h) := by
  subst b
  subst c
  simp

/-- The direct successor-source-to-zero transport followed by the inverse
cast-zero transport is precisely the reindex source transport. -/
theorem successorChain_initial_object_transport {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C) :
    (successorChainInitialObjectIso hm A).hom ≫
      (eqToIso (congrArg A (successorChainCastZero_eq_zero hm))).inv =
    (objectIsoOfIndexEq A (successorChainVertex_eq hm 0)).hom := by
  simpa [successorChainInitialObjectIso, objectIsoOfIndexEq] using
    eqToHom_trans_comp_inv A
      (successorChainVertex_eq hm 0) (successorChainCastZero_eq_zero hm)

theorem dependentArrow_conjugation_fin {m : ℕ}
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ)
    {a b : Fin m} (h : a = b) :
    f a = eqToHom (congrArg A (congrArg Fin.castSucc h)) ≫ f b ≫
      eqToHom (congrArg A (congrArg Fin.succ h)).symm := by
  subst b
  simp

/-- The total fold of the successor-shaped presentation is the original fold,
with only the endpoint isomorphisms produced by its index equality. -/
theorem successorChainComposeFin_eq {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin (A ∘ successorChainVertex hm)
        (successorChainArrow hm A f) =
      (objectIsoOfIndexEq A (successorChainVertex_eq hm 0)).hom ≫
        TwoOpenDescentDatum.composeFin
          (A ∘ fun i : Fin ((m - 1) + 2) => Fin.cast (by omega) i)
          (fun i : Fin ((m - 1) + 1) => f (Fin.cast (by omega) i)) ≫
        (objectIsoOfIndexEq A
          (successorChainVertex_eq hm (Fin.last (m - 1 + 1)))).inv := by
  let r : Fin ((m - 1) + 2) → Fin (m + 1) := fun i => Fin.cast (by omega) i
  let s : Fin ((m - 1) + 2) → Fin (m + 1) := successorChainVertex hm
  have hv : ∀ i, s i = r i := successorChainVertex_eq hm
  have hs : ∀ i : Fin ((m - 1) + 1),
      successorChainSegment hm i = Fin.cast (by omega) i :=
    successorChainSegment_eq hm
  have harr : ∀ i : Fin ((m - 1) + 1),
      successorChainArrow hm A f i =
        (objectIsoOfIndexEq A (hv i.castSucc)).hom ≫
          f (Fin.cast (by omega) i) ≫
          (objectIsoOfIndexEq A (hv i.succ)).inv := by
    intro i
    rw [successorChainArrow_eq]
    rw [dependentArrow_conjugation_fin A f (hs i)]
    exact conjugatedArrow_compose A (f (Fin.cast (by omega) i))
      (successorChainEndpoint_castSucc hm i)
      (congrArg Fin.castSucc (hs i)) (hv i.castSucc)
      (successorChainEndpoint_succ hm i)
      (congrArg Fin.succ (hs i)) (hv i.succ)
  simpa [r, s] using
    (composeFin_reindex_of_index_eq A r s hv
      (fun i => f (Fin.cast (by omega) i))
      (successorChainArrow hm A f) harr)

/-- The cast-indexed copy of a positive-length chain has the same total fold
as the literal chain.  Positivity is eliminated first, so all casts become
same-size casts before the dependent arrow families are compared. -/
theorem castIndexedComposeFin_eq {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin
        (A ∘ fun i : Fin ((m - 1) + 2) => Fin.cast (by omega) i)
        (fun i : Fin ((m - 1) + 1) => f (Fin.cast (by omega) i)) =
      eqToHom (congrArg A (successorChainCastZero_eq_zero hm)) ≫
        TwoOpenDescentDatum.composeFin A f ≫
        eqToHom (congrArg A (successorChainCastLast_eq_last hm)).symm := by
  cases m with
  | zero => omega
  | succ n =>
      change TwoOpenDescentDatum.composeFin A f =
        eqToHom _ ≫ TwoOpenDescentDatum.composeFin A f ≫ eqToHom _
      rw [show successorChainCastZero_eq_zero hm = rfl from
        Subsingleton.elim _ _]
      rw [show successorChainCastLast_eq_last hm = rfl from
        Subsingleton.elim _ _]
      simp

/-- The successor-shaped whole chain splits syntactically into its prefix and
terminal transported arrow. -/
theorem successorChainComposeFin_terminal_split {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin (A ∘ successorChainVertex hm)
        (successorChainArrow hm A f) =
      TwoOpenDescentDatum.composeFin
          ((A ∘ successorChainVertex hm) ∘ Fin.castSucc)
          (fun i => successorChainArrow hm A f i.castSucc) ≫
        successorChainArrow hm A f (Fin.last (m - 1)) := by
  exact composeFin_terminal_split _ _

/-- The source objects of successive stages are canonically equal. -/
def shrinkingPrefixInitialIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) :
    shrinkingPrefixObject D S T r 0 ≅
      shrinkingPrefixObject D S T (r + 1) 0 :=
  eqToIso (by simp [shrinkingPrefixObject])

/-- The last vertex at stage `r+1` is the source of the terminal stage-`r`
arrow. -/
def shrinkingPrefixBoundaryIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r < concatSegmentCount S T) :
    shrinkingPrefixObject D S T (r + 1)
        (Fin.last (concatSegmentCount S T - (r + 1))) ≅
      shrinkingPrefixObject D S T r
        ⟨concatSegmentCount S T - r - 1, by
          omega⟩ :=
  eqToIso (by
    apply congrArg (fun k => D.obj ((concatSubdivision S T).point k))
    apply Fin.ext
    change concatSegmentCount S T - (r + 1) =
      concatSegmentCount S T - r - 1
    omega)

def shrinkingPrefixTerminalIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r < concatSegmentCount S T) :
    shrinkingPrefixObject D S T r
        (⟨concatSegmentCount S T - r - 1, by omega⟩ :
          Fin (concatSegmentCount S T - r)).succ ≅
      shrinkingPrefixObject D S T r
        (Fin.last (concatSegmentCount S T - r)) :=
  eqToIso (by
    apply congrArg (shrinkingPrefixObject D S T r)
    apply Fin.ext
    change concatSegmentCount S T - r - 1 + 1 =
      concatSegmentCount S T - r
    omega)

#print axioms shrinkingVertexEmbedding_zero_stage
#print axioms shrinkingSegmentEmbedding_zero_stage
#print axioms composeFin_terminal_split
#print axioms terminalArrow_transport
#print axioms successorChainComposeFin_eq
#print axioms castIndexedComposeFin_eq
#print axioms successorChainComposeFin_terminal_split
#print axioms successorChain_initial_object_transport
#print axioms successorChainCastLast_eq_last
#print axioms successorChain_final_object_transport
#print axioms shrinkingPrefixInitialIso
#print axioms shrinkingPrefixBoundaryIso
#print axioms shrinkingPrefixTerminalIso

end ConstructionTargets.ConcatSubdivisionShrinkingFoldRecurrence
