import ConstructionTargets.ConcatSubdivisionShrinkingFold
import ConstructionTargets.ComposeFinIndexReindex
import ConstructionTargets.ComposeFinConjugation

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
open ConstructionTargets.ConcatSubdivisionRightSuffix
open ConstructionTargets.ConcatSubdivisionRightFold
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

theorem successorChainSegment_last_eq_terminal {m : ℕ} (hm : 0 < m) :
    successorChainSegment hm (Fin.last (m - 1)) =
      terminalSegmentIndex hm := by
  apply Fin.ext
  simp [successorChainSegment, terminalSegmentIndex]

theorem successorChainLastSource_eq_terminal {m : ℕ} (hm : 0 < m) :
    successorChainVertex hm (Fin.last (m - 1)).castSucc =
      (terminalSegmentIndex hm).castSucc := by
  rw [successorChainEndpoint_castSucc]
  exact congrArg Fin.castSucc (successorChainSegment_last_eq_terminal hm)

/-- The exposed successor-chain terminal arrow, followed by its final-object
coordinate, is the literal terminal arrow with its source and target
transports displayed. -/
theorem successorChain_terminal_arrow_normalization {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ) :
    successorChainArrow hm A f (Fin.last (m - 1)) ≫
        (successorChainFinalObjectIso hm A).hom =
      eqToHom (congrArg A (successorChainLastSource_eq_terminal hm)) ≫
        f (terminalSegmentIndex hm) ≫
        eqToHom (congrArg A (terminalSegmentIndex_succ hm)) := by
  cases m with
  | zero => omega
  | succ n =>
      simp [successorChainArrow, successorChainFinalObjectIso,
        successorChainVertex, successorChainSegment, terminalSegmentIndex]

/-- The literal original fold in successor-shaped coordinates, with only the
direct initial and final object isomorphisms remaining. -/
theorem composeFin_eq_successorChain {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin A f =
      (successorChainInitialObjectIso hm A).inv ≫
        TwoOpenDescentDatum.composeFin (A ∘ successorChainVertex hm)
          (successorChainArrow hm A f) ≫
        (successorChainFinalObjectIso hm A).hom := by
  rw [successorChainComposeFin_eq, castIndexedComposeFin_eq]
  simp [successorChainInitialObjectIso, successorChainFinalObjectIso,
    objectIsoOfIndexEq]
  assumption

/-- Original-coordinate terminal split, retaining the single direct initial
and final coordinate isomorphisms around the syntactic prefix and terminal
arrow. -/
theorem composeFin_terminal_split_of_pos {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin A f =
      (successorChainInitialObjectIso hm A).inv ≫
        (TwoOpenDescentDatum.composeFin
            ((A ∘ successorChainVertex hm) ∘ Fin.castSucc)
            (fun i => successorChainArrow hm A f i.castSucc) ≫
          successorChainArrow hm A f (Fin.last (m - 1))) ≫
        (successorChainFinalObjectIso hm A).hom := by
  rw [composeFin_eq_successorChain hm A f,
    successorChainComposeFin_terminal_split]
  simp [Category.assoc]

/-- Original-coordinate positive-length split with the exposed terminal arrow
literally `f (terminalSegmentIndex hm)`. -/
theorem composeFin_terminal_split_of_pos_literal {m : ℕ} (hm : 0 < m)
    (A : Fin (m + 1) → C)
    (f : (i : Fin m) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin A f =
      (successorChainInitialObjectIso hm A).inv ≫
        TwoOpenDescentDatum.composeFin
          ((A ∘ successorChainVertex hm) ∘ Fin.castSucc)
          (fun i => successorChainArrow hm A f i.castSucc) ≫
        eqToHom (congrArg A (successorChainLastSource_eq_terminal hm)) ≫
        f (terminalSegmentIndex hm) ≫
        eqToHom (congrArg A (terminalSegmentIndex_succ hm)) := by
  rw [composeFin_terminal_split_of_pos hm A f]
  simpa only [Category.assoc] using congrArg
    (fun k => (successorChainInitialObjectIso hm A).inv ≫
      TwoOpenDescentDatum.composeFin
        ((A ∘ successorChainVertex hm) ∘ Fin.castSucc)
        (fun i => successorChainArrow hm A f i.castSucc) ≫ k)
    (successorChain_terminal_arrow_normalization hm A f)

/-- The literal positive-length split specialized to a shrinking prefix
stage. -/
theorem shrinkingPrefixFold_terminal_split_literal
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r < concatSegmentCount S T) :
    shrinkingPrefixFold D S T r =
      (successorChainInitialObjectIso (Nat.sub_pos_of_lt hr)
          (shrinkingPrefixObject D S T r)).inv ≫
        TwoOpenDescentDatum.composeFin
          (((shrinkingPrefixObject D S T r) ∘
              successorChainVertex (Nat.sub_pos_of_lt hr)) ∘ Fin.castSucc)
          (fun i => successorChainArrow (Nat.sub_pos_of_lt hr)
            (shrinkingPrefixObject D S T r)
            (shrinkingPrefixArrow D S T r) i.castSucc) ≫
        eqToHom (congrArg (shrinkingPrefixObject D S T r)
          (successorChainLastSource_eq_terminal (Nat.sub_pos_of_lt hr))) ≫
        shrinkingPrefixArrow D S T r
          (terminalSegmentIndex (Nat.sub_pos_of_lt hr)) ≫
        eqToHom (congrArg (shrinkingPrefixObject D S T r)
          (terminalSegmentIndex_succ (Nat.sub_pos_of_lt hr))) := by
  exact composeFin_terminal_split_of_pos_literal (Nat.sub_pos_of_lt hr)
    (shrinkingPrefixObject D S T r) (shrinkingPrefixArrow D S T r)

/-- While the terminal arrow remains in the right block, its generic positive
length coordinate is the decreasing literal `rightSegment` coordinate. -/
theorem shrinkingTerminalSegment_eq_rightSegment
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) (hr : r ≤ T.n) :
    shrinkingSegmentEmbedding S T r
        (terminalSegmentIndex (by
          exact Nat.sub_pos_of_lt
            (by simp [concatSegmentCount]; omega))) =
      rightSegment S T ⟨T.n - r, by omega⟩ := by
  let hp : 0 < concatSegmentCount S T - r := Nat.sub_pos_of_lt
    (by simp [concatSegmentCount]; omega)
  have hi : terminalSegmentIndex hp =
      (⟨concatSegmentCount S T - r - 1, by omega⟩ :
        Fin (concatSegmentCount S T - r)) := by
    apply Fin.ext
    rfl
  change shrinkingSegmentEmbedding S T r (terminalSegmentIndex hp) = _
  rw [hi]
  exact shrinkingSegment_last_eq_rightSegment S T r hr

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

/-- Vertex-level identification of the successor-shaped displayed prefix with
stage `r+1`. -/
theorem shrinkingSuccessorPrefixVertex_eq
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T)
    (i : Fin (concatSegmentCount S T - (r + 1) + 1)) :
    shrinkingVertexEmbedding S T r
        (successorChainVertex (Nat.sub_pos_of_lt (by omega))
          (Fin.cast (by omega) i).castSucc) =
      shrinkingVertexEmbedding S T (r + 1) i := by
  apply Fin.ext
  rfl

/-- Segment-level identification for the same prefix. -/
theorem shrinkingSuccessorPrefixSegment_eq
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T)
    (i : Fin (concatSegmentCount S T - (r + 1))) :
    shrinkingSegmentEmbedding S T r
        (successorChainSegment (Nat.sub_pos_of_lt (by omega))
          (Fin.cast (by omega) i).castSucc) =
      shrinkingSegmentEmbedding S T (r + 1) i := by
  apply Fin.ext
  rfl

/-- The displayed successor-prefix arrow, reindexed to the stage-`r+1`
segment coordinate. -/
def shrinkingSuccessorPrefixArrow
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T)
    (i : Fin (concatSegmentCount S T - (r + 1))) :=
  successorChainArrow (Nat.sub_pos_of_lt (by omega))
    (shrinkingPrefixObject D S T r) (shrinkingPrefixArrow D S T r)
    (Fin.cast (by omega) i).castSucc

theorem shrinkingSuccessorPrefixArrow_eq_conjugate
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T)
    (i : Fin (concatSegmentCount S T - (r + 1))) :
    shrinkingSuccessorPrefixArrow D S T r hr i =
      eqToHom (congrArg
          (fun k => D.obj ((concatSubdivision S T).point k))
          (shrinkingSuccessorPrefixVertex_eq S T r hr i.castSucc)) ≫
        shrinkingPrefixArrow D S T (r + 1) i ≫
        eqToHom (congrArg
          (fun k => D.obj ((concatSubdivision S T).point k))
          (shrinkingSuccessorPrefixVertex_eq S T r hr i.succ)).symm := by
  unfold shrinkingSuccessorPrefixArrow successorChainArrow
  unfold shrinkingPrefixArrow shrinkingPrefixObject
  rw [dependentArrow_conjugation
    (fun k => D.obj ((concatSubdivision S T).point k))
    (D.mappedPiece (concatSubdivision S T))
    (shrinkingSuccessorPrefixSegment_eq S T r hr i)]
  exact whisker_conjugatedArrow_compose
    (fun k => D.obj ((concatSubdivision S T).point k))
    (D.mappedPiece (concatSubdivision S T)
      (shrinkingSegmentEmbedding S T (r + 1) i))
    (by apply Fin.ext; rfl) (by apply Fin.ext; rfl) (by apply Fin.ext; rfl)
    (by apply Fin.ext; rfl) (by apply Fin.ext; rfl) (by apply Fin.ext; rfl)
    (l := _) (r := _)

/-- Whole-fold comparison between the successor-shaped displayed prefix and
stage `r+1`, with the two endpoint transports retained. -/
theorem shrinkingSuccessorPrefixFold_eq
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T) :
    TwoOpenDescentDatum.composeFin
        (fun i : Fin (concatSegmentCount S T - (r + 1) + 1) =>
          D.obj ((concatSubdivision S T).point
            (shrinkingVertexEmbedding S T r
              (successorChainVertex (Nat.sub_pos_of_lt (by omega))
                (Fin.cast (by omega) i).castSucc))))
        (shrinkingSuccessorPrefixArrow D S T r hr) =
      (objectIsoOfIndexEq
        (fun k => D.obj ((concatSubdivision S T).point k))
        (shrinkingSuccessorPrefixVertex_eq S T r hr 0)).hom ≫
      shrinkingPrefixFold D S T (r + 1) ≫
      (objectIsoOfIndexEq
        (fun k => D.obj ((concatSubdivision S T).point k))
        (shrinkingSuccessorPrefixVertex_eq S T r hr
          (Fin.last (concatSegmentCount S T - (r + 1))))).inv := by
  let O := fun k => D.obj ((concatSubdivision S T).point k)
  let newVertex := fun i : Fin (concatSegmentCount S T - (r + 1) + 1) =>
    shrinkingVertexEmbedding S T (r + 1) i
  let shownVertex := fun i : Fin (concatSegmentCount S T - (r + 1) + 1) =>
    shrinkingVertexEmbedding S T r
      (successorChainVertex (Nat.sub_pos_of_lt (by omega))
        (Fin.cast (by omega) i).castSucc)
  have hv : ∀ i, shownVertex i = newVertex i :=
    shrinkingSuccessorPrefixVertex_eq S T r hr
  have h := composeFin_reindex_of_index_eq O newVertex shownVertex hv
    (shrinkingPrefixArrow D S T (r + 1))
    (shrinkingSuccessorPrefixArrow D S T r hr)
    (shrinkingSuccessorPrefixArrow_eq_conjugate D S T r hr)
  simpa [shrinkingPrefixFold, shrinkingPrefixObject, O, newVertex,
    shownVertex] using h

/-- The syntactic prefix emitted by the positive-length terminal split is the
stage-sized displayed successor prefix.  The casts connecting the two `Fin`
presentations are kept in the index maps and discharged through the generic
whole-chain reindex theorem. -/
theorem shrinkingSyntacticSuccessorPrefixFold_eq
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T) :
    TwoOpenDescentDatum.composeFin
        (((shrinkingPrefixObject D S T r) ∘
            successorChainVertex (Nat.sub_pos_of_lt (by omega))) ∘ Fin.castSucc)
        (fun i => successorChainArrow (Nat.sub_pos_of_lt (by omega))
          (shrinkingPrefixObject D S T r)
          (shrinkingPrefixArrow D S T r) i.castSucc) =
      (objectIsoOfIndexEq
        (fun k : Fin (concatSegmentCount S T - (r + 1) + 1) =>
          D.obj ((concatSubdivision S T).point
            (shrinkingVertexEmbedding S T r
              (successorChainVertex (Nat.sub_pos_of_lt (by omega))
                k.castSucc))))
        (show (0 : Fin _) = Fin.cast (by omega) 0 by apply Fin.ext; rfl)).hom ≫
      TwoOpenDescentDatum.composeFin
        (fun i : Fin (concatSegmentCount S T - (r + 1) + 1) =>
          D.obj ((concatSubdivision S T).point
            (shrinkingVertexEmbedding S T r
              (successorChainVertex (Nat.sub_pos_of_lt (by omega))
                (Fin.cast (by omega) i).castSucc))))
        (shrinkingSuccessorPrefixArrow D S T r hr) ≫
      (objectIsoOfIndexEq
        (fun k : Fin (concatSegmentCount S T - (r + 1) + 1) =>
          D.obj ((concatSubdivision S T).point
            (shrinkingVertexEmbedding S T r
              (successorChainVertex (Nat.sub_pos_of_lt (by omega))
                k.castSucc))))
        (show (Fin.last _ : Fin _) = Fin.cast (by omega) (Fin.last _) by
          apply Fin.ext; rfl)).inv := by
  let O := fun k : Fin (concatSegmentCount S T - (r + 1) + 1) =>
    D.obj ((concatSubdivision S T).point
      (shrinkingVertexEmbedding S T r
        (successorChainVertex (Nat.sub_pos_of_lt (by omega)) k.castSucc)))
  let oldVertex := fun i : Fin (concatSegmentCount S T - (r + 1) + 1) => i
  let castVertex := fun i : Fin (concatSegmentCount S T - (r + 1) + 1) =>
    (Fin.cast (by omega) i : Fin (concatSegmentCount S T - (r + 1) + 1))
  have hv : ∀ i, oldVertex i = castVertex i := by
    intro i
    apply Fin.ext
    rfl
  let g : (i : Fin (concatSegmentCount S T - (r + 1))) →
      O i.castSucc ⟶ O i.succ := fun i =>
    successorChainArrow (Nat.sub_pos_of_lt (by omega))
      (shrinkingPrefixObject D S T r)
      (shrinkingPrefixArrow D S T r) i.castSucc
  have ha : ∀ i : Fin (concatSegmentCount S T - (r + 1)),
      g i =
        (objectIsoOfIndexEq O (hv i.castSucc)).hom ≫
          shrinkingSuccessorPrefixArrow D S T r hr i ≫
          (objectIsoOfIndexEq O (hv i.succ)).inv := by
    intro i
    have hi : (Fin.cast (by omega) i :
        Fin (concatSegmentCount S T - (r + 1))) = i := by
      apply Fin.ext
      rfl
    cases hi
    have h₀ : castVertex i.castSucc = oldVertex i.castSucc := by
      apply Fin.ext
      rfl
    have h₁ : castVertex i.succ = oldVertex i.succ := by
      apply Fin.ext
      rfl
    cases h₀
    cases h₁
    change g i = _
    change g i = (objectIsoOfIndexEq O (hv i.castSucc)).hom ≫
      g i ≫ (objectIsoOfIndexEq O (hv i.succ)).inv
    calc
      g i = eqToHom (congrArg O
            (rfl : oldVertex i.castSucc = oldVertex i.castSucc)) ≫
          g i ≫ eqToHom (congrArg O
            (rfl : oldVertex i.succ = oldVertex i.succ)).symm := by simp
      _ = eqToHom (congrArg O (hv i.castSucc)) ≫
          g i ≫ eqToHom (congrArg O (hv i.succ)).symm :=
        conjugatedArrow_proof_irrel O (g i)
          (rfl : oldVertex i.castSucc = oldVertex i.castSucc)
          (hv i.castSucc)
          (rfl : oldVertex i.succ = oldVertex i.succ)
          (hv i.succ)
  have h := composeFin_reindex_of_index_eq O castVertex oldVertex hv
    (shrinkingSuccessorPrefixArrow D S T r hr)
    g ha
  simpa only [O, oldVertex, castVertex, g] using h

theorem eqToHom_three_step_coherence
    {A B C₀ D₀ : C}
    (h₁ : A = B) (h₂ : B = C₀) (h₃ : C₀ = D₀)
    (h : A = D₀) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ =
      eqToHom h := by
  subst B
  subst C₀
  subst D₀
  simp

/-- The three initial-object transports produced by the terminal split and
the two whole-chain reindexings are the named initial-stage transport. -/
theorem shrinkingPrefix_initial_transport_coherence
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T) :
    (successorChainInitialObjectIso (Nat.sub_pos_of_lt (by omega))
        (shrinkingPrefixObject D S T r)).inv ≫
      (objectIsoOfIndexEq
        (fun k : Fin (concatSegmentCount S T - (r + 1) + 1) =>
          D.obj ((concatSubdivision S T).point
            (shrinkingVertexEmbedding S T r
              (successorChainVertex (Nat.sub_pos_of_lt (by omega))
                k.castSucc))))
        (show (0 : Fin _) = Fin.cast (by omega) 0 by
          apply Fin.ext
          rfl)).hom ≫
      (objectIsoOfIndexEq
        (fun k => D.obj ((concatSubdivision S T).point k))
        (shrinkingSuccessorPrefixVertex_eq S T r hr 0)).hom =
      (shrinkingPrefixInitialIso D S T r).hom := by
  simp only [successorChainInitialObjectIso, objectIsoOfIndexEq,
    shrinkingPrefixInitialIso]
  apply eqToHom_three_step_coherence
  · unfold shrinkingPrefixObject
    congr 2
  · unfold shrinkingPrefixObject
    congr 2
  · congr 2
  · unfold shrinkingPrefixObject
    congr 2

/-- The initial transport coherence in the association produced by
substituting the two whole-fold comparisons. -/
theorem shrinkingPrefix_initial_transport_whisker
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T)
    {W : C} (f : shrinkingPrefixObject D S T (r + 1) 0 ⟶ W) :
    (successorChainInitialObjectIso (Nat.sub_pos_of_lt (by omega))
        (shrinkingPrefixObject D S T r)).inv ≫
      ((objectIsoOfIndexEq
          (fun k : Fin (concatSegmentCount S T - (r + 1) + 1) =>
            D.obj ((concatSubdivision S T).point
              (shrinkingVertexEmbedding S T r
                (successorChainVertex (Nat.sub_pos_of_lt (by omega))
                  k.castSucc))))
          (show (0 : Fin _) = Fin.cast (by omega) 0 by
            apply Fin.ext
            rfl)).hom ≫
        ((objectIsoOfIndexEq
          (fun k => D.obj ((concatSubdivision S T).point k))
          (shrinkingSuccessorPrefixVertex_eq S T r hr 0)).hom ≫ f)) =
      (shrinkingPrefixInitialIso D S T r).hom ≫ f := by
  simpa only [← Category.assoc] using congrArg
    (fun k => k ≫ f)
    (shrinkingPrefix_initial_transport_coherence D S T r hr)

/-- Three equality transports can be normalized while a dependent arrow and
its final transport remain explicitly whiskered on the right. -/
theorem eqToHom_three_step_whisker_arrow
    {A B C₀ D₀ E F : C}
    (h₁ : A = B) (h₂ : B = C₀) (h₃ : C₀ = D₀)
    (h : A = D₀) (f : D₀ ⟶ E) (k : E = F) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ ≫ f ≫ eqToHom k =
      eqToHom h ≫ f ≫ eqToHom k := by
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ f ≫ eqToHom k)
    (eqToHom_three_step_coherence h₁ h₂ h₃ h)

/-- Two source transports and three target transports around a dependent
arrow normalize to direct endpoint transports.  Equality proofs are
eliminated only after every intermediate object has been named in the type. -/
theorem eqToHom_two_three_conjugation
    {A₀ A₁ A₂ B₀ B₁ B₂ B₃ : C}
    (h₁ : A₀ = A₁) (h₂ : A₁ = A₂) (h : A₀ = A₂)
    (f : A₂ ⟶ B₀)
    (k₁ : B₀ = B₁) (k₂ : B₁ = B₂) (k₃ : B₂ = B₃)
    (k : B₀ = B₃) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ f ≫ eqToHom k₁ ≫
        eqToHom k₂ ≫ eqToHom k₃ =
      eqToHom h ≫ f ≫ eqToHom k := by
  subst A₁
  subst A₂
  subst B₁
  subst B₂
  subst B₃
  simp

/-- Four independently generated transports on either side of an arrow agree
with a two-transport presentation once their intermediate objects are stated
explicitly. -/
theorem eqToHom_four_four_eq_two_two_conjugation
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (h₁ : A₀ = A₁) (h₂ : A₁ = A₂) (h₃ : A₂ = A₃) (h₄ : A₃ = A₄)
    (l₁ : A₀ = A₅) (l₂ : A₅ = A₄) (f : A₄ ⟶ B₀)
    (k₁ : B₀ = B₁) (k₂ : B₁ = B₂) (k₃ : B₂ = B₃) (k₄ : B₃ = B₄)
    (r₁ : B₀ = B₅) (r₂ : B₅ = B₄) :
    eqToHom h₁ ≫ eqToHom h₂ ≫
        (eqToHom h₃ ≫ eqToHom h₄ ≫ f ≫ eqToHom k₁ ≫ eqToHom k₂) ≫
        eqToHom k₃ ≫ eqToHom k₄ =
      eqToHom l₁ ≫ eqToHom l₂ ≫ f ≫ eqToHom r₁ ≫ eqToHom r₂ := by
  subst A₁
  subst A₂
  subst A₃
  subst A₄
  subst A₅
  subst B₁
  subst B₂
  subst B₃
  subst B₄
  subst B₅
  simp

/-- The terminal transports produced by the two fold reindexings and the
literal terminal split normalize to the named boundary and terminal
isomorphisms, without moving the dependent terminal arrow. -/
theorem shrinkingPrefix_terminal_transport_coherence
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T) :
    (objectIsoOfIndexEq
        (fun k => D.obj ((concatSubdivision S T).point k))
        (shrinkingSuccessorPrefixVertex_eq S T r hr
          (Fin.last (concatSegmentCount S T - (r + 1))))).inv ≫
      (objectIsoOfIndexEq
        (fun k : Fin (concatSegmentCount S T - (r + 1) + 1) =>
          D.obj ((concatSubdivision S T).point
            (shrinkingVertexEmbedding S T r
              (successorChainVertex (Nat.sub_pos_of_lt (by omega))
                k.castSucc))))
        (show (Fin.last _ : Fin _) = Fin.cast (by omega) (Fin.last _) by
          apply Fin.ext
          rfl)).inv ≫
      eqToHom (congrArg (shrinkingPrefixObject D S T r)
        (successorChainLastSource_eq_terminal
          (Nat.sub_pos_of_lt (by omega)))) ≫
      shrinkingPrefixArrow D S T r
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by omega))) ≫
      eqToHom (congrArg (shrinkingPrefixObject D S T r)
        (terminalSegmentIndex_succ (Nat.sub_pos_of_lt (by omega)))) =
    (shrinkingPrefixBoundaryIso D S T r (by omega)).hom ≫
      shrinkingPrefixArrow D S T r
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by omega))) ≫
      (shrinkingPrefixTerminalIso D S T r (by omega)).hom := by
  simp only [objectIsoOfIndexEq, shrinkingPrefixBoundaryIso,
    shrinkingPrefixTerminalIso]
  apply eqToHom_three_step_whisker_arrow
  · congr 2
  · congr 4
  · rfl

/-- Substitute independently proved three-arrow prefix and three-arrow suffix
equalities around an unchanged central morphism.  The nested association is
the one produced by the two successive `composeFin` reindexings. -/
theorem comp_eq_of_three_prefix_three_suffix
    {A B C₀ D₀ E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ D₀)
    (middle : D₀ ⟶ E) (d : E ⟶ F) (e : F ⟶ G)
    (terminal : G ⟶ H) (prefixMap : A ⟶ D₀) (suffix : E ⟶ H)
    (hprefix : a ≫ b ≫ c = prefixMap)
    (hsuffix : d ≫ e ≫ terminal = suffix) :
    a ≫ (b ≫ (c ≫ middle ≫ d) ≫ e) ≫ terminal =
      prefixMap ≫ middle ≫ suffix := by
  rw [← hprefix, ← hsuffix]
  simp only [Category.assoc]

/-- One shrinking step: remove the terminal arrow and identify the remaining
prefix with stage `r+1`.  All surviving endpoint changes use the named stage
isomorphisms. -/
theorem shrinkingPrefixFold_succ
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T) :
    shrinkingPrefixFold D S T r =
      (shrinkingPrefixInitialIso D S T r).hom ≫
        shrinkingPrefixFold D S T (r + 1) ≫
        (shrinkingPrefixBoundaryIso D S T r (by omega)).hom ≫
        shrinkingPrefixArrow D S T r
          (terminalSegmentIndex (Nat.sub_pos_of_lt (by omega))) ≫
        (shrinkingPrefixTerminalIso D S T r (by omega)).hom := by
  rw [shrinkingPrefixFold_terminal_split_literal D S T r (by omega)]
  rw [shrinkingSyntacticSuccessorPrefixFold_eq D S T r hr]
  rw [shrinkingSuccessorPrefixFold_eq D S T r hr]
  apply comp_eq_of_three_prefix_three_suffix
  · exact shrinkingPrefix_initial_transport_coherence D S T r hr
  · exact shrinkingPrefix_terminal_transport_coherence D S T r hr

/-- While the removed arrow is still in the right block, expose its actual
concatenated mapped piece.  The endpoint transports already belonging to the
shrinking prefix remain outside the proof-carrying transports induced by the
segment-coordinate equality. -/
theorem shrinkingPrefixArrow_terminal_eq_rightMappedPiece
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r ≤ T.n) :
    shrinkingPrefixArrow D S T r
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by
          simp [concatSegmentCount]
          omega))) =
      eqToHom (congrArg
          (fun k => D.obj ((concatSubdivision S T).point k))
          (shrinkingEndpoint_castSucc S T r
            (terminalSegmentIndex (Nat.sub_pos_of_lt (by
              simp [concatSegmentCount]
              omega))))) ≫
        (eqToHom (congrArg
            (fun k => D.obj ((concatSubdivision S T).point k))
            (congrArg Fin.castSucc
              (shrinkingTerminalSegment_eq_rightSegment S T r hr))) ≫
          D.mappedPiece (concatSubdivision S T)
            (rightSegment S T ⟨T.n - r, by omega⟩) ≫
          eqToHom (congrArg
            (fun k => D.obj ((concatSubdivision S T).point k))
            (congrArg Fin.succ
              (shrinkingTerminalSegment_eq_rightSegment S T r hr))).symm) ≫
        eqToHom (congrArg
          (fun k => D.obj ((concatSubdivision S T).point k))
          (shrinkingEndpoint_succ S T r
            (terminalSegmentIndex (Nat.sub_pos_of_lt (by
              simp [concatSegmentCount]
              omega))))).symm := by
  unfold shrinkingPrefixArrow
  rw [dependentArrow_conjugation_fin
    (fun k => D.obj ((concatSubdivision S T).point k))
    (D.mappedPiece (concatSubdivision S T))
    (shrinkingTerminalSegment_eq_rightSegment S T r hr)]
  congr 1

/-- The one-step recurrence specialized to the part of the shrinking process
that still removes a literal right-block segment. -/
theorem shrinkingPrefixFold_succ_right
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r ≤ T.n) :
    shrinkingPrefixFold D S T r =
      (shrinkingPrefixInitialIso D S T r).hom ≫
        shrinkingPrefixFold D S T (r + 1) ≫
        (shrinkingPrefixBoundaryIso D S T r (by
          simp [concatSegmentCount]
          omega)).hom ≫
        (eqToHom (congrArg
            (fun k => D.obj ((concatSubdivision S T).point k))
            (shrinkingEndpoint_castSucc S T r
              (terminalSegmentIndex (Nat.sub_pos_of_lt (by
                simp [concatSegmentCount]
                omega))))) ≫
          (eqToHom (congrArg
              (fun k => D.obj ((concatSubdivision S T).point k))
              (congrArg Fin.castSucc
                (shrinkingTerminalSegment_eq_rightSegment S T r hr))) ≫
            D.mappedPiece (concatSubdivision S T)
              (rightSegment S T ⟨T.n - r, by omega⟩) ≫
            eqToHom (congrArg
              (fun k => D.obj ((concatSubdivision S T).point k))
              (congrArg Fin.succ
                (shrinkingTerminalSegment_eq_rightSegment S T r hr))).symm) ≫
          eqToHom (congrArg
            (fun k => D.obj ((concatSubdivision S T).point k))
            (shrinkingEndpoint_succ S T r
              (terminalSegmentIndex (Nat.sub_pos_of_lt (by
                simp [concatSegmentCount]
                omega))))).symm) ≫
        (shrinkingPrefixTerminalIso D S T r (by
          simp [concatSegmentCount]
          omega)).hom := by
  rw [shrinkingPrefixFold_succ D S T r (by
    simp [concatSegmentCount]
    omega)]
  rw [shrinkingPrefixArrow_terminal_eq_rightMappedPiece D S T r hr]
  congr 1

/-- The finite family of precisely those recurrence steps which remove the
right block. Its index order is the removal order: step `r` removes the
literal right segment with coordinate `T.n - r`. -/
def shrinkingPrefixFold_rightBlockIteration
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (r : Fin (T.n + 1)) :=
  shrinkingPrefixFold_succ_right D S T r
    (Nat.le_of_lt_succ r.isLt)

theorem rightBlockIteration_segment_coordinate
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (r : Fin (T.n + 1)) :
    shrinkingSegmentEmbedding S T r
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by
          simp [concatSegmentCount]
          omega))) =
      rightSegment S T ⟨T.n - r, by omega⟩ :=
  shrinkingTerminalSegment_eq_rightSegment S T r
    (Nat.le_of_lt_succ r.isLt)

/-- The last legal member is exactly the step from stage `T.n` to the
midpoint stage `T.n + 1`. -/
theorem shrinkingPrefixFold_rightBlockIteration_last
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    shrinkingPrefixFold_rightBlockIteration D S T (Fin.last T.n) =
      shrinkingPrefixFold_succ_right D S T T.n (le_refl T.n) := by
  rfl

theorem rightBlockIteration_stops_at_midpoint
    (T : PathTwoOpenSubdivision q U V) :
    ((Fin.last T.n : Fin (T.n + 1)).val + 1) = T.n + 1 := by
  simp

/-- The terminal object of a shrinking stage. -/
abbrev shrinkingPrefixTerminalObject
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) : C :=
  shrinkingPrefixObject D S T r
    (Fin.last (concatSegmentCount S T - r))

/-- The suffix morphism contributed by one legal right-block removal. -/
def rightRemovalStep
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) (hr : r ≤ T.n) :
    shrinkingPrefixTerminalObject (C := C) D S T (r + 1) ⟶
      shrinkingPrefixTerminalObject (C := C) D S T r :=
  (shrinkingPrefixBoundaryIso D S T r (by
      simp [concatSegmentCount]
      omega)).hom ≫
    shrinkingPrefixArrow D S T r
      (terminalSegmentIndex (Nat.sub_pos_of_lt (by
        simp [concatSegmentCount]
        omega))) ≫
    (shrinkingPrefixTerminalIso D S T r (by
      simp [concatSegmentCount]
      omega)).hom

/-- Reindex one removal step across an equality of stages, retaining the
induced source and target transports. -/
theorem rightRemovalStep_conjugation
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) {a b : ℕ}
    (ha : a ≤ T.n) (hb : b ≤ T.n) (h : a = b) :
    rightRemovalStep D S T a ha =
      eqToHom (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
        (congrArg Nat.succ h)) ≫
      rightRemovalStep D S T b hb ≫
      eqToHom (congrArg (shrinkingPrefixTerminalObject (C := C) D S T) h).symm := by
  subst b
  simp

/-- Initial-end transports accumulated through `k` shrinking stages. -/
def rightInitialAccum
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    (k : ℕ) → shrinkingPrefixObject D S T 0 0 ⟶
      shrinkingPrefixObject D S T k 0
  | 0 => 𝟙 _
  | k + 1 => rightInitialAccum D S T k ≫
      (shrinkingPrefixInitialIso D S T k).hom

/-- Terminal-end transports accumulated in removal order.  The proof bounds
the recursion to exactly the right block. -/
def rightSuffixAccum
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    (k : ℕ) → k ≤ T.n + 1 →
      (shrinkingPrefixTerminalObject (C := C) D S T k ⟶
        shrinkingPrefixTerminalObject (C := C) D S T 0)
  | 0, _ => 𝟙 _
  | k + 1, hk => rightRemovalStep D S T k (by omega) ≫
      rightSuffixAccum D S T k (by omega)

@[simp] theorem rightInitialAccum_zero
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    rightInitialAccum D S T 0 = 𝟙 _ := rfl

theorem rightInitialAccum_succ
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) :
    rightInitialAccum D S T (k + 1) =
      rightInitialAccum D S T k ≫
        (shrinkingPrefixInitialIso D S T k).hom := rfl

@[simp] theorem rightSuffixAccum_zero
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (h0 : 0 ≤ T.n + 1) :
    rightSuffixAccum D S T 0 h0 = 𝟙 _ := rfl

theorem rightSuffixAccum_succ
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) :
    rightSuffixAccum D S T (k + 1) hk =
      rightRemovalStep D S T k (by omega) ≫
        rightSuffixAccum D S T k (by omega) := by
  rfl

/-- Reverse the removal-stage coordinate into the forward right-segment
coordinate. Stage `T.n - j` removes actual segment `j`. -/
theorem reverseRemovalStage_segment_coordinate
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    shrinkingSegmentEmbedding S T (T.n - j)
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by
          simp [concatSegmentCount]
          omega))) = rightSegment S T j := by
  rw [shrinkingTerminalSegment_eq_rightSegment S T (T.n - j) (by omega)]
  congr 1
  apply Fin.ext
  simp
  omega

/-- Pointwise actual-mapped-piece comparison in forward segment coordinates.
The theorem's inferred equality retains all source and target transports from
`shrinkingPrefixArrow_terminal_eq_rightMappedPiece`. -/
theorem reverseRemovalStage_terminalArrow_eq_rightMappedPiece
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    shrinkingPrefixArrow D S T (T.n - j)
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by
          simp [concatSegmentCount]
          omega))) =
      eqToHom (congrArg
          (fun k => D.obj ((concatSubdivision S T).point k))
          (shrinkingEndpoint_castSucc S T (T.n - j)
            (terminalSegmentIndex (Nat.sub_pos_of_lt (by
              simp [concatSegmentCount]
              omega))))) ≫
        (eqToHom (congrArg
            (fun k => D.obj ((concatSubdivision S T).point k))
            (congrArg Fin.castSucc
              (reverseRemovalStage_segment_coordinate S T j))) ≫
          D.mappedPiece (concatSubdivision S T) (rightSegment S T j) ≫
          eqToHom (congrArg
            (fun k => D.obj ((concatSubdivision S T).point k))
            (congrArg Fin.succ
              (reverseRemovalStage_segment_coordinate S T j))).symm) ≫
        eqToHom (congrArg
          (fun k => D.obj ((concatSubdivision S T).point k))
          (shrinkingEndpoint_succ S T (T.n - j)
            (terminalSegmentIndex (Nat.sub_pos_of_lt (by
              simp [concatSegmentCount]
              omega))))).symm := by
  unfold shrinkingPrefixArrow
  rw [dependentArrow_conjugation_fin
    (fun k => D.obj ((concatSubdivision S T).point k))
    (D.mappedPiece (concatSubdivision S T))
    (reverseRemovalStage_segment_coordinate S T j)]
  congr 1

/-- The complete accumulator starts with removal stage `T.n`, hence with
forward right segment zero, and then continues with the shorter accumulator.
-/
theorem rightSuffixAccum_full_unfold
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    rightSuffixAccum D S T (T.n + 1) (le_refl _) =
      rightRemovalStep D S T T.n (le_refl _) ≫
        rightSuffixAccum D S T T.n (by omega) := by
  exact rightSuffixAccum_succ D S T T.n (le_refl _)

/-- Removal stage attached to forward right-block vertex `j`. -/
def reverseRightStage (T : PathTwoOpenSubdivision q U V)
    (j : Fin (T.n + 2)) : ℕ := T.n + 1 - j

theorem reverseRightStage_zero (T : PathTwoOpenSubdivision q U V) :
    reverseRightStage T 0 = T.n + 1 := by
  simp [reverseRightStage]

theorem reverseRightStage_last (T : PathTwoOpenSubdivision q U V) :
    reverseRightStage T (Fin.last (T.n + 1)) = 0 := by
  simp [reverseRightStage]

theorem reverseRightStage_castSucc
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    reverseRightStage T j.castSucc = T.n + 1 - j := by
  simp [reverseRightStage]

theorem reverseRightStage_succ
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    reverseRightStage T j.succ = T.n - j := by
  simp [reverseRightStage]

/-- The terminal vertex of the reverse removal stage is the corresponding
literal right-block vertex. -/
theorem reverseRightTerminalVertex_eq_rightBlockVertex
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 2)) :
    shrinkingVertexEmbedding S T (reverseRightStage T j)
        (Fin.last (concatSegmentCount S T - reverseRightStage T j)) =
      rightBlockVertex S T j := by
  apply Fin.ext
  rw [rightBlockVertex_val]
  change concatSegmentCount S T - (T.n + 1 - j) = S.n + 1 + j
  simp only [concatSegmentCount]
  omega

def reverseRightObject
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 2)) : C :=
  shrinkingPrefixTerminalObject (C := C) D S T (reverseRightStage T j)

/-- Objectwise comparison from the reverse-stage terminal chain to the
structural forward right-block chain. -/
def reverseRightObjectIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 2)) :
    reverseRightObject D S T j ≅ rightBlockObject D S T j :=
  eqToIso (congrArg
    (fun k => D.obj ((concatSubdivision S T).point k))
    (reverseRightTerminalVertex_eq_rightBlockVertex S T j))

theorem reverseRightObjectIso_zero
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    reverseRightObjectIso D S T 0 =
      eqToIso (congrArg
        (fun k => D.obj ((concatSubdivision S T).point k))
        (reverseRightTerminalVertex_eq_rightBlockVertex S T 0)) := rfl

theorem reverseRightObjectIso_last
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    reverseRightObjectIso D S T (Fin.last (T.n + 1)) =
      eqToIso (congrArg
        (fun k => D.obj ((concatSubdivision S T).point k))
        (reverseRightTerminalVertex_eq_rightBlockVertex S T
          (Fin.last (T.n + 1)))) := rfl

/-- The penultimate vertex of reverse removal stage `T.n-j` is the source of
literal right segment `j`. -/
theorem reverseRemovalStage_sourceVertex_eq_rightSegment
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    shrinkingVertexEmbedding S T (T.n - j)
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by
          simp [concatSegmentCount]
          omega))).castSucc =
      (rightSegment S T j).castSucc :=
  (shrinkingEndpoint_castSucc S T (T.n - j)
    (terminalSegmentIndex (Nat.sub_pos_of_lt (by
      simp [concatSegmentCount]
      omega)))).trans
    (congrArg Fin.castSucc
      (reverseRemovalStage_segment_coordinate S T j))

/-- The terminal vertex of reverse removal stage `T.n-j` is the target of
literal right segment `j`. -/
theorem reverseRemovalStage_targetVertex_eq_rightSegment
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    shrinkingVertexEmbedding S T (T.n - j)
        (terminalSegmentIndex (Nat.sub_pos_of_lt (by
          simp [concatSegmentCount]
          omega))).succ =
      (rightSegment S T j).succ :=
  (shrinkingEndpoint_succ S T (T.n - j)
    (terminalSegmentIndex (Nat.sub_pos_of_lt (by
      simp [concatSegmentCount]
      omega)))).trans
    (congrArg Fin.succ
      (reverseRemovalStage_segment_coordinate S T j))

def reverseRemovalStageSourceIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :=
  eqToIso (congrArg
    (fun k => D.obj ((concatSubdivision S T).point k))
    (reverseRemovalStage_sourceVertex_eq_rightSegment S T j))

def reverseRemovalStageTargetIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :=
  eqToIso (congrArg
    (fun k => D.obj ((concatSubdivision S T).point k))
    (reverseRemovalStage_targetVertex_eq_rightSegment S T j))

/-- The removal arrow in forward right-block indexing.  Its two outer
transports identify the arithmetic removal stages with the structural
`castSucc`/`succ` objects of `reverseRightObject`. -/
def reverseRightArrow
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    reverseRightObject D S T j.castSucc ⟶
      reverseRightObject D S T j.succ :=
  eqToHom (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
      (show reverseRightStage T j.castSucc = (T.n - j) + 1 by
        rw [reverseRightStage_castSucc]
        omega)) ≫
    rightRemovalStep D S T (T.n - j) (by omega) ≫
    eqToHom (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
      (show reverseRightStage T j.succ = T.n - j by
        exact reverseRightStage_succ T j)).symm

/-- Pointwise comparison of the reverse removal chain with the literal
forward right-block chain. -/
theorem reverseRightArrow_eq_conjugate
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    reverseRightArrow D S T j =
      (reverseRightObjectIso D S T j.castSucc).hom ≫
        rightBlockArrow D S T j ≫
        (reverseRightObjectIso D S T j.succ).inv := by
  unfold reverseRightArrow rightRemovalStep reverseRightObjectIso
  rw [reverseRemovalStage_terminalArrow_eq_rightMappedPiece D S T j]
  unfold rightBlockArrow
  simp only [shrinkingPrefixBoundaryIso, shrinkingPrefixTerminalIso,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  exact
    (eqToHom_four_four_eq_two_two_conjugation
      (f := D.mappedPiece (concatSubdivision S T) (rightSegment S T j))
      (h₁ := _) (h₂ := _) (h₃ := _) (h₄ := _)
      (l₁ := _) (l₂ := _)
      (k₁ := _) (k₂ := _) (k₃ := _) (k₄ := _)
      (r₁ := _) (r₂ := _))

/-- The entire reverse-stage removal chain is the literal forward right-block
fold with only its two outer object transports remaining. -/
theorem reverseRightComposeFin_eq
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    TwoOpenDescentDatum.composeFin (reverseRightObject D S T)
        (reverseRightArrow D S T) =
      (reverseRightObjectIso D S T 0).hom ≫
        TwoOpenDescentDatum.composeFin (rightBlockObject D S T)
          (rightBlockArrow D S T) ≫
        (reverseRightObjectIso D S T (Fin.last (T.n + 1))).inv := by
  apply ConstructionTargets.ComposeFinConjugation.composeFin_conjugation_from_comparisonIso
  exact reverseRightArrow_eq_conjugate D S T

/-- Source coordinate from the reverse-stage fold to the full accumulator. -/
def reverseRightAccumSourceIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    reverseRightObject D S T 0 ≅
      shrinkingPrefixTerminalObject (C := C) D S T (T.n + 1) :=
  eqToIso (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
    (reverseRightStage_zero T))

/-- Target coordinate from the reverse-stage fold to accumulator stage zero.
-/
def reverseRightAccumTargetIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    reverseRightObject D S T (Fin.last (T.n + 1)) ≅
      shrinkingPrefixTerminalObject (C := C) D S T 0 :=
  eqToIso (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
    (reverseRightStage_last T))

theorem reverseRightAccumSourceIso_hom
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    (reverseRightAccumSourceIso D S T).hom =
      eqToHom (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
        (reverseRightStage_zero T)) := rfl

theorem reverseRightAccumTargetIso_hom
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    (reverseRightAccumTargetIso D S T).hom =
      eqToHom (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
        (reverseRightStage_last T)) := rfl

/-- Vertex embedding of the last `k` arrows of the forward reverse-right
chain.  This slice represents removal stages `k-1, ..., 0`. -/
def rightSuffixSliceVertex
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1)
    (i : Fin (k + 1)) : Fin (T.n + 2) :=
  ⟨T.n + 1 - k + i, by omega⟩

/-- Segment embedding belonging to `rightSuffixSliceVertex`. -/
def rightSuffixSliceSegment
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1)
    (i : Fin k) : Fin (T.n + 1) :=
  ⟨T.n + 1 - k + i, by omega⟩

theorem rightSuffixSliceSegment_castSucc
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1)
    (i : Fin k) :
    (rightSuffixSliceSegment T k hk i).castSucc =
      rightSuffixSliceVertex T k hk i.castSucc := by
  apply Fin.ext
  rfl

theorem rightSuffixSliceSegment_succ
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1)
    (i : Fin k) :
    (rightSuffixSliceSegment T k hk i).succ =
      rightSuffixSliceVertex T k hk i.succ := by
  apply Fin.ext
  rfl

theorem rightSuffixSliceVertex_zero
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1) :
    rightSuffixSliceVertex T k hk 0 =
      ⟨T.n + 1 - k, by omega⟩ := by
  apply Fin.ext
  simp [rightSuffixSliceVertex]

theorem rightSuffixSliceVertex_last
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1) :
    rightSuffixSliceVertex T k hk (Fin.last k) =
      Fin.last (T.n + 1) := by
  apply Fin.ext
  simp [rightSuffixSliceVertex]
  omega

/-- The new first segment of the `(k+1)`-slice is forward coordinate
`T.n-k`, hence removal stage `k`. -/
theorem rightSuffixSliceSegment_succ_zero
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) :
    rightSuffixSliceSegment T (k + 1) hk 0 =
      ⟨T.n - k, by omega⟩ := by
  apply Fin.ext
  simp [rightSuffixSliceSegment]

/-- Dropping the newly prepended segment recovers the preceding slice's
segment embedding. -/
theorem rightSuffixSliceSegment_succ_tail
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) (i : Fin k) :
    rightSuffixSliceSegment T (k + 1) hk i.succ =
      rightSuffixSliceSegment T k (by omega) i := by
  apply Fin.ext
  simp [rightSuffixSliceSegment]
  omega

/-- The vertex tail of the `(k+1)`-slice is the complete `k`-slice. -/
theorem rightSuffixSliceVertex_succ_tail
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) (i : Fin (k + 1)) :
    rightSuffixSliceVertex T (k + 1) hk i.succ =
      rightSuffixSliceVertex T k (by omega) i := by
  apply Fin.ext
  simp [rightSuffixSliceVertex]
  omega

/-- Objects of the proof-carrying terminal slice. -/
def rightSuffixSliceObject
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1)
    (i : Fin (k + 1)) : C :=
  reverseRightObject D S T (rightSuffixSliceVertex T k hk i)

/-- Arrows of the terminal slice, transported from the actual reverse-right
chain only after the segment and vertex embeddings have been aligned. -/
def rightSuffixSliceArrow
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1)
    (i : Fin k) :
    rightSuffixSliceObject D S T k hk i.castSucc ⟶
      rightSuffixSliceObject D S T k hk i.succ :=
  eqToHom (congrArg (reverseRightObject D S T)
      (rightSuffixSliceSegment_castSucc T k hk i).symm) ≫
    reverseRightArrow D S T (rightSuffixSliceSegment T k hk i) ≫
    eqToHom (congrArg (reverseRightObject D S T)
      (rightSuffixSliceSegment_succ T k hk i))

/-- The dependent fold of the last `k` forward reverse-right arrows. -/
def rightSuffixSliceFold
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1) :
    rightSuffixSliceObject D S T k hk 0 ⟶
      rightSuffixSliceObject D S T k hk (Fin.last k) :=
  TwoOpenDescentDatum.composeFin (rightSuffixSliceObject D S T k hk)
    (rightSuffixSliceArrow D S T k hk)

@[simp] theorem rightSuffixSliceFold_zero
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (hk : 0 ≤ T.n + 1) :
    rightSuffixSliceFold D S T 0 hk = 𝟙 _ := by
  exact TwoOpenDescentDatum.composeFin_zero _ _

/-- Front recursion for the terminal slice.  The displayed tail deliberately
retains the literal successor restriction of the `(k+1)` slice; its comparison
with the separately constructed `k` slice is the next reindex step. -/
theorem rightSuffixSliceFold_succ_front
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) :
    rightSuffixSliceFold D S T (k + 1) hk =
      rightSuffixSliceArrow D S T (k + 1) hk 0 ≫
        TwoOpenDescentDatum.composeFin
          (rightSuffixSliceObject D S T (k + 1) hk ∘
            fun i : Fin (k + 1) ↦ i.succ)
          (fun i : Fin k ↦
            rightSuffixSliceArrow D S T (k + 1) hk i.succ) := by
  exact ConstructionTargets.ComposeFinAppend.composeFin_front_split _ _

/-- Two independently generated two-step endpoint transports around the same
dependent arrow agree. -/
theorem eqToHom_two_two_conjugation
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    (h₁ : A₀ = A₁) (h₂ : A₁ = A₂)
    (l₁ : A₀ = A₃) (l₂ : A₃ = A₂) (f : A₂ ⟶ B₀)
    (k₁ : B₀ = B₁) (k₂ : B₁ = B₂)
    (r₁ : B₀ = B₃) (r₂ : B₃ = B₂) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ f ≫ eqToHom k₁ ≫ eqToHom k₂ =
      eqToHom l₁ ≫ (eqToHom l₂ ≫ f ≫ eqToHom r₁) ≫ eqToHom r₂ := by
  subst A₁
  subst A₂
  subst A₃
  subst B₁
  subst B₂
  subst B₃
  simp

/-- Two equality transports with the same composite endpoints equal any
direct transport between those endpoints. -/
theorem eqToHom_two_eq_one {A B C₀ : C}
    (h₁ : A = B) (h₂ : B = C₀) (h : A = C₀) :
    eqToHom h₁ ≫ eqToHom h₂ = eqToHom h := by
  subst B
  subst C₀
  simp

/-- Four source transports and five target transports can be collapsed once
the dependent central arrow has been aligned. -/
theorem eqToHom_four_five_conjugation
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (h₁ : A₀ = A₁) (h₂ : A₁ = A₂)
    (h₃ : A₂ = A₃) (h₄ : A₃ = A₄) (h : A₀ = A₄)
    (f : A₄ ⟶ B₀)
    (k₁ : B₀ = B₁) (k₂ : B₁ = B₂) (k₃ : B₂ = B₃)
    (k₄ : B₃ = B₄) (k₅ : B₄ = B₅) (k : B₀ = B₅) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ ≫ eqToHom h₄ ≫ f ≫
        eqToHom k₁ ≫ eqToHom k₂ ≫ eqToHom k₃ ≫ eqToHom k₄ ≫ eqToHom k₅ =
      eqToHom h ≫ f ≫ eqToHom k := by
  subst A₁
  subst A₂
  subst A₃
  subst A₄
  subst B₁
  subst B₂
  subst B₃
  subst B₄
  subst B₅
  simp

/-- Normalize the two transported arrows and final transport occurring in a
recursive fold step. -/
theorem eqToHom_two_arrow_blocks
    {A₀ A₁ A₂ A₃ A₅ A₆ B : C}
    (h₁ : A₀ = A₁) (a : A₁ ⟶ A₂) (h₂ : A₂ = A₃)
    (h₃ : A₃ = A₂) (b : A₂ ⟶ A₅) (h₄ : A₅ = A₆)
    (h₅ : A₆ = B) (h : A₀ = A₁) (k : A₅ = B) :
    (eqToHom h₁ ≫ a ≫ eqToHom h₂) ≫
        (eqToHom h₃ ≫ b ≫ eqToHom h₄) ≫ eqToHom h₅ =
      eqToHom h ≫ (a ≫ b) ≫ eqToHom k := by
  subst A₁
  subst A₃
  subst A₆
  subst B
  simp [Category.assoc]

/-- The literal successor tail arrow of the `(k+1)` slice is the corresponding
`k`-slice arrow, conjugated by the proof-carrying vertex-tail equalities. -/
theorem rightSuffixSliceArrow_succ_tail_eq_conjugate
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) (i : Fin k) :
    rightSuffixSliceArrow D S T (k + 1) hk i.succ =
      (objectIsoOfIndexEq (reverseRightObject D S T)
        (rightSuffixSliceVertex_succ_tail T k hk i.castSucc)).hom ≫
      rightSuffixSliceArrow D S T k (by omega) i ≫
      (objectIsoOfIndexEq (reverseRightObject D S T)
        (rightSuffixSliceVertex_succ_tail T k hk i.succ)).inv := by
  unfold rightSuffixSliceArrow
  rw [dependentArrow_conjugation
    (reverseRightObject D S T) (reverseRightArrow D S T)
    (rightSuffixSliceSegment_succ_tail T k hk i)]
  simp only [objectIsoOfIndexEq, eqToIso.hom, eqToIso.inv,
    Category.assoc]
  exact eqToHom_two_two_conjugation (C := C) _ _ _ _ _ _ _ _ _

/-- The successor-restricted tail fold of the `(k+1)` slice is the `k`-slice
fold with only its two outer vertex transports remaining. -/
theorem rightSuffixSliceTailFold_eq
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) :
    TwoOpenDescentDatum.composeFin
        (rightSuffixSliceObject D S T (k + 1) hk ∘
          fun i : Fin (k + 1) ↦ i.succ)
        (fun i : Fin k ↦
          rightSuffixSliceArrow D S T (k + 1) hk i.succ) =
      (objectIsoOfIndexEq (reverseRightObject D S T)
        (rightSuffixSliceVertex_succ_tail T k hk 0)).hom ≫
      rightSuffixSliceFold D S T k (by omega) ≫
      (objectIsoOfIndexEq (reverseRightObject D S T)
        (rightSuffixSliceVertex_succ_tail T k hk (Fin.last k))).inv := by
  apply composeFin_reindex_of_index_eq
    (reverseRightObject D S T)
    (rightSuffixSliceVertex T k (by omega))
    (fun i : Fin (k + 1) ↦ rightSuffixSliceVertex T (k + 1) hk i.succ)
    (rightSuffixSliceVertex_succ_tail T k hk)
    (rightSuffixSliceArrow D S T k (by omega))
    (fun i : Fin k ↦ rightSuffixSliceArrow D S T (k + 1) hk i.succ)
  exact rightSuffixSliceArrow_succ_tail_eq_conjugate D S T k hk

/-- Successor recurrence for the slice fold, with the front arrow and the two
tail-reindex endpoint transports still explicit. -/
theorem rightSuffixSliceFold_succ
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) :
    rightSuffixSliceFold D S T (k + 1) hk =
      rightSuffixSliceArrow D S T (k + 1) hk 0 ≫
        (objectIsoOfIndexEq (reverseRightObject D S T)
          (rightSuffixSliceVertex_succ_tail T k hk 0)).hom ≫
        rightSuffixSliceFold D S T k (by omega) ≫
        (objectIsoOfIndexEq (reverseRightObject D S T)
          (rightSuffixSliceVertex_succ_tail T k hk (Fin.last k))).inv := by
  rw [rightSuffixSliceFold_succ_front D S T k hk]
  rw [rightSuffixSliceTailFold_eq D S T k hk]
  congr 1

theorem rightSuffixSlice_source_stage
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1) :
    reverseRightStage T (rightSuffixSliceVertex T k hk 0) = k := by
  simp [reverseRightStage, rightSuffixSliceVertex]
  omega

theorem rightSuffixSlice_target_stage
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1) :
    reverseRightStage T
        (rightSuffixSliceVertex T k hk (Fin.last k)) = 0 := by
  rw [rightSuffixSliceVertex_last]
  exact reverseRightStage_last T

/-- Source coordinate for comparing the `k`-slice fold with the recursive
accumulator at stage `k`. -/
def rightSuffixSliceSourceIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1) :
    rightSuffixSliceObject D S T k hk 0 ≅
      shrinkingPrefixTerminalObject (C := C) D S T k :=
  eqToIso (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
    (rightSuffixSlice_source_stage T k hk))

/-- Target coordinate for comparing every `k`-slice with accumulator stage
zero. -/
def rightSuffixSliceTargetIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ) (hk : k ≤ T.n + 1) :
    rightSuffixSliceObject D S T k hk (Fin.last k) ≅
      shrinkingPrefixTerminalObject (C := C) D S T 0 :=
  eqToIso (congrArg (shrinkingPrefixTerminalObject (C := C) D S T)
    (rightSuffixSlice_target_stage T k hk))

/-- The exposed first slice arrow and the tail-source reindex transport are
exactly the next recursive removal, between the named slice source
coordinates. -/
theorem rightSuffixSlice_front_source_coherence
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) :
    rightSuffixSliceArrow D S T (k + 1) hk 0 ≫
        (objectIsoOfIndexEq (reverseRightObject D S T)
          (rightSuffixSliceVertex_succ_tail T k hk 0)).hom =
      (rightSuffixSliceSourceIso D S T (k + 1) hk).hom ≫
        rightRemovalStep D S T k (by omega) ≫
        (rightSuffixSliceSourceIso D S T k (by omega)).inv := by
  unfold rightSuffixSliceArrow
  rw [dependentArrow_conjugation
    (reverseRightObject D S T) (reverseRightArrow D S T)
    (rightSuffixSliceSegment_succ_zero T k hk)]
  unfold reverseRightArrow rightSuffixSliceSourceIso
  rw [rightRemovalStep_conjugation D S T _ _
    (show T.n - (T.n - k) = k by omega)]
  simp only [objectIsoOfIndexEq, eqToIso.hom, eqToIso.inv,
    Category.assoc]
  exact eqToHom_four_five_conjugation
    (f := rightRemovalStep D S T k (by omega))
    (h₁ := _) (h₂ := _) (h₃ := _) (h₄ := _) (h := _)
    (k₁ := _) (k₂ := _) (k₃ := _) (k₄ := _) (k₅ := _) (k := _)

/-- The old slice target coordinate followed by the tail reindex transport is
the new slice target coordinate. -/
theorem rightSuffixSlice_target_coherence
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (k : ℕ)
    (hk : k + 1 ≤ T.n + 1) :
    (rightSuffixSliceTargetIso D S T k (by omega)).inv ≫
        (objectIsoOfIndexEq (reverseRightObject D S T)
          (rightSuffixSliceVertex_succ_tail T k hk (Fin.last k))).inv =
      (rightSuffixSliceTargetIso D S T (k + 1) hk).inv := by
  simp only [rightSuffixSliceTargetIso, objectIsoOfIndexEq,
    eqToIso.inv]
  exact eqToHom_two_eq_one _ _ _

/-- The accumulator/slice comparison at length zero, with both endpoint
coordinates retained. -/
theorem rightSuffixSliceFold_zero_eq_accum
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (hk : 0 ≤ T.n + 1) :
    rightSuffixSliceFold D S T 0 hk =
      (rightSuffixSliceSourceIso D S T 0 hk).hom ≫
        rightSuffixAccum D S T 0 hk ≫
        (rightSuffixSliceTargetIso D S T 0 hk).inv := by
  simp only [rightSuffixSliceFold_zero, rightSuffixAccum_zero,
    Category.comp_id, Category.id_comp]
  simp [rightSuffixSliceSourceIso, rightSuffixSliceTargetIso]

/-- Every proof-carrying terminal slice is the recursive removal accumulator,
with only its named source and target coordinate isomorphisms remaining. -/
theorem rightSuffixSliceFold_eq_accum
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    ∀ (k : ℕ) (hk : k ≤ T.n + 1),
      rightSuffixSliceFold D S T k hk =
        (rightSuffixSliceSourceIso D S T k hk).hom ≫
          rightSuffixAccum D S T k hk ≫
          (rightSuffixSliceTargetIso D S T k hk).inv
  | 0, hk => rightSuffixSliceFold_zero_eq_accum D S T hk
  | k + 1, hk => by
      rw [rightSuffixSliceFold_succ D S T k hk]
      rw [rightSuffixSliceFold_eq_accum D S T k (by omega)]
      rw [← Category.assoc]
      rw [rightSuffixSlice_front_source_coherence D S T k hk]
      simp only [rightSuffixSliceSourceIso, rightSuffixSliceTargetIso,
        rightSuffixAccum, eqToIso.hom, eqToIso.inv]
      exact eqToHom_two_arrow_blocks (C := C) _ _ _ _ _ _
        (congrArg (reverseRightObject D S T)
          (rightSuffixSliceVertex_succ_tail T k hk (Fin.last k)).symm)
        _ _

/-- Heterogeneous iteration of the right-block recurrence.  The suffix is
ordered as the removals `T.n, ..., 0` when read from the midpoint back to the
original terminal object. -/
theorem shrinkingPrefixFold_rightBlockAccum
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    ∀ (k : ℕ) (hk : k ≤ T.n + 1),
      shrinkingPrefixFold D S T 0 =
        rightInitialAccum D S T k ≫
          shrinkingPrefixFold D S T k ≫
          rightSuffixAccum D S T k hk
  | 0, hk => by
      simp only [rightInitialAccum, rightSuffixAccum, Category.id_comp,
        Category.comp_id]
  | k + 1, hk => by
      rw [shrinkingPrefixFold_rightBlockAccum D S T k (by omega)]
      rw [shrinkingPrefixFold_succ D S T k (by
        simp [concatSegmentCount]
        omega)]
      rw [rightInitialAccum_succ, rightSuffixAccum_succ]
      unfold rightRemovalStep
      simp only [Category.assoc]

/-- Stage zero compared directly with the midpoint stage after every legal
right-block removal. -/
theorem shrinkingPrefixFold_zero_eq_midpoint
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    shrinkingPrefixFold D S T 0 =
      rightInitialAccum D S T (T.n + 1) ≫
        shrinkingPrefixFold D S T (T.n + 1) ≫
        rightSuffixAccum D S T (T.n + 1) (le_refl _) :=
  shrinkingPrefixFold_rightBlockAccum D S T (T.n + 1) (le_refl _)

/-- The full concatenated segment fold, with the stage-zero endpoint
transports retained, equals the midpoint fold followed by the complete
right-block removal suffix. -/
theorem concatComposeFin_eq_midpoint_rightAccum
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    (objectIsoOfIndexEq
        (D.obj ∘ (concatSubdivision S T).point)
        (shrinkingVertexEmbedding_zero_eq_id S T 0)).hom ≫
      TwoOpenDescentDatum.composeFin
        (D.obj ∘ (concatSubdivision S T).point)
        (D.mappedPiece (concatSubdivision S T)) ≫
      (objectIsoOfIndexEq
        (D.obj ∘ (concatSubdivision S T).point)
        (shrinkingVertexEmbedding_zero_eq_id S T
          (Fin.last (concatSegmentCount S T)))).inv =
    rightInitialAccum D S T (T.n + 1) ≫
      shrinkingPrefixFold D S T (T.n + 1) ≫
      rightSuffixAccum D S T (T.n + 1) (le_refl _) := by
  rw [← shrinkingPrefixFold_zero D S T]
  exact shrinkingPrefixFold_zero_eq_midpoint D S T

#print axioms shrinkingVertexEmbedding_zero_stage
#print axioms shrinkingSegmentEmbedding_zero_stage
#print axioms composeFin_terminal_split
#print axioms terminalArrow_transport
#print axioms successorChainComposeFin_eq
#print axioms castIndexedComposeFin_eq
#print axioms successorChainComposeFin_terminal_split
#print axioms successorChain_terminal_arrow_normalization
#print axioms composeFin_eq_successorChain
#print axioms composeFin_terminal_split_of_pos
#print axioms composeFin_terminal_split_of_pos_literal
#print axioms shrinkingPrefixFold_terminal_split_literal
#print axioms shrinkingTerminalSegment_eq_rightSegment
#print axioms successorChain_initial_object_transport
#print axioms successorChainCastLast_eq_last
#print axioms successorChain_final_object_transport
#print axioms shrinkingPrefixInitialIso
#print axioms shrinkingPrefixBoundaryIso
#print axioms shrinkingPrefixTerminalIso
#print axioms shrinkingSuccessorPrefixVertex_eq
#print axioms shrinkingSuccessorPrefixSegment_eq
#print axioms shrinkingSuccessorPrefixArrow_eq_conjugate
#print axioms shrinkingSuccessorPrefixFold_eq
#print axioms shrinkingSyntacticSuccessorPrefixFold_eq
#print axioms eqToHom_three_step_coherence
#print axioms shrinkingPrefix_initial_transport_coherence
#print axioms shrinkingPrefix_initial_transport_whisker
#print axioms eqToHom_three_step_whisker_arrow
#print axioms eqToHom_two_three_conjugation
#print axioms eqToHom_four_four_eq_two_two_conjugation
#print axioms shrinkingPrefix_terminal_transport_coherence
#print axioms comp_eq_of_three_prefix_three_suffix
#print axioms shrinkingPrefixFold_succ
#print axioms shrinkingPrefixArrow_terminal_eq_rightMappedPiece
#print axioms shrinkingPrefixFold_succ_right
#print axioms shrinkingPrefixFold_rightBlockIteration
#print axioms rightBlockIteration_segment_coordinate
#print axioms shrinkingPrefixFold_rightBlockIteration_last
#print axioms rightBlockIteration_stops_at_midpoint
#print axioms rightRemovalStep
#print axioms rightInitialAccum
#print axioms rightSuffixAccum
#print axioms reverseRemovalStage_segment_coordinate
#print axioms reverseRemovalStage_terminalArrow_eq_rightMappedPiece
#print axioms rightSuffixAccum_full_unfold
#print axioms reverseRightStage_zero
#print axioms reverseRightStage_last
#print axioms reverseRightStage_castSucc
#print axioms reverseRightStage_succ
#print axioms reverseRightTerminalVertex_eq_rightBlockVertex
#print axioms reverseRightObjectIso
#print axioms reverseRightObjectIso_zero
#print axioms reverseRightObjectIso_last
#print axioms reverseRemovalStage_sourceVertex_eq_rightSegment
#print axioms reverseRemovalStage_targetVertex_eq_rightSegment
#print axioms reverseRemovalStageSourceIso
#print axioms reverseRemovalStageTargetIso
#print axioms reverseRightArrow
#print axioms reverseRightArrow_eq_conjugate
#print axioms reverseRightComposeFin_eq
#print axioms reverseRightAccumSourceIso
#print axioms reverseRightAccumTargetIso
#print axioms reverseRightAccumSourceIso_hom
#print axioms reverseRightAccumTargetIso_hom
#print axioms rightSuffixSliceVertex
#print axioms rightSuffixSliceSegment
#print axioms rightSuffixSliceSegment_succ_zero
#print axioms rightSuffixSliceSegment_succ_tail
#print axioms rightSuffixSliceVertex_succ_tail
#print axioms rightSuffixSliceArrow
#print axioms rightSuffixSliceFold
#print axioms rightSuffixSliceFold_zero
#print axioms rightSuffixSliceFold_succ_front
#print axioms eqToHom_two_two_conjugation
#print axioms eqToHom_two_eq_one
#print axioms eqToHom_four_five_conjugation
#print axioms eqToHom_two_arrow_blocks
#print axioms rightRemovalStep_conjugation
#print axioms rightSuffixSliceArrow_succ_tail_eq_conjugate
#print axioms rightSuffixSliceTailFold_eq
#print axioms rightSuffixSliceFold_succ
#print axioms rightSuffixSlice_source_stage
#print axioms rightSuffixSlice_target_stage
#print axioms rightSuffixSliceSourceIso
#print axioms rightSuffixSliceTargetIso
#print axioms rightSuffixSliceFold_zero_eq_accum
#print axioms rightSuffixSlice_front_source_coherence
#print axioms rightSuffixSlice_target_coherence
#print axioms rightSuffixSliceFold_eq_accum
#print axioms shrinkingPrefixFold_rightBlockAccum
#print axioms shrinkingPrefixFold_zero_eq_midpoint
#print axioms concatComposeFin_eq_midpoint_rightAccum

end ConstructionTargets.ConcatSubdivisionShrinkingFoldRecurrence
