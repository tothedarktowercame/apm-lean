import ConstructionTargets.ConcatSubdivisionShrinkingPrefix
import ConstructionTargets.ComposeFinConjugation
import ConstructionTargets.ComposeFinIndexReindex
import ConstructionTargets.ComposeFinAppend

/-!
# Restricted folds of shrinking concatenated prefixes
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionShrinkingFold

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionShrinkingPrefix
open ConstructionTargets.ComposeFinConjugation
open ConstructionTargets.ComposeFinIndexReindex
open ConstructionTargets.ComposeFinAppend

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}
variable {C : Type*} [Category C]

/-- Independently generated proofs of the same two endpoint equalities give
the same conjugated arrow once their index propositions have been aligned. -/
theorem conjugatedArrow_proof_irrel {ι : Type*} (O : ι → C)
    {a₀ a₁ b₀ b₁ : ι} (f : O a₀ ⟶ O a₁)
    (h₀ h₀' : b₀ = a₀) (h₁ h₁' : b₁ = a₁) :
    eqToHom (congrArg O h₀) ≫ f ≫ eqToHom (congrArg O h₁).symm =
      eqToHom (congrArg O h₀') ≫ f ≫ eqToHom (congrArg O h₁').symm := by
  subst a₀
  subst a₁
  simp

/-- Composing two independently generated endpoint transports agrees with a
single supplied composite endpoint transport. -/
theorem conjugatedArrow_compose {ι : Type*} (O : ι → C)
    {a₀ a₁ b₀ b₁ c₀ c₁ : ι} (f : O a₀ ⟶ O a₁)
    (hbc₀ : b₀ = c₀) (hca₀ : c₀ = a₀) (hba₀ : b₀ = a₀)
    (hbc₁ : b₁ = c₁) (hca₁ : c₁ = a₁) (hba₁ : b₁ = a₁) :
    eqToHom (congrArg O hbc₀) ≫
        (eqToHom (congrArg O hca₀) ≫ f ≫
          eqToHom (congrArg O hca₁).symm) ≫
        eqToHom (congrArg O hbc₁).symm =
      eqToHom (congrArg O hba₀) ≫ f ≫
        eqToHom (congrArg O hba₁).symm := by
  subst c₀
  subst a₀
  subst c₁
  subst a₁
  simp

/-- The endpoint-conjugation composition law remains valid under explicit
left and right whiskering. -/
theorem whisker_conjugatedArrow_compose {ι : Type*} (O : ι → C)
    {a₀ a₁ b₀ b₁ c₀ c₁ : ι} (f : O a₀ ⟶ O a₁)
    (hbc₀ : b₀ = c₀) (hca₀ : c₀ = a₀) (hba₀ : b₀ = a₀)
    (hbc₁ : b₁ = c₁) (hca₁ : c₁ = a₁) (hba₁ : b₁ = a₁)
    {Z W : C} (l : Z ⟶ O b₀) (r : O b₁ ⟶ W) :
    l ≫ (eqToHom (congrArg O hbc₀) ≫
        (eqToHom (congrArg O hca₀) ≫ f ≫
          eqToHom (congrArg O hca₁).symm) ≫
        eqToHom (congrArg O hbc₁).symm) ≫ r =
      l ≫ (eqToHom (congrArg O hba₀) ≫ f ≫
        eqToHom (congrArg O hba₁).symm) ≫ r := by
  rw [conjugatedArrow_compose O f hbc₀ hca₀ hba₀
    hbc₁ hca₁ hba₁]

theorem shrinkingEndpoint_castSucc
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (i : Fin (concatSegmentCount S T - r)) :
    shrinkingVertexEmbedding S T r i.castSucc =
      (shrinkingSegmentEmbedding S T r i).castSucc := by
  apply Fin.ext
  rfl

theorem shrinkingEndpoint_succ
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (i : Fin (concatSegmentCount S T - r)) :
    shrinkingVertexEmbedding S T r i.succ =
      (shrinkingSegmentEmbedding S T r i).succ := by
  apply Fin.ext
  rfl

/-- Objects of the prefix remaining after `r` terminal arrows are removed. -/
def shrinkingPrefixObject
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (r : ℕ) (i : Fin (concatSegmentCount S T - r + 1)) : C :=
  D.obj ((concatSubdivision S T).point (shrinkingVertexEmbedding S T r i))

/-- Actual concatenated arrows transported to the endpoints of a shrinking
prefix. -/
def shrinkingPrefixArrow
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (r : ℕ) (i : Fin (concatSegmentCount S T - r)) :
    shrinkingPrefixObject D S T r i.castSucc ⟶
      shrinkingPrefixObject D S T r i.succ :=
  eqToHom (congrArg (fun k ↦ D.obj ((concatSubdivision S T).point k))
      (shrinkingEndpoint_castSucc S T r i)) ≫
    D.mappedPiece (concatSubdivision S T) (shrinkingSegmentEmbedding S T r i) ≫
    eqToHom (congrArg (fun k ↦ D.obj ((concatSubdivision S T).point k))
      (shrinkingEndpoint_succ S T r i)).symm

def shrinkingPrefixFold
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (r : ℕ) :
    shrinkingPrefixObject D S T r 0 ⟶
      shrinkingPrefixObject D S T r
        (Fin.last (concatSegmentCount S T - r)) :=
  TwoOpenDescentDatum.composeFin (shrinkingPrefixObject D S T r)
    (shrinkingPrefixArrow D S T r)

theorem shrinkingVertexEmbedding_zero_eq_id
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (i : Fin (concatSegmentCount S T + 1)) :
    shrinkingVertexEmbedding S T 0 i = i := by
  apply Fin.ext
  rfl

/-- At stage zero the shrinking fold is the full concatenated fold. -/
theorem shrinkingPrefixFold_zero
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V) :
    shrinkingPrefixFold D S T 0 =
      (objectIsoOfIndexEq
          (D.obj ∘ (concatSubdivision S T).point)
          (shrinkingVertexEmbedding_zero_eq_id S T 0)).hom ≫
        TwoOpenDescentDatum.composeFin
          (D.obj ∘ (concatSubdivision S T).point)
          (D.mappedPiece (concatSubdivision S T)) ≫
        (objectIsoOfIndexEq
          (D.obj ∘ (concatSubdivision S T).point)
          (shrinkingVertexEmbedding_zero_eq_id S T
            (Fin.last (concatSegmentCount S T)))).inv := by
  let O := D.obj ∘ (concatSubdivision S T).point
  let r : Fin (concatSegmentCount S T + 1) →
      Fin (concatSegmentCount S T + 1) := id
  let s : Fin (concatSegmentCount S T + 1) →
      Fin (concatSegmentCount S T + 1) := shrinkingVertexEmbedding S T 0
  have hr : ∀ i, s i = r i := fun i => by
    apply Fin.ext
    rfl
  have hs : ∀ i : Fin (concatSegmentCount S T),
      shrinkingSegmentEmbedding S T 0 i = i := fun i => by
    apply Fin.ext
    rfl
  have harr : ∀ i : Fin (concatSegmentCount S T),
      shrinkingPrefixArrow D S T 0 i =
        (objectIsoOfIndexEq O (hr i.castSucc)).hom ≫
          D.mappedPiece (concatSubdivision S T) i ≫
          (objectIsoOfIndexEq O (hr i.succ)).inv := by
    intro i
    rw [shrinkingPrefixArrow]
    rw [dependentArrow_conjugation O
      (D.mappedPiece (concatSubdivision S T)) (hs i)]
    exact conjugatedArrow_compose O
      (D.mappedPiece (concatSubdivision S T) i)
      (shrinkingEndpoint_castSucc S T 0 i)
      (congrArg Fin.castSucc (hs i)) (hr i.castSucc)
      (shrinkingEndpoint_succ S T 0 i)
      (congrArg Fin.succ (hs i)) (hr i.succ)
  have hfold := composeFin_reindex_of_index_eq O r s hr
    (D.mappedPiece (concatSubdivision S T))
    (shrinkingPrefixArrow D S T 0) harr
  simpa [shrinkingPrefixFold, shrinkingPrefixObject, O, r, s,
    concatSegmentCount, concatSubdivision] using hfold

#print axioms shrinkingEndpoint_castSucc
#print axioms shrinkingEndpoint_succ
#print axioms conjugatedArrow_proof_irrel
#print axioms conjugatedArrow_compose
#print axioms whisker_conjugatedArrow_compose
#print axioms shrinkingPrefixFold_zero

end ConstructionTargets.ConcatSubdivisionShrinkingFold
