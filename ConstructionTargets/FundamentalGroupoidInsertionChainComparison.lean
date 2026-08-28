import ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
import ConstructionTargets.FunctorMapPreorderTransport
import ConstructionTargets.PathMapPathTransport

/-!
# Object coordinates for the single-insertion chain comparison
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidInsertionChainComparison

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
open ConstructionTargets.FundamentalGroupoidTwoOpenRefinement
open ConstructionTargets.FundamentalGroupoidTwoOpenRefinement.TwoOpenDescentDatum
open ConstructionTargets.FunctorMapPreorderTransport
open ConstructionTargets.PathMapPathTransport

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
variable {C : Type*} [Category C]

namespace TwoOpenDescentDatum

variable (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)
variable {x y : X} {p : Path x y} {S : PathTwoOpenSubdivision p U V}

/-- Coherence of the three equality transports occurring in an objectwise
comparison square.  The six equality propositions are explicit; only their
proofs are identified by proof irrelevance after the objects are aligned. -/
theorem eqToHom_conjugation_square
    {A R E B R' E' : C} (f : E ⟶ E')
    (ha : A = E) (hb : B = E')
    (ea : A = R) (eb : B = R')
    (ra : R = E) (rb : R' = E') :
    (eqToHom ha ≫ f ≫ eqToHom hb.symm) ≫ eqToHom eb =
      eqToHom ea ≫ (eqToHom ra ≫ f ≫ eqToHom rb.symm) := by
  subst E
  subst E'
  subst R
  subst R'
  simp

/-- Two independently constructed equality transports through the same
intermediate object cancel inside an explicitly reassociated composite. -/
theorem eqToHom_middle_cancel
    {A A' B M C₀ E : C} (a : A ⟶ A') (f : A' ⟶ M)
    (b : M ⟶ C₀) (c : C₀ ⟶ E)
    (h h' : B = M) :
    (a ≫ f ≫ eqToHom h.symm) ≫ eqToHom h' ≫ b ≫ c =
      a ≫ (f ≫ b) ≫ c := by
  subst M
  cases h'
  simp

/-- A pair of source transports which returns to the original source, and two
independently proved copies of the same target transport, do not change a
morphism square. -/
theorem eqToHom_double_conjugation_square
    {A B R B' : C} (f : A ⟶ B) (hb hb' : B = B')
    (ha : A = R) (ha' : R = A) :
    f ≫ eqToHom hb = eqToHom ha ≫ eqToHom ha' ≫ f ≫ eqToHom hb' := by
  subst B'
  subst R
  simp

/-- Explicit inverse endpoint transports cancel a conjugated morphism. -/
theorem eqToHom_conjugation_cancel
    {A A' B B' : C} (f : A ⟶ B) (ha : A' = A) (hb : B' = B) :
    eqToHom ha.symm ≫ (eqToHom ha ≫ f ≫ eqToHom hb.symm) ≫
        eqToHom hb = f := by
  subst A
  subst B
  simp

/-- Two equality-transport paths with the same endpoints agree even when they
pass through different propositionally equal intermediate objects. -/
theorem eqToHom_two_step_coherence
    {A B B' C₀ : C} (h₁ : A = B) (h₂ : B = C₀)
    (h₁' : A = B') (h₂' : B' = C₀) :
    eqToHom h₁ ≫ eqToHom h₂ = eqToHom h₁' ≫ eqToHom h₂' := by
  subst B
  subst B'
  subst C₀
  simp

/-- Changing a Boolean cover label along an actual equality changes neither
the common-coordinate morphism nor its proof-carrying membership argument. -/
theorem mapPath_label_eq {b b' : Bool} {a z : X} (q : Path a z)
    (h : b = b') (hq : ∀ t, q t ∈ twoChart U V b)
    (hq' : ∀ t, q t ∈ twoChart U V b') :
    D.mapPath b q hq = D.mapPath b' q hq' := by
  subst b'
  congr

/-- Every old chain object is literally the refined chain object selected by
the `succAbove` restriction, after exposing the inserted vertex coordinate. -/
theorem subdivisionChain_obj_eq_refinedRestrictedChain_obj
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 2)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).obj i =
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain D ins).obj i := by
  change D.obj (p (S.vertex i)) =
    D.obj (p (PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
      ((PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i)))
  rw [PathTwoOpenSubdivision.insertedVertex_old]

/-- The canonical object-coordinate isomorphism used in every successor
square of the insertion comparison. -/
def subdivisionRefinementObjectIso
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 2)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).obj i ≅
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain D ins).obj i :=
  eqToIso (subdivisionChain_obj_eq_refinedRestrictedChain_obj D ins i)

@[simp] theorem subdivisionRefinementObjectIso_hom
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 2)) :
    (subdivisionRefinementObjectIso D ins i).hom =
      eqToHom (subdivisionChain_obj_eq_refinedRestrictedChain_obj D ins i) := rfl

/-- Before the split segment, the skip embedding fixes both endpoints of an
old successor edge. -/
theorem succAbove_old_successor_before
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : i < ins.segment) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.castSucc =
        i.castSucc.castSucc ∧
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.succ =
        i.succ.castSucc := by
  let pivot₀ := PathTwoOpenSubdivision.insertedSidePosition S ins.segment
  have h₀ : i.castSucc < pivot₀ := by
    apply Fin.mk_lt_mk.mpr
    exact Nat.lt_succ_of_lt hi
  have h₁ : i.succ < pivot₀ := by
    apply Fin.mk_lt_mk.mpr
    exact Nat.succ_lt_succ hi
  constructor
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_lt pivot₀ i.castSucc h₀
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_lt pivot₀ i.succ h₁

/-- At the split segment, the skip embedding jumps from the old left endpoint
to the old right endpoint after the inserted vertex. -/
theorem succAbove_old_successor_crossing
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
          ins.segment.castSucc = ins.segment.castSucc.castSucc ∧
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
          ins.segment.succ = ins.segment.succ.succ := by
  let pivot₀ := PathTwoOpenSubdivision.insertedSidePosition S ins.segment
  have hp : pivot₀ = ins.segment.succ := by
    apply Fin.ext
    rfl
  have hlt : ins.segment.castSucc < pivot₀ := by
    rw [hp]
    exact Fin.castSucc_lt_succ
  constructor
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_lt pivot₀ ins.segment.castSucc hlt
  · have hp' : PathTwoOpenSubdivision.insertedVertexPosition S ins.segment =
        ins.segment.succ.castSucc := by
      apply Fin.ext
      rfl
    rw [hp']
    exact Fin.succAbove_castSucc_self _

/-- After the split segment, the skip embedding shifts both endpoints by one. -/
theorem succAbove_old_successor_after
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : ins.segment < i) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.castSucc =
        i.castSucc.succ ∧
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.succ =
        i.succ.succ := by
  let pivot₀ := PathTwoOpenSubdivision.insertedSidePosition S ins.segment
  have h₀ : pivot₀ ≤ i.castSucc := by
    apply Fin.mk_le_mk.mpr
    exact Nat.succ_le_of_lt hi
  have h₁ : pivot₀ ≤ i.succ := h₀.trans (Fin.castSucc_le_succ i)
  constructor
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_le pivot₀ i.castSucc h₀
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_le pivot₀ i.succ h₁

/-- Typed map normalization for the refined chain restricted along the
inserted-vertex skip embedding. -/
theorem refinedRestrictedChain_map_transport
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    {a b : Fin (S.n + 2)} (hab : a ≤ b)
    {a' b' : Fin (S.n + 3)} (ha :
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove a = a')
    (hb :
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove b = b') :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE hab) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj ha) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE (by
            rw [← ha, ← hb]
            exact (Fin.succAboveOrderEmb
              (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment)).monotone hab)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj hb).symm := by
  exact comp_map_eq_eqToHom_comp_map_comp_eqToHom
    (Fin.succAboveOrderEmb
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment)).monotone.functor
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
      D ins.refined) (homOfLE hab) _ (by simpa using ha) (by simpa using hb)

/-- Before the insertion, a restricted successor map is the corresponding
full refined successor map with its endpoint transports made explicit. -/
theorem refinedRestrictedChain_map_before
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : i < ins.segment) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE i.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_before ins i hi).1) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE
            (Fin.castSucc_le_castSucc_iff.mpr i.castSucc_le_succ)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_before ins i hi).2).symm := by
  exact refinedRestrictedChain_map_transport D ins i.castSucc_le_succ
    (succAbove_old_successor_before ins i hi).1
    (succAbove_old_successor_before ins i hi).2

/-- After the insertion, a restricted successor map is the corresponding
shifted full refined successor map with explicit endpoint transports. -/
theorem refinedRestrictedChain_map_after
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : ins.segment < i) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE i.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_after ins i hi).1) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE
            (Fin.succ_le_succ_iff.mpr i.castSucc_le_succ)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_after ins i hi).2).symm := by
  exact refinedRestrictedChain_map_transport D ins i.castSucc_le_succ
    (succAbove_old_successor_after ins i hi).1
    (succAbove_old_successor_after ins i hi).2

/-- At the inserted segment, the restricted successor map is the full refined
map across the two explicit endpoints surrounding the skipped vertex. -/
theorem refinedRestrictedChain_map_crossing
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE ins.segment.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_crossing ins).1) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE (by
            apply Fin.mk_le_mk.mpr
            change ins.segment.val ≤ ins.segment.val + 1 + 1
            omega)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_crossing ins).2).symm := by
  exact refinedRestrictedChain_map_transport D ins ins.segment.castSucc_le_succ
    (succAbove_old_successor_crossing ins).1
    (succAbove_old_successor_crossing ins).2

/-- The full refined map exposed in the before case is its adjacent mapped
piece. -/
theorem fullRefined_map_before_eq_mappedPiece
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D ins.refined).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr i.castSucc_le_succ)) =
        D.mappedPiece ins.refined ⟨i.val, by
          rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
          omega⟩ := by
  exact FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.adjacentChain_map_succ
    _ _ i.val (by
      rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
      omega)

/-- A full old-chain successor map is its mapped piece, with an arbitrary
`Fin` proof for the displayed segment index. -/
theorem fullOld_map_eq_mappedPiece
    (i : Fin (S.n + 1)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).map
      (homOfLE i.castSucc_le_succ) = D.mappedPiece S i := by
  exact FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.adjacentChain_map_succ
    _ _ i.val i.isLt

/-- The shifted full refined map exposed in the after case is its adjacent
mapped piece. -/
theorem fullRefined_map_after_eq_mappedPiece
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D ins.refined).map
      (homOfLE (Fin.succ_le_succ_iff.mpr i.castSucc_le_succ)) =
        D.mappedPiece ins.refined ⟨i.val + 1, by
          rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
          omega⟩ := by
  exact FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.adjacentChain_map_succ
    _ _ (i.val + 1) (by
      rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
      omega)

/-- Before the insertion, the old mapped piece is the unchanged refined
piece, with the endpoint transports induced by the two vertex equalities
displayed explicitly. -/
theorem mappedPiece_before_eq_transport_refined
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : i < ins.segment) :
    D.mappedPiece S i =
      eqToHom (congrArg D.obj (congrArg p (by
        change S.vertex i.castSucc = ins.refined.vertex
          (⟨i.val, by simp [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]⟩ :
            Fin (ins.refined.n + 1)).castSucc
        change S.vertex i.castSucc =
          PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _
        rw [show
          (⟨i.val, by
            simp [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]⟩ :
              Fin (ins.refined.n + 1)).castSucc =
            (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
              i.castSucc by
          apply Fin.ext
          exact congrArg Fin.val (succAbove_old_successor_before ins i hi).1.symm]
        exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm))) ≫
        D.mappedPiece ins.refined
          ⟨i.val, lt_trans i.isLt (Nat.lt_succ_self _)⟩ ≫
        eqToHom ((congrArg D.obj (congrArg p (by
          change S.vertex i.succ = ins.refined.vertex
            (⟨i.val, by simp [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]⟩ :
              Fin (ins.refined.n + 1)).succ
          change S.vertex i.succ =
            PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _
          rw [show
            (⟨i.val, by
              simp [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]⟩ :
                Fin (ins.refined.n + 1)).succ =
              (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
                i.succ by
            apply Fin.ext
            exact congrArg Fin.val
              (succAbove_old_successor_before ins i hi).2.symm]
          exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm))).symm) := by
  unfold FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mappedPiece
  have hs : ins.refined.side
      (⟨i.val, by simp [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]⟩ :
        Fin (ins.refined.n + 1)) = S.side i := by
    change PathTwoOpenSubdivision.insertedSide S ins.segment _ = S.side i
    let j : Fin (S.n + 2) := ⟨i.val, by omega⟩
    have hlt : j < PathTwoOpenSubdivision.insertedSidePosition S ins.segment := by
      apply Fin.mk_lt_mk.mpr
      change i.val < ins.segment.val + 1
      omega
    simpa [PathTwoOpenSubdivision.insertedSide, j] using
      Fin.insertNth_apply_below (α := fun _ ↦ Bool) hlt
        (S.side ins.segment) S.side
  let j : Fin (ins.refined.n + 1) := ⟨i.val, lt_trans i.isLt (Nat.lt_succ_self _)⟩
  have ha : S.vertex i.castSucc = ins.refined.vertex j.castSucc := by
    change S.vertex i.castSucc =
      PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter j.castSucc
    rw [show j.castSucc =
        (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.castSucc by
      apply Fin.ext
      exact congrArg Fin.val (succAbove_old_successor_before ins i hi).1.symm]
    exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm
  have hb : S.vertex i.succ = ins.refined.vertex j.succ := by
    change S.vertex i.succ =
      PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter j.succ
    rw [show j.succ =
        (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.succ by
      apply Fin.ext
      exact congrArg Fin.val (succAbove_old_successor_before ins i hi).2.symm]
    exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm
  have hp : ∀ t, p.subpath (ins.refined.vertex j.castSucc)
      (ins.refined.vertex j.succ) t ∈ twoChart U V (S.side i) := by
    simpa only [← hs] using ins.refined.piece_mem j
  have hmap :
      D.mapPath (ins.refined.side j) (ins.refined.piece j) (ins.refined.piece_mem j) =
        D.mapPath (S.side i) (ins.refined.piece j) hp :=
    mapPath_label_eq D (ins.refined.piece j) hs _ _
  rw [hmap]
  simpa only [PathTwoOpenSubdivision.piece] using
    PathMapPathTransport.TwoOpenDescentDatum.mapPath_subpath_parameter_eq
      D p ha hb hp (S.piece_mem i)

/-- After the insertion, the shifted refined piece is the old mapped piece,
with its endpoint transports displayed explicitly. -/
theorem mappedPiece_after_eq_transport_refined
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : ins.segment < i) :
    D.mappedPiece S i =
      eqToHom (congrArg D.obj (congrArg p (by
        change S.vertex i.castSucc = ins.refined.vertex
          (⟨i.val + 1, by
            rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
            omega⟩ :
            Fin (ins.refined.n + 1)).castSucc
        change S.vertex i.castSucc =
          PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _
        rw [show
          (⟨i.val + 1, by
            rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
            omega⟩ :
              Fin (ins.refined.n + 1)).castSucc =
            (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
              i.castSucc by
          apply Fin.ext
          exact congrArg Fin.val (succAbove_old_successor_after ins i hi).1.symm]
        exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm))) ≫
        D.mappedPiece ins.refined
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≫
        eqToHom ((congrArg D.obj (congrArg p (by
          change S.vertex i.succ = ins.refined.vertex
            (⟨i.val + 1, by
              rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
              omega⟩ :
              Fin (ins.refined.n + 1)).succ
          change S.vertex i.succ =
            PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _
          rw [show
            (⟨i.val + 1, by
              rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
              omega⟩ :
                Fin (ins.refined.n + 1)).succ =
              (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
                i.succ by
            apply Fin.ext
            exact congrArg Fin.val
              (succAbove_old_successor_after ins i hi).2.symm]
          exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm))).symm) := by
  unfold FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mappedPiece
  let j : Fin (ins.refined.n + 1) := ⟨i.val + 1, by
    rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
    omega⟩
  have hs : ins.refined.side j = S.side i := by
    change PathTwoOpenSubdivision.insertedSide S ins.segment j = S.side i
    have he : j =
        (PathTwoOpenSubdivision.insertedSidePosition S ins.segment).succAbove i := by
      have hle : PathTwoOpenSubdivision.insertedSidePosition S ins.segment ≤
          i.castSucc := by
        apply Fin.mk_le_mk.mpr
        simpa [PathTwoOpenSubdivision.insertedSidePosition] using hi
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      apply Fin.ext
      rfl
    rw [he, PathTwoOpenSubdivision.insertedSide_old]
  have ha : S.vertex i.castSucc = ins.refined.vertex j.castSucc := by
    change S.vertex i.castSucc =
      PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter j.castSucc
    rw [show j.castSucc =
        (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.castSucc by
      apply Fin.ext
      exact congrArg Fin.val (succAbove_old_successor_after ins i hi).1.symm]
    exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm
  have hb : S.vertex i.succ = ins.refined.vertex j.succ := by
    change S.vertex i.succ =
      PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter j.succ
    rw [show j.succ =
        (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.succ by
      apply Fin.ext
      exact congrArg Fin.val (succAbove_old_successor_after ins i hi).2.symm]
    exact (PathTwoOpenSubdivision.insertedVertex_old _ _ _ _).symm
  have hp : ∀ t, p.subpath (ins.refined.vertex j.castSucc)
      (ins.refined.vertex j.succ) t ∈ twoChart U V (S.side i) := by
    simpa only [← hs] using ins.refined.piece_mem j
  have hmap :
      D.mapPath (ins.refined.side j) (ins.refined.piece j) (ins.refined.piece_mem j) =
        D.mapPath (S.side i) (ins.refined.piece j) hp :=
    mapPath_label_eq D (ins.refined.piece j) hs _ _
  rw [hmap]
  simpa only [PathTwoOpenSubdivision.piece] using
    PathMapPathTransport.TwoOpenDescentDatum.mapPath_subpath_parameter_eq
      D p ha hb hp (S.piece_mem i)

/-- The before-insertion restricted map with its internal preorder-arrow
witness normalized before applying the adjacent-map formula. -/
theorem refinedRestrictedChain_map_before_mappedPiece
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : i < ins.segment) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE i.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_before ins i hi).1) ≫
        D.mappedPiece ins.refined ⟨i.val, by
          rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
          omega⟩ ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_before ins i hi).2).symm := by
  rw [refinedRestrictedChain_map_before D ins i hi]
  congr 1
  congr 1
  calc
    _ = (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map
          (homOfLE (Fin.castSucc_le_castSucc_iff.mpr i.castSucc_le_succ)) :=
      map_eq_of_fixed_endpoints _ _ _
    _ = _ := fullRefined_map_before_eq_mappedPiece D ins i

/-- The after-insertion restricted map with the shifted internal arrow
normalized before applying the adjacent-map formula. -/
theorem refinedRestrictedChain_map_after_mappedPiece
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : ins.segment < i) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE i.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_after ins i hi).1) ≫
        D.mappedPiece ins.refined ⟨i.val + 1, by
          rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
          omega⟩ ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_after ins i hi).2).symm := by
  rw [refinedRestrictedChain_map_after D ins i hi]
  congr 1
  congr 1
  calc
    _ = (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map
          (homOfLE (Fin.succ_le_succ_iff.mpr i.castSucc_le_succ)) :=
      map_eq_of_fixed_endpoints _ _ _
    _ = _ := fullRefined_map_after_eq_mappedPiece D ins i

/-- Successor naturality for an old edge strictly before the insertion. -/
theorem subdivisionRefinement_naturality_before
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : i < ins.segment) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).map
          (homOfLE i.castSucc_le_succ) ≫
        (subdivisionRefinementObjectIso D ins i.succ).hom =
      (subdivisionRefinementObjectIso D ins i.castSucc).hom ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
          D ins).map (homOfLE i.castSucc_le_succ) := by
  rw [fullOld_map_eq_mappedPiece D i,
    refinedRestrictedChain_map_before_mappedPiece D ins i hi,
    mappedPiece_before_eq_transport_refined D ins i hi]
  rw [subdivisionRefinementObjectIso_hom, subdivisionRefinementObjectIso_hom]
  apply eqToHom_conjugation_square
  · exact (subdivisionChain_obj_eq_refinedRestrictedChain_obj D ins i.succ).trans
      (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_before ins i hi).2)
  · exact congrArg
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
        D ins.refined).obj (succAbove_old_successor_before ins i hi).2

/-- Successor naturality for an old edge strictly after the insertion. -/
theorem subdivisionRefinement_naturality_after
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : ins.segment < i) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).map
          (homOfLE i.castSucc_le_succ) ≫
        (subdivisionRefinementObjectIso D ins i.succ).hom =
      (subdivisionRefinementObjectIso D ins i.castSucc).hom ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
          D ins).map (homOfLE i.castSucc_le_succ) := by
  rw [fullOld_map_eq_mappedPiece D i,
    refinedRestrictedChain_map_after_mappedPiece D ins i hi,
    mappedPiece_after_eq_transport_refined D ins i hi]
  rw [subdivisionRefinementObjectIso_hom, subdivisionRefinementObjectIso_hom]
  apply eqToHom_conjugation_square
  · exact (subdivisionChain_obj_eq_refinedRestrictedChain_obj D ins i.succ).trans
      (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_after ins i hi).2)
  · exact congrArg
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
        D ins.refined).obj (succAbove_old_successor_after ins i hi).2

/-- The nonadjacent refined map across the inserted vertex factors as its two
adjacent mapped pieces. -/
theorem fullRefined_map_crossing_eq_mappedPieces
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
        D ins.refined).map (homOfLE (show
          (⟨ins.segment.val, by
            change ins.segment.val < S.n + 3
            omega⟩ : Fin (ins.refined.n + 2)) ≤
            ⟨ins.segment.val + 2, by
              change ins.segment.val + 2 < S.n + 3
              omega⟩ by exact Fin.mk_le_mk.mpr (by omega))) =
      D.mappedPiece ins.refined
          ⟨ins.segment.val, by
            change ins.segment.val < S.n + 2
            omega⟩ ≫
        D.mappedPiece ins.refined
          ⟨ins.segment.val + 1, by
            change ins.segment.val + 1 < S.n + 2
            omega⟩ := by
  let F := FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
    D ins.refined
  have h₀₁ : (⟨ins.segment.val, by
      change ins.segment.val < S.n + 3
      omega⟩ : Fin (ins.refined.n + 2)) ≤
      ⟨ins.segment.val + 1, by
        change ins.segment.val + 1 < S.n + 3
        omega⟩ := Fin.mk_le_mk.mpr (by omega)
  have h₁₂ : (⟨ins.segment.val + 1, by
      change ins.segment.val + 1 < S.n + 3
      omega⟩ : Fin (ins.refined.n + 2)) ≤
      ⟨ins.segment.val + 2, by
        change ins.segment.val + 2 < S.n + 3
        omega⟩ := Fin.mk_le_mk.mpr (by omega)
  have e₀₁ : F.map (homOfLE h₀₁) =
      D.mappedPiece ins.refined ⟨ins.segment.val, by
        change ins.segment.val < S.n + 2
        omega⟩ := by
    calc
      F.map (homOfLE h₀₁) =
          F.map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr
            ins.segment.castSucc_le_succ)) := map_eq_of_fixed_endpoints F _ _
      _ = _ := by
        simpa only [F] using
          fullRefined_map_before_eq_mappedPiece D ins ins.segment
  have e₁₂ : F.map (homOfLE h₁₂) =
      D.mappedPiece ins.refined ⟨ins.segment.val + 1, by
        change ins.segment.val + 1 < S.n + 2
        omega⟩ := by
    calc
      F.map (homOfLE h₁₂) =
          F.map (homOfLE (Fin.succ_le_succ_iff.mpr
            ins.segment.castSucc_le_succ)) := map_eq_of_fixed_endpoints F _ _
      _ = _ := by
        simpa only [F] using
          fullRefined_map_after_eq_mappedPiece D ins ins.segment
  calc
    F.map _ = F.map (homOfLE h₀₁) ≫ F.map (homOfLE h₁₂) := by
      rw [← F.map_comp]
      exact map_eq_of_fixed_endpoints F _ _
    _ = _ := by rw [e₀₁, e₁₂]
                rfl

/-- The left refined segment index at the inserted crossing. -/
def crossingLeftIndex (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    Fin (ins.refined.n + 1) :=
  ⟨ins.segment.val, by change ins.segment.val < S.n + 2; omega⟩

/-- The right refined segment index at the inserted crossing. -/
def crossingRightIndex (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    Fin (ins.refined.n + 1) :=
  ⟨ins.segment.val + 1, by change ins.segment.val + 1 < S.n + 2; omega⟩

/-- Left endpoint of the left refined crossing piece. -/
theorem crossingLeft_vertex_castSucc
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    ins.refined.vertex (crossingLeftIndex ins).castSucc =
      S.vertex ins.segment.castSucc := by
  change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _ = _
  rw [show (crossingLeftIndex ins).castSucc =
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
        ins.segment.castSucc by
    apply Fin.ext
    exact congrArg Fin.val (succAbove_old_successor_crossing ins).1.symm]
  exact PathTwoOpenSubdivision.insertedVertex_old _ _ _ _

/-- Both new crossing pieces meet at the inserted parameter. -/
theorem crossingLeft_vertex_succ
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    ins.refined.vertex (crossingLeftIndex ins).succ = ins.parameter := by
  change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _ = _
  rw [show (crossingLeftIndex ins).succ =
      PathTwoOpenSubdivision.insertedVertexPosition S ins.segment by
    apply Fin.ext
    rfl]
  exact PathTwoOpenSubdivision.insertedVertex_at _ _ _

theorem crossingRight_vertex_castSucc
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    ins.refined.vertex (crossingRightIndex ins).castSucc = ins.parameter := by
  change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _ = _
  rw [show (crossingRightIndex ins).castSucc =
      PathTwoOpenSubdivision.insertedVertexPosition S ins.segment by
    apply Fin.ext
    rfl]
  exact PathTwoOpenSubdivision.insertedVertex_at _ _ _

/-- Right endpoint of the right refined crossing piece. -/
theorem crossingRight_vertex_succ
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    ins.refined.vertex (crossingRightIndex ins).succ = S.vertex ins.segment.succ := by
  change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter _ = _
  rw [show (crossingRightIndex ins).succ =
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
        ins.segment.succ by
    apply Fin.ext
    exact congrArg Fin.val (succAbove_old_successor_crossing ins).2.symm]
  exact PathTwoOpenSubdivision.insertedVertex_old _ _ _ _

/-- Both crossing pieces carry the duplicated old segment label. -/
theorem crossingLeft_side
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    ins.refined.side (crossingLeftIndex ins) = S.side ins.segment := by
  change PathTwoOpenSubdivision.insertedSide S ins.segment _ = _
  rw [show crossingLeftIndex ins =
      (PathTwoOpenSubdivision.insertedSidePosition S ins.segment).succAbove
        ins.segment by
    apply Fin.ext
    have hp : PathTwoOpenSubdivision.insertedSidePosition S ins.segment =
        ins.segment.succ := by apply Fin.ext; rfl
    rw [hp]
    exact congrArg Fin.val (Fin.succAbove_succ_self ins.segment).symm]
  exact PathTwoOpenSubdivision.insertedSide_old _ _ _

theorem crossingRight_side
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    ins.refined.side (crossingRightIndex ins) = S.side ins.segment := by
  change PathTwoOpenSubdivision.insertedSide S ins.segment _ = _
  rw [show crossingRightIndex ins =
      PathTwoOpenSubdivision.insertedSidePosition S ins.segment by
    apply Fin.ext
    rfl]
  exact PathTwoOpenSubdivision.insertedSide_at _ _

theorem mappedPiece_crossingLeft_eq_transport
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    D.mappedPiece ins.refined (crossingLeftIndex ins) =
      eqToHom (congrArg D.obj (congrArg p (crossingLeft_vertex_castSucc ins))) ≫
        D.mapPath (S.side ins.segment)
          (p.subpath (S.vertex ins.segment.castSucc) ins.parameter)
          (subpath_mem_of_mem_ordered_segment p
            (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
            (S.vertex ins.segment.castSucc) ins.parameter
            (S.monotone_vertex ins.segment.castSucc_le_succ) le_rfl ins.upper
            ins.lower (S.piece_mem ins.segment)) ≫
        eqToHom (congrArg D.obj (congrArg p
          (crossingLeft_vertex_succ ins))).symm := by
  unfold FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mappedPiece
  let hp := subpath_mem_of_mem_ordered_segment p
    (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
    (S.vertex ins.segment.castSucc) ins.parameter
    (S.monotone_vertex ins.segment.castSucc_le_succ) le_rfl ins.upper
    ins.lower (S.piece_mem ins.segment)
  have hs := crossingLeft_side ins
  have hmem : ∀ t, p.subpath
      (ins.refined.vertex (crossingLeftIndex ins).castSucc)
      (ins.refined.vertex (crossingLeftIndex ins).succ) t ∈
        twoChart U V (S.side ins.segment) := by
    intro t
    rw [crossingLeft_vertex_castSucc, crossingLeft_vertex_succ]
    exact hp t
  change D.mapPath (ins.refined.side (crossingLeftIndex ins))
    (p.subpath (ins.refined.vertex (crossingLeftIndex ins).castSucc)
      (ins.refined.vertex (crossingLeftIndex ins).succ)) _ = _
  rw [mapPath_label_eq D _ hs _ hmem]
  simpa only [PathTwoOpenSubdivision.piece] using
    PathMapPathTransport.TwoOpenDescentDatum.mapPath_subpath_parameter_eq D p
      (crossingLeft_vertex_castSucc ins) (crossingLeft_vertex_succ ins)
      hp hmem

theorem mappedPiece_crossingRight_eq_transport
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    D.mappedPiece ins.refined (crossingRightIndex ins) =
      eqToHom (congrArg D.obj (congrArg p (crossingRight_vertex_castSucc ins))) ≫
        D.mapPath (S.side ins.segment)
          (p.subpath ins.parameter (S.vertex ins.segment.succ))
          (subpath_mem_of_mem_ordered_segment p
            (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
            ins.parameter (S.vertex ins.segment.succ)
            (S.monotone_vertex ins.segment.castSucc_le_succ) ins.lower le_rfl
            ins.upper (S.piece_mem ins.segment)) ≫
        eqToHom (congrArg D.obj (congrArg p
          (crossingRight_vertex_succ ins))).symm := by
  unfold FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mappedPiece
  let hp := subpath_mem_of_mem_ordered_segment p
    (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
    ins.parameter (S.vertex ins.segment.succ)
    (S.monotone_vertex ins.segment.castSucc_le_succ) ins.lower le_rfl
    ins.upper (S.piece_mem ins.segment)
  have hs := crossingRight_side ins
  have hmem : ∀ t, p.subpath
      (ins.refined.vertex (crossingRightIndex ins).castSucc)
      (ins.refined.vertex (crossingRightIndex ins).succ) t ∈
        twoChart U V (S.side ins.segment) := by
    intro t
    rw [crossingRight_vertex_castSucc, crossingRight_vertex_succ]
    exact hp t
  change D.mapPath (ins.refined.side (crossingRightIndex ins))
    (p.subpath (ins.refined.vertex (crossingRightIndex ins).castSucc)
      (ins.refined.vertex (crossingRightIndex ins).succ)) _ = _
  rw [mapPath_label_eq D _ hs _ hmem]
  simpa only [PathTwoOpenSubdivision.piece] using
    PathMapPathTransport.TwoOpenDescentDatum.mapPath_subpath_parameter_eq D p
      (crossingRight_vertex_castSucc ins) (crossingRight_vertex_succ ins)
      hp hmem

/-- The two refined crossing pieces, after cancelling their independently
constructed transports at the inserted point, are the transported composite
of the two old subpath maps. -/
theorem mappedPieces_crossing_eq_transport_split
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    D.mappedPiece ins.refined (crossingLeftIndex ins) ≫
        D.mappedPiece ins.refined (crossingRightIndex ins) =
      eqToHom (congrArg D.obj (congrArg p
          (crossingLeft_vertex_castSucc ins))) ≫
        (D.mapPath (S.side ins.segment)
            (p.subpath (S.vertex ins.segment.castSucc) ins.parameter)
            (subpath_mem_of_mem_ordered_segment p
              (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
              (S.vertex ins.segment.castSucc) ins.parameter
              (S.monotone_vertex ins.segment.castSucc_le_succ) le_rfl ins.upper
              ins.lower (S.piece_mem ins.segment)) ≫
          D.mapPath (S.side ins.segment)
            (p.subpath ins.parameter (S.vertex ins.segment.succ))
            (subpath_mem_of_mem_ordered_segment p
              (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
              ins.parameter (S.vertex ins.segment.succ)
              (S.monotone_vertex ins.segment.castSucc_le_succ) ins.lower le_rfl
              ins.upper (S.piece_mem ins.segment))) ≫
        eqToHom (congrArg D.obj (congrArg p
          (crossingRight_vertex_succ ins))).symm := by
  rw [mappedPiece_crossingLeft_eq_transport,
    mappedPiece_crossingRight_eq_transport]
  apply eqToHom_middle_cancel
    (eqToHom (congrArg D.obj (congrArg p
      (crossingLeft_vertex_castSucc ins))))
    (D.mapPath (S.side ins.segment)
      (p.subpath (S.vertex ins.segment.castSucc) ins.parameter) _)
    (D.mapPath (S.side ins.segment)
      (p.subpath ins.parameter (S.vertex ins.segment.succ)) _)
    (eqToHom (congrArg D.obj (congrArg p
      (crossingRight_vertex_succ ins))).symm)
    (congrArg D.obj (congrArg p (crossingLeft_vertex_succ ins)))
    (congrArg D.obj (congrArg p (crossingRight_vertex_castSucc ins)))

/-- The two refined crossing pieces are the old unsplit mapped piece, conjugated
by the explicit outer endpoint transports. -/
theorem mappedPieces_crossing_eq_transport_old
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    D.mappedPiece ins.refined (crossingLeftIndex ins) ≫
        D.mappedPiece ins.refined (crossingRightIndex ins) =
      eqToHom (congrArg D.obj (congrArg p
          (crossingLeft_vertex_castSucc ins))) ≫
        D.mappedPiece S ins.segment ≫
        eqToHom (congrArg D.obj (congrArg p
          (crossingRight_vertex_succ ins))).symm := by
  rw [mappedPieces_crossing_eq_transport_split]
  unfold FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mappedPiece
  simp only [PathTwoOpenSubdivision.piece]
  have hsplit := mapPath_subpath_split_of_subpath_mem D p
    (S.vertex ins.segment.castSucc) ins.parameter
    (S.vertex ins.segment.succ) ins.lower ins.upper (S.piece_mem ins.segment)
  have hmap :
      D.mapPath (S.side ins.segment)
          (p.subpath (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ))
          (S.piece_mem ins.segment) =
        D.mapPath (S.side ins.segment)
            (p.subpath (S.vertex ins.segment.castSucc) ins.parameter)
            (subpath_mem_of_mem_ordered_segment p
              (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
              (S.vertex ins.segment.castSucc) ins.parameter
              (S.monotone_vertex ins.segment.castSucc_le_succ) le_rfl ins.upper
              ins.lower (S.piece_mem ins.segment)) ≫
          D.mapPath (S.side ins.segment)
            (p.subpath ins.parameter (S.vertex ins.segment.succ))
            (subpath_mem_of_mem_ordered_segment p
              (S.vertex ins.segment.castSucc) (S.vertex ins.segment.succ)
              ins.parameter (S.vertex ins.segment.succ)
              (S.monotone_vertex ins.segment.castSucc_le_succ) ins.lower le_rfl
              ins.upper (S.piece_mem ins.segment)) := by
    simpa only using hsplit
  rw [← hmap]
  rfl

/-- The restricted crossing map with the skipped refined arrow normalized to
the two adjacent mapped pieces. -/
theorem refinedRestrictedChain_map_crossing_mappedPieces
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE ins.segment.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_crossing ins).1) ≫
        (D.mappedPiece ins.refined (crossingLeftIndex ins) ≫
          D.mappedPiece ins.refined (crossingRightIndex ins)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_crossing ins).2).symm := by
  rw [refinedRestrictedChain_map_crossing D ins]
  congr 1
  congr 1
  calc
    _ = (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE (show
            (⟨ins.segment.val, by change ins.segment.val < S.n + 3; omega⟩ :
              Fin (ins.refined.n + 2)) ≤
            ⟨ins.segment.val + 2, by
              change ins.segment.val + 2 < S.n + 3
              omega⟩ by exact Fin.mk_le_mk.mpr (by omega))) :=
      map_eq_of_fixed_endpoints _ _ _
    _ = _ := by
      simpa only [crossingLeftIndex, crossingRightIndex] using
        fullRefined_map_crossing_eq_mappedPieces D ins

/-- The restricted crossing map normalized all the way to the transported old
mapped piece. -/
theorem refinedRestrictedChain_map_crossing_old
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE ins.segment.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_crossing ins).1) ≫
        (eqToHom (congrArg D.obj (congrArg p
            (crossingLeft_vertex_castSucc ins))) ≫
          D.mappedPiece S ins.segment ≫
          eqToHom (congrArg D.obj (congrArg p
            (crossingRight_vertex_succ ins))).symm) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_crossing ins).2).symm := by
  rw [refinedRestrictedChain_map_crossing_mappedPieces D ins]
  congr 1
  congr 1
  exact mappedPieces_crossing_eq_transport_old D ins

/-- Successor naturality at the old edge which is split by the inserted
vertex. -/
theorem subdivisionRefinement_naturality_crossing
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).map
          (homOfLE ins.segment.castSucc_le_succ) ≫
        (subdivisionRefinementObjectIso D ins ins.segment.succ).hom =
      (subdivisionRefinementObjectIso D ins ins.segment.castSucc).hom ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
          D ins).map (homOfLE ins.segment.castSucc_le_succ) := by
  rw [fullOld_map_eq_mappedPiece D ins.segment,
    refinedRestrictedChain_map_crossing_old D ins]
  rw [subdivisionRefinementObjectIso_hom, subdivisionRefinementObjectIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  apply eqToHom_double_conjugation_square

/-- The vertex-skipping embedding preserves the first vertex. -/
theorem succAbove_insertedVertexPosition_zero
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove 0 = 0 := by
  apply Fin.ext
  simp [PathTwoOpenSubdivision.insertedVertexPosition,
    PathTwoOpenSubdivision.insertedSidePosition]

/-- The vertex-skipping embedding sends the old last vertex to the refined
last vertex. -/
theorem succAbove_insertedVertexPosition_last
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
        (Fin.last (S.n + 1)) = Fin.last (S.n + 2) := by
  have hle : PathTwoOpenSubdivision.insertedVertexPosition S ins.segment ≤
      (Fin.last (S.n + 1)).castSucc := by
    apply Fin.mk_le_mk.mpr
    simp [PathTwoOpenSubdivision.insertedVertexPosition,
      PathTwoOpenSubdivision.insertedSidePosition]
    omega
  rw [Fin.succAbove_of_le_castSucc _ _ hle]
  rfl

/-- The total morphism of the restricted refined chain is the total refined
chain morphism, with the two explicit endpoint transports retained. -/
theorem refinedRestrictedChain_hom_eq_refined_hom
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).hom =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_insertedVertexPosition_zero ins)) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).hom ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_insertedVertexPosition_last ins)).symm := by
  exact refinedRestrictedChain_map_transport D ins (Fin.zero_le _)
    (succAbove_insertedVertexPosition_zero ins)
    (succAbove_insertedVertexPosition_last ins)

/-- Inverse form of the restricted/full total-map comparison. -/
theorem refined_hom_eq_refinedRestrictedChain_hom
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
        D ins.refined).hom =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_insertedVertexPosition_zero ins)).symm ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
          D ins).hom ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_insertedVertexPosition_last ins)) := by
  rw [refinedRestrictedChain_hom_eq_refined_hom D ins]
  exact eqToHom_conjugation_cancel
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
      D ins.refined).hom
    (congrArg
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
        D ins.refined).obj (succAbove_insertedVertexPosition_zero ins))
    (congrArg
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
        D ins.refined).obj (succAbove_insertedVertexPosition_last ins)) |>.symm

/-- The composable-arrow chain of an old subdivision is canonically
isomorphic to the refined chain restricted along the vertex-skipping order
embedding. -/
def subdivisionRefinementChainIso
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S ≅
      FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain D ins :=
  ComposableArrows.isoMk (subdivisionRefinementObjectIso D ins) (by
    intro i hi
    let j : Fin (S.n + 1) := ⟨i, hi⟩
    change
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).map
            (homOfLE j.castSucc_le_succ) ≫
          (subdivisionRefinementObjectIso D ins j.succ).hom =
        (subdivisionRefinementObjectIso D ins j.castSucc).hom ≫
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
            D ins).map (homOfLE j.castSucc_le_succ)
    rcases lt_trichotomy j ins.segment with h | h | h
    · exact subdivisionRefinement_naturality_before D ins j h
    · rw [h]
      exact subdivisionRefinement_naturality_crossing D ins
    · exact subdivisionRefinement_naturality_after D ins j h)

/-- Naturality of the assembled chain isomorphism on the total old and
restricted-refined morphisms. -/
theorem subdivisionRefinement_hom_naturality
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
        D S).hom ≫
        (subdivisionRefinementChainIso D ins).hom.app (Fin.last (S.n + 1)) =
      (subdivisionRefinementChainIso D ins).hom.app 0 ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
          D ins).hom := by
  exact ComposableArrows.naturality' (subdivisionRefinementChainIso D ins).hom
    0 (S.n + 1)

#print axioms subdivisionChain_obj_eq_refinedRestrictedChain_obj
#print axioms subdivisionRefinementObjectIso
#print axioms succAbove_old_successor_before
#print axioms succAbove_old_successor_crossing
#print axioms succAbove_old_successor_after
#print axioms refinedRestrictedChain_map_transport
#print axioms refinedRestrictedChain_map_before
#print axioms refinedRestrictedChain_map_after
#print axioms refinedRestrictedChain_map_crossing
#print axioms fullRefined_map_before_eq_mappedPiece
#print axioms fullRefined_map_after_eq_mappedPiece
#print axioms fullOld_map_eq_mappedPiece
#print axioms mapPath_label_eq
#print axioms mappedPiece_before_eq_transport_refined
#print axioms mappedPiece_after_eq_transport_refined
#print axioms refinedRestrictedChain_map_before_mappedPiece
#print axioms refinedRestrictedChain_map_after_mappedPiece
#print axioms subdivisionRefinement_naturality_before
#print axioms subdivisionRefinement_naturality_after
#print axioms fullRefined_map_crossing_eq_mappedPieces
#print axioms crossingLeft_vertex_castSucc
#print axioms crossingLeft_vertex_succ
#print axioms crossingRight_vertex_castSucc
#print axioms crossingRight_vertex_succ
#print axioms crossingLeft_side
#print axioms crossingRight_side
#print axioms mappedPiece_crossingLeft_eq_transport
#print axioms mappedPiece_crossingRight_eq_transport
#print axioms eqToHom_middle_cancel
#print axioms mappedPieces_crossing_eq_transport_split
#print axioms mappedPieces_crossing_eq_transport_old
#print axioms refinedRestrictedChain_map_crossing_mappedPieces
#print axioms refinedRestrictedChain_map_crossing_old
#print axioms eqToHom_double_conjugation_square
#print axioms subdivisionRefinement_naturality_crossing
#print axioms subdivisionRefinementChainIso
#print axioms eqToHom_conjugation_square

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidInsertionChainComparison
