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
#print axioms eqToHom_conjugation_square

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidInsertionChainComparison
