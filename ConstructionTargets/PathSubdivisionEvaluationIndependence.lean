import ConstructionTargets.PathSubdivisionInheritedSegmentOrigin
import ConstructionTargets.PathSubdivisionLabelChangeInvariance

open Set CategoryTheory
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionEvaluationIndependence

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionInsertionReachability
open ConstructionTargets.PathSubdivisionMergedReconstruction
open ConstructionTargets.PathSubdivisionInheritedSegmentOrigin
open ConstructionTargets.PathSubdivisionLabelChangeInvariance

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}

/-- Segment membership recovered from an inherited source segment, rather
than merely from the target's Boolean label. -/
theorem InheritedSegmentOrigin.piece_mem_source
    {S R : PathTwoOpenSubdivision p U V}
    (h : InheritedSegmentOrigin S R) (k : Fin (R.n + 1)) (t : unitInterval) :
    R.piece k t ∈ twoChart U V (R.side k) := by
  obtain ⟨i, hside, hlo, hhi⟩ := h.origin k
  have hrange : R.piece k t ∈ Set.range (R.piece k) := Set.mem_range_self t
  change (p.subpath (R.vertex k.castSucc) (R.vertex k.succ)) t ∈
    Set.range (p.subpath (R.vertex k.castSucc) (R.vertex k.succ)) at hrange
  rw [Path.range_subpath_of_le p _ _ (R.vertex_le_succ k)] at hrange
  obtain ⟨r, hr, hrt⟩ := hrange
  rw [hside]
  change (p.subpath (R.vertex k.castSucc) (R.vertex k.succ)) t ∈ _
  rw [← hrt]
  exact S.segment_mem i ⟨hlo.trans hr.1, hr.2.trans hhi⟩

theorem relabelSubdivision_eq_of_eq
    (L R : PathTwoOpenSubdivision p U V)
    (hn : L.n = R.n)
    (hv : ∀ i : Fin (L.n + 2),
      L.vertex i = R.vertex (Fin.cast (congrArg (fun q : ℕ ↦ q + 2) hn) i)) :
    ∃ hmem : ∀ k : Fin (L.n + 1),
        Icc (L.vertex k.castSucc) (L.vertex k.succ) ⊆
          p ⁻¹' twoChart U V
            (R.side (Fin.cast (congrArg (fun q : ℕ ↦ q + 1) hn) k)),
      relabelSubdivision L
        (fun k ↦ R.side (Fin.cast (congrArg (fun q : ℕ ↦ q + 1) hn) k)) hmem = R := by
  cases L with
  | mk ln lv ls lzero llast lmono lmem =>
    cases R with
    | mk rn rv rs rzero rlast rmono rmem =>
      dsimp at hn
      subst rn
      dsimp at hv
      have hvfun : lv = rv := funext hv
      subst rv
      let hmem : ∀ k : Fin (ln + 1),
          Icc (lv k.castSucc) (lv k.succ) ⊆ p ⁻¹' twoChart U V (rs k) := rmem
      exact ⟨hmem, rfl⟩

variable {C : Type*} [Category C]

/-- Evaluation of a two-open descent datum is independent of the chosen
subordinate subdivision of a fixed path. -/
theorem evaluate_eq_of_subdivisions
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S T : PathTwoOpenSubdivision p U V) :
    D.evaluate S = D.evaluate T := by
  let L := (leftMergedReconstruction S T).subdivision
  let R := (rightMergedReconstruction S T).subdivision
  have hn : L.n = R.n := by
    dsimp [L, R]
    rw [leftMergedReconstruction_size, rightMergedReconstruction_size_common]
  have hv : ∀ i : Fin (L.n + 2),
      L.vertex i = R.vertex (Fin.cast (congrArg (fun q : ℕ ↦ q + 2) hn) i) := by
    intro i
    dsimp [L, R]
    rw [leftMergedReconstruction_vertex, rightMergedReconstruction_vertex]
    congr 1
  obtain ⟨hmem, hrelabel⟩ := relabelSubdivision_eq_of_eq L R hn hv
  let rside : Fin (L.n + 1) → Bool :=
    fun k ↦ R.side (Fin.cast (congrArg (fun q : ℕ ↦ q + 1) hn) k)
  have hoverlap : ∀ k, L.side k ≠ rside k →
      (∀ t, L.piece k t ∈ U) ∧ (∀ t, L.piece k t ∈ V) := by
    intro k hk
    let kr : Fin (R.n + 1) := Fin.cast (congrArg (fun q : ℕ ↦ q + 1) hn) k
    have hkr0 : kr.castSucc =
        Fin.cast (congrArg (fun q : ℕ ↦ q + 2) hn) k.castSucc := by
      apply Fin.ext
      rfl
    have hkr1 : kr.succ =
        Fin.cast (congrArg (fun q : ℕ ↦ q + 2) hn) k.succ := by
      apply Fin.ext
      rfl
    have hL := leftMergedReconstruction_segmentOrigin S T
    have hR := rightMergedReconstruction_segmentOrigin S T
    have hmL := InheritedSegmentOrigin.piece_mem_source hL k
    have hmR := InheritedSegmentOrigin.piece_mem_source hR kr
    change ∀ t, L.piece k t ∈ twoChart U V (L.side k) at hmL
    change ∀ t, R.piece kr t ∈ twoChart U V (R.side kr) at hmR
    cases hLs : L.side k <;> cases hRs : R.side kr
    · exact (hk (by simpa [rside, kr, hLs, hRs])).elim
    · refine ⟨?_, ?_⟩
      · intro t
        have ht : R.piece kr t ∈ U := by simpa [twoChart, hRs] using hmR t
        change (p.subpath (L.vertex k.castSucc) (L.vertex k.succ)) t ∈ U
        change (p.subpath (R.vertex kr.castSucc) (R.vertex kr.succ)) t ∈ U at ht
        rw [hkr0, hkr1, ← hv k.castSucc, ← hv k.succ] at ht
        exact ht
      · intro t
        simpa [twoChart, hLs] using hmL t
    · refine ⟨?_, ?_⟩
      · intro t
        simpa [twoChart, hLs] using hmL t
      · intro t
        have ht : R.piece kr t ∈ V := by simpa [twoChart, hRs] using hmR t
        change (p.subpath (L.vertex k.castSucc) (L.vertex k.succ)) t ∈ V
        change (p.subpath (R.vertex kr.castSucc) (R.vertex kr.succ)) t ∈ V at ht
        rw [hkr0, hkr1, ← hv k.castSucc, ← hv k.succ] at ht
        exact ht
    · exact (hk (by simpa [rside, kr, hLs, hRs])).elim
  have hRL : D.evaluate R = D.evaluate L := by
    rw [← hrelabel]
    exact PathSubdivisionLabelChangeInvariance.LabelChange.evaluate_relabel_eq
      D L rside hmem hoverlap
  exact (leftMergedReconstruction_reachable S T).evaluate_eq_source D |>.trans
    (hRL.symm.trans ((rightMergedReconstruction_reachable S T).evaluate_eq D))

#print axioms InheritedSegmentOrigin.piece_mem_source
#print axioms relabelSubdivision_eq_of_eq
#print axioms evaluate_eq_of_subdivisions

end ConstructionTargets.PathSubdivisionEvaluationIndependence
