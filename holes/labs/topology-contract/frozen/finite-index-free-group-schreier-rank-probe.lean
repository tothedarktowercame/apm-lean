import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

noncomputable section

namespace FiniteIndexFreeGroupSchreierRankProbe

/-- The isolated missing finite-rank refinement of Nielsen--Schreier.

Owner repair 2026-10-10 (claude-14): the previous version quantified over all
`r n : ℕ` and was false twice over. At `r = 0` natural subtraction makes
`(r - 1) * n + 1 = 1`; at `n = 0` Mathlib's `Subgroup.index` is `0` for an
infinite-index subgroup, so `⊥ ≤ FreeGroup (Fin 3)` would be free of rank 1.
Both refutations compile (standard axioms only). The consumers' LaTeX and
registered statements are correct: t99J01 has `0 < n`, r = 3; t97A03 has
r = 2, n = 2. -/
axiom finiteIndexSubgroupEquiv (r n : ℕ) (hr : 0 < r) (hn : 0 < n)
    (H : Subgroup (FreeGroup (Fin r))) (hindex : H.index = n) :
    Nonempty (H ≃* FreeGroup (Fin ((r - 1) * n + 1)))

theorem indexSubgroupFreeGroupFinThreeEquiv (n : ℕ) (hn : 0 < n)
    (H : Subgroup (FreeGroup (Fin 3))) (hindex : H.index = n) :
    Nonempty (H ≃* FreeGroup (Fin (2 * n + 1))) := by
  simpa using finiteIndexSubgroupEquiv 3 n (by decide) hn H hindex

theorem indexTwoSubgroupFreeGroupFinTwoEquiv
    (H : Subgroup (FreeGroup (Fin 2))) (hindex : H.index = 2) :
    Nonempty (H ≃* FreeGroup (Fin 3)) := by
  simpa using finiteIndexSubgroupEquiv 2 2 (by decide) (by decide) H hindex

#print axioms indexSubgroupFreeGroupFinThreeEquiv
#print axioms indexTwoSubgroupFreeGroupFinTwoEquiv

end FiniteIndexFreeGroupSchreierRankProbe
