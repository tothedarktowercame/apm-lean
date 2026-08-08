import Mathlib

/-!
# APM t93J02 — nested intersections of compact connected sets

## Statement repairs

None. The sequence beginning at one in the source is harmlessly reindexed by
Lean's natural numbers beginning at zero.

## Encoding questions

None.
-/

open Set

noncomputable section

theorem apm_t93j02 {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (C : ℕ → Set Y)
    (hcompact : ∀ n, IsCompact (C n))
    (hconn : ∀ n, IsConnected (C n))
    (hclosed : ∀ n, IsClosed (C n))
    (hsubset : ∀ n, C (n + 1) ⊆ C n)
    (hne : ∀ n, (C n).Nonempty) :
    IsCompact (⋂ n, C n) ∧ IsConnected (⋂ n, C n) := by
  have hKclosed : IsClosed (⋂ n, C n) := isClosed_iInter hclosed
  have hKcompact : IsCompact (⋂ n, C n) :=
    (hcompact 0).of_isClosed_subset hKclosed (iInter_subset C 0)
  -- Cantor intersection, used as in the solved sibling `t91J04`.
  have hKne : (⋂ n, C n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      C hsubset hne (hcompact 0) hclosed
  refine ⟨hKcompact, hKne, ?_⟩
  intro u v hu hv hcover hmeet hmeet'
  by_contra hinter
  have hAu : (⋂ n, C n) ∩ u = (⋂ n, C n) \ v := by
    ext x
    constructor
    · rintro ⟨hxK, hxu⟩
      exact ⟨hxK, fun hxv => hinter ⟨x, hxK, hxu, hxv⟩⟩
    · rintro ⟨hxK, hxv⟩
      exact ⟨hxK, (hcover hxK).resolve_right hxv⟩
  have hBv : (⋂ n, C n) ∩ v = (⋂ n, C n) \ u := by
    ext x
    constructor
    · rintro ⟨hxK, hxv⟩
      exact ⟨hxK, fun hxu => hinter ⟨x, hxK, hxu, hxv⟩⟩
    · rintro ⟨hxK, hxu⟩
      exact ⟨hxK, (hcover hxK).resolve_left hxu⟩
  have hAcompact : IsCompact ((⋂ n, C n) ∩ u) := hAu ▸ hKcompact.diff hv
  have hBcompact : IsCompact ((⋂ n, C n) ∩ v) := hBv ▸ hKcompact.diff hu
  have hABdisjoint : Disjoint ((⋂ n, C n) ∩ u) ((⋂ n, C n) ∩ v) := by
    rw [Set.disjoint_left]
    exact fun x hxA hxB => hinter ⟨x, hxA.1, hxA.2, hxB.2⟩
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    -- Mathlib separates disjoint compact sets in a Hausdorff space.
    SeparatedNhds.of_isCompact_isCompact hAcompact hBcompact hABdisjoint
  have hKcover : ⋂ n, C n ⊆ U ∪ V := by
    intro x hxK
    rcases hcover hxK with hxu | hxv
    · exact Or.inl (hAU ⟨hxK, hxu⟩)
    · exact Or.inr (hBV ⟨hxK, hxv⟩)
  have hstage : ∃ N, C N ⊆ U ∪ V := by
    by_contra hall
    push_neg at hall
    let D : ℕ → Set Y := fun n => C n \ (U ∪ V)
    have hDsubset : ∀ n, D (n + 1) ⊆ D n := fun n =>
      diff_subset_diff_left (hsubset n)
    have hDne : ∀ n, (D n).Nonempty := fun n => not_subset.mp (hall n)
    have hDclosed : ∀ n, IsClosed (D n) := fun n =>
      (hclosed n).inter (hU.union hV).isClosed_compl
    have hDcompact : IsCompact (D 0) :=
      (hcompact 0).diff (hU.union hV)
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        D hDsubset hDne hDcompact hDclosed
    have hxK : x ∈ ⋂ n, C n :=
      mem_iInter.2 fun n => (Set.mem_diff x).1 (mem_iInter.1 hx n) |>.1
    exact ((Set.mem_diff x).1 (mem_iInter.1 hx 0)).2 (hKcover hxK)
  obtain ⟨N, hN⟩ := hstage
  have hCNK : ⋂ n, C n ⊆ C N := iInter_subset C N
  have hmeetU : (C N ∩ U).Nonempty := hmeet.mono fun x hx =>
    ⟨hCNK hx.1, hAU hx⟩
  have hmeetV : (C N ∩ V).Nonempty := hmeet'.mono fun x hx =>
    ⟨hCNK hx.1, hBV hx⟩
  obtain ⟨x, hxCN, hxU, hxV⟩ :=
    (hconn N).isPreconnected U V hU hV hN hmeetU hmeetV
  exact Set.disjoint_left.1 hUV hxU hxV
