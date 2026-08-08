import Mathlib

/-!
# APM t97J01

## Statement repairs

The printed claim omits the necessary assumption that the covering space `X`
is Hausdorff. Without it, the identity map of any connected non-Hausdorff
space is a one-sheeted covering and is an immediate counterexample. The
minimal `T2Space X` hypothesis is therefore added.

## Encoding questions

A finite cover is encoded as an actual Mathlib `IsCoveringMap` whose fibers
are finite sets. Connectedness is retained for both spaces exactly as printed.
-/

open Set

/-- A covering map from a nonempty space onto a preconnected space is
surjective.  Empty fibers are allowed by `IsCoveringMap`, but their evenly
covered neighborhoods show that the complement of the range is open. -/
theorem apm_t97J01_surjective_of_connected
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [PreconnectedSpace Y]
    (p : X → Y) (hp : IsCoveringMap p) : Function.Surjective p := by
  have hopen : IsOpen (Set.range p) := by
    simpa only [Set.image_univ] using hp.isOpenMap Set.univ isOpen_univ
  have hclosed : IsClosed (Set.range p) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hyrange : y ∉ Set.range p := by simpa using hy
    rcases hp y with ⟨_, U, hyU, hU, _, H, _⟩
    refine Filter.mem_of_superset (hU.mem_nhds hyU) ?_
    rintro z hzU ⟨x, rfl⟩
    let i : p ⁻¹' ({y} : Set Y) := (H ⟨x, hzU⟩).2
    exact hyrange ⟨i.1, i.2⟩
  have hrange : Set.range p = Set.univ :=
    (show IsClopen (Set.range p) from ⟨hclosed, hopen⟩).eq_univ (Set.range_nonempty p)
  exact Set.range_eq_univ.mp hrange

theorem apm_t97j01
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [ConnectedSpace Y] [T2Space X]
    (p : X → Y) (hp : IsCoveringMap p)
    (hfinite : ∀ y : Y, (p ⁻¹' ({y} : Set Y)).Finite) :
    T2Space Y := by
  classical
  have hsurj : Function.Surjective p :=
    apm_t97J01_surjective_of_connected p hp
  choose U hyU hU hpU H hH using fun y ↦ (hp y).2
  let Uo : Y → TopologicalSpace.Opens Y := fun y ↦ ⟨U y, hU y⟩
  have hcover : TopologicalSpace.IsOpenCover Uo :=
    TopologicalSpace.IsOpenCover.of_sets (fun y ↦ hU y) <| by
      apply Set.eq_univ_of_forall
      intro y
      exact Set.mem_iUnion.2 ⟨y, hyU y⟩
  have hclosed : IsClosedMap p :=
    (hcover.isClosedMap_iff_restrictPreimage).2 fun y ↦ by
      letI : Fintype (p ⁻¹' ({y} : Set Y)) := (hfinite y).fintype
      have heq : (Uo y).1.restrictPreimage p = Prod.fst ∘ H y := by
        funext x
        apply Subtype.ext
        exact (hH y x).symm
      rw [heq]
      exact isClosedMap_fst_of_compactSpace.comp (H y).isClosedMap
  refine ⟨?_⟩
  intro y₁ y₂ hne
  let F₁ : Set X := p ⁻¹' ({y₁} : Set Y)
  let F₂ : Set X := p ⁻¹' ({y₂} : Set Y)
  have hF₁c : IsCompact F₁ := (hfinite y₁).isCompact
  have hF₂c : IsCompact F₂ := (hfinite y₂).isCompact
  have hF₂closed : IsClosed F₂ := (hfinite y₂).isClosed
  have hdisj : Disjoint F₁ F₂ := by
    refine Set.disjoint_left.2 ?_
    intro x hx₁ hx₂
    exact hne (hx₁.symm.trans hx₂)
  rcases SeparatedNhds.of_isCompact_isCompact_isClosed
      hF₁c hF₂c hF₂closed hdisj with
    ⟨V₁, V₂, hV₁, hV₂, hFV₁, hFV₂, hVV⟩
  refine ⟨kernImage p V₁, kernImage p V₂,
    (isClosedMap_iff_kernImage.1 hclosed) hV₁,
    (isClosedMap_iff_kernImage.1 hclosed) hV₂, ?_, ?_, ?_⟩
  · exact hFV₁
  · exact hFV₂
  · refine Set.disjoint_left.2 ?_
    intro y hy₁ hy₂
    obtain ⟨x, rfl⟩ := hsurj y
    exact Set.disjoint_left.1 hVV (hy₁ rfl) (hy₂ rfl)
