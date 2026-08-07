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
  /- Boundary (closer hop 1): `apm_t97J01_surjective_of_connected` closes the
  surjectivity gap (Mathlib deliberately permits empty fibers in
  `IsCoveringMap`).  Hence `p` is an `IsOpenQuotientMap`.  Mathlib's exact
  reduction `t2Space_iff_of_isOpenQuotientMap` leaves the closedness of
  `{q : X × X | p q.1 = p q.2}`.

  `hp.isSeparatedMap` only proves that the relative diagonal is closed inside
  the pullback, not that this kernel relation is closed in `X × X`.  Finite
  fibers must still be combined with the local covering trivializations to
  prove that stronger fact (equivalently, prove that this finite covering is
  a closed/proper map).  Searches of Mathlib, `LEMMA-INDEX.md`, all candidate
  attempts and closed siblings, `ConstructionTargets/`, and git history found
  no packaged finite-cover closedness theorem. -/
  sorry
