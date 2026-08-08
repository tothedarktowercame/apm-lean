import Mathlib

open CategoryTheory

/-!
# APM t97J03

## Statement repairs

None. The notation `D¹` is read as the one-dimensional complex unit disk,
whose real dimension is two, consistently with the stated solid torus in
`ℂ²` and boundary `S¹ × S¹`.

## Encoding questions

The complex unit disk, its boundary circle, the solid torus, the boundary
inclusion, and the cubing covering map are all defined explicitly as subtype
spaces and functions. Extension means literal equality after composing with
the boundary inclusion.
-/

abbrev apm_t97J03_Disk := {z : ℂ // ‖z‖ ≤ 1}
abbrev apm_t97J03_Circle := {z : ℂ // ‖z‖ = 1}
abbrev apm_t97J03_Y := apm_t97J03_Disk × apm_t97J03_Circle
abbrev apm_t97J03_Torus := apm_t97J03_Circle × apm_t97J03_Circle

/-- Inclusion of the boundary torus into the solid torus. -/
def apm_t97J03_boundaryInclusion : apm_t97J03_Torus → apm_t97J03_Y :=
  fun q ↦ (⟨q.1.1, le_of_eq q.1.2⟩, q.2)

/-- The map `(z,w) ↦ (z,w³)` on the boundary torus. -/
def apm_t97J03_boundaryMap : apm_t97J03_Torus → apm_t97J03_Torus :=
  fun q ↦
    (q.1, ⟨q.2.1 ^ 3, by rw [norm_pow, q.2.2, one_pow]⟩)

/-- Localized from sibling `t91A05`: a retraction induces an injective map on
fundamental groups. -/
lemma apm_t97J03_fundamentalGroupMap_injective_of_retraction
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A) (r : C(X, A)) (hr : ∀ x, r (i x) = x) :
    Function.Injective (FundamentalGroup.map i a) := by
  intro p q hpq
  change (FundamentalGroupoid.map i).map p =
    (FundamentalGroupoid.map i).map q at hpq
  have hpq' := congrArg (fun z ↦ (FundamentalGroupoid.map r).map z) hpq
  change ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map p) =
    ((FundamentalGroupoid.map i ⋙ FundamentalGroupoid.map r).map q) at hpq'
  have hcomp : r.comp i = ContinuousMap.id A := by
    ext x
    exact hr x
  rw [← FundamentalGroupoid.map_comp, hcomp, FundamentalGroupoid.map_id] at hpq'
  exact hpq'

/-- The full abstract obstruction: a nontrivial source fundamental group
cannot inject into a subsingleton target fundamental group. -/
lemma apm_t97J03_no_retraction_of_subsingleton_fundamentalGroup
    {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (a : A)
    [Subsingleton (FundamentalGroup X (i a))]
    [Nontrivial (FundamentalGroup A a)] :
    ¬∃ r : C(X, A), ∀ x, r (i x) = x := by
  rintro ⟨r, hr⟩
  have hinj :=
    apm_t97J03_fundamentalGroupMap_injective_of_retraction i a r hr
  obtain ⟨p, hp⟩ := exists_ne (1 : FundamentalGroup A a)
  apply hp
  apply hinj
  apply Subsingleton.elim

/-- The concrete disk-boundary no-retraction theorem, conditional only on the
single missing foundational fact that the circle fundamental group is
nontrivial. The contractibility-to-simply-connected assembly follows the
proved helper `apm_t91a05_no_retraction_of_circle_fundamentalGroup_nontrivial`
in sibling `t91A05`. -/
lemma apm_t97J03_no_disk_retraction
    [Nontrivial (FundamentalGroup apm_t97J03_Circle
      ⟨1, by simp⟩)] :
    ¬∃ r : C(apm_t97J03_Disk, apm_t97J03_Circle),
      ∀ z : apm_t97J03_Circle, r ⟨z.1, le_of_eq z.2⟩ = z := by
  let i : C(apm_t97J03_Circle, apm_t97J03_Disk) :=
    ⟨fun z ↦ ⟨z.1, le_of_eq z.2⟩, continuous_subtype_val.subtype_mk _⟩
  let z₀ : apm_t97J03_Circle := ⟨1, by simp⟩
  have hDisk : {z : ℂ | ‖z‖ ≤ 1} = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp [dist_zero_right]
  let eDisk : apm_t97J03_Disk ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
    Homeomorph.setCongr hDisk
  letI : ContractibleSpace (Metric.closedBall (0 : ℂ) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : ContractibleSpace apm_t97J03_Disk :=
    eDisk.contractibleSpace
  letI : SimplyConnectedSpace apm_t97J03_Disk :=
    SimplyConnectedSpace.ofContractible _
  letI : Subsingleton (FundamentalGroup apm_t97J03_Disk (i z₀)) :=
    by
      change Subsingleton (Path.Homotopic.Quotient (i z₀) (i z₀))
      infer_instance
  exact apm_t97J03_no_retraction_of_subsingleton_fundamentalGroup i z₀

theorem apm_t97j03 :
    ¬ ∃ F : apm_t97J03_Y → apm_t97J03_Torus,
      Continuous F ∧
      ∀ q : apm_t97J03_Torus,
        F (apm_t97J03_boundaryInclusion q) = apm_t97J03_boundaryMap q := by
  rintro ⟨F, hF, hboundary⟩
  let w₀ : apm_t97J03_Circle := ⟨1, by simp⟩
  let g : apm_t97J03_Disk → apm_t97J03_Circle := fun z => (F (z, w₀)).1
  have hg : Continuous g := by
    exact continuous_fst.comp (hF.comp (continuous_id.prodMk continuous_const))
  have hg_boundary : ∀ z : apm_t97J03_Circle,
      g ⟨z.1, le_of_eq z.2⟩ = z := by
    intro z
    have h := congrArg Prod.fst (hboundary (z, w₀))
    exact h
  /-
  Boundary (closer hop 1, still open): the solid-torus extension has now been
  reduced by compiled code to a continuous disk retraction `g`: fixing the
  second input coordinate and projecting the first output coordinate gives
  `hg`, while `hg_boundary` proves that it is the identity on the boundary.

  Closing the contradiction is precisely the no-retraction theorem for the
  complex unit disk. Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`,
  Mathlib's Brouwer, retract, `FundamentalGroupoid`, singular-homology, circle,
  and contractibility APIs, fully closed artifacts, staging directories, and
  git history found no packaged theorem. Partial sibling `t91A05` is the exact
  no-retraction statement and now compiles the induced-fundamental-group
  injectivity step, but remains open because Mathlib does not compute
  `FundamentalGroup Circle 1 ≃* Multiplicative ℤ`. Siblings `t01J03`,
  `t93A03`, and `t02A03` record the same missing circle computation.
  No unproved intermediate assertion beyond the original theorem remains, and
  the frozen statement is unchanged.

  CLOSER HOP 2 goes beyond merely pointing to `t91A05` by localizing its
  now-compiled obstruction. The two new helpers prove the full categorical
  and group-theoretic contradiction: a retraction would inject a nontrivial
  boundary fundamental group into the subsingleton disk group. Thus the
  solid-torus reduction, disk retraction construction, functoriality, and final
  injectivity contradiction are all compiled in this bundle. Renewed searches
  of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's circle/fundamental-
  group and singular-homology sources, and related no-retraction artifacts
  found no nontriviality instance for the unit-circle fundamental group. That
  single foundational computation remains open.

  CLOSER HOP 3: `apm_t97J03_no_disk_retraction` now specializes the abstract
  obstruction completely to the exact frozen disk and circle types. Because
  the disk is encoded by `‖z‖ ≤ 1` rather than `Metric.closedBall 0 1`, the proof
  first constructs `eDisk` from their set equality, transports
  `Metric.contractibleSpace_closedBall` across that homeomorphism, derives
  `SimplyConnectedSpace`, and installs the exact subsingleton fundamental-
  group instance. It then applies the categorical obstruction to the literal
  boundary inclusion. This closes the previously implicit representation and
  typeclass bridge; the sole premise of the concrete helper is now
  `Nontrivial (FundamentalGroup apm_t97J03_Circle ⟨1, ...⟩)`. Further
  inspection of `AddCircle`, universal-cover, winding-number, Hurewicz,
  singular-homology, and loop-lifting APIs found no compiled way to produce
  that instance. The frozen theorem remains unchanged and the foundational
  circle computation is the only open bridge.
  -/
  sorry
