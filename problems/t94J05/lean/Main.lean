import Mathlib

/-!
# APM t94J05

## Statement repairs

None.

## Encoding questions

The source torus is the actual product of two circles and the target is the
unit `3`-sphere in Euclidean `ℝ⁴`.  Mathlib does not expose a convenient
single smooth-map predicate between these particular embedded-manifold
instances, so smoothness is isolated as a typed predicate on the genuine
continuous map.  Homotopy is Mathlib's native continuous-map homotopy.
-/

open scoped ContDiff

abbrev apm_t94J05_Torus := Circle × Circle
abbrev apm_t94J05_R4 := EuclideanSpace ℝ (Fin 4)
abbrev apm_t94J05_S3 := Metric.sphere (0 : apm_t94J05_R4) 1

/-- The point `(0,0,0,1)` on the unit three-sphere. -/
noncomputable def apm_t94J05_northPole : apm_t94J05_S3 :=
  ⟨EuclideanSpace.single (3 : Fin 4) 1, by simp⟩

/-- Smoothness of a map between the embedded torus and three-sphere. -/
opaque apm_t94J05_IsSmooth (f : C(apm_t94J05_Torus, apm_t94J05_S3)) : Prop

/-- A nonsurjective map to the sphere factors through the complement of a
missed point. This is the sphere-specialized form of the bridge proved in
problem `t01A01`. -/
lemma apm_t94J05_factor_through_complement
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (hnot_surj : ¬Function.Surjective f) :
    ∃ q : apm_t94J05_S3,
      ∃ g : C(apm_t94J05_Torus, {y : apm_t94J05_S3 // y ≠ q}),
        ∀ x, (g x : apm_t94J05_S3) = f x := by
  obtain ⟨q, hq⟩ : ∃ q : apm_t94J05_S3, ∀ x, f x ≠ q := by
    simpa [Function.Surjective] using hnot_surj
  refine ⟨q, ⟨fun x ↦ ⟨f x, hq x⟩, f.continuous.subtype_mk _⟩, ?_⟩
  intro x
  rfl

/-- A null-homotopy of the complement-valued factor descends along the
subtype inclusion. -/
lemma apm_t94J05_nullhomotopic_of_factor
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (q : apm_t94J05_S3)
    (g : C(apm_t94J05_Torus, {y : apm_t94J05_S3 // y ≠ q}))
    (hfg : ∀ x, (g x : apm_t94J05_S3) = f x)
    (p : {y : apm_t94J05_S3 // y ≠ q})
    (hg : ContinuousMap.Homotopic g (ContinuousMap.const _ p)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus (p : apm_t94J05_S3)) := by
  let inclusion : C({y : apm_t94J05_S3 // y ≠ q}, apm_t94J05_S3) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hcomp := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl inclusion) hg
  have hleft : inclusion.comp g = f := by
    apply ContinuousMap.ext
    intro x
    exact hfg x
  simpa [hleft, inclusion] using hcomp

/-- On the path-connected three-sphere, the endpoint of a null-homotopy can
always be moved to the fixed north pole used by the theorem statement. -/
lemma apm_t94J05_nullhomotopic_to_northPole
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (p : apm_t94J05_S3)
    (hf : ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus p)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole) := by
  have hs : IsPathConnected (Metric.sphere (0 : apm_t94J05_R4) 1) :=
    isPathConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  letI : PathConnectedSpace apm_t94J05_S3 :=
    isPathConnected_iff_pathConnectedSpace.mp hs
  have hp : Joined p apm_t94J05_northPole := PathConnectedSpace.joined _ _
  exact hf.trans (ContinuousMap.homotopic_const_iff.mpr hp)

/-- The complement of any point of the unit sphere is contractible, obtained
by transporting the vector-space contraction through stereographic
projection. -/
lemma apm_t94J05_contractibleSpace_complement (q : apm_t94J05_S3) :
    ContractibleSpace {y : apm_t94J05_S3 // y ≠ q} := by
  let hs := stereographic (norm_eq_of_mem_sphere q)
  have hsource : ({y : apm_t94J05_S3 | y ≠ q} : Set apm_t94J05_S3) = hs.source := by
    ext y
    simp [hs]
  have htarget : hs.target = Set.univ := stereographic_target _
  let eSource : {y : apm_t94J05_S3 // y ≠ q} ≃ₜ hs.source :=
    Homeomorph.setCongr hsource
  let eTarget : hs.target ≃ₜ (ℝ ∙ (q : apm_t94J05_R4))ᗮ :=
    (Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ _)
  let e : {y : apm_t94J05_S3 // y ≠ q} ≃ₜ
      (ℝ ∙ (q : apm_t94J05_R4))ᗮ :=
    eSource.trans (hs.toHomeomorphSourceTarget.trans eTarget)
  exact e.contractibleSpace

/-- Every nonsurjective torus map is null-homotopic to the fixed north pole. -/
lemma apm_t94J05_nullhomotopic_of_not_surjective
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (hf : ¬ Function.Surjective f) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole) := by
  rcases apm_t94J05_factor_through_complement f hf with ⟨q, g, hfg⟩
  letI : ContractibleSpace {y : apm_t94J05_S3 // y ≠ q} :=
    apm_t94J05_contractibleSpace_complement q
  have hg0 : g.Nullhomotopic := by
    simpa using (id_nullhomotopic {y : apm_t94J05_S3 // y ≠ q}).comp_left g
  rcases hg0 with ⟨p, hg⟩
  exact apm_t94J05_nullhomotopic_to_northPole f p
    (apm_t94J05_nullhomotopic_of_factor f q g hfg p hg)

theorem apm_t94j05
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (hf : apm_t94J05_IsSmooth f) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole) := by
  /-
  Boundary (skipped): the intended proof uses the dimension gap and Sard's
  theorem to show that `f` misses a point, then stereographic projection and
  contractibility of the punctured sphere. I searched Mathlib's `Sard`,
  manifold `ContDiff`, sphere connectivity, stereographic projection,
  contractibility, and `ContinuousMap.Homotopic` APIs. Mathlib only has a
  special Sard theorem for maps between finite-dimensional vector spaces and
  an open partial stereographic chart; it does not package the required
  manifold Sard or null-homotopy result. More decisively, the frozen
  `apm_t94J05_IsSmooth` is an opaque predicate with no theorem relating `hf`
  to `ContDiff`, derivatives, critical values, or non-surjectivity, so the
  stated smoothness assumption cannot feed the informal route. Developing an
  independent obstruction-theory proof for all continuous maps from the
  torus to `S³` is also absent from Mathlib and beyond this pass.

  Closer hop 1 reused the elementary factorization pattern from sibling
  `t01A01`: `apm_t94J05_factor_through_complement` now factors any
  nonsurjective `f` through the complement of a missed sphere point, and
  `apm_t94J05_nullhomotopic_of_factor` transports a null-homotopy of that
  factor back through the subtype inclusion. Mathlib's `stereographic` has
  source exactly the complement of one point and target `univ`, but no
  packaged contraction of that source was found; constructing it requires
  scaling in the orthogonal-complement target and transporting the homotopy
  through the partial homeomorphism. Before that, the opaque
  `apm_t94J05_IsSmooth` still supplies no nonsurjectivity consequence.

  Closer hop 2 closes the endpoint-normalization step omitted above.
  `apm_t94J05_nullhomotopic_to_northPole` uses `isPathConnected_sphere`, the
  finite rank of `EuclideanSpace ℝ (Fin 4)`, and
  `ContinuousMap.homotopic_const_iff` to move any constant endpoint to the
  theorem's fixed north pole. Thus a contraction of the complement can end at
  whichever point stereographic scaling naturally chooses. Renewed inspection
  of the stereographic partial homeomorphism found the inverse and zero-value
  formulas, but no packaged continuous homotopy on its source; constructing
  that transported scaling remains open. Independently, the opaque smoothness
  hypothesis still has no eliminator yielding nonsurjectivity. The frozen
  statement is unchanged.

  CLOSER HOP 3: the stereographic contraction is now complete without an
  explicit pointwise homotopy. `apm_t94J05_contractibleSpace_complement`
  transports Mathlib's `ContractibleSpace` instance on the orthogonal
  complement through `stereographic.toHomeomorphSourceTarget`, and
  `apm_t94J05_nullhomotopic_of_not_surjective` combines this with the earlier
  factorization and endpoint-normalization lemmas. Hence every nonsurjective
  continuous map has exactly the frozen conclusion. Renewed searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib's Sard/Jacobian and
  manifold sources, topology siblings, and git history found only the
  finite-dimensional vector-space Sard theorem, not an eliminator for the
  opaque `apm_t94J05_IsSmooth` predicate or a manifold Sard theorem deriving
  nonsurjectivity. That single implication remains open.
  -/
  sorry
