import Mathlib

/-!
# APM t02A04 — fixed points after a `(1,2)` cell attachment

## Statement repairs

None.

## Encoding note

The solid torus is the product of the closed complex unit disk with the unit
circle.  The attaching curve is the `(1,2)` curve `z ↦ (z,z²)`.  The attached
space is the quotient identifying the boundary of a second disk with that
curve; thus the geometric object itself, rather than only its homology, is the
subject of the theorem.
-/

abbrev apm_t02a04_Disk := Metric.closedBall (0 : ℂ) 1
abbrev apm_t02a04_SolidTorus := apm_t02a04_Disk × Circle

inductive apm_t02a04_Glue :
    Sum apm_t02a04_SolidTorus apm_t02a04_Disk →
      Sum apm_t02a04_SolidTorus apm_t02a04_Disk → Prop
  | boundary (z : Circle) :
      apm_t02a04_Glue
        (.inr ⟨(z : ℂ), by simpa using z.property.le⟩)
        (.inl (⟨(z : ℂ), by simpa using z.property.le⟩, z ^ 2))

def apm_t02a04_X :=
  Quotient (Relation.EqvGen.setoid apm_t02a04_Glue)

noncomputable instance : TopologicalSpace apm_t02a04_X :=
  TopologicalSpace.coinduced
    (fun a => Quotient.mk (Relation.EqvGen.setoid apm_t02a04_Glue) a)
    inferInstance

/-- The quotient identifies each point of the attaching circle with its
`(1,2)` image in the solid torus.  This is the point-set gluing fact needed
before any cellular or Lefschetz calculation can begin. -/
lemma apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve (z : Circle) :
    (Quotient.mk _
        (Sum.inr
          (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk)) :
      apm_t02a04_X) =
    Quotient.mk _
      (Sum.inl
        ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk),
          z ^ 2)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (apm_t02a04_Glue.boundary z)

/-- The canonical map of the solid torus into the attached quotient. -/
def apm_t02a04_solidInclusion (x : apm_t02a04_SolidTorus) : apm_t02a04_X :=
  Quotient.mk _ (Sum.inl x)

/-- The canonical map of the attached disk into the quotient. -/
def apm_t02a04_diskInclusion (x : apm_t02a04_Disk) : apm_t02a04_X :=
  Quotient.mk _ (Sum.inr x)

/-- The solid-torus canonical map is continuous for the coinduced topology. -/
lemma apm_t02a04_continuous_solidInclusion :
    Continuous apm_t02a04_solidInclusion := by
  exact continuous_coinduced_rng.comp continuous_inl

/-- The disk canonical map is continuous for the coinduced topology. -/
lemma apm_t02a04_continuous_diskInclusion :
    Continuous apm_t02a04_diskInclusion := by
  exact continuous_coinduced_rng.comp continuous_inr

/-- The two continuous canonical maps agree along the `(1,2)` attaching map. -/
lemma apm_t02a04_diskInclusion_boundary_eq_solidInclusion_attachingCurve :
    (fun z : Circle => apm_t02a04_diskInclusion
      (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk)) =
    (fun z : Circle => apm_t02a04_solidInclusion
      ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2)) := by
  funext z
  exact apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve z

/-- A compatible pair of maps on the solid torus and attached disk respects
the generated gluing equivalence. -/
lemma apm_t02a04_gluedDesc_respects
    {Y : Type*} [TopologicalSpace Y]
    (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y))
    (hfg : ∀ z : Circle,
      g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2))
    {x y} (hxy : Relation.EqvGen apm_t02a04_Glue x y) :
    Sum.elim f g x = Sum.elim f g y := by
  induction hxy with
  | rel a b hab =>
    cases hab with
    | boundary z => exact hfg z
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Continuous pushout eliminator for the concrete cell attachment. -/
noncomputable def apm_t02a04_gluedDesc
    {Y : Type*} [TopologicalSpace Y]
    (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y))
    (hfg : ∀ z : Circle,
      g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2)) :
    C(apm_t02a04_X, Y) := by
  let raw : Sum apm_t02a04_SolidTorus apm_t02a04_Disk → Y := Sum.elim f g
  have hraw : Continuous raw := continuous_sum_dom.2 ⟨f.continuous, g.continuous⟩
  exact ⟨Quotient.lift raw (fun _ _ hxy =>
      apm_t02a04_gluedDesc_respects f g hfg hxy),
    hraw.quotient_lift (fun _ _ hxy =>
      apm_t02a04_gluedDesc_respects f g hfg hxy)⟩

@[simp] lemma apm_t02a04_gluedDesc_solidInclusion
    {Y : Type*} [TopologicalSpace Y]
    (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y))
    (hfg : ∀ z : Circle,
      g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2))
    (x : apm_t02a04_SolidTorus) :
    apm_t02a04_gluedDesc f g hfg (apm_t02a04_solidInclusion x) = f x := rfl

@[simp] lemma apm_t02a04_gluedDesc_diskInclusion
    {Y : Type*} [TopologicalSpace Y]
    (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y))
    (hfg : ∀ z : Circle,
      g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2))
    (x : apm_t02a04_Disk) :
    apm_t02a04_gluedDesc f g hfg (apm_t02a04_diskInclusion x) = g x := rfl

/-- A continuous map from the attachment is determined by its restrictions to
the solid torus and disk. -/
lemma apm_t02a04_gluedDesc_unique
    {Y : Type*} [TopologicalSpace Y]
    (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y))
    (hfg : ∀ z : Circle,
      g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) =
      f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2))
    (u : C(apm_t02a04_X, Y))
    (hus : ∀ x, u (apm_t02a04_solidInclusion x) = f x)
    (hud : ∀ x, u (apm_t02a04_diskInclusion x) = g x) :
    u = apm_t02a04_gluedDesc f g hfg := by
  ext q
  refine Quotient.inductionOn q ?_
  rintro (x | x)
  · exact hus x
  · exact hud x

/-- Rational singular homology of the `(1,2)` attachment.  This is the
homological content of its standard homotopy identification with `ℝP²`. -/
noncomputable abbrev apm_t02A04_HQ (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of apm_t02a04_X))

/-- Why this unblocks `apm_t02a04`: the attachment is rationally acyclic,
exactly as `ℝP²`; this supplies the homology input whose Lefschetz number is
one for every self-map. -/
theorem apm_t02A04_bridge_1 :
    Nonempty (apm_t02A04_HQ 0 ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k : ℕ, 0 < k → CategoryTheory.Limits.IsZero (apm_t02A04_HQ k) := by
  sorry

/-- Why this unblocks `apm_t02a04`: this is the specialized Lefschetz bridge
for the concrete finite cell attachment.  Rational acyclicity makes the
Lefschetz number of every continuous self-map equal to one, hence nonzero. -/
theorem apm_t02A04_bridge_2
    (hH : Nonempty (apm_t02A04_HQ 0 ≅ ModuleCat.of ℚ ℚ) ∧
      ∀ k : ℕ, 0 < k → CategoryTheory.Limits.IsZero (apm_t02A04_HQ k))
    (f : apm_t02a04_X → apm_t02a04_X) (hf : Continuous f) :
    ∃ x, f x = x := by
  sorry

theorem apm_t02a04 :
    ∀ f : apm_t02a04_X → apm_t02a04_X,
      Continuous f → ∃ x, f x = x := by
  /-
  Boundary (closer hop 2, still open): the informal route needs a homotopy
  equivalence from
  this explicit quotient to the degree-two cell attachment model of `ℝP²`,
  its rational singular-homology computation, and the Lefschetz fixed-point
  theorem. I searched Mathlib for `Lefschetz`, fixed-point theorems,
  `singularHomologyFunctor`, quotient/cell attachments, and degree-two circle
  attachments. Mathlib has metric contraction fixed-point theorems, but no
  Lefschetz number or Lefschetz fixed-point theorem, and no packaged result
  identifying this quotient with `ℝP²`. The closer search additionally checked
  `LEMMA-INDEX.md`, all `RealProjective`/`Projectivization` occurrences,
  singular-homology siblings (`t01J03`, `t97A01`), Lefsche siblings (`t01A02`,
  `t00J01`), the sphere antipodal API, all fully closed artifacts,
  `ConstructionTargets/`, and git history. None provides a CW attachment
  equivalence, the required rational homology computation, or topological
  Lefschetz theorem. The local lemma
  `apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve` now verifies the encoded
  attaching identification itself. This hop strengthens it to the continuous
  gluing cocone needed by a future cell-attachment API:
  `apm_t02a04_continuous_solidInclusion` and
  `apm_t02a04_continuous_diskInclusion` prove continuity of the canonical
  piece maps, and
  `apm_t02a04_diskInclusion_boundary_eq_solidInclusion_attachingCurve`
  packages their attaching compatibility as a function equality. These facts do not supply
  those three theorem-level bridges. No conjunct or intermediate conclusion
  is exposed in the frozen statement for a larger partial proof.

  CLOSER HOP 3: the continuous cocone is now promoted to the full
  function-level topological pushout property. `apm_t02a04_gluedDesc_respects`
  proves compatible maps on the solid torus and disk respect the generated
  relation; `apm_t02a04_gluedDesc` descends them continuously to `X`; its two
  restriction lemmas recover the input maps; and
  `apm_t02a04_gluedDesc_unique` proves uniqueness by quotient induction. Thus
  a future cell-attachment theorem can consume an actual continuous
  eliminator, rather than only a compatibility equation. Renewed searches of
  `LEMMA-INDEX.md`, `ConstructionTargets/`, all problem artifacts, Mathlib's
  pushout, singular-homology, projective-space, and fixed-point sources, and
  git history found no theorem transporting this pushout to rational homology
  or a topological Lefschetz number. The available Mayer--Vietoris sequence is
  for sheaf cohomology, and Mathlib's other “Lefschetz” results concern the
  model-theoretic Lefschetz principle. The RP²/homology/Lefschetz bridges remain
  open and the frozen statement is unchanged.
  -/
  sorry
