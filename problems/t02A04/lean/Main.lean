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

theorem apm_t02a04 :
    ∀ f : apm_t02a04_X → apm_t02a04_X,
      Continuous f → ∃ x, f x = x := by
  /-
  Boundary (skipped): the informal route needs a homotopy equivalence from
  this explicit quotient to the degree-two cell attachment model of `ℝP²`,
  its rational singular-homology computation, and the Lefschetz fixed-point
  theorem. I searched Mathlib for `Lefschetz`, fixed-point theorems,
  `singularHomologyFunctor`, quotient/cell attachments, and degree-two circle
  attachments. Mathlib has metric contraction fixed-point theorems, but no
  Lefschetz number or Lefschetz fixed-point theorem, and no packaged result
  identifying this quotient with `ℝP²`. Establishing these foundations is
  beyond this pass, and no conjunct or intermediate conclusion is exposed in
  the frozen statement for an honest partial proof.
  -/
  sorry
