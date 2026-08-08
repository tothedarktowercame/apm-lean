import Mathlib

/-!
# APM t99J04 — inverse function theorem and compact local diffeomorphisms

## Statement repairs

In part (a), `X in an n-dimensional manifold` is read as `X is an
n-dimensional manifold`. In part (b), the customary implicit assumption that
the manifold `X` is nonempty is made explicit: without it the empty compact
manifold would give a counterexample to surjectivity.

## Encoding questions

None. The differentials, their linear independence, local coordinate systems,
and the everywhere-invertible derivative are represented by Mathlib's genuine
manifold derivative and local-diffeomorphism structures.
-/

open scoped Manifold

noncomputable section

abbrev apm_t99J04_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def apm_t99J04_coordinateMap {n : ℕ} {X : Type} (f : Fin n → X → ℝ) :
    X → apm_t99J04_Euclidean n :=
  fun p ↦ WithLp.toLp 2 (fun i ↦ f i p)

/-- A local diffeomorphism from a nonempty compact space to a connected
Hausdorff space is surjective. The range is open by local invertibility and
closed by compactness. -/
lemma apm_t99J04_surjective_of_isLocalDiffeomorph
    {E E' X Y : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace E X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [ChartedSpace E' Y] (f : X → Y)
    (hf : IsLocalDiffeomorph (𝓘(ℝ, E)) (𝓘(ℝ, E')) ⊤ f) :
    Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := hf.isOpen_range
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf.contMDiff.continuous).isClosed
  have hrange : Set.range f = Set.univ :=
    (show IsClopen (Set.range f) from ⟨hclosed, hopen⟩).eq_univ
      (Set.range_nonempty f)
  exact Set.range_eq_univ.mp hrange

theorem apm_t99j04 :
    (∀ (n : ℕ) (X : Type) [TopologicalSpace X]
      [ChartedSpace (apm_t99J04_Euclidean n) X]
      [IsManifold (𝓘(ℝ, apm_t99J04_Euclidean n)) ⊤ X]
      (x : X) (f : Fin n → X → ℝ),
      (∀ i, ContMDiff (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) ⊤ (f i)) →
      LinearIndependent ℝ
        (fun i : Fin n ↦
          (NormedSpace.fromTangentSpace (f i x)).toContinuousLinearMap ∘L
            mfderiv (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) (f i) x) →
      IsLocalDiffeomorphAt (𝓘(ℝ, apm_t99J04_Euclidean n))
        𝓘(ℝ, apm_t99J04_Euclidean n) ⊤ (apm_t99J04_coordinateMap f) x) ∧
    (∀ (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
      [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [FiniteDimensional ℝ E'] [CompleteSpace E']
      (X Y : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [Nonempty X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ⊤ X]
      [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
      [ChartedSpace E' Y] [IsManifold (𝓘(ℝ, E')) ⊤ Y]
      (f : X → Y),
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E')) ⊤ f →
      (∀ x, Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E')) f x)) →
      Function.Surjective f) := by
  /-
  PARTIAL boundary (closer hop 1).

  `apm_t99J04_surjective_of_isLocalDiffeomorph` closes the global topological
  part of the second conjunct. A local diffeomorphism has open range by
  `IsLocalDiffeomorph.isOpen_range`; its smoothness makes the range compact,
  hence closed in the Hausdorff target; connectedness and nonemptiness then
  force that clopen range to be all of `Y`.

  The remaining common bridge for both frozen conjuncts is the manifold
  inverse function theorem from derivative data. Mathlib's
  `ContDiffAt.toOpenPartialHomeomorph` proves the Banach-space theorem in
  charts, but `Geometry.Manifold.LocalDiffeomorph` explicitly lists as a TODO
  the desired promotion from `ContMDiffAt` plus invertible `mfderiv` to
  `IsLocalDiffeomorphAt`. Applying the Banach theorem manually requires
  transporting through `extChartAt`, proving its coordinate derivative is a
  continuous linear equivalence, and assembling the resulting chart-local
  partial homeomorphism into a `PartialDiffeomorph`.

  For the first conjunct one must additionally compute the manifold derivative
  of `apm_t99J04_coordinateMap` and turn linear independence of its `n`
  coordinate covectors into bijectivity between the two `n`-dimensional
  tangent/model spaces. Searches of `LEMMA-INDEX.md`, all
  `ConstructionTargets/`, manifold/inverse-function siblings, Mathlib's
  `MFDeriv`, atlas, finite-dimensional dual-basis, and inverse-function
  sources, and git history found no packaged theorem performing either
  assembly. The statement is unchanged.
  -/
  sorry
