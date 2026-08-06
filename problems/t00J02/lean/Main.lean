import Mathlib

/-!
# APM t00J02

## Statement repairs

None.

## Encoding questions

The surface is represented as an actual compact smooth real two-manifold.
Mathlib does not currently package genus, smooth embedded curves,
transversality to a submanifold, embedded-disk bounding, or the mapping degree
of closed oriented manifolds in a common interface.  These notions are
therefore isolated as typed predicates/functions below; the surface, map,
curve, inverse image, and integer-valued degree are retained explicitly.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t00J02_E := EuclideanSpace ℝ (Fin 2)
abbrev apm_t00J02_I := 𝓘(ℝ, apm_t00J02_E)

/-- The assertion that a compact oriented smooth surface has genus two. -/
opaque apm_t00J02_IsOrientedGenusTwoSurface
    (S : Type*) [TopologicalSpace S] [ChartedSpace apm_t00J02_E S] : Prop

/-- A subset is a smooth embedded closed curve in the given surface. -/
opaque apm_t00J02_IsSmoothCurve
    {S : Type*} [TopologicalSpace S] [ChartedSpace apm_t00J02_E S]
    (C : Set S) : Prop

/-- The curve represents a standard nonseparating loop around a handle. -/
opaque apm_t00J02_WrapsHandle
    {S : Type*} [TopologicalSpace S] [ChartedSpace apm_t00J02_E S]
    (C : Set S) : Prop

/-- Smooth transversality of a map to an embedded curve. -/
opaque apm_t00J02_TransverseTo
    {S : Type*} [TopologicalSpace S] [ChartedSpace apm_t00J02_E S]
    (f : S → S) (C : Set S) : Prop

/-- Every connected component of a set bounds a smoothly embedded disk. -/
opaque apm_t00J02_ComponentsBoundEmbeddedDisks
    {X : Type*} [TopologicalSpace X] [ChartedSpace apm_t00J02_E X]
    (S : Set X) : Prop

/-- The mapping degree of a self-map of a closed oriented surface. -/
opaque apm_t00J02_degree
    {S : Type*} [TopologicalSpace S] [ChartedSpace apm_t00J02_E S]
    (f : S → S) : ℤ

theorem apm_t00j02
    {S : Type*} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ChartedSpace apm_t00J02_E S]
    [IsManifold (𝓘(ℝ, apm_t00J02_E)) ∞ S]
    (hS : apm_t00J02_IsOrientedGenusTwoSurface S)
    (f : S → S) (hf : ContMDiff apm_t00J02_I apm_t00J02_I ∞ f)
    (C : Set S) (hC : apm_t00J02_IsSmoothCurve C)
    (hhandle : apm_t00J02_WrapsHandle C)
    (htrans : apm_t00J02_TransverseTo f C)
    (hdisks : apm_t00J02_ComponentsBoundEmbeddedDisks (f ⁻¹' C)) :
    apm_t00J02_degree f = 0 := by
  sorry
