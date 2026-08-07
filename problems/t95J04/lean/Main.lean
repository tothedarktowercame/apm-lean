import Mathlib

/-! # APM t95J04: low-dimensional maps to spheres and six-manifolds

## Statement repairs

None.

## Encoding question

Mathlib does not bundle compact smooth manifolds by dimension with a uniform
model. We bundle their actual compact Hausdorff carriers. For the only
smooth-specific step in (a), a smooth map records the concrete Sard
consequence that it misses a point when the source dimension is smaller.
Null-homotopy, simple connectivity, and inequivalence are native topological
statements. For (b) we use `S⁶`, `S² × S⁴`, and `S³ × S³`.
-/

open scoped ContDiff Manifold

noncomputable section

structure T95J04CompactSmoothManifold (n : ℕ) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  t2 : T2Space Carrier
  compact : CompactSpace Carrier

abbrev t95J04SphereType (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

def t95J04Sphere (n : ℕ) : T95J04CompactSmoothManifold n where
  Carrier := t95J04SphereType n
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance

structure T95J04SmoothMap {k n : ℕ}
    (M : T95J04CompactSmoothManifold k)
    (N : T95J04CompactSmoothManifold n) where
  toFun : M.Carrier → N.Carrier
  continuous_toFun :
    @Continuous M.Carrier N.Carrier M.topology N.topology toFun
  missesPoint_of_dim_lt : k < n → ¬Function.Surjective toFun

def IsT95J04NullHomotopic {k n : ℕ}
    {M : T95J04CompactSmoothManifold k}
    {N : T95J04CompactSmoothManifold n}
    (f : T95J04SmoothMap M N) : Prop :=
  let _ := M.topology
  let _ := N.topology
  ∃ y : N.Carrier,
    ContinuousMap.Homotopic ⟨f.toFun, f.continuous_toFun⟩
      (ContinuousMap.const _ y)

def IsT95J04SimplyConnected {n : ℕ}
    (M : T95J04CompactSmoothManifold n) : Prop :=
  let _ := M.topology
  Nonempty M.Carrier ∧ ∀ x : M.Carrier, Subsingleton (FundamentalGroup M.Carrier x)

def T95J04Diffeomorphic {n : ℕ}
    (M N : T95J04CompactSmoothManifold n) : Prop :=
  let _ := M.topology
  let _ := N.topology
  Nonempty (M.Carrier ≃ₜ N.Carrier)

def t95J04SphereSix : T95J04CompactSmoothManifold 6 := t95J04Sphere 6

def t95J04SphereTwoFourProduct : T95J04CompactSmoothManifold 6 where
  Carrier := t95J04SphereType 2 × t95J04SphereType 4
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance

def t95J04SphereThreeProduct : T95J04CompactSmoothManifold 6 where
  Carrier := t95J04SphereType 3 × t95J04SphereType 3
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance

/-- The Sard consequence stored in `T95J04SmoothMap` supplies an actual point
missed by every map in the dimension-gap clause. -/
lemma t95J04_exists_missed_point {k n : ℕ} (hn : k < n)
    (M : T95J04CompactSmoothManifold k)
    (f : T95J04SmoothMap M (t95J04Sphere n)) :
    ∃ y : (t95J04Sphere n).Carrier, ∀ x, f.toFun x ≠ y := by
  have h := f.missesPoint_of_dim_lt hn
  simp only [Function.Surjective] at h
  push_neg at h
  exact h

lemma t95J04_sphere_nonempty (n : ℕ) : Nonempty (t95J04SphereType n) := by
  exact ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

lemma t95J04_sphereSix_nonempty : Nonempty t95J04SphereSix.Carrier :=
  t95J04_sphere_nonempty 6

lemma t95J04_sphereTwoFourProduct_nonempty :
    Nonempty t95J04SphereTwoFourProduct.Carrier :=
  Nonempty.map2 (·, ·) (t95J04_sphere_nonempty 2) (t95J04_sphere_nonempty 4)

lemma t95J04_sphereThreeProduct_nonempty :
    Nonempty t95J04SphereThreeProduct.Carrier :=
  Nonempty.map2 (·, ·) (t95J04_sphere_nonempty 3) (t95J04_sphere_nonempty 3)

theorem apm_t95j04 :
    (∀ (k n : ℕ), k < n →
      ∀ (M : T95J04CompactSmoothManifold k)
        (f : T95J04SmoothMap M (t95J04Sphere n)),
        IsT95J04NullHomotopic f) ∧
    IsT95J04SimplyConnected t95J04SphereSix ∧
    IsT95J04SimplyConnected t95J04SphereTwoFourProduct ∧
    IsT95J04SimplyConnected t95J04SphereThreeProduct ∧
    ¬T95J04Diffeomorphic t95J04SphereSix t95J04SphereTwoFourProduct ∧
    ¬T95J04Diffeomorphic t95J04SphereSix t95J04SphereThreeProduct ∧
    ¬T95J04Diffeomorphic t95J04SphereTwoFourProduct
      t95J04SphereThreeProduct := by
  /-
  PARTIAL boundary (closer hop 1).

  New progress: `t95J04_exists_missed_point` extracts the exact point omitted
  by a dimension-gap smooth map from the Sard consequence already stored in
  `T95J04SmoothMap`.  Thus the first conjunct no longer needs any Sard theorem;
  it is reduced to contracting a metric sphere with one point removed.  The
  helpers `t95J04_sphere_nonempty`, `t95J04_sphereSix_nonempty`,
  `t95J04_sphereTwoFourProduct_nonempty`, and
  `t95J04_sphereThreeProduct_nonempty` close the nonemptiness halves of all
  three frozen simple-connectivity predicates using explicit coordinate
  points.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, all closed artifacts,
  Mathlib's sphere-manifold, stereographic, fundamental-groupoid product, and
  singular-homology sources, and git history found no packaged theorem that a
  punctured metric sphere is contractible, no computation proving
  `FundamentalGroup (Metric.sphere 0 1) x` is subsingleton in dimension at
  least two, and no integral homology computation for metric spheres or their
  products.  Mathlib's `stereographic` open partial homeomorphism supplies the
  chart needed for a local construction, but a homotopy must still be built by
  scaling in its orthogonal-complement target and transported back while using
  the omitted-point proof.  The three non-homeomorphism claims then require
  new homology/Künneth calculations (degrees 2 and 3 suffice).  Siblings
  `t94J05`, `t98J03`, `t02A06`, and `t02A03` record the same missing sphere
  contractibility, homology, and fundamental-group bridges rather than closed
  reusable declarations.
  -/
  sorry
