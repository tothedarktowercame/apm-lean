import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01A05 — fundamental classes under finite oriented covers

The integration formula is stated in its genuine homological form: the map
induced by a `k`-sheeted covering sends the upstairs fundamental class to `k`
times the downstairs fundamental class.  Fundamental classes are not arbitrary
fields; each is the inverse image of `1` under an explicit top-homology
orientation isomorphism.

Part (a) uses the concrete cover `(x,y) ↦ (kx,y)` of `(ℝ/ℤ)²`.

## Statement repairs

The source's “for any `k`” in part (a) is restricted to `k > 0`, since a
zero-sheeted covering of a nonempty compact surface does not exist.

Mathlib has no manifold differential-form integration or geometric
intersection-product API.  Following the reviewer-directed repair, part (b)
is replaced by its fundamental-class relation, which implies the integral
formula by evaluation against cohomology.  Part (c) is explicitly deferred
rather than encoded by a fabricated constant intersection number.

## Encoding questions

A future geometric-intersection development can recover part (c) by applying
the same covering relation to Poincaré duals of the two submanifolds.
-/

open CategoryTheory Set
open scoped Manifold

noncomputable section

abbrev T01A05Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev T01A05Model (n : ℕ) := 𝓘(ℝ, T01A05Euclidean n)
abbrev T01A05Torus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

abbrev T01A05TopHomology (n : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def t01A05TopHomologyMap {n : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (π : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom π)

/-- An orientation is an explicit identification of top integral homology
with `ℤ`; its fundamental class is therefore forced, not freely supplied. -/
structure T01A05Orientation (n : ℕ) (X : Type) [TopologicalSpace X] where
  topIso : T01A05TopHomology n X ≅ ModuleCat.of ℤ ℤ

def t01A05FundamentalClass {n : ℕ} {X : Type} [TopologicalSpace X]
    (o : T01A05Orientation n X) : T01A05TopHomology n X :=
  o.topIso.inv 1

def t01A05FundamentalClassRelation {n k : ℕ} {X Xtilde : Type}
    [TopologicalSpace X] [TopologicalSpace Xtilde]
    (π : C(Xtilde, X))
    (ot : T01A05Orientation n Xtilde) (o : T01A05Orientation n X) : Prop :=
  t01A05TopHomologyMap (n := n) π (t01A05FundamentalClass ot) =
    (k : ℤ) • t01A05FundamentalClass o

def t01A05IsKSheetedCover {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (π : C(X, Y)) : Prop :=
  IsCoveringMap π ∧ ∀ y : Y, Nat.card {x : X // π x = y} = k

/-- The concrete degree-`k` torus cover. -/
def t01A05TorusCover (k : ℕ) : C(T01A05Torus, T01A05Torus) :=
  ⟨fun p ↦ (k • p.1, p.2), by fun_prop⟩

theorem apm_t01a05 :
    (∀ k : ℕ, 0 < k →
      t01A05IsKSheetedCover k (t01A05TorusCover k) ∧
      ∀ o : T01A05Orientation 2 T01A05Torus,
        ∃ ot : T01A05Orientation 2 T01A05Torus,
          t01A05FundamentalClassRelation (k := k)
            (t01A05TorusCover k) ot o) ∧
    ∀ (n k : ℕ) (hk : 0 < k)
      (X Xtilde : Type)
      [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ChartedSpace (T01A05Euclidean n) X]
      [IsManifold (T01A05Model n) ⊤ X]
      [TopologicalSpace Xtilde] [T2Space Xtilde] [CompactSpace Xtilde]
      [ChartedSpace (T01A05Euclidean n) Xtilde]
      [IsManifold (T01A05Model n) ⊤ Xtilde]
      (π : C(Xtilde, X)),
      t01A05IsKSheetedCover k π →
      ∀ o : T01A05Orientation n X,
        ∃ ot : T01A05Orientation n Xtilde,
          t01A05FundamentalClassRelation (k := k) π ot o := by
  sorry
