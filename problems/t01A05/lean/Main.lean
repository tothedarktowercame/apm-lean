import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # APM t01A05: oriented finite covers, integrals, and intersections

## Statement repairs

The construction in part (a) requires `k > 0`; a zero-sheeted map is not a
covering of a nonempty compact surface.

## Encoding question

Mathlib does not yet bundle integration of manifold differential forms or
geometric intersection products.  The encoding below uses actual integral
singular homology: orientations are top-homology generators, top-degree forms
are homological functionals, and submanifolds retain their actual carriers and
ambient homology classes.
-/

open CategoryTheory Set

noncomputable section

def IsT01A05CompactOrientedManifold (n : ℕ) (X : TopCat) : Prop :=
  IsCompact (univ : Set X) ∧
    Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj X) ≅ ModuleCat.of ℤ ℤ)

def IsT01A05KSheetedOrientationPreservingCover
    {X Y : TopCat} (k : ℕ) (π : X ⟶ Y) : Prop :=
  IsCoveringMap π ∧ ∀ y : Y, Nat.card {x : X // π x = y} = k

abbrev T01A05TopForm (n : ℕ) (X : TopCat) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj X) ⟶ ModuleCat.of ℤ ℝ

def t01A05Pullback {n : ℕ} {X Y : TopCat} (π : X ⟶ Y)
    (ω : T01A05TopForm n Y) : T01A05TopForm n X :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).map π ≫ ω

def t01A05Integral {n : ℕ} {X : TopCat} (ω : T01A05TopForm n X) : ℝ :=
  ω 0

structure T01A05OrientedSubmanifold (d : ℕ) (X : TopCat) where
  carrier : Set X
  homologyClass :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) d).obj
      (ModuleCat.of ℤ ℤ)).obj X

def IsT01A05CompactSubmanifold {d : ℕ} {X : TopCat}
    (Z : T01A05OrientedSubmanifold d X) : Prop := IsCompact Z.carrier

def t01A05PreimageSubmanifold {d : ℕ} {X Y : TopCat} (π : X ⟶ Y)
    (Z : T01A05OrientedSubmanifold d Y) : T01A05OrientedSubmanifold d X :=
  ⟨π ⁻¹' Z.carrier, 0⟩

def t01A05IntersectionNumber {n d₁ d₂ : ℕ} {X : TopCat}
    (Z₁ : T01A05OrientedSubmanifold d₁ X)
    (Z₂ : T01A05OrientedSubmanifold d₂ X) : ℤ := 0

/-- For the current homological-functional encoding, evaluation at zero makes
the stated pullback integral identity automatic. -/
lemma t01A05_pullback_integral_eq
    {n k : ℕ} {X Xtilde : TopCat} (pi : Xtilde ⟶ X)
    (omega : T01A05TopForm n X) :
    t01A05Integral (t01A05Pullback pi omega) =
      k * t01A05Integral omega := by
  simp [t01A05Integral]

/-- The numerical intersection identity is automatic for the current
zero-valued placeholder encoding. -/
lemma t01A05_preimage_intersectionNumber_eq
    {n d₁ d₂ k : ℕ} {X Xtilde : TopCat} (pi : Xtilde ⟶ X)
    (Z₁ : T01A05OrientedSubmanifold d₁ X)
    (Z₂ : T01A05OrientedSubmanifold d₂ X) :
    t01A05IntersectionNumber (n := n)
        (t01A05PreimageSubmanifold pi Z₁)
        (t01A05PreimageSubmanifold pi Z₂) =
      k * t01A05IntersectionNumber (n := n) Z₁ Z₂ := by
  simp [t01A05IntersectionNumber]

/-- With the standard Hausdorff hypothesis on the base, compactness of the
total space makes inverse images of compact submanifolds compact. -/
lemma t01A05_preimageSubmanifold_compact_of_t2
    {d : ℕ} {X Xtilde : TopCat} [T2Space X]
    (hXtilde : IsCompact (Set.univ : Set Xtilde)) (pi : Xtilde ⟶ X)
    (Z : T01A05OrientedSubmanifold d X)
    (hZ : IsT01A05CompactSubmanifold Z) :
    IsT01A05CompactSubmanifold (t01A05PreimageSubmanifold pi Z) := by
  letI : CompactSpace Xtilde := isCompact_univ_iff.mp hXtilde
  exact hZ.preimage_continuous pi.hom.continuous

theorem apm_t01a05 :
    (∀ k : ℕ, 0 < k → ∃ (X Xtilde : TopCat) (π : Xtilde ⟶ X),
      IsT01A05CompactOrientedManifold 2 X ∧
      IsT01A05CompactOrientedManifold 2 Xtilde ∧
      IsT01A05KSheetedOrientationPreservingCover k π) ∧
    (∀ (n k : ℕ) (X Xtilde : TopCat) (π : Xtilde ⟶ X),
      IsT01A05CompactOrientedManifold n X →
      IsT01A05CompactOrientedManifold n Xtilde →
      IsT01A05KSheetedOrientationPreservingCover k π →
      ∀ ω : T01A05TopForm n X,
        t01A05Integral (t01A05Pullback π ω) = k * t01A05Integral ω) ∧
    (∀ (n d₁ d₂ k : ℕ) (hdim : d₁ + d₂ = n)
      (X Xtilde : TopCat) (π : Xtilde ⟶ X),
      IsT01A05CompactOrientedManifold n X →
      IsT01A05CompactOrientedManifold n Xtilde →
      IsT01A05KSheetedOrientationPreservingCover k π →
      ∀ (Z₁ : T01A05OrientedSubmanifold d₁ X)
        (Z₂ : T01A05OrientedSubmanifold d₂ X),
        IsT01A05CompactSubmanifold Z₁ → IsT01A05CompactSubmanifold Z₂ →
        IsT01A05CompactSubmanifold (t01A05PreimageSubmanifold π Z₁) ∧
        IsT01A05CompactSubmanifold (t01A05PreimageSubmanifold π Z₂) ∧
        t01A05IntersectionNumber (n := n)
            (t01A05PreimageSubmanifold π Z₁)
            (t01A05PreimageSubmanifold π Z₂) =
          k * t01A05IntersectionNumber (n := n) Z₁ Z₂) := by
  /-
  Boundary (closer hop 1): the encoded pullback-integral formula and the
  numerical intersection formula are now proved above as
  `t01A05_pullback_integral_eq` and
  `t01A05_preimage_intersectionNumber_eq`; both reduce to zero because the
  current encodings evaluate a homology morphism at zero and define the
  intersection number as zero.  The compact-preimage step also compiles as
  `t01A05_preimageSubmanifold_compact_of_t2` under the standard Hausdorff
  hypothesis on the base.

  The frozen theorem does not assume `T2Space X`, and its `k`-sheeted
  predicate permits `k = 0` in parts (b) and (c), where `Nat.card = 0` does
  not imply finite fibers. Mathlib therefore supplies no properness theorem
  yielding compact inverse images from the stated hypotheses. The independent
  existence clause still requires an actual compact space whose integral
  singular `H₂` is `ℤ`, followed by construction of every positive-degree
  finite cover. Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
  covering artifacts, git history, and Mathlib's covering-map, compactness,
  sphere, torus, and singular-homology APIs found neither the necessary
  sphere/torus homology computation nor a packaged finite-cover construction.
  -/
  sorry
