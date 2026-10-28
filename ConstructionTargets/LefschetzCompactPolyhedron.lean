import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.SingularHomologyHomotopy

/-! # The rational Lefschetz theorem for finite polyhedra -/

open Set CategoryTheory
open ConstructionTargets.RationalLefschetz

noncomputable section
namespace ConstructionTargets.LefschetzCompactPolyhedron

/-- A concrete finite triangulation of `X`. -/
def IsFinitePolyhedron (X : Type) [TopologicalSpace X] : Prop :=
  ∃ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))),
    K.faces.Finite ∧ Nonempty (X ≃ₜ K.space)

/-- Every point of each closed simplex is sent outside that simplex. -/
def FaceAvoiding {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (e : X ≃ₜ K.space) (g : C(X, X)) : Prop :=
  ∀ s ∈ K.faces, ∀ x : X,
    (e x : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (s : Set _) →
      (e (g x) : EuclideanSpace ℝ (Fin n)) ∉ convexHull ℝ (s : Set _)

/-- **LIBRARY (barycentric subdivision).** Every finite geometric simplicial
complex has a finite subdivision with the same underlying space whose closed
faces all have diameter less than any prescribed `ε > 0`.  (Review fix,
claude-14 2026-10-28: the split's first leaf asked for a face-avoiding map with
respect to the ORIGINAL complex, which needs a subdivision in the standard
proof; with the subdivision explicit, `f` itself is face-avoiding.) -/
theorem exists_fine_subdivision {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K'.faces.Finite ∧ K'.space = K.space ∧
      ∀ s ∈ K'.faces, Metric.diam (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) < ε := by
  sorry

/-- A fixed-point-free self-map of a finite polyhedron moves every point by at
least a uniform positive distance (compactness of the realization). -/
theorem fixedPointFree_uniform_separation
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (f : C(X, X))
    (hfree : ∀ x, f x ≠ x) :
    ∃ ε > 0, ∀ x : X,
      ε ≤ dist (e x : EuclideanSpace ℝ (Fin n)) (e (f x)) := by
  sorry

/-- If every face is shorter than the distance each point is moved, the map
avoids every face. -/
theorem faceAvoiding_of_fine
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (e : X ≃ₜ K.space) (f : C(X, X)) {ε : ℝ}
    (hfine : ∀ s ∈ K.faces, Metric.diam (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) < ε)
    (hsep : ∀ x : X, ε ≤ dist (e x : EuclideanSpace ℝ (Fin n)) (e (f x))) :
    FaceAvoiding K e f := by
  sorry

/-- Homotopic maps have the same rational Lefschetz number. -/
theorem hasLefschetzNumber_of_homotopic
    {X : Type} [TopologicalSpace X] {f g : C(X, X)} {L : ℚ}
    (hfg : ContinuousMap.Homotopic f g) (hL : HasLefschetzNumber f L) :
    HasLefschetzNumber g L := by
  sorry

/-- **LIBRARY (Hopf trace and comparison).** A face-avoiding map on a finite
polyhedron has Lefschetz number zero. -/
theorem lefschetzNumber_eq_zero_of_faceAvoiding
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X)) {L : ℚ}
    (havoid : FaceAvoiding K e g) (hL : HasLefschetzNumber g L) : L = 0 := by
  sorry

/-- Rational Lefschetz fixed-point theorem for a finite polyhedron. -/
theorem fixedPointOfNonzeroLefschetz
    {X : Type} [TopologicalSpace X] (hX : IsFinitePolyhedron X)
    (f : C(X, X)) {L : ℚ} (hL : HasLefschetzNumber f L) (hne : L ≠ 0) :
    ∃ x, f x = x := by
  by_contra hfixed
  push_neg at hfixed
  obtain ⟨n, K, hK, ⟨e⟩⟩ := hX
  obtain ⟨ε, hε, hsep⟩ := fixedPointFree_uniform_separation K hK e f hfixed
  obtain ⟨K', hK', hspace, hfine⟩ := exists_fine_subdivision K hK hε
  let e' : X ≃ₜ K'.space := e.trans (Homeomorph.setCongr hspace.symm)
  have havoid : FaceAvoiding K' e' f :=
    faceAvoiding_of_fine K' e' f hfine (fun x => hsep x)
  exact hne (lefschetzNumber_eq_zero_of_faceAvoiding K' hK' e' f havoid hL)

end ConstructionTargets.LefschetzCompactPolyhedron

#print axioms ConstructionTargets.LefschetzCompactPolyhedron.exists_fine_subdivision
#print axioms ConstructionTargets.LefschetzCompactPolyhedron.hasLefschetzNumber_of_homotopic
#print axioms ConstructionTargets.LefschetzCompactPolyhedron.lefschetzNumber_eq_zero_of_faceAvoiding
#print axioms ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz
