import Mathlib
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.GeometricSimplicialSubdivision

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
  exact ConstructionTargets.GeometricSimplicialSubdivision.exists_fine_subdivision K hK hε

/-- A fixed-point-free self-map of a finite polyhedron moves every point by at
least a uniform positive distance (compactness of the realization). -/
theorem fixedPointFree_uniform_separation
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (f : C(X, X))
    (hfree : ∀ x, f x ≠ x) :
    ∃ ε > 0, ∀ x : X,
      ε ≤ dist (e x : EuclideanSpace ℝ (Fin n)) (e (f x)) := by
  have hcompact : IsCompact K.space := by
    rw [Geometry.SimplicialComplex.space]
    exact hK.isCompact_biUnion fun s hs =>
      s.finite_toSet.isCompact_convexHull ℝ
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hcompact
  letI : CompactSpace X := e.symm.compactSpace
  let d : X → ℝ := fun x =>
    dist (e x : EuclideanSpace ℝ (Fin n)) (e (f x))
  have hd : Continuous d := by
    fun_prop
  obtain ⟨ε, hε, hbound⟩ :=
    isCompact_univ.exists_forall_le' hd.continuousOn
      (fun x _ => dist_pos.mpr (fun heq =>
        hfree x ((e.injective (Subtype.ext heq)).symm)))
  exact ⟨ε, hε, fun x => hbound x (mem_univ x)⟩

/-- If every face is shorter than the distance each point is moved, the map
avoids every face. -/
theorem faceAvoiding_of_fine
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (e : X ≃ₜ K.space) (f : C(X, X)) {ε : ℝ}
    (hfine : ∀ s ∈ K.faces, Metric.diam (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) < ε)
    (hsep : ∀ x : X, ε ≤ dist (e x : EuclideanSpace ℝ (Fin n)) (e (f x))) :
    FaceAvoiding K e f := by
  intro s hs x hx hfx
  have hb : Bornology.IsBounded
      (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) :=
    isBounded_convexHull.mpr s.finite_toSet.isBounded
  have hd : dist (e x : EuclideanSpace ℝ (Fin n)) (e (f x)) ≤
      Metric.diam (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))) :=
    Metric.dist_le_diam_of_mem hb hx hfx
  exact (not_lt_of_ge (hsep x)) (hd.trans_lt (hfine s hs))

/-- Homotopic maps have the same rational Lefschetz number. -/
theorem hasLefschetzNumber_of_homotopic
    {X : Type} [TopologicalSpace X] {f g : C(X, X)} {L : ℚ}
    (hfg : ContinuousMap.Homotopic f g) (hL : HasLefschetzNumber f L) :
    HasLefschetzNumber g L := by
  rcases hL with ⟨hfinite, bound, habove, hsum⟩
  refine ⟨hfinite, bound, habove, ?_⟩
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hmap :=
    ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) hfg k
  change induced f k = induced g k at hmap
  rw [← hmap]

/-- A bounded, degreewise finite-dimensional rational chain complex together
with an endomorphism. -/
structure FiniteChainEndomorphism where
  C : ChainComplex (ModuleCat ℚ) ℕ
  φ : C ⟶ C
  bound : ℕ
  finiteChain : ∀ k, FiniteDimensional ℚ (C.X k)
  finiteHomology : ∀ k, FiniteDimensional ℚ (C.homology k)
  chainAbove : ∀ k, bound < k → Subsingleton (C.X k)

namespace FiniteChainEndomorphism

noncomputable def chainTrace (M : FiniteChainEndomorphism) (k : ℕ) : ℚ := by
  letI := M.finiteChain k
  exact LinearMap.trace ℚ (M.C.X k) (M.φ.f k).hom

noncomputable def homologyTrace (M : FiniteChainEndomorphism) (k : ℕ) : ℚ := by
  letI := M.finiteHomology k
  exact LinearMap.trace ℚ (M.C.homology k)
    (HomologicalComplex.homologyMap M.φ k).hom

end FiniteChainEndomorphism

/-- A chain model represents a topological endomorphism when its homology
endomorphism is conjugate, degree by degree, to the induced singular-homology
endomorphism.  This records the comparison isomorphisms, rather than merely
recording equality of their traces. -/
def HomologyModels {X : Type} [TopologicalSpace X]
    (M : FiniteChainEndomorphism) (g : C(X, X)) : Prop :=
  ∃ E : ∀ k, M.C.homology k ≃ₗ[ℚ] Homology X k,
    ∀ k,
      (E k).toLinearMap.comp
          (HomologicalComplex.homologyMap M.φ k).hom =
        (induced g k).hom.comp (E k).toLinearMap

/-- Face avoidance has a uniform positive carrier margin.  The quantified
point `y` ranges over the whole closed face, not only over `e x`; this is the
margin needed to retain carrier avoidance during simplicial approximation. -/
theorem faceAvoiding_uniform_carrier_margin
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X))
    (havoid : FaceAvoiding K e g) :
    ∃ δ > 0, ∀ s ∈ K.faces, ∀ x : X,
      (e x : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (s : Set _) →
      ∀ y ∈ convexHull ℝ (s : Set _),
        δ ≤ dist (e (g x) : EuclideanSpace ℝ (Fin n)) y := by
  sorry

/-- **LIBRARY (oriented simplicial chains and direct comparison).** Given the
uniform carrier margin, construct the finite oriented simplicial chain model,
its carrier-avoiding subdivision/approximation endomorphism, and the direct
simplicial-to-singular comparison.  Zero chain trace is the zero-diagonal
consequence; `HomologyModels` is the stronger, conjugacy-level naturality
statement consumed separately below. -/
theorem exists_carrier_avoiding_oriented_chain_model
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X))
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ s ∈ K.faces, ∀ x : X,
      (e x : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (s : Set _) →
      ∀ y ∈ convexHull ℝ (s : Set _),
        δ ≤ dist (e (g x) : EuclideanSpace ℝ (Fin n)) y) :
    ∃ M : FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧ HomologyModels M g := by
  sorry

/-- Conjugate finite-dimensional homology endomorphisms have equal traces. -/
theorem homologyTrace_eq_of_models
    {X : Type} [TopologicalSpace X] (M : FiniteChainEndomorphism)
    (g : C(X, X)) (hmodel : HomologyModels M g) :
    ∀ k, M.homologyTrace k =
      LinearMap.trace ℚ (Homology X k) (induced g k).hom := by
  sorry

/-- **LIBRARY (direct simplicial--singular comparison).** A face-avoiding map
admits a bounded oriented simplicial chain model.  Its chain diagonal is zero,
and its homology traces are the traces of the singular-homology maps of `g`.
The latter clause is naturality of the direct simplicial-to-singular comparison,
not a Lefschetz-number conclusion. -/
theorem exists_faceAvoiding_simplicial_trace_model
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X))
    (havoid : FaceAvoiding K e g) :
    ∃ M : FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧
      (∀ k, M.homologyTrace k =
        LinearMap.trace ℚ (Homology X k) (induced g k).hom) := by
  obtain ⟨δ, hδ, hmargin⟩ :=
    faceAvoiding_uniform_carrier_margin K hK e g havoid
  obtain ⟨M, hchain, hmodel⟩ :=
    exists_carrier_avoiding_oriented_chain_model K hK e g δ hδ hmargin
  exact ⟨M, hchain, homologyTrace_eq_of_models M g hmodel⟩

/-- The Hopf trace formula for a bounded complex of finite-dimensional rational
vector spaces. -/
theorem hopf_trace_formula (M : FiniteChainEndomorphism) :
    (∑ k ∈ Finset.range (M.bound + 1),
      (-1 : ℚ)^k * M.homologyTrace k) =
    ∑ k ∈ Finset.range (M.bound + 1),
      (-1 : ℚ)^k * M.chainTrace k := by
  sorry

/-- The bound in a simplicial trace model can replace the bound occurring in a
`HasLefschetzNumber` certificate. -/
theorem lefschetzNumber_eq_model_homology_trace
    {X : Type} [TopologicalSpace X] (g : C(X, X)) {L : ℚ}
    (hL : HasLefschetzNumber g L) (M : FiniteChainEndomorphism)
    (htrace : ∀ k, M.homologyTrace k =
      LinearMap.trace ℚ (Homology X k) (induced g k).hom) :
    L = ∑ k ∈ Finset.range (M.bound + 1),
      (-1 : ℚ)^k * M.homologyTrace k := by
  rcases hL with ⟨hfinite, b, habove, hsum⟩
  letI (k : ℕ) := hfinite k
  let N := max b M.bound
  have hsingular (k : ℕ) (hk : b < k) :
      LinearMap.trace ℚ (Homology X k) (induced g k).hom = 0 := by
    letI := habove k hk
    rw [Subsingleton.elim (induced g k).hom 0]
    exact map_zero (LinearMap.trace ℚ (Homology X k))
  have hmodel (k : ℕ) (hk : M.bound < k) : M.homologyTrace k = 0 := by
    letI hCX : Subsingleton (M.C.X k) := M.chainAbove k hk
    have hzX : Limits.IsZero (M.C.X k) := ModuleCat.isZero_of_subsingleton _
    have hz : Limits.IsZero (M.C.homology k) :=
      (M.C.sc k).isZero_homology_of_isZero_X₂ (by simpa using hzX)
    letI : Subsingleton (M.C.homology k) := ModuleCat.subsingleton_of_isZero hz
    unfold FiniteChainEndomorphism.homologyTrace
    rw [Subsingleton.elim (HomologicalComplex.homologyMap M.φ k).hom 0]
    exact map_zero (LinearMap.trace ℚ (M.C.homology k))
  have hbN : Finset.range (b + 1) ⊆ Finset.range (N + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.succ_le_succ (le_max_left _ _))
  have hMN : Finset.range (M.bound + 1) ⊆ Finset.range (N + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.succ_le_succ (le_max_right _ _))
  have hpadSingular :
      (∑ k ∈ Finset.range (b + 1),
        (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k) (induced g k).hom) =
      ∑ k ∈ Finset.range (N + 1),
        (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k) (induced g k).hom := by
    apply Finset.sum_subset hbN
    intro k hkN hkb
    simp only [Finset.mem_range, not_lt] at hkN hkb
    rw [hsingular k (lt_of_lt_of_le (Nat.lt_succ_self b) hkb), mul_zero]
  have hpadModel :
      (∑ k ∈ Finset.range (M.bound + 1), (-1 : ℚ)^k * M.homologyTrace k) =
      ∑ k ∈ Finset.range (N + 1), (-1 : ℚ)^k * M.homologyTrace k := by
    apply Finset.sum_subset hMN
    intro k hkN hkM
    simp only [Finset.mem_range, not_lt] at hkN hkM
    rw [hmodel k (lt_of_lt_of_le (Nat.lt_succ_self M.bound) hkM), mul_zero]
  calc
    L = ∑ k ∈ Finset.range (b + 1),
        (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k) (induced g k).hom := hsum.symm
    _ = ∑ k ∈ Finset.range (N + 1),
        (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k) (induced g k).hom := hpadSingular
    _ = ∑ k ∈ Finset.range (N + 1), (-1 : ℚ)^k * M.homologyTrace k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [htrace k]
    _ = ∑ k ∈ Finset.range (M.bound + 1),
        (-1 : ℚ)^k * M.homologyTrace k := hpadModel.symm

/-- A face-avoiding map on a finite polyhedron has Lefschetz number zero. -/
theorem lefschetzNumber_eq_zero_of_faceAvoiding
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X)) {L : ℚ}
    (havoid : FaceAvoiding K e g) (hL : HasLefschetzNumber g L) : L = 0 := by
  obtain ⟨M, hchain, htrace⟩ :=
    exists_faceAvoiding_simplicial_trace_model K hK e g havoid
  rw [lefschetzNumber_eq_model_homology_trace g hL M htrace,
    hopf_trace_formula M]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hchain k, mul_zero]

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
#print axioms ConstructionTargets.LefschetzCompactPolyhedron.exists_faceAvoiding_simplicial_trace_model
#print axioms ConstructionTargets.LefschetzCompactPolyhedron.hasLefschetzNumber_of_homotopic
#print axioms ConstructionTargets.LefschetzCompactPolyhedron.lefschetzNumber_eq_zero_of_faceAvoiding
#print axioms ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz
