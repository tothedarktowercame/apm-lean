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
  have hcompact : IsCompact K.space := by
    rw [Geometry.SimplicialComplex.space]
    exact hK.isCompact_biUnion fun s hs =>
      s.finite_toSet.isCompact_convexHull ℝ
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hcompact
  letI : CompactSpace X := e.symm.compactSpace
  let E := EuclideanSpace ℝ (Fin n)
  let T : Set (X × E) := ⋃ s ∈ K.faces,
    {x : X | (e x : E) ∈ convexHull ℝ (s : Set E)} ×ˢ
      convexHull ℝ (s : Set E)
  have hecont : Continuous (fun x : X => (e x : E)) :=
    continuous_subtype_val.comp e.continuous
  have hT : IsCompact T := by
    apply hK.isCompact_biUnion
    intro s hs
    apply IsCompact.prod
    · exact ((s.finite_toSet.isClosed_convexHull ℝ).preimage hecont).isCompact
    · exact s.finite_toSet.isCompact_convexHull ℝ
  let d : X × E → ℝ := fun p => dist (e (g p.1) : E) p.2
  have hd : Continuous d := by
    fun_prop
  by_cases hne : T.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hT.exists_isMinOn hne hd.continuousOn
    have hdp : 0 < d p := by
      rcases mem_iUnion.mp hp with ⟨s, hp⟩
      rcases mem_iUnion.mp hp with ⟨hs, hp⟩
      exact dist_pos.mpr fun heq => havoid s hs p.1 hp.1 (heq ▸ hp.2)
    refine ⟨d p, hdp, ?_⟩
    intro s hs x hx y hy
    have hxy : (x, y) ∈ T := by
      exact mem_iUnion₂.mpr ⟨s, hs, hx, hy⟩
    change d p ≤ d (x, y)
    exact hmin hxy
  · refine ⟨1, zero_lt_one, ?_⟩
    intro s hs x hx y hy
    exfalso
    apply hne
    refine ⟨(x, y), ?_⟩
    change (x, y) ∈ T
    exact mem_iUnion₂.mpr ⟨s, hs, hx, hy⟩

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
  obtain ⟨E, hE⟩ := hmodel
  intro k
  letI := M.finiteHomology k
  have hconj :
      (E k).conj (HomologicalComplex.homologyMap M.φ k).hom =
        (induced g k).hom := by
    ext x
    have h := LinearMap.congr_fun (hE k) ((E k).symm x)
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply]
    simpa using h
  unfold FiniteChainEndomorphism.homologyTrace
  rw [← hconj, LinearMap.trace_conj']

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

/-! ### Hopf trace formula (split by claude-14, 2026-10-28, after lemma-3's
partial banked the telescoping and the final assembly) -/

lemma hopf_trace_formula_aux_boundary_sum (n : ℕ) (b : ℕ → ℚ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ)^k * (b k + b (k + 1))) =
      b 0 + (-1 : ℚ)^n * b (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [pow_succ]
      ring

lemma hopf_trace_formula_aux_telescope (n : ℕ) (h b : ℕ → ℚ)
    (hb0 : b 0 = 0) (hbtop : b (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ)^k * (h k + b k + b (k + 1))) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ)^k * h k := by
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℚ)^k * h k + (-1 : ℚ)^k * (b k + b (k + 1))) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (∑ k ∈ Finset.range (n + 1), (-1 : ℚ)^k * h k) +
        ∑ k ∈ Finset.range (n + 1), (-1 : ℚ)^k * (b k + b (k + 1)) := by
          rw [Finset.sum_add_distrib]
    _ = _ := by rw [hopf_trace_formula_aux_boundary_sum, hb0, hbtop]; simp

/-- (T) Trace is additive over an invariant subspace and its quotient. -/
theorem trace_eq_trace_restrict_add_trace_mapQ
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (φ : V →ₗ[ℚ] V) (W : Submodule ℚ V) (hW : ∀ x ∈ W, φ x ∈ W) :
    LinearMap.trace ℚ V φ =
      LinearMap.trace ℚ W (φ.restrict hW) +
        LinearMap.trace ℚ (V ⧸ W) (W.mapQ W φ (fun x hx => hW x hx)) := by
  classical
  obtain ⟨U, hU⟩ := W.exists_isCompl
  let e : (W × U) ≃ₗ[ℚ] V := W.prodEquivOfIsCompl U hU
  let p : V →ₗ[ℚ] W := (LinearMap.fst ℚ W U).comp e.symm.toLinearMap
  let q : V →ₗ[ℚ] V ⧸ W := W.mkQ
  let s : (V ⧸ W) →ₗ[ℚ] V :=
    U.subtype.comp (W.quotientEquivOfIsCompl U hU).toLinearMap
  have hp (x : W) : p x = x := by
    change (e.symm x).1 = x
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  have hq (x : V ⧸ W) : q (s x) = x := by
    change W.mkQ (W.quotientEquivOfIsCompl U hU x) = x
    exact W.mk_quotientEquivOfIsCompl_apply U hU x
  have hdecomp : W.subtype.comp p + s.comp q = LinearMap.id := by
    ext x
    let y : W × U := e.symm x
    have hxy : e y = x := e.apply_symm_apply x
    change (p x : V) + s (q x) = x
    rw [← hxy]
    simp [p, q, s, e]
  have hφ : φ = W.subtype.comp (p.comp φ) + s.comp (q.comp φ) := by
    ext x
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] using
      (LinearMap.congr_fun hdecomp (φ x)).symm
  calc
    LinearMap.trace ℚ V φ = LinearMap.trace ℚ V
        (W.subtype.comp (p.comp φ) + s.comp (q.comp φ)) := congrArg _ hφ
    _ = LinearMap.trace ℚ V (W.subtype.comp (p.comp φ)) +
        LinearMap.trace ℚ V (s.comp (q.comp φ)) := map_add _ _ _
    _ = _ := by
      have hfirst : (p.comp φ).comp W.subtype = φ.restrict hW := by
        ext x
        exact congrArg Subtype.val (hp ⟨φ x, hW x x.property⟩)
      have hsecond : (q.comp φ).comp s =
          W.mapQ W φ (fun x hx => hW x hx) := by
        apply LinearMap.ext
        intro x
        change q (φ (s x)) = W.mapQ W φ (fun x hx => hW x hx) x
        calc
          _ = W.mapQ W φ (fun x hx => hW x hx) (q (s x)) := by
            simp [q, Submodule.mapQ_apply]
          _ = _ := congrArg _ (hq x)
      rw [LinearMap.trace_comp_comm', hfirst,
        LinearMap.trace_comp_comm', hsecond]

namespace FiniteChainEndomorphism

/-- Cycles in degree `k`: the kernel of the outgoing differential. -/
def cycles (M : FiniteChainEndomorphism) (k : ℕ) : Submodule ℚ (M.C.X k) :=
  LinearMap.ker (M.C.d k (k - 1)).hom

/-- Boundaries in degree `k`: the image of the incoming differential. -/
def bdries (M : FiniteChainEndomorphism) (k : ℕ) : Submodule ℚ (M.C.X k) :=
  LinearMap.range (M.C.d (k + 1) k).hom

lemma cycles_invariant (M : FiniteChainEndomorphism) (k : ℕ) :
    ∀ x ∈ M.cycles k, (M.φ.f k).hom x ∈ M.cycles k := by
  intro x hx
  have h := congrArg (fun g => g.hom x) (M.φ.comm k (k - 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change (M.C.d k (k - 1)).hom ((M.φ.f k).hom x) = 0
  rw [h, show (M.C.d k (k - 1)).hom x = 0 from hx, map_zero]

lemma bdries_invariant (M : FiniteChainEndomorphism) (k : ℕ) :
    ∀ x ∈ M.bdries k, (M.φ.f k).hom x ∈ M.bdries k := by
  rintro _ ⟨y, rfl⟩
  refine ⟨(M.φ.f (k + 1)).hom y, ?_⟩
  have h := congrArg (fun g => g.hom y) (M.φ.comm (k + 1) k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- Trace of the chain endomorphism on the cycles of degree `k`. -/
noncomputable def cyclesTrace (M : FiniteChainEndomorphism) (k : ℕ) : ℚ :=
  LinearMap.trace ℚ (M.cycles k) ((M.φ.f k).hom.restrict (M.cycles_invariant k))

/-- Trace of the chain endomorphism on the boundaries of degree `k`. -/
noncomputable def bdriesTrace (M : FiniteChainEndomorphism) (k : ℕ) : ℚ :=
  LinearMap.trace ℚ (M.bdries k) ((M.φ.f k).hom.restrict (M.bdries_invariant k))

end FiniteChainEndomorphism

/-- (A0) In degree `0` every chain is a cycle (the outgoing differential
`d 0 0` is zero by the shape of a `ℕ`-indexed chain complex). -/
theorem FiniteChainEndomorphism.chainTrace_zero_eq_cyclesTrace
    (M : FiniteChainEndomorphism) : M.chainTrace 0 = M.cyclesTrace 0 := by
  letI := M.finiteChain 0
  unfold FiniteChainEndomorphism.chainTrace FiniteChainEndomorphism.cyclesTrace
  symm
  apply LinearMap.trace_restrict_eq_of_forall_mem
  intro x
  change (M.C.d 0 0).hom ((M.φ.f 0).hom x) = 0
  rw [M.C.shape 0 0 (by simp [ComplexShape.down, ComplexShape.down'])]
  rfl

/-- (A) In degree `k + 1`, the chain trace splits into the trace on cycles and
the trace on the boundaries one degree down: `X (k+1) ⧸ Z (k+1) ≅ B k`
equivariantly via the differential.  Takes (T) as a hypothesis. -/
theorem FiniteChainEndomorphism.chainTrace_succ_eq
    (hT : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (φ : V →ₗ[ℚ] V) (W : Submodule ℚ V) (hW : ∀ x ∈ W, φ x ∈ W),
      LinearMap.trace ℚ V φ =
        LinearMap.trace ℚ W (φ.restrict hW) +
          LinearMap.trace ℚ (V ⧸ W) (W.mapQ W φ (fun x hx => hW x hx)))
    (M : FiniteChainEndomorphism) (k : ℕ) :
    M.chainTrace (k + 1) = M.cyclesTrace (k + 1) + M.bdriesTrace k := by
  letI := M.finiteChain (k + 1)
  letI := M.finiteChain k
  let d : M.C.X (k + 1) →ₗ[ℚ] M.C.X k := (M.C.d (k + 1) k).hom
  let e : (M.C.X (k + 1) ⧸ M.cycles (k + 1)) ≃ₗ[ℚ] M.bdries k :=
    d.quotKerEquivRange
  have hcomm :
      e.toLinearMap.comp ((M.cycles (k + 1)).mapQ (M.cycles (k + 1))
        (M.φ.f (k + 1)).hom (M.cycles_invariant (k + 1))) =
        ((M.φ.f k).hom.restrict (M.bdries_invariant k)).comp e.toLinearMap := by
    ext x
    change d ((M.φ.f (k + 1)).hom x) = (M.φ.f k).hom (d x)
    have h := congrArg (fun g => g.hom x) (M.φ.comm (k + 1) k)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have heq :
      e.conj ((M.cycles (k + 1)).mapQ (M.cycles (k + 1))
        (M.φ.f (k + 1)).hom (M.cycles_invariant (k + 1))) =
        (M.φ.f k).hom.restrict (M.bdries_invariant k) := by
    ext x
    have h := LinearMap.congr_fun hcomm (e.symm x)
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply]
    convert congrArg Subtype.val h using 1 <;> simp
  unfold FiniteChainEndomorphism.chainTrace FiniteChainEndomorphism.cyclesTrace
    FiniteChainEndomorphism.bdriesTrace
  rw [hT (M.φ.f (k + 1)).hom (M.cycles (k + 1))
    (M.cycles_invariant (k + 1))]
  congr 1
  rw [← heq, LinearMap.trace_conj']

/-- (H1) Inside the cycles, the boundaries (`B ⊆ Z` since `d ∘ d = 0`) split
off the quotient trace; the boundary part is `bdriesTrace`. -/
theorem FiniteChainEndomorphism.cyclesTrace_eq_aux_boundary_quotient
    (hT : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (φ : V →ₗ[ℚ] V) (W : Submodule ℚ V) (hW : ∀ x ∈ W, φ x ∈ W),
      LinearMap.trace ℚ V φ =
        LinearMap.trace ℚ W (φ.restrict hW) +
          LinearMap.trace ℚ (V ⧸ W) (W.mapQ W φ (fun x hx => hW x hx)))
    (M : FiniteChainEndomorphism) (k : ℕ) :
    ∀ (hW : ∀ x ∈ (M.bdries k).comap (M.cycles k).subtype,
        (M.φ.f k).hom.restrict (M.cycles_invariant k) x ∈
          (M.bdries k).comap (M.cycles k).subtype),
      M.cyclesTrace k = M.bdriesTrace k +
        LinearMap.trace ℚ
          (M.cycles k ⧸ (M.bdries k).comap (M.cycles k).subtype)
          (((M.bdries k).comap (M.cycles k).subtype).mapQ
            ((M.bdries k).comap (M.cycles k).subtype)
            ((M.φ.f k).hom.restrict (M.cycles_invariant k)) hW) := by
  intro hW
  letI := M.finiteChain k
  have hBZ : M.bdries k ≤ M.cycles k := by
    rintro _ ⟨y, rfl⟩
    have hdd := congrArg (fun f => f.hom y) (M.C.d_comp_d (k + 1) k (k - 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using hdd
  let e : (M.bdries k).comap (M.cycles k).subtype ≃ₗ[ℚ] M.bdries k :=
    Submodule.comapSubtypeEquivOfLe hBZ
  have heq :
      e.conj (((M.φ.f k).hom.restrict (M.cycles_invariant k)).restrict hW) =
        (M.φ.f k).hom.restrict (M.bdries_invariant k) := by
    ext x
    rw [LinearEquiv.conj_apply]
    rfl
  unfold FiniteChainEndomorphism.cyclesTrace FiniteChainEndomorphism.bdriesTrace
  rw [hT ((M.φ.f k).hom.restrict (M.cycles_invariant k))
    ((M.bdries k).comap (M.cycles k).subtype) hW]
  congr 1
  rw [← heq, LinearMap.trace_conj']

lemma FiniteChainEndomorphism.cyclesTrace_eq_aux_homology_quotient_aux_cycles
    (M : FiniteChainEndomorphism) (k : ℕ) :
    LinearMap.ker (M.C.sc k).g.hom = M.cycles k := by
  unfold FiniteChainEndomorphism.cycles
  change LinearMap.ker (M.C.d k ((ComplexShape.down ℕ).next k)).hom =
    LinearMap.ker (M.C.d k (k - 1)).hom
  cases k with
  | zero => rw [ChainComplex.next_nat_zero]
  | succ n =>
      simp only [Nat.succ_sub_one]
      rw [ChainComplex.next_nat_succ]
      rfl

/-- Banked from lemma-1's partial (2026-10-28). Route for H2a: quotient this
equivalence by the boundaries (`Submodule.Quotient.equiv`; show the boundary
submodule maps onto `range moduleCatToCycles`), compose with
`ShortComplex.moduleCatHomologyIso`, and get equivariance from
`HomologicalComplex.homologyπ_naturality`. -/
noncomputable def FiniteChainEndomorphism.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv
    (M : FiniteChainEndomorphism) (k : ℕ) :
    M.cycles k ≃ₗ[ℚ] LinearMap.ker (M.C.sc k).g.hom := by
  have hZ : LinearMap.ker (M.C.sc k).g.hom = M.cycles k :=
    M.cyclesTrace_eq_aux_homology_quotient_aux_cycles k
  exact
    { toFun := fun x =>
        ⟨by simpa using x.1, by simpa using (hZ.symm ▸ x.property)⟩
      invFun := fun x =>
        ⟨by simpa using x.1, by simpa using (hZ ▸ x.property)⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }

namespace FiniteChainEndomorphism

variable (M : FiniteChainEndomorphism) (k : ℕ)

/-- class of a cycle in Mathlib's homology -/
noncomputable def h2aCls : M.cycles k →ₗ[ℚ] M.C.homology k :=
  (M.C.homologyπ k).hom ∘ₗ ((M.C.sc k).moduleCatCyclesIso.inv.hom ∘ₗ
    (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k).toLinearMap)

lemma h2a_iCycles (x : M.cycles k) :
    (M.C.iCycles k).hom ((M.C.sc k).moduleCatCyclesIso.inv.hom
      (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k x)) = x.1 := by
  have := congrArg (fun f => f.hom (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k x))
    (M.C.sc k).moduleCatCyclesIso_inv_iCycles
  simpa using this

lemma h2a_natural (x : M.cycles k) :
    (HomologicalComplex.homologyMap M.φ k).hom (M.h2aCls k x) =
      M.h2aCls k ((M.φ.f k).hom.restrict (M.cycles_invariant k) x) := by
  have hinj : Function.Injective (M.C.iCycles k).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hc : (HomologicalComplex.cyclesMap M.φ k).hom ((M.C.sc k).moduleCatCyclesIso.inv.hom
      (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k x)) =
      (M.C.sc k).moduleCatCyclesIso.inv.hom
        (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k
          ((M.φ.f k).hom.restrict (M.cycles_invariant k) x)) := by
    apply hinj
    have h1 := congrArg (fun f => f.hom ((M.C.sc k).moduleCatCyclesIso.inv.hom
      (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k x)))
      (HomologicalComplex.cyclesMap_i M.φ k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [h1, M.h2a_iCycles k, M.h2a_iCycles k]
    rfl
  have h2 := congrArg (fun f => f.hom ((M.C.sc k).moduleCatCyclesIso.inv.hom
      (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k x)))
      (HomologicalComplex.homologyπ_naturality M.φ k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  simp only [h2aCls, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  exact h2.trans (congrArg (fun y => (M.C.homologyπ k).hom y) hc)

lemma h2a_surjective : Function.Surjective (M.h2aCls k) := by
  have hπ : Function.Surjective (M.C.homologyπ k).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinv : Function.Surjective (M.C.sc k).moduleCatCyclesIso.inv.hom := fun y =>
    ⟨(M.C.sc k).moduleCatCyclesIso.hom.hom y, by
      have := congrArg (fun f => ModuleCat.Hom.hom f y) (M.C.sc k).moduleCatCyclesIso.hom_inv_id
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using this⟩
  exact hπ.comp (hinv.comp
    (M.cyclesTrace_eq_aux_homology_quotient_aux_conj_aux_cyclesEquiv k).surjective)

lemma h2a_range_prev (j : ℕ) (hj : j = k + 1) :
    LinearMap.range (M.C.d j k).hom = LinearMap.range (M.C.d (k + 1) k).hom := by
  subst hj; rfl

lemma h2a_ker : LinearMap.ker (M.h2aCls k) = (M.bdries k).comap (M.cycles k).subtype := by
  have hk : ∀ y, (M.C.homologyπ k).hom ((M.C.sc k).moduleCatCyclesIso.inv.hom y) =
      (M.C.sc k).moduleCatHomologyIso.inv.hom
        ((LinearMap.range (M.C.sc k).moduleCatToCycles).mkQ y) := fun y => by
    simpa using congrArg (fun f => f.hom y) (M.C.sc k).moduleCatCyclesIso_inv_π
  have hinj : Function.Injective (M.C.sc k).moduleCatHomologyIso.inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hr : LinearMap.range (M.C.sc k).f.hom = M.bdries k :=
    M.h2a_range_prev k _ (ChainComplex.prev ℕ k)
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, h2aCls,
    LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  erw [hk]
  erw [map_eq_zero_iff _ hinj]
  rw [Submodule.mkQ_apply]
  erw [Submodule.Quotient.mk_eq_zero]
  rw [← hr]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩
end FiniteChainEndomorphism

/-- (H2a) `Z k ⧸ B k` is linearly equivalent to the homology object, and the
equivalence intertwines the induced endomorphisms (`ShortComplex.moduleCatHomologyIso`
and its naturality; the cycles identification above matches its kernel). -/
theorem FiniteChainEndomorphism.cyclesTrace_eq_aux_homology_quotient_aux_conj
    (M : FiniteChainEndomorphism) (k : ℕ)
    (hW : ∀ x ∈ (M.bdries k).comap (M.cycles k).subtype,
      (M.φ.f k).hom.restrict (M.cycles_invariant k) x ∈
        (M.bdries k).comap (M.cycles k).subtype) :
    ∃ E : (M.cycles k ⧸ (M.bdries k).comap (M.cycles k).subtype) ≃ₗ[ℚ] M.C.homology k,
      E.toLinearMap ∘ₗ (((M.bdries k).comap (M.cycles k).subtype).mapQ
          ((M.bdries k).comap (M.cycles k).subtype)
          ((M.φ.f k).hom.restrict (M.cycles_invariant k)) hW) =
        (HomologicalComplex.homologyMap M.φ k).hom ∘ₗ E.toLinearMap := by
  let E := (Submodule.quotEquivOfEq _ _ (M.h2a_ker k).symm).trans
    ((M.h2aCls k).quotKerEquivOfSurjective (M.h2a_surjective k))
  refine ⟨E, ?_⟩
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe, E, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact (M.h2a_natural k x).symm

/-- (H2) `Z k ⧸ B k` is the homology in degree `k`, compatibly with `φ`. -/
theorem FiniteChainEndomorphism.cyclesTrace_eq_aux_homology_quotient
    (M : FiniteChainEndomorphism) (k : ℕ)
    (hW : ∀ x ∈ (M.bdries k).comap (M.cycles k).subtype,
      (M.φ.f k).hom.restrict (M.cycles_invariant k) x ∈
        (M.bdries k).comap (M.cycles k).subtype) :
    LinearMap.trace ℚ
        (M.cycles k ⧸ (M.bdries k).comap (M.cycles k).subtype)
        (((M.bdries k).comap (M.cycles k).subtype).mapQ
          ((M.bdries k).comap (M.cycles k).subtype)
          ((M.φ.f k).hom.restrict (M.cycles_invariant k)) hW) =
      M.homologyTrace k := by
  obtain ⟨E, hE⟩ := M.cyclesTrace_eq_aux_homology_quotient_aux_conj k hW
  have h : (HomologicalComplex.homologyMap M.φ k).hom =
      E.conj (((M.bdries k).comap (M.cycles k).subtype).mapQ
        ((M.bdries k).comap (M.cycles k).subtype)
        ((M.φ.f k).hom.restrict (M.cycles_invariant k)) hW) := by
    ext y
    have := congrArg (fun g => g (E.symm y)) hE
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at this
    simp [LinearEquiv.conj_apply, this]
  unfold FiniteChainEndomorphism.homologyTrace
  rw [h, LinearMap.trace_conj']

/-- (H) The trace on cycles is the trace on boundaries plus the homology
trace: `Z k ⧸ B k ≅ homology k` equivariantly (`ShortComplex.moduleCatHomologyIso`
or the `ModuleCat` homology API).  Takes (T) as a hypothesis. -/
theorem FiniteChainEndomorphism.cyclesTrace_eq
    (hT : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
      (φ : V →ₗ[ℚ] V) (W : Submodule ℚ V) (hW : ∀ x ∈ W, φ x ∈ W),
      LinearMap.trace ℚ V φ =
        LinearMap.trace ℚ W (φ.restrict hW) +
          LinearMap.trace ℚ (V ⧸ W) (W.mapQ W φ (fun x hx => hW x hx)))
    (M : FiniteChainEndomorphism) (k : ℕ) :
    M.cyclesTrace k = M.bdriesTrace k + M.homologyTrace k := by
  have hW : ∀ x ∈ (M.bdries k).comap (M.cycles k).subtype,
      (M.φ.f k).hom.restrict (M.cycles_invariant k) x ∈
        (M.bdries k).comap (M.cycles k).subtype :=
    fun x hx => M.bdries_invariant k _ hx
  rw [M.cyclesTrace_eq_aux_boundary_quotient hT k hW,
    M.cyclesTrace_eq_aux_homology_quotient k hW]

/-- (E) Above the bound there are no chains, so the top boundaries vanish. -/
theorem FiniteChainEndomorphism.bdriesTrace_bound
    (M : FiniteChainEndomorphism) : M.bdriesTrace M.bound = 0 := by
  letI : Subsingleton (M.C.X (M.bound + 1)) :=
    M.chainAbove (M.bound + 1) (Nat.lt_succ_self M.bound)
  have hb : M.bdries M.bound = ⊥ := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      have hy : y = 0 := Subsingleton.elim y 0
      rw [hy, map_zero]
      exact Submodule.zero_mem ⊥
    · exact bot_le
  letI : Subsingleton (M.bdries M.bound) := by
    rw [hb]
    infer_instance
  unfold FiniteChainEndomorphism.bdriesTrace
  rw [show (M.φ.f M.bound).hom.restrict (M.bdries_invariant M.bound) = 0 by
    ext x
    have hx : (M.φ.f M.bound).hom x ∈ (⊥ : Submodule ℚ (M.C.X M.bound)) := by
      rw [← hb]
      exact M.bdries_invariant M.bound x x.property
    exact hx]
  simp

lemma hopf_trace_formula_aux_trace_decomposition (M : FiniteChainEndomorphism) :
    ∃ b : ℕ → ℚ,
      b 0 = 0 ∧ b (M.bound + 1) = 0 ∧
      ∀ k ∈ Finset.range (M.bound + 1),
        M.chainTrace k = M.homologyTrace k + b k + b (k + 1) := by
  have hT := @trace_eq_trace_restrict_add_trace_mapQ
  refine ⟨fun k => if k = 0 then 0 else M.bdriesTrace (k - 1), by simp,
    by simpa using M.bdriesTrace_bound, ?_⟩
  intro k _
  cases k with
  | zero =>
      rw [M.chainTrace_zero_eq_cyclesTrace, M.cyclesTrace_eq hT 0]
      simp only [if_true, Nat.one_ne_zero, if_false, Nat.sub_self, zero_add]
      ring
  | succ j =>
      rw [M.chainTrace_succ_eq hT j, M.cyclesTrace_eq hT (j + 1)]
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      ring

/-- The Hopf trace formula for a bounded complex of finite-dimensional rational
vector spaces. -/
theorem hopf_trace_formula (M : FiniteChainEndomorphism) :
    (∑ k ∈ Finset.range (M.bound + 1),
      (-1 : ℚ)^k * M.homologyTrace k) =
    ∑ k ∈ Finset.range (M.bound + 1),
      (-1 : ℚ)^k * M.chainTrace k := by
  obtain ⟨b, hb0, hbtop, hb⟩ := hopf_trace_formula_aux_trace_decomposition M
  rw [← hopf_trace_formula_aux_telescope M.bound M.homologyTrace b hb0 hbtop]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hb k hk]

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
