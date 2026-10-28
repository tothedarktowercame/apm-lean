import ConstructionTargets.FiniteTriangulation
import ConstructionTargets.CompactClosedEquivalenceQuotient

/-! # A finite marked triangulation of the real projective plane

This file isolates the concrete polygon-triangulation input from the compact-to-Hausdorff
topological upgrade.  The intended proof of `rp2_explicit_finite_model` uses the six-vertex
triangulation of `RP²` (ten triangles), realized by coordinate vertices.
-/

open Set

noncomputable section

namespace ConstructionTargets.RealProjectivePlaneTriangulation

open ConstructionTargets.FiniteTriangulation
open ConstructionTargets.StatementSurfaceModels

/-- The one-crosscap polygon quotient is Hausdorff.  Concretely, its generating relation
identifies a boundary point with its antipode and is a closed equivalence relation on the
compact disk. -/
theorem rp2_t2Space_aux_edge_neg (t : Set.Icc (0 : ℝ) 1) :
    ((Surfaces.edgePoint 2 1 t : Surfaces.Disk) : ℂ) =
      -((Surfaces.edgePoint 2 0 t : Surfaces.Disk) : ℂ) := by
  simp only [Surfaces.edgePoint, Subtype.coe_mk]
  norm_num
  change Complex.exp (Complex.I * (2 * (Real.pi : ℂ) *
    (1 + (t.1 : ℂ)) / 2)) =
    -Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (t.1 : ℂ) / 2))
  calc
    _ = Complex.exp (Real.pi * Complex.I) *
        Complex.exp (Complex.I * (Real.pi * t.1)) := by
          rw [← Complex.exp_add]
          congr 1
          ring_nf
    _ = _ := by rw [Complex.exp_pi_mul_I]; ring

theorem rp2_t2Space_aux_rel_cases {x y : Surfaces.Disk}
    (h : Surfaces.SurfaceRel false 1 x y) :
    ‖(x : ℂ)‖ = 1 ∧ (y : ℂ) = -(x : ℂ) := by
  simp only [Surfaces.SurfaceRel, Bool.false_eq_true, if_false] at h
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  have : j = 0 := by omega
  subst j
  constructor
  · simp [Surfaces.edgePoint, Complex.norm_exp]
  · exact rp2_t2Space_aux_edge_neg t

theorem rp2_t2Space_aux_eqv_cases {x y : Surfaces.Disk}
    (h : Relation.EqvGen (Surfaces.SurfaceRel false 1) x y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ (y : ℂ) = -(x : ℂ)) := by
  induction h with
  | rel x y h => exact Or.inr (rp2_t2Space_aux_rel_cases h)
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
      rcases ih with rfl | ⟨hx, hy⟩
      · exact Or.inl rfl
      · right
        constructor
        · rw [hy, norm_neg, hx]
        · rw [hy, neg_neg]
  | trans x y z _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨hx, hy⟩
      · exact ih₂
      · rcases ih₂ with rfl | ⟨hy', hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · left
          apply Subtype.ext
          change (x : ℂ) = (z : ℂ)
          rw [hz, hy, neg_neg]

/-- Converse of `rp2_t2Space_aux_eqv_cases`: every boundary point is identified
with its antipode (write it as `edgePoint 2 0 t` or `edgePoint 2 1 t`). -/
theorem rp2_t2Space_aux_boundary_rel {x y : Surfaces.Disk}
    (hx : ‖(x : ℂ)‖ = 1) (hy : (y : ℂ) = -(x : ℂ)) :
    Relation.EqvGen (Surfaces.SurfaceRel false 1) x y := by
  by_cases harg : 0 ≤ Complex.arg (x : ℂ)
  · let t : Set.Icc (0 : ℝ) 1 :=
      ⟨Complex.arg (x : ℂ) / Real.pi, by
        constructor
        · exact div_nonneg harg Real.pi_pos.le
        · exact (div_le_one Real.pi_pos).2 (Complex.arg_le_pi _)⟩
    apply Relation.EqvGen.rel _ _
    simp only [Surfaces.SurfaceRel, Bool.false_eq_true, if_false]
    refine ⟨0, by omega, t, ?_, ?_⟩
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (x : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * t.1 / 2))
      rw [show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      congr 1
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (y : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * ((1 : ℝ) + t.1) / 2))
      rw [hy, show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      rw [show -Complex.exp (Complex.arg (x : ℂ) * Complex.I) =
          Complex.exp (Real.pi * Complex.I) *
            Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        rw [Complex.exp_pi_mul_I]
        simp]
      rw [← Complex.exp_add]
      apply congrArg Complex.exp
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
  · let t : Set.Icc (0 : ℝ) 1 :=
      ⟨Complex.arg (x : ℂ) / Real.pi + 1, by
        constructor
        · have h := Complex.neg_pi_lt_arg (x : ℂ)
          have : (-1 : ℝ) < Complex.arg (x : ℂ) / Real.pi :=
            (lt_div_iff₀ Real.pi_pos).2 (by linarith)
          linarith
        · have ha : Complex.arg (x : ℂ) ≤ 0 := le_of_not_ge harg
          have := div_nonpos_of_nonpos_of_nonneg ha Real.pi_pos.le
          linarith⟩
    apply Relation.EqvGen.symm _ _
    apply Relation.EqvGen.rel _ _
    simp only [Surfaces.SurfaceRel, Bool.false_eq_true, if_false]
    refine ⟨0, by omega, t, ?_, ?_⟩
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (y : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * t.1 / 2))
      rw [hy, show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      rw [show -Complex.exp (Complex.arg (x : ℂ) * Complex.I) =
          Complex.exp (Real.pi * Complex.I) *
            Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        rw [Complex.exp_pi_mul_I]
        simp]
      rw [← Complex.exp_add]
      apply congrArg Complex.exp
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
      ring
    · apply Subtype.ext
      simp only [Surfaces.edgePoint, Subtype.coe_mk]
      norm_num
      change (x : ℂ) = Complex.exp
        (Complex.I * (2 * Real.pi * ((1 : ℝ) + t.1) / 2))
      rw [show (x : ℂ) = Complex.exp (Complex.arg (x : ℂ) * Complex.I) by
        symm
        simpa [hx] using Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      rw [← mul_one (Complex.exp (Complex.arg (x : ℂ) * Complex.I)),
        ← Complex.exp_two_pi_mul_I, ← Complex.exp_add]
      apply congrArg Complex.exp
      simp [t]
      field_simp [ne_of_gt Real.pi_pos]
      ring

theorem rp2_t2Space_aux_isClosed :
    IsClosed {p : Surfaces.Disk × Surfaces.Disk |
      (Relation.EqvGen.setoid (Surfaces.SurfaceRel false 1)).r p.1 p.2} := by
  have hset : {p : Surfaces.Disk × Surfaces.Disk |
      (Relation.EqvGen.setoid (Surfaces.SurfaceRel false 1)).r p.1 p.2} =
      {p | p.1 = p.2} ∪ {p | ‖(p.1 : ℂ)‖ = 1 ∧ (p.2 : ℂ) = -(p.1 : ℂ)} := by
    ext p
    constructor
    · intro h
      exact rp2_t2Space_aux_eqv_cases h
    · rintro (h | ⟨hx, hy⟩)
      · obtain ⟨a, b⟩ := p
        change a = b at h
        subst h
        exact Relation.EqvGen.refl _
      · exact rp2_t2Space_aux_boundary_rel hx hy
  rw [hset]
  refine (isClosed_diagonal).union (IsClosed.inter ?_ ?_)
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) (by fun_prop)

theorem rp2_t2Space : T2Space RealProjectivePlane := by
  haveI : CompactSpace Surfaces.Disk :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  exact compact_closed_equivalence_quotient_t2 _ rp2_t2Space_aux_isClosed

/-- A finite geometric simplicial complex has compact underlying space. -/
theorem finite_simplicialComplex_space_isCompact
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) : IsCompact K.space := by
  rw [Geometry.SimplicialComplex.space]
  exact hK.isCompact_biUnion fun s _ =>
    s.finite_toSet.isCompact_convexHull ℝ

/-- Standard basis vector, used to realize an abstract complex on `Fin N`. -/
def basisVertex (N : ℕ) (i : Fin N) : EuclideanSpace ℝ (Fin N) :=
  EuclideanSpace.single i 1

/-- Basis vertices of any finite vertex set are affinely independent. -/
-- BEGIN SEAT AREA
lemma rp2_explicit_finite_model_aux_basis_indep {N : ℕ} (s : Finset (Fin N)) :
    AffineIndependent ℝ
      ((↑) : ↥(s.image (basisVertex N)) → EuclideanSpace ℝ (Fin N)) := by
  sorry
-- END SEAT AREA

/-- Convex hulls of basis-vertex faces meet in the hull of the common face
(a point of either hull has nonnegative coordinates summing to `1`, supported
on the face's index set). -/
lemma rp2_explicit_finite_model_aux_basis_inter {N : ℕ} (s t : Finset (Fin N)) :
    convexHull ℝ (↑(s.image (basisVertex N)) : Set (EuclideanSpace ℝ (Fin N))) ∩
        convexHull ℝ ↑(t.image (basisVertex N)) ⊆
      convexHull ℝ
        ((↑(s.image (basisVertex N)) : Set (EuclideanSpace ℝ (Fin N))) ∩
          ↑(t.image (basisVertex N))) := by
  sorry

/-- **LIBRARY (explicit six-vertex model).** There is a finite coordinate realization of
the standard six-vertex, ten-triangle triangulation of `RP²`, together with a continuous
bijection to the disk quotient.  The distinguished vertex maps to the disk centre.

The combinatorial model has vertices `Fin 6`; its ten facets are the complementary pairs
in the standard minimal triangulation.  Realizing vertices by standard basis vectors makes
affine independence and the face-intersection axiom coordinate-support calculations. -/
theorem rp2_explicit_finite_model :
    ∃ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
      (v : K.space) (f : K.space → RealProjectivePlane),
      K.faces.Finite ∧ {(v : EuclideanSpace ℝ (Fin n))} ∈ K.faces ∧
      Continuous f ∧ Function.Bijective f ∧
      f v = surfacePoint false 1 := by
  sorry

/-- Upgrade the explicit continuous bijection to a marked finite vertex triangulation. -/
theorem realProjectivePlane_hasFiniteVertexTriangulation :
    HasFiniteVertexTriangulation RealProjectivePlane (surfacePoint false 1) := by
  obtain ⟨n, K, v, f, hfin, hv, hfcont, hfbij, hmark⟩ :=
    rp2_explicit_finite_model
  letI : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (finite_simplicialComplex_space_isCompact K hfin)
  letI : T2Space RealProjectivePlane := rp2_t2Space
  let e' : K.space ≃ₜ RealProjectivePlane :=
    hfcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hfbij)
  let e : RealProjectivePlane ≃ₜ K.space := e'.symm
  refine ⟨n, K, e, (v : EuclideanSpace ℝ (Fin n)), hfin, hv, ?_⟩
  have heq : e (surfacePoint false 1) = v := by
    apply e'.injective
    simpa [e, e'] using hmark.symm
  exact congrArg Subtype.val heq

#print axioms realProjectivePlane_hasFiniteVertexTriangulation

end ConstructionTargets.RealProjectivePlaneTriangulation
