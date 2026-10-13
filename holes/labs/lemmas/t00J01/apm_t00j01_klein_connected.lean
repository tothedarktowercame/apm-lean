import ConstructionTargets.CoefficientSphereEndpoints
import ConstructionTargets.CircleWindingUniqueness
import ConstructionTargets.KleinClosedSquareOrbitInverseContinuity
import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t00J01 — three false manifold claims

The three counterexamples are concrete: a Klein-bottle quotient times a
circle, the identity map of the genuine two-sphere, and an explicit folding
self-map of the genuine circle.  For part (b), the Lefschetz number is the
actual alternating trace of the endomorphisms induced on rational singular
homology.

## Statement repairs

None.

## Encoding questions

The required rational-homology identifications of `S²` are explicit witnesses
inside `t00J01HasSphereLefschetzNumber`; their induced maps and traces cannot be
detached from the self-map under study.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t00j01_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t00j01_S2 := Metric.sphere (0 : apm_t00j01_E3) 1

abbrev apm_t00j01_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

abbrev T00J01RationalHomology (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def t00J01RationalHomologyMap {X : Type} [TopologicalSpace X]
    (k : ℕ) (f : C(X, X)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)

/-- The standard square presentation of the Klein bottle. -/
inductive apm_t00j01_kleinRel : (ℝ × ℝ) → (ℝ × ℝ) → Prop
  | horizontal (x y : ℝ) : apm_t00j01_kleinRel (x, y) (x + 1, y)
  | twisted (x y : ℝ) : apm_t00j01_kleinRel (x, y) (-x, y + 1)

def apm_t00j01_Klein :=
  Quotient (Relation.EqvGen.setoid apm_t00j01_kleinRel)

noncomputable instance : TopologicalSpace apm_t00j01_Klein :=
  TopologicalSpace.coinduced
    (fun p : ℝ × ℝ => Quotient.mk (Relation.EqvGen.setoid apm_t00j01_kleinRel) p)
    inferInstance

abbrev apm_t00j01_nonorientable3 := apm_t00j01_Klein × Circle

def apm_t00j01_isThreeManifold (M : Type) [TopologicalSpace M] : Prop :=
  IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) ∧
  ∀ x : M, ∃ (U : Set M) (V : Set apm_t00j01_E3),
    x ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V)

def t00J01SphereIdentityHomeomorph : apm_t00j01_S2 ≃ₜ apm_t00j01_S2 :=
  Homeomorph.refl apm_t00j01_S2

def t00J01SphereIdentity : C(apm_t00j01_S2, apm_t00j01_S2) :=
  ⟨t00J01SphereIdentityHomeomorph, t00J01SphereIdentityHomeomorph.continuous⟩

/-- `L` is the alternating trace of the maps genuinely induced by `f`, after
identifying `H₀(S²;ℚ)`, `H₁(S²;ℚ)`, and `H₂(S²;ℚ)` with `ℚ`, `0`, and `ℚ`. -/
def t00J01HasSphereLefschetzNumber
    (f : C(apm_t00j01_S2, apm_t00j01_S2)) (L : ℚ) : Prop :=
  ∃ h0 : T00J01RationalHomology 0 apm_t00j01_S2 ≅ ModuleCat.of ℚ ℚ,
    ∃ h1 : T00J01RationalHomology 1 apm_t00j01_S2 ≅
        ModuleCat.of ℚ (Fin 0 → ℚ),
      ∃ h2 : T00J01RationalHomology 2 apm_t00j01_S2 ≅ ModuleCat.of ℚ ℚ,
        L =
          LinearMap.trace ℚ ℚ
              (h0.inv ≫ t00J01RationalHomologyMap 0 f ≫ h0.hom).hom -
            LinearMap.trace ℚ (Fin 0 → ℚ)
              (h1.inv ≫ t00J01RationalHomologyMap 1 f ≫ h1.hom).hom +
            LinearMap.trace ℚ ℚ
              (h2.inv ≫ t00J01RationalHomologyMap 2 f ≫ h2.hom).hom

/-- The degree-one circle fold with lift `θ ↦ θ + 2 sin θ`. -/
def apm_t00j01_fold (z : Circle) : Circle :=
  z * Circle.exp (2 * (z : ℂ).im)

def apm_t00j01_foldLift (θ : ℝ) : ℝ := θ + 2 * Real.sin θ

lemma apm_t00j01_fold_exp (θ : ℝ) :
    apm_t00j01_fold (Circle.exp θ) =
      Circle.exp (apm_t00j01_foldLift θ) := by
  rw [apm_t00j01_fold, apm_t00j01_foldLift, Circle.exp_add]
  congr 2
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

lemma apm_t00j01_hasDerivAt_foldLift (θ : ℝ) :
    HasDerivAt apm_t00j01_foldLift (1 + 2 * Real.cos θ) θ := by
  simpa [apm_t00j01_foldLift] using
    (hasDerivAt_id θ).add ((Real.hasDerivAt_sin θ).const_mul 2)

@[simp] lemma apm_t00j01_deriv_foldLift (θ : ℝ) :
    deriv apm_t00j01_foldLift θ = 1 + 2 * Real.cos θ :=
  (apm_t00j01_hasDerivAt_foldLift θ).deriv

/-- For this explicit lift, regularity is nonvanishing of its derivative at
every lift of a point in the fiber. -/
def apm_t00j01_foldRegular (y : Circle) : Prop :=
  ∀ θ : ℝ, apm_t00j01_fold (Circle.exp θ) = y →
  1 + 2 * Real.cos θ ≠ 0

lemma apm_t00j01_fold_continuous : Continuous apm_t00j01_fold := by
  unfold apm_t00j01_fold
  fun_prop

/-- The evident preimage of `1` is regular. -/
lemma apm_t00j01_fold_zero : apm_t00j01_fold (Circle.exp 0) = 1 := by
  rw [apm_t00j01_fold_exp]
  simp [apm_t00j01_foldLift]

lemma apm_t00j01_fold_zero_deriv_ne : 1 + 2 * Real.cos 0 ≠ 0 := by
  norm_num

/-- The evident preimage of `exp π` is regular. -/
lemma apm_t00j01_fold_pi :
    apm_t00j01_fold (Circle.exp Real.pi) = Circle.exp Real.pi := by
  rw [apm_t00j01_fold_exp]
  simp [apm_t00j01_foldLift]

lemma apm_t00j01_fold_pi_deriv_ne :
    1 + 2 * Real.cos Real.pi ≠ 0 := by
  norm_num


lemma t00J01Identity_conjugate (k : ℕ) {V : ModuleCat ℚ}
    (h : T00J01RationalHomology k apm_t00j01_S2 ≅ V) :
    h.inv ≫ t00J01RationalHomologyMap k t00J01SphereIdentity ≫ h.hom = 𝟙 V := by
  change h.inv ≫ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).map (𝟙 (TopCat.of apm_t00j01_S2)) ≫ h.hom = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, h.inv_hom_id]

lemma t00J01Identity_lefschetz_value (L : ℚ)
    (h : t00J01HasSphereLefschetzNumber t00J01SphereIdentity L) : L = 2 := by
  obtain ⟨h0, h1, h2, h⟩ := h
  rw [t00J01Identity_conjugate, t00J01Identity_conjugate, t00J01Identity_conjugate] at h
  norm_num at h ⊢
  exact h

theorem apm_t00j01_sphere_identity_bridge :
    t00J01HasSphereLefschetzNumber t00J01SphereIdentity 2 ∧
      ¬t00J01HasSphereLefschetzNumber t00J01SphereIdentity 1 := by
  constructor
  · refine ⟨ConstructionTargets.CoefficientSphereEndpoints.rationalS2H0,
      ConstructionTargets.CoefficientSphereEndpoints.rationalS2H1,
      ConstructionTargets.CoefficientSphereEndpoints.rationalS2H2, ?_⟩
    rw [t00J01Identity_conjugate, t00J01Identity_conjugate, t00J01Identity_conjugate]
    norm_num
  · intro h
    have := t00J01Identity_lefschetz_value 1 h
    norm_num at this

/-- Every equivalence in the presented Klein quotient has the expected affine
normal form.  This is kept separate from topology so the group calculation and
the local-chart construction can be proved in parallel. -/
theorem apm_t00j01_kleinRel_normal_form {p q : ℝ × ℝ}
    (h : Relation.EqvGen apm_t00j01_kleinRel p q) :
    ∃ m n : ℤ,
      q.1 = (m : ℝ) + (-1 : ℝ) ^ n * p.1 ∧
      q.2 = (n : ℝ) + p.2 := by
  sorry

/-- The explicit Klein quotient is compact.  The closed fundamental square
and its orbit classification are supplied by the imported construction chain. -/
theorem apm_t00j01_klein_compact :
    IsCompact (Set.univ : Set apm_t00j01_Klein) := by
  sorry

/-- The explicit Klein quotient is connected, as a quotient of the connected
plane (equivalently, as the image of the connected fundamental square). -/
-- BEGIN SEAT AREA
theorem apm_t00j01_klein_connected :
    IsConnected (Set.univ : Set apm_t00j01_Klein) := by
  let q : ℝ × ℝ → apm_t00j01_Klein :=
    fun p => Quotient.mk (Relation.EqvGen.setoid apm_t00j01_kleinRel) p
  have hq : Continuous q := continuous_coinduced_rng
  have hsurj : Function.Surjective q := Quotient.mk_surjective
  rw [← hsurj.range_eq]
  exact isConnected_range hq
-- END SEAT AREA

/-- The normal form gives a small evenly-covered rectangle at every point of
the plane quotient, hence a two-dimensional Euclidean chart.  Its algebraic
input is an explicit hypothesis so this seat is independent of the normal-form
seat. -/
theorem apm_t00j01_klein_local_chart
    (_hnf : ∀ {p q : ℝ × ℝ},
      Relation.EqvGen apm_t00j01_kleinRel p q →
        ∃ m n : ℤ,
          q.1 = (m : ℝ) + (-1 : ℝ) ^ n * p.1 ∧
          q.2 = (n : ℝ) + p.2) :
    ∀ x : apm_t00j01_Klein,
      ∃ (U : Set apm_t00j01_Klein) (V : Set (EuclideanSpace ℝ (Fin 2))),
        x ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V) := by
  sorry

/-- The circle has its usual one-dimensional punctured-circle charts. -/
theorem apm_t00j01_circle_local_chart :
    ∀ z : Circle, ∃ (U : Set Circle) (V : Set ℝ),
      z ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V) := by
  sorry

/-- Compactness of the two factors assembles to compactness of their product.
The factor facts are hypotheses so all three seats are independent. -/
theorem apm_t00j01_klein_circle_compact
    (_hK : IsCompact (Set.univ : Set apm_t00j01_Klein)) :
    IsCompact (Set.univ : Set apm_t00j01_nonorientable3) := by
  sorry

/-- Connectedness of the two nonempty factors assembles to connectedness of
their product. -/
theorem apm_t00j01_klein_circle_connected
    (_hK : IsConnected (Set.univ : Set apm_t00j01_Klein)) :
    IsConnected (Set.univ : Set apm_t00j01_nonorientable3) := by
  sorry

/-- A two-dimensional Klein chart and a one-dimensional circle chart combine,
after the standard coordinate reassociation, to an open chart in `ℝ³`. -/
theorem apm_t00j01_klein_circle_local_chart
    (_hK : ∀ x : apm_t00j01_Klein,
      ∃ (U : Set apm_t00j01_Klein) (V : Set (EuclideanSpace ℝ (Fin 2))),
        x ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V))
    (_hC : ∀ z : Circle, ∃ (U : Set Circle) (V : Set ℝ),
      z ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V)) :
    ∀ x : apm_t00j01_nonorientable3,
      ∃ (U : Set apm_t00j01_nonorientable3) (V : Set apm_t00j01_E3),
        x ∈ U ∧ IsOpen U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V) := by
  sorry

/-- The explicit coinduced plane quotient, times the circle, is a compact
connected topological three-manifold in the concrete sense used by the
registered statement. -/
theorem apm_t00j01_klein_quotient_charts :
    apm_t00j01_isThreeManifold apm_t00j01_nonorientable3 := by
  refine ⟨apm_t00j01_klein_circle_compact apm_t00j01_klein_compact,
    apm_t00j01_klein_circle_connected apm_t00j01_klein_connected, ?_⟩
  exact apm_t00j01_klein_circle_local_chart
    (apm_t00j01_klein_local_chart fun {_ _} h =>
      apm_t00j01_kleinRel_normal_form h)
    apm_t00j01_circle_local_chart

/-- LIBRARY: the integral top singular homology of the concrete Klein-bottle
product vanishes.  The manifold conclusion is passed in explicitly so this
contract can be developed independently of the chart contract. -/
theorem apm_t00j01_klein_product_H3_zero
    (_hM : apm_t00j01_isThreeManifold apm_t00j01_nonorientable3) :
    Limits.IsZero (apm_t00j01_H 3 apm_t00j01_nonorientable3) := by
  sorry

/-- Every lift of the fiber over `exp π` has nonzero derivative. -/
lemma apm_t00j01_foldRegular_pi_aux_cos :
    Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]

lemma apm_t00j01_foldRegular_pi_aux_delta_pos :
    0 < Real.sqrt 3 - Real.pi / 3 := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs4 : (4 / 3 : ℝ) < Real.sqrt 3 := by nlinarith
  have hp4 : Real.pi / 3 < (4 / 3 : ℝ) := by
    nlinarith [Real.pi_lt_four]
  linarith

lemma apm_t00j01_foldRegular_pi_aux_delta_lt :
    Real.sqrt 3 - Real.pi / 3 < 2 * Real.pi := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hs2 : Real.sqrt 3 < 2 := by nlinarith
  nlinarith [Real.pi_gt_three]

lemma apm_t00j01_foldRegular_pi_aux_not_multiple (m : ℤ) :
    Real.sqrt 3 - Real.pi / 3 ≠ (m : ℝ) * (2 * Real.pi) := by
  intro h
  have hm0 : (0 : ℝ) < m := by
    have hd := apm_t00j01_foldRegular_pi_aux_delta_pos
    rw [h] at hd
    rcases (mul_pos_iff.mp hd) with hm | hm
    · exact hm.1
    · exfalso
      exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤ 2 * Real.pi)) hm.2
  have hm1 : (m : ℝ) < 1 := by
    have hp : 0 < 2 * Real.pi := by positivity
    have hd := apm_t00j01_foldRegular_pi_aux_delta_lt
    rw [h] at hd
    by_contra hm
    have hm' : (1 : ℝ) ≤ m := le_of_not_gt hm
    have := mul_le_mul_of_nonneg_right hm' hp.le
    linarith
  have hm0z : 0 < m := by exact_mod_cast hm0
  have hm1z : m < 1 := by exact_mod_cast hm1
  omega

theorem apm_t00j01_foldRegular_pi :
    apm_t00j01_foldRegular (Circle.exp Real.pi) := by
  intro θ hfiber hzero
  have hcos : Real.cos θ = -(1 / 2 : ℝ) := by linarith
  have hclass := (Real.cos_eq_cos_iff.mp
    (apm_t00j01_foldRegular_pi_aux_cos.trans hcos.symm))
  obtain ⟨k, hk | hk⟩ := hclass
  · have hspecial : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.sin_pi_sub, Real.sin_pi_div_three]
    have hsin : Real.sin θ = Real.sqrt 3 / 2 := calc
      Real.sin θ = Real.sin (2 * Real.pi / 3 + (k : ℝ) * (2 * Real.pi)) := by
        rw [hk]
        congr 1 <;> ring
      _ = Real.sin (2 * Real.pi / 3) := Real.sin_add_int_mul_two_pi _ _
      _ = Real.sqrt 3 / 2 := hspecial
    rw [apm_t00j01_fold_exp] at hfiber
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hfiber
    apply apm_t00j01_foldRegular_pi_aux_not_multiple (n - k)
    dsimp [apm_t00j01_foldLift] at hn
    rw [hsin, hk] at hn
    norm_num [Int.cast_sub] at hn ⊢
    linarith
  · have hspecial : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.sin_pi_sub, Real.sin_pi_div_three]
    have hsin : Real.sin θ = -(Real.sqrt 3 / 2) := calc
      Real.sin θ = Real.sin ((k : ℝ) * (2 * Real.pi) - 2 * Real.pi / 3) := by
        rw [hk]
        congr 1 <;> ring
      _ = -Real.sin (2 * Real.pi / 3) := Real.sin_int_mul_two_pi_sub _ _
      _ = -(Real.sqrt 3 / 2) := by rw [hspecial]
    rw [apm_t00j01_fold_exp] at hfiber
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hfiber
    apply apm_t00j01_foldRegular_pi_aux_not_multiple (k - n - 1)
    dsimp [apm_t00j01_foldLift] at hn
    rw [hsin, hk] at hn
    norm_num [Int.cast_sub] at hn ⊢
    linarith

/-- Every lift of the fiber over `1` has nonzero derivative. -/
lemma apm_t00j01_foldRegular_one_aux_int_gap (j : ℤ) :
    (1 / 3 : ℝ) ≤ |(j : ℝ) - 1 / 3| := by
  by_cases hj : j ≤ 0
  · have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hj : 1 ≤ j := by omega
    have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma apm_t00j01_foldRegular_one_aux_cos_two_pi_div_three :
    Real.cos (2 * Real.pi / 3) = (-1 / 2 : ℝ) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
  rw [Real.cos_sub, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  ring

theorem apm_t00j01_foldRegular_one :
    apm_t00j01_foldRegular 1 := by
  intro θ hfold hderiv
  have hexp : Circle.exp (apm_t00j01_foldLift θ) = Circle.exp 0 := by
    rw [← apm_t00j01_fold_exp]
    simpa using hfold
  obtain ⟨n, hn, -⟩ :=
    (ConstructionTargets.CircleWindingUniqueness.exp_eq_iff_existsUnique_endpointWinding
      (apm_t00j01_foldLift θ) 0).mp hexp
  have hcos : Real.cos θ = (-1 / 2 : ℝ) := by linarith
  have hclass := (Real.cos_eq_cos_iff).mp
    (hcos.trans apm_t00j01_foldRegular_one_aux_cos_two_pi_div_three.symm)
  rcases hclass with ⟨k, hk | hk⟩
  · let j : ℤ := n + k
    have heq : Real.sin θ = Real.pi * ((j : ℝ) - 1 / 3) := by
      unfold ConstructionTargets.CircleWindingUniqueness.IsEndpointWinding at hn
      simp only [apm_t00j01_foldLift, zero_add] at hn
      dsimp [j]
      push_cast
      nlinarith [hk]
    have hgap := apm_t00j01_foldRegular_one_aux_int_gap j
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have habs : 1 < |Real.sin θ| := by
      rw [heq, abs_mul]
      rw [abs_of_pos (by positivity : 0 < Real.pi)]
      nlinarith
    exact (not_lt_of_ge (Real.abs_sin_le_one θ)) habs
  · let j : ℤ := k - n
    have heq : Real.sin θ = -Real.pi * ((j : ℝ) - 1 / 3) := by
      unfold ConstructionTargets.CircleWindingUniqueness.IsEndpointWinding at hn
      simp only [apm_t00j01_foldLift, zero_add] at hn
      dsimp [j]
      push_cast
      nlinarith [hk]
    have hgap := apm_t00j01_foldRegular_one_aux_int_gap j
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have habs : 1 < |Real.sin θ| := by
      rw [heq, abs_mul]
      rw [abs_neg, abs_of_pos (by positivity : 0 < Real.pi)]
      nlinarith
    exact (not_lt_of_ge (Real.abs_sin_le_one θ)) habs

def apm_t00j01_foldFiberCard_pi_aux_angleEquiv :
    {z : Circle // apm_t00j01_fold z = Circle.exp Real.pi} ≃
      {θ : Set.Ioc (-Real.pi) Real.pi //
        Circle.exp (apm_t00j01_foldLift θ.1) = Circle.exp Real.pi} where
  toFun z := ⟨⟨Complex.arg z.1, Complex.arg_mem_Ioc z.1⟩, by
    rw [← apm_t00j01_fold_exp, Circle.exp_arg]
    exact z.2⟩
  invFun θ := ⟨Circle.exp θ.1.1, by
    rw [apm_t00j01_fold_exp]
    exact θ.2⟩
  left_inv z := by
    apply Subtype.ext
    exact Circle.exp_arg z.1
  right_inv θ := by
    apply Subtype.ext
    apply Subtype.ext
    exact Circle.arg_exp θ.1.2.1 θ.1.2.2

lemma apm_t00j01_foldFiberCard_pi_aux_reduce_to_angles :
    Nat.card {z : Circle // apm_t00j01_fold z = Circle.exp Real.pi} =
      Nat.card {θ : Set.Ioc (-Real.pi) Real.pi //
        Circle.exp (apm_t00j01_foldLift θ.1) = Circle.exp Real.pi} := by
  exact Nat.card_congr apm_t00j01_foldFiberCard_pi_aux_angleEquiv

lemma apm_t00j01_foldFiberCard_pi_aux_angle_count_aux_strictConcave :
    StrictConcaveOn ℝ (Set.Icc 0 Real.pi) apm_t00j01_foldLift := by
  refine ⟨strictConcaveOn_sin_Icc.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hs := strictConcaveOn_sin_Icc.2 hx hy hxy ha hb hab
  dsimp [apm_t00j01_foldLift] at hs ⊢
  nlinarith

lemma apm_t00j01_foldFiberCard_pi_aux_angle_count_aux_odd (x : ℝ) :
    apm_t00j01_foldLift (-x) = -apm_t00j01_foldLift x := by
  simp [apm_t00j01_foldLift]
  ring

lemma apm_t00j01_foldFiberCard_pi_aux_angle_count_aux_inner_root :
    ∃ x ∈ Set.Ioo 0 (Real.pi / 2), apm_t00j01_foldLift x = Real.pi := by
  have hcont : ContinuousOn apm_t00j01_foldLift (Set.Icc 0 (Real.pi / 2)) := by
    exact (continuous_id.add (Real.continuous_sin.const_mul 2)).continuousOn
  have h0 : apm_t00j01_foldLift 0 < Real.pi := by
    simp [apm_t00j01_foldLift, Real.pi_pos]
  have hmid : Real.pi < apm_t00j01_foldLift (Real.pi / 2) := by
    rw [apm_t00j01_foldLift, Real.sin_pi_div_two]
    linarith [Real.pi_lt_four]
  have himage : Real.pi ∈ apm_t00j01_foldLift '' Set.Icc 0 (Real.pi / 2) :=
    (intermediate_value_Icc (by positivity) hcont) ⟨h0.le, hmid.le⟩
  rcases himage with ⟨x, hx, hfx⟩
  refine ⟨x, ⟨?_, ?_⟩, hfx⟩
  · exact lt_of_not_ge fun h => by
      have : x = 0 := le_antisymm h hx.1
      subst x
      simp [apm_t00j01_foldLift] at hfx
      exact Real.pi_ne_zero hfx.symm
  · exact lt_of_le_of_ne hx.2 fun h => by
      subst x
      exact hmid.ne' hfx

/-- Seat: on `(-π, π]`, `exp (g θ) = exp π` iff `g θ = π` or `g θ = -π`
(`|g θ| ≤ π + 2 < 3π`; `Circle.exp_eq_exp` up to `2π ℤ`). -/
theorem apm_t00j01_angle_classify (θ : ℝ) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) :
    Circle.exp (apm_t00j01_foldLift θ) = Circle.exp Real.pi ↔
      apm_t00j01_foldLift θ = Real.pi ∨ apm_t00j01_foldLift θ = -Real.pi := by
  constructor
  · intro hexp
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
    have hbound : |apm_t00j01_foldLift θ| < 2 * Real.pi := by
      rw [apm_t00j01_foldLift]
      calc
        |θ + 2 * Real.sin θ| ≤ |θ| + 2 * |Real.sin θ| := by
          simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
            abs_add_le θ (2 * Real.sin θ)
        _ ≤ Real.pi + 2 := by
          have ha : |θ| ≤ Real.pi :=
            (abs_le).2 ⟨by linarith [hθ.1], hθ.2⟩
          have hs : |Real.sin θ| ≤ 1 :=
            (abs_le).2 ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
          linarith
        _ < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hnlt : n < 1 := by
      have hu : apm_t00j01_foldLift θ < 2 * Real.pi := (abs_lt.mp hbound).2
      have hpi : 0 < Real.pi := Real.pi_pos
      have : (n : ℝ) < 1 := by
        rw [hn] at hu
        nlinarith
      exact_mod_cast this
    have hnneg : -2 < n := by
      have hl : -(2 * Real.pi) < apm_t00j01_foldLift θ := (abs_lt.mp hbound).1
      have hpi : 0 < Real.pi := Real.pi_pos
      have : (-2 : ℝ) < n := by
        rw [hn] at hl
        nlinarith
      exact_mod_cast this
    have hn_cases : n = 0 ∨ n = -1 := by omega
    rcases hn_cases with rfl | rfl
    · left
      simpa using hn
    · right
      rw [hn]
      ring
  · rintro (h | h)
    · rw [h]
    · rw [h]
      exact Circle.exp_eq_exp.mpr ⟨-1, by ring⟩

/-- Seat: on `[0, π]` the equation `g θ = π` has exactly the interior root and
`θ = π` (strict concavity: a strictly concave function takes a value at most
twice; `g 0 = 0`; use the banked concavity and root lemmas above). -/
theorem apm_t00j01_angle_positive_roots :
    ∃ x₀ ∈ Set.Ioo 0 (Real.pi / 2), ∀ θ ∈ Set.Icc 0 Real.pi,
      apm_t00j01_foldLift θ = Real.pi ↔ θ = x₀ ∨ θ = Real.pi := by
  obtain ⟨x₀, hx₀, hroot⟩ :=
    apm_t00j01_foldFiberCard_pi_aux_angle_count_aux_inner_root
  refine ⟨x₀, hx₀, ?_⟩
  intro θ hθ
  constructor
  · intro hrootθ
    by_cases hθx : θ = x₀
    · exact Or.inl hθx
    by_cases hθπ : θ = Real.pi
    · exact Or.inr hθπ
    exfalso
    have hxπ : x₀ < Real.pi := by
      exact lt_trans hx₀.2 (by linarith [Real.pi_pos])
    have hθπlt : θ < Real.pi := lt_of_le_of_ne hθ.2 hθπ
    have hconc :=
      apm_t00j01_foldFiberCard_pi_aux_angle_count_aux_strictConcave
    have hrootπ : apm_t00j01_foldLift Real.pi = Real.pi := by
      simp [apm_t00j01_foldLift]
    rcases lt_or_gt_of_ne hθx with hθxlt | hxθlt
    · have hxseg : x₀ ∈ openSegment ℝ θ Real.pi := by
        rw [openSegment_eq_Ioo hθπlt, Set.mem_Ioo]
        exact ⟨hθxlt, hxπ⟩
      have hne : θ ≠ Real.pi := hθπ
      have hlt := hconc.lt_on_openSegment hθ (by
        exact ⟨Real.pi_pos.le, le_rfl⟩) hne hxseg
      rw [hrootθ, hrootπ, hroot, min_self] at hlt
      exact (lt_irrefl Real.pi hlt)
    · have hθseg : θ ∈ openSegment ℝ x₀ Real.pi := by
        rw [openSegment_eq_Ioo hxπ, Set.mem_Ioo]
        exact ⟨hxθlt, hθπlt⟩
      have hxne : x₀ ≠ Real.pi := ne_of_lt hxπ
      have hlt := hconc.lt_on_openSegment
        ⟨hx₀.1.le, hxπ.le⟩ (by exact ⟨Real.pi_pos.le, le_rfl⟩)
        hxne hθseg
      rw [hroot, hrootπ, hrootθ, min_self] at hlt
      exact (lt_irrefl Real.pi hlt)
  · rintro (rfl | rfl)
    · exact hroot
    · simp [apm_t00j01_foldLift]

/-- Seat (assembly from hypotheses): with oddness (banked) and `g ≥ 0` on `[0, π]`
(`sin ≥ 0` there), the solutions in `(-π, π]` are exactly `x₀, π, -x₀`. -/
theorem apm_t00j01_angle_count_of_parts
    (hclass : ∀ θ ∈ Set.Ioc (-Real.pi) Real.pi,
      Circle.exp (apm_t00j01_foldLift θ) = Circle.exp Real.pi ↔
        apm_t00j01_foldLift θ = Real.pi ∨ apm_t00j01_foldLift θ = -Real.pi)
    (hpos : ∃ x₀ ∈ Set.Ioo 0 (Real.pi / 2), ∀ θ ∈ Set.Icc 0 Real.pi,
      apm_t00j01_foldLift θ = Real.pi ↔ θ = x₀ ∨ θ = Real.pi) :
    Nat.card {θ : Set.Ioc (-Real.pi) Real.pi //
      Circle.exp (apm_t00j01_foldLift θ.1) = Circle.exp Real.pi} = 3 := by
  obtain ⟨x₀, hx₀, hpos⟩ := hpos
  have hsolutions : ∀ θ ∈ Set.Ioc (-Real.pi) Real.pi,
      Circle.exp (apm_t00j01_foldLift θ) = Circle.exp Real.pi ↔
        θ = x₀ ∨ θ = Real.pi ∨ θ = -x₀ := by
    intro θ hθ
    rw [hclass θ hθ]
    constructor
    · intro hg
      by_cases hnonneg : 0 ≤ θ
      · have hsin : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_nonneg_of_le_pi hnonneg hθ.2
        rcases hg with hg | hg
        · rcases (hpos θ ⟨hnonneg, hθ.2⟩).mp hg with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exfalso
          dsimp [apm_t00j01_foldLift] at hg
          nlinarith [Real.pi_pos]
      · have hneg : θ < 0 := lt_of_not_ge hnonneg
        have hmθ : -θ ∈ Set.Icc (0 : ℝ) Real.pi := by
          constructor <;> linarith [hθ.1]
        rcases hg with hg | hg
        · have hsin : Real.sin θ ≤ 0 := by
            have := Real.sin_nonneg_of_nonneg_of_le_pi hmθ.1 hmθ.2
            simpa using this
          exfalso
          dsimp [apm_t00j01_foldLift] at hg
          nlinarith [Real.pi_pos]
        · have hm : apm_t00j01_foldLift (-θ) = Real.pi := by
            rw [apm_t00j01_foldFiberCard_pi_aux_angle_count_aux_odd, hg]
            ring
          rcases (hpos (-θ) hmθ).mp hm with hm | hm
          · exact Or.inr (Or.inr (by linarith))
          · exfalso
            linarith [hθ.1]
    · intro h
      rcases h with h | h | h
      · subst θ
        exact Or.inl ((hpos x₀ ⟨hx₀.1.le, le_trans hx₀.2.le
          (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)⟩).2 (Or.inl rfl))
      · subst θ
        exact Or.inl ((hpos Real.pi ⟨Real.pi_pos.le, le_rfl⟩).2 (Or.inr rfl))
      · subst θ
        exact Or.inr (by
          rw [apm_t00j01_foldFiberCard_pi_aux_angle_count_aux_odd]
          have := (hpos x₀ ⟨hx₀.1.le, le_trans hx₀.2.le
            (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)⟩).2 (Or.inl rfl)
          rw [this])
  have hmem : ∀ θ : ℝ, θ = x₀ ∨ θ = Real.pi ∨ θ = -x₀ →
      θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    intro θ h
    rcases h with h | h | h
    · rw [h]
      constructor <;> linarith [hx₀.1, hx₀.2, Real.pi_pos]
    · rw [h]
      exact ⟨by linarith [Real.pi_pos], le_rfl⟩
    · rw [h]
      constructor <;> linarith [hx₀.1, hx₀.2, Real.pi_pos]
  let e : {θ : Set.Ioc (-Real.pi) Real.pi //
      Circle.exp (apm_t00j01_foldLift θ.1) = Circle.exp Real.pi} ≃
      {θ : ℝ // θ = x₀ ∨ θ = Real.pi ∨ θ = -x₀} :=
    { toFun := fun θ => ⟨θ.1, (hsolutions θ.1 θ.1.2).mp θ.2⟩
      invFun := fun θ => ⟨⟨θ.1, hmem θ.1 θ.2⟩,
        (hsolutions θ.1 (hmem θ.1 θ.2)).2 θ.2⟩
      left_inv := fun θ => by apply Subtype.ext; rfl
      right_inv := fun θ => by apply Subtype.ext; rfl }
  rw [Nat.card_congr e]
  have hne₁ : x₀ ≠ Real.pi := by linarith [hx₀.2, Real.pi_pos]
  have hne₂ : x₀ ≠ -x₀ := by linarith [hx₀.1]
  have hne₃ : Real.pi ≠ -x₀ := by linarith [hx₀.1, Real.pi_pos]
  let e' : {θ : ℝ // θ = x₀ ∨ θ = Real.pi ∨ θ = -x₀} ≃ Fin 3 :=
    { toFun := fun θ => if θ.1 = x₀ then 0 else if θ.1 = Real.pi then 1 else 2
      invFun := fun i => ⟨![x₀, Real.pi, -x₀] i, by fin_cases i <;> simp⟩
      left_inv := fun θ => by
        rcases θ.2 with h | h | h
        · apply Subtype.ext
          simp [h]
        · apply Subtype.ext
          simp [h, hne₁.symm]
        · apply Subtype.ext
          simp [h, hne₂.symm, hne₃.symm]
      right_inv := fun i => by
        fin_cases i
        · simp
        · simp [hne₁.symm]
        · simp [hne₂.symm, hne₃.symm] }
  rw [Nat.card_congr e']
  simp

lemma apm_t00j01_foldFiberCard_pi_aux_angle_count :
    Nat.card {θ : Set.Ioc (-Real.pi) Real.pi //
      Circle.exp (apm_t00j01_foldLift θ.1) = Circle.exp Real.pi} = 3 := by
  exact apm_t00j01_angle_count_of_parts apm_t00j01_angle_classify
    apm_t00j01_angle_positive_roots

theorem apm_t00j01_foldFiberCard_pi :
    Nat.card {z : Circle // apm_t00j01_fold z = Circle.exp Real.pi} = 3 := by
  rw [apm_t00j01_foldFiberCard_pi_aux_reduce_to_angles]
  exact apm_t00j01_foldFiberCard_pi_aux_angle_count

/-- The other selected regular fiber has exactly one circle point. -/
lemma apm_t00j01_foldFiberCard_one_aux_angle (z : Circle) :
    ∃ θ : ℝ, θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Circle.exp θ = z := by
  simpa only [Set.mem_univ, and_true] using Circle.surjOn_exp_neg_pi_pi (Set.mem_univ z)

lemma apm_t00j01_foldFiberCard_one_aux_unique (z : Circle)
    (hz : apm_t00j01_fold z = 1) : z = 1 := by
  obtain ⟨θ, hθ, rfl⟩ := apm_t00j01_foldFiberCard_one_aux_angle z
  rw [apm_t00j01_fold_exp] at hz
  have hexp : Circle.exp (apm_t00j01_foldLift θ) = Circle.exp 0 := by simpa using hz
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  have hsin_nonneg : 0 ≤ θ → 0 ≤ Real.sin θ := by
    intro h0
    exact Real.sin_nonneg_of_nonneg_of_le_pi h0 hθ.2
  have hsin_nonpos : θ ≤ 0 → Real.sin θ ≤ 0 := by
    intro h0
    have hneg : 0 ≤ -θ := neg_nonneg.mpr h0
    have hle : -θ ≤ Real.pi := by linarith [hθ.1]
    simpa only [Real.sin_neg, neg_nonneg] using
      (Real.sin_nonneg_of_nonneg_of_le_pi hneg hle)
  have hbound : |apm_t00j01_foldLift θ| < 2 * Real.pi := by
    rw [apm_t00j01_foldLift]
    calc
      |θ + 2 * Real.sin θ| ≤ |θ| + 2 * |Real.sin θ| := by
        simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
          abs_add_le θ (2 * Real.sin θ)
      _ ≤ Real.pi + 2 := by
        have ha : |θ| ≤ Real.pi := (abs_le).2 ⟨by linarith [hθ.1], hθ.2⟩
        have hs : |Real.sin θ| ≤ 1 :=
          (abs_le).2 ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
        linarith
      _ < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn0 : n = 0 := by
    have hnabs : |(n : ℝ)| < 1 := by
      rw [apm_t00j01_foldLift] at hn hbound
      have hpi : 0 < 2 * Real.pi := by positivity
      rw [hn, zero_add, abs_mul, abs_of_pos hpi] at hbound
      nlinarith
    have hnlt : (n : ℝ) < 1 := lt_of_le_of_lt (le_abs_self _) hnabs
    have hnneglt : (-(n : ℝ)) < 1 := lt_of_le_of_lt (neg_le_abs _) hnabs
    have hn_lt : n < 1 := by exact_mod_cast hnlt
    have hn_gt : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
    omega
  have hphi : θ + 2 * Real.sin θ = 0 := by
    simpa [apm_t00j01_foldLift, hn0] using hn
  have hθ0 : θ = 0 := by
    rcases le_total θ 0 with hneg | hpos
    · have hs := hsin_nonpos hneg
      linarith
    · have hs := hsin_nonneg hpos
      linarith
  simp [hθ0]

theorem apm_t00j01_foldFiberCard_one :
    Nat.card {z : Circle // apm_t00j01_fold z = 1} = 1 := by
  let x : {z : Circle // apm_t00j01_fold z = 1} :=
    ⟨1, by simpa using apm_t00j01_fold_zero⟩
  letI : Unique {z : Circle // apm_t00j01_fold z = 1} := {
    default := x
    uniq := fun y => Subtype.ext (apm_t00j01_foldFiberCard_one_aux_unique y y.property) }
  exact Nat.card_unique

theorem apm_t00j01 :
    (apm_t00j01_isThreeManifold apm_t00j01_nonorientable3 ∧
      Limits.IsZero (apm_t00j01_H 3 apm_t00j01_nonorientable3)) ∧
    (t00J01HasSphereLefschetzNumber t00J01SphereIdentity 2 ∧
      ¬t00J01HasSphereLefschetzNumber t00J01SphereIdentity 1) ∧
    (Continuous apm_t00j01_fold ∧
      apm_t00j01_foldRegular (Circle.exp Real.pi) ∧
      apm_t00j01_foldRegular 1 ∧
      Nat.card {z : Circle // apm_t00j01_fold z = Circle.exp Real.pi} = 3 ∧
      Nat.card {z : Circle // apm_t00j01_fold z = 1} = 1) := by
  have hM := apm_t00j01_klein_quotient_charts
  exact
    ⟨⟨hM, apm_t00j01_klein_product_H3_zero hM⟩,
      apm_t00j01_sphere_identity_bridge,
      apm_t00j01_fold_continuous,
      apm_t00j01_foldRegular_pi,
      apm_t00j01_foldRegular_one,
      apm_t00j01_foldFiberCard_pi,
      apm_t00j01_foldFiberCard_one⟩

#print axioms apm_t00j01
