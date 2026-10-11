import Mathlib
import ConstructionTargets.CircleHomology
import ConstructionTargets.CoefficientCoordinateReflections
import ConstructionTargets.CoefficientFirstReflection
import ConstructionTargets.SingularHomologyHomotopy

/-! # APM t95J02: retractions of the Klein bottle onto its core circles

## Statement repairs

None.

## Encoding question

The standard square picture is encoded as the quotient of `ℝ × ℝ` generated
by vertical translation and a horizontal glide reflection. The two circles
are the images of the coordinate axes, bundled as subspaces of that concrete
quotient, and their inclusions are the corresponding continuous subtype maps.
-/

open CategoryTheory

noncomputable section

/-- Generating identifications `(x,y) ∼ (x+1,-y)` and
`(x,y) ∼ (x,y+1)` for the Klein bottle. -/
inductive t95J02KleinRel : (ℝ × ℝ) → (ℝ × ℝ) → Prop
  | glide (x y : ℝ) : t95J02KleinRel (x, y) (x + 1, -y)
  | vertical (x y : ℝ) : t95J02KleinRel (x, y) (x, y + 1)

def t95J02KleinBottleType :=
  Quotient (Relation.EqvGen.setoid t95J02KleinRel)

noncomputable instance : TopologicalSpace t95J02KleinBottleType :=
  TopologicalSpace.coinduced
    (fun p : ℝ × ℝ ↦ Quotient.mk (Relation.EqvGen.setoid t95J02KleinRel) p)
    inferInstance

def t95J02QuotientPoint (p : ℝ × ℝ) : t95J02KleinBottleType :=
  Quotient.mk _ p

/-- The vertical period holds as an equality in the concrete quotient. -/
lemma t95J02QuotientPoint_vertical (x y : ℝ) :
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x, y + 1) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (t95J02KleinRel.vertical x y))

/-- The glide reflection holds as an equality in the concrete quotient. -/
lemma t95J02QuotientPoint_glide (x y : ℝ) :
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 1, -y) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (t95J02KleinRel.glide x y))

/-- Applying the glide twice produces the horizontal period two in the
quotient.  This is the point-set shadow of squaring the horizontal generator
in the usual Klein-bottle presentation. -/
lemma t95J02QuotientPoint_glide_twice (x y : ℝ) :
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 2, y) := by
  calc
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 1, -y) :=
      t95J02QuotientPoint_glide x y
    _ = t95J02QuotientPoint (x + 2, y) := by
      convert t95J02QuotientPoint_glide (x + 1) (-y) using 1
      all_goals ring_nf

/-- A vertical translate is carried by the glide to the inverse vertical
translate.  This compiles the concrete endpoint identity underlying the
presentation relation `b a b⁻¹ = a⁻¹`; only its transport to loops or
homology remains unavailable. -/
lemma t95J02QuotientPoint_glide_vertical_inverse (x y : ℝ) :
    t95J02QuotientPoint (x, y + 1) =
      t95J02QuotientPoint (x + 1, -y - 1) := by
  convert t95J02QuotientPoint_glide x (y + 1) using 1
  all_goals ring_nf

def t95J02KleinBottle : TopCat := TopCat.of t95J02KleinBottleType

/-- The horizontal core circle in the standard quotient picture. -/
def t95J02CircleA : TopCat :=
  TopCat.of {z : t95J02KleinBottleType // ∃ x : ℝ, z = t95J02QuotientPoint (x, 0)}

/-- The vertical core circle in the standard quotient picture. -/
def t95J02CircleB : TopCat :=
  TopCat.of {z : t95J02KleinBottleType // ∃ y : ℝ, z = t95J02QuotientPoint (0, y)}

def t95J02InclusionA : t95J02CircleA ⟶ t95J02KleinBottle :=
  ⟨Subtype.val, continuous_subtype_val⟩

def t95J02InclusionB : t95J02CircleB ⟶ t95J02KleinBottle :=
  ⟨Subtype.val, continuous_subtype_val⟩

def HasT95J02Retraction {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∃ r : X ⟶ A, i ≫ r = 𝟙 A

private def t95J02CollapseARaw (p : ℝ × ℝ) : t95J02CircleA :=
  ⟨t95J02QuotientPoint (p.1, 0), ⟨p.1, rfl⟩⟩

private lemma t95J02CollapseARaw_generator
    {p q : ℝ × ℝ} (h : t95J02KleinRel p q) :
    t95J02CollapseARaw p = t95J02CollapseARaw q := by
  cases h with
  | glide x y =>
      apply Subtype.ext
      change t95J02QuotientPoint (x, 0) = t95J02QuotientPoint (x + 1, 0)
      have hg : t95J02KleinRel (x, 0) (x + 1, 0) := by
        simpa using t95J02KleinRel.glide x 0
      exact Quotient.sound (Relation.EqvGen.rel _ _ hg)
  | vertical x y => rfl

private lemma t95J02CollapseARaw_eqvGen
    {p q : ℝ × ℝ} (h : Relation.EqvGen t95J02KleinRel p q) :
    t95J02CollapseARaw p = t95J02CollapseARaw q := by
  exact Relation.EqvGen.rec
    (fun _ _ hrel => t95J02CollapseARaw_generator hrel)
    (fun _ => rfl)
    (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂) h

private lemma t95J02CollapseARaw_continuous : Continuous t95J02CollapseARaw := by
  exact (continuous_coinduced_rng.comp
    (continuous_fst.prodMk continuous_const)).subtype_mk _

private def t95J02RetractionA : t95J02KleinBottle ⟶ t95J02CircleA :=
  ⟨Quotient.lift t95J02CollapseARaw
    (fun _ _ h => t95J02CollapseARaw_eqvGen h),
    t95J02CollapseARaw_continuous.quotient_lift _⟩

private lemma t95J02RetractionA_comp_inclusion :
    t95J02InclusionA ≫ t95J02RetractionA = 𝟙 t95J02CircleA := by
  ext z
  rcases z with ⟨z, ⟨x, rfl⟩⟩
  rfl

namespace t95J02Closure

open unitInterval

/-- A quotient-invariant pair of trigonometric coordinates.  On the vertical
core this is the usual cosine-sine parametrization of the circle. -/
def separatingRaw (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos (2 * Real.pi * p.2),
    Real.sin (2 * Real.pi * p.2) * Real.cos (Real.pi * p.1)]

theorem separatingRaw_generator {p q : ℝ × ℝ} (h : t95J02KleinRel p q) :
    separatingRaw p = separatingRaw q := by
  cases h with
  | glide x y =>
      ext i
      fin_cases i
      · change Real.cos (2 * Real.pi * y) = Real.cos (2 * Real.pi * -y)
        rw [show 2 * Real.pi * -y = -(2 * Real.pi * y) by ring, Real.cos_neg]
      · change Real.sin (2 * Real.pi * y) * Real.cos (Real.pi * x) =
          Real.sin (2 * Real.pi * -y) * Real.cos (Real.pi * (x + 1))
        have hy : 2 * Real.pi * -y = -(2 * Real.pi * y) := by ring
        have hx : Real.pi * (x + 1) = Real.pi * x + Real.pi := by ring
        rw [hy, Real.sin_neg, hx, Real.cos_add_pi]
        simp
  | vertical x y =>
      ext i
      fin_cases i
      · change Real.cos (2 * Real.pi * y) = Real.cos (2 * Real.pi * (y + 1))
        have hy : 2 * Real.pi * (y + 1) = 2 * Real.pi * y + 2 * Real.pi := by ring
        rw [hy, Real.cos_add_two_pi]
      · change Real.sin (2 * Real.pi * y) * Real.cos (Real.pi * x) =
          Real.sin (2 * Real.pi * (y + 1)) * Real.cos (Real.pi * x)
        have hy : 2 * Real.pi * (y + 1) = 2 * Real.pi * y + 2 * Real.pi := by ring
        rw [hy, Real.sin_add_two_pi]

theorem separatingRaw_eqvGen {p q : ℝ × ℝ}
    (h : Relation.EqvGen t95J02KleinRel p q) : separatingRaw p = separatingRaw q := by
  exact Relation.EqvGen.rec
    (fun _ _ hrel => separatingRaw_generator hrel)
    (fun _ => rfl)
    (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂) h

theorem separatingRaw_continuous : Continuous separatingRaw := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · change Continuous (fun p : ℝ × ℝ => Real.cos (2 * Real.pi * p.2))
    fun_prop
  · change Continuous (fun p : ℝ × ℝ =>
      Real.sin (2 * Real.pi * p.2) * Real.cos (Real.pi * p.1))
    fun_prop

/-- The separating coordinates descended to the concrete Klein-bottle
quotient. -/
def separatingMap : C(t95J02KleinBottleType, EuclideanSpace ℝ (Fin 2)) where
  toFun := Quotient.lift separatingRaw (fun _ _ h => separatingRaw_eqvGen h)
  continuous_toFun := separatingRaw_continuous.quotient_lift _

@[simp] theorem separatingMap_quotientPoint (p : ℝ × ℝ) :
    separatingMap (t95J02QuotientPoint p) = separatingRaw p := rfl

/-- The real-line parametrization of the vertical core circle. -/
def verticalParam : C(ℝ, t95J02CircleB) where
  toFun y := ⟨t95J02QuotientPoint (0, y), ⟨y, rfl⟩⟩
  continuous_toFun := by
    exact (continuous_coinduced_rng.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _

@[simp] theorem verticalParam_apply (y : ℝ) :
    (verticalParam y).1 = t95J02QuotientPoint (0, y) := rfl

theorem verticalParam_add_nat (y : ℝ) (n : ℕ) :
    verticalParam (y + (n : ℝ)) = verticalParam y := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        verticalParam (y + ((n + 1 : ℕ) : ℝ)) =
            verticalParam ((y + (n : ℝ)) + 1) := by
          apply congrArg verticalParam
          push_cast
          ring
        _ = verticalParam (y + (n : ℝ)) := by
          apply Subtype.ext
          exact (t95J02QuotientPoint_vertical 0 (y + (n : ℝ))).symm
        _ = verticalParam y := ih

theorem verticalParam_add_int (y : ℝ) (n : ℤ) :
    verticalParam (y + (n : ℝ)) = verticalParam y := by
  cases n with
  | ofNat n => simpa using verticalParam_add_nat y n
  | negSucc n =>
      have h := verticalParam_add_nat (y - (n + 1 : ℕ)) (n + 1)
      rw [Int.cast_negSucc]
      have hleft : y + -((n + 1 : ℕ) : ℝ) = y - (n + 1 : ℕ) := by ring
      rw [hleft]
      calc
        verticalParam (y - (n + 1 : ℕ)) =
            verticalParam (y - (n + 1 : ℕ) + (n + 1 : ℕ)) := h.symm
        _ = verticalParam y := by
          congr 1
          push_cast
          ring

theorem verticalParam_eq_iff (y y' : ℝ) :
    verticalParam y = verticalParam y' ↔ ∃ n : ℤ, y' = y + n := by
  constructor
  · intro h
    have hq : t95J02QuotientPoint (0, y) = t95J02QuotientPoint (0, y') := by
      exact congrArg Subtype.val h
    have hs : separatingRaw (0, y) = separatingRaw (0, y') := by
      have := congrArg separatingMap hq
      simpa using this
    have hcos : Real.cos (2 * Real.pi * y) = Real.cos (2 * Real.pi * y') := by
      have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hs
      simpa [separatingRaw] using h0
    have hsin : Real.sin (2 * Real.pi * y) = Real.sin (2 * Real.pi * y') := by
      have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hs
      simpa [separatingRaw] using h1
    have hexp : Circle.exp (2 * Real.pi * y') = Circle.exp (2 * Real.pi * y) := by
      apply Subtype.ext
      simp only [Circle.coe_exp, Complex.exp_mul_I]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpi
    calc
      (2 * Real.pi) * y' = 2 * Real.pi * y' := rfl
      _ = 2 * Real.pi * y + (n : ℝ) * (2 * Real.pi) := hn
      _ = (2 * Real.pi) * (y + (n : ℝ)) := by ring
  · rintro ⟨n, rfl⟩
    exact (verticalParam_add_int y n).symm

theorem verticalParam_periodic : Function.Periodic verticalParam 1 := by
  intro y
  simpa using verticalParam_add_int y 1

/-- The vertical parametrization descended to the period-one additive circle. -/
def verticalAddCircle : C(AddCircle (1 : ℝ), t95J02CircleB) where
  toFun := verticalParam_periodic.lift
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact verticalParam.continuous

@[simp] theorem verticalAddCircle_coe (y : ℝ) :
    verticalAddCircle (y : AddCircle (1 : ℝ)) = verticalParam y := rfl

theorem verticalAddCircle_surjective : Function.Surjective verticalAddCircle := by
  rintro ⟨z, y, rfl⟩
  exact ⟨(y : AddCircle (1 : ℝ)), rfl⟩

theorem verticalAddCircle_injective : Function.Injective verticalAddCircle := by
  intro a b h
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  rw [verticalAddCircle_coe, verticalAddCircle_coe] at h
  obtain ⟨n, hn⟩ := (verticalParam_eq_iff _ _).mp h
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  refine ⟨n, ?_⟩
  simp [hn]

theorem verticalAddCircle_bijective : Function.Bijective verticalAddCircle :=
  ⟨verticalAddCircle_injective, verticalAddCircle_surjective⟩

/-- The separating coordinate restricted to the vertical core. -/
def circleBSeparating : C(t95J02CircleB, EuclideanSpace ℝ (Fin 2)) :=
  separatingMap.comp ⟨Subtype.val, continuous_subtype_val⟩

theorem circleBSeparating_injective : Function.Injective circleBSeparating := by
  rintro ⟨z, y, rfl⟩ ⟨z', y', rfl⟩ h
  apply Subtype.ext
  apply congrArg Subtype.val
  apply (verticalParam_eq_iff y y').mpr
  have hs : separatingRaw (0, y) = separatingRaw (0, y') := by
    simpa [circleBSeparating] using h
  have hcos : Real.cos (2 * Real.pi * y) = Real.cos (2 * Real.pi * y') := by
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hs
    simpa [separatingRaw] using h0
  have hsin : Real.sin (2 * Real.pi * y) = Real.sin (2 * Real.pi * y') := by
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hs
    simpa [separatingRaw] using h1
  have hexp : Circle.exp (2 * Real.pi * y') = Circle.exp (2 * Real.pi * y) := by
    apply Subtype.ext
    simp only [Circle.coe_exp, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpi
  calc
    (2 * Real.pi) * y' = 2 * Real.pi * y' := rfl
    _ = 2 * Real.pi * y + (n : ℝ) * (2 * Real.pi) := hn
    _ = (2 * Real.pi) * (y + (n : ℝ)) := by ring

noncomputable instance circleB_t2 : T2Space t95J02CircleB :=
  T2Space.of_injective_continuous circleBSeparating_injective
    circleBSeparating.continuous

noncomputable def verticalAddCircleHomeomorph :
    AddCircle (1 : ℝ) ≃ₜ t95J02CircleB :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective verticalAddCircle verticalAddCircle_bijective)
    verticalAddCircle.continuous

/-- The frozen vertical core, in the Euclidean circle presentation used by
the homology calculation. -/
noncomputable def t95J02CircleB_homeo :
    T02A06.euclideanUnitSphere 2 ≃ₜ t95J02CircleB :=
  ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.symm.trans
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
      verticalAddCircleHomeomorph)

noncomputable def sphereToAddCircle :
    T02A06.euclideanUnitSphere 2 ≃ₜ AddCircle (1 : ℝ) :=
  ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.symm.trans
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

noncomputable def sphereToAddCircleMap :
    C(T02A06.euclideanUnitSphere 2, AddCircle (1 : ℝ)) :=
  ⟨sphereToAddCircle, sphereToAddCircle.continuous⟩

theorem sphereToAddCircle_reflection (x : T02A06.euclideanUnitSphere 2) :
    sphereToAddCircle
        (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
          (1 : Fin 2) x) =
      -sphereToAddCircle x := by
  apply (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).injective
  simp only [sphereToAddCircle, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply]
  rw [AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_neg,
    ← AddCircle.homeomorphCircle_apply one_ne_zero,
    Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rw [Circle.coe_inv_eq_conj]
  simp [
    ConstructionTargets.CircleHomology.circleHomeomorphSphereOne,
    ConstructionTargets.CoefficientCoordinateReflections.reflectionMap,
    ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo,
    ConstructionTargets.CoefficientCoordinateReflections.reflection_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]

/-- The raw glide sweep before descending the vertical coordinate modulo one. -/
def verticalSweepRaw (p : I × ℝ) : t95J02KleinBottleType :=
  t95J02QuotientPoint ((p.1 : ℝ), p.2)

theorem verticalSweepRaw_continuous : Continuous verticalSweepRaw := by
  exact continuous_coinduced_rng.comp
    ((continuous_subtype_val.comp (continuous_fst : Continuous (Prod.fst : I × ℝ → I))).prodMk
      (continuous_snd : Continuous (Prod.snd : I × ℝ → ℝ)))

theorem verticalSweepRaw_periodic (t : I) :
    Function.Periodic (fun y : ℝ => verticalSweepRaw (t, y)) 1 := by
  intro y
  exact (t95J02QuotientPoint_vertical (t : ℝ) y).symm

/-- The glide sweep on the period-one additive circle. -/
def verticalSweep (p : I × AddCircle (1 : ℝ)) : t95J02KleinBottleType :=
  (verticalSweepRaw_periodic p.1).lift p.2

theorem verticalSweep_continuous : Continuous verticalSweep := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  simpa [verticalSweep] using verticalSweepRaw_continuous

@[simp] theorem verticalSweep_coe (t : I) (y : ℝ) :
    verticalSweep (t, (y : AddCircle (1 : ℝ))) =
      t95J02QuotientPoint ((t : ℝ), y) := rfl

theorem verticalSweep_zero (a : AddCircle (1 : ℝ)) :
    verticalSweep (0, a) = t95J02InclusionB (verticalAddCircle a) := by
  induction a using QuotientAddGroup.induction_on
  simp only [verticalSweep_coe]
  change t95J02QuotientPoint (0, _) = (verticalAddCircle _).1
  rw [verticalAddCircle_coe]
  rfl

theorem verticalSweep_one (a : AddCircle (1 : ℝ)) :
    verticalSweep (1, a) = t95J02InclusionB (verticalAddCircle (-a)) := by
  induction a using QuotientAddGroup.induction_on
  simp only [verticalSweep_coe]
  change t95J02QuotientPoint (1, _) = t95J02QuotientPoint (0, _)
  simpa using (t95J02QuotientPoint_glide 0 (-_)).symm

def verticalCoreMap : C(AddCircle (1 : ℝ), t95J02KleinBottleType) :=
  ⟨fun a => t95J02InclusionB (verticalAddCircle a),
    t95J02InclusionB.hom.continuous.comp verticalAddCircle.continuous⟩

def addCircleNeg : C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)) :=
  ⟨fun a => -a, continuous_neg⟩

/-- The quotient-level glide homotopy before transporting its source from
`AddCircle 1` to the Euclidean unit circle. -/
def verticalSweepHomotopy : ContinuousMap.Homotopy verticalCoreMap
    (verticalCoreMap.comp addCircleNeg) where
  toContinuousMap := ⟨verticalSweep, verticalSweep_continuous⟩
  map_zero_left := by simpa [verticalCoreMap] using verticalSweep_zero
  map_one_left := by simpa [verticalCoreMap, addCircleNeg] using verticalSweep_one

noncomputable def beta :
    C(T02A06.euclideanUnitSphere 2, t95J02KleinBottleType) :=
  ⟨fun x => t95J02InclusionB (t95J02CircleB_homeo x),
    t95J02InclusionB.hom.continuous.comp t95J02CircleB_homeo.continuous⟩

theorem beta_eq_verticalCoreMap :
    beta = verticalCoreMap.comp sphereToAddCircleMap := by
  ext x
  rfl

theorem beta_reflection_eq :
    beta.comp
        (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
          (1 : Fin 2)) =
      (verticalCoreMap.comp addCircleNeg).comp sphereToAddCircleMap := by
  ext x
  change t95J02InclusionB (verticalAddCircle (sphereToAddCircle _)) =
    t95J02InclusionB (verticalAddCircle (-sphereToAddCircle x))
  rw [sphereToAddCircle_reflection]

theorem t95J02_beta_homotopic_beta_reflection :
    ContinuousMap.Homotopic beta
      (beta.comp
        (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
          (1 : Fin 2))) := by
  rw [beta_eq_verticalCoreMap]
  have href := beta_reflection_eq
  rw [beta_eq_verticalCoreMap] at href
  rw [href]
  exact ⟨verticalSweepHomotopy.compContinuousMap sphereToAddCircleMap⟩

end t95J02Closure

/-- Integral first singular homology, used only to state the missing invariant
without assuming a presentation for the quotient's fundamental group. -/
abbrev apm_t95J02_H1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t95J02_H1Map {X Y : TopCat} (f : X ⟶ Y) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map f

/-- Why this unblocks `apm_t95j02`: this is the missing concrete invariant
calculation. It identifies a nonzero integral first-homology class of the
vertical core whose image in the Klein bottle vanishes (the class twice a
circle generator, since the vertical class has order two after abelianizing). -/
theorem apm_t95J02_bridge_vertical_H1_kernel :
    ∃ gamma : apm_t95J02_H1 t95J02CircleB,
      gamma ≠ 0 ∧
      apm_t95J02_H1Map t95J02InclusionB gamma = 0 := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  let e := ConstructionTargets.CoefficientFirstReflection.topIso ℤ 0
  let g := e.inv.hom (1 : ℤ)
  let c : C(T02A06.euclideanUnitSphere 2, t95J02CircleB) :=
    ⟨t95J02Closure.t95J02CircleB_homeo,
      t95J02Closure.t95J02CircleB_homeo.continuous⟩
  let cInv : C(t95J02CircleB, T02A06.euclideanUnitSphere 2) :=
    ⟨t95J02Closure.t95J02CircleB_homeo.symm,
      t95J02Closure.t95J02CircleB_homeo.symm.continuous⟩
  let h := F.map (TopCat.ofHom c)
  refine ⟨h.hom (2 • g), ?_, ?_⟩
  · intro hzero
    have hleft :
        F.map (TopCat.ofHom c) ≫ F.map (TopCat.ofHom cInv) =
          𝟙 _ := by
      have hc : TopCat.ofHom c ≫ TopCat.ofHom cInv =
          𝟙 (TopCat.of (T02A06.euclideanUnitSphere 2)) := by
        ext x
        simp [c, cInv]
      rw [← F.map_comp, hc, F.map_id]
    have hz := congrArg
      (fun z ↦ (F.map
        (TopCat.ofHom cInv)).hom z)
      hzero
    have hg : 2 • g ≠ 0 := by
      intro hgzero
      have := congrArg e.hom.hom hgzero
      simp [g] at this
    apply hg
    have hpoint := congrArg
      (fun q : (F.obj (TopCat.of (T02A06.euclideanUnitSphere 2)) ⟶
          F.obj (TopCat.of (T02A06.euclideanUnitSphere 2))) ↦ q.hom (2 • g)) hleft
    have hz' :
        (F.map (TopCat.ofHom cInv)).hom (h.hom (2 • g)) = 0 := by
      simpa using hz
    simpa [h, CategoryTheory.comp_apply] using hpoint.symm.trans hz'
  · have hhom :=
      ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
        (ModuleCat ℤ) (ModuleCat.of ℤ ℤ)
        t95J02Closure.t95J02_beta_homotopic_beta_reflection 1
    have href := ConstructionTargets.CoefficientFirstReflection.integral_circle
      (1 : Fin 2)
    have hbeta :
        (F.map (TopCat.ofHom t95J02Closure.beta)).hom g =
          (F.map (TopCat.ofHom t95J02Closure.beta)).hom (-g) := by
      have hcomp :
          F.map (TopCat.ofHom (t95J02Closure.beta.comp
              (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
                (1 : Fin 2)))) =
            F.map (TopCat.ofHom
              (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
                (1 : Fin 2))) ≫ F.map (TopCat.ofHom t95J02Closure.beta) := by
        rw [← F.map_comp]
        rfl
      calc
        _ = (F.map (TopCat.ofHom (t95J02Closure.beta.comp
              (ConstructionTargets.CoefficientCoordinateReflections.reflectionMap
                (1 : Fin 2))))).hom g := congrArg (fun q ↦ q.hom g) hhom
        _ = _ := by
          rw [hcomp, href]
          change (F.map (TopCat.ofHom t95J02Closure.beta)).hom (-g) =
            (F.map (TopCat.ofHom t95J02Closure.beta)).hom (-g)
          rfl
    have htwo : (F.map (TopCat.ofHom t95J02Closure.beta)).hom (2 • g) = 0 := by
      have := congrArg
        (fun z ↦ z + (F.map (TopCat.ofHom t95J02Closure.beta)).hom g) hbeta
      simpa [two_smul] using this
    change (F.map t95J02InclusionB).hom (h.hom (2 • g)) = 0
    have hfactor :
        F.map (TopCat.ofHom c) ≫
            F.map t95J02InclusionB =
          F.map (TopCat.ofHom t95J02Closure.beta) := by
      rw [← F.map_comp]
      congr 1
    have hpoint := congrArg
      (fun q : F.obj (TopCat.of (T02A06.euclideanUnitSphere 2)) ⟶
          F.obj (TopCat.of t95J02KleinBottleType) ↦ q.hom (2 • g)) hfactor
    simpa [h, CategoryTheory.comp_apply] using hpoint.trans htwo

/-- Why this unblocks `apm_t95j02`: functoriality makes the first-homology map
of any retract inclusion injective. Combined with
`apm_t95J02_bridge_vertical_H1_kernel`, this rules out a retraction onto the
vertical core without requiring any further quotient computation. -/
theorem apm_t95J02_bridge_retraction_injective
    (hret : HasT95J02Retraction t95J02InclusionB) :
    Function.Injective
      (apm_t95J02_H1Map t95J02InclusionB) := by
  rcases hret with ⟨r, hr⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hcomp :
      apm_t95J02_H1Map t95J02InclusionB ≫ apm_t95J02_H1Map r =
        𝟙 (apm_t95J02_H1 t95J02CircleB) := by
    change F.map t95J02InclusionB ≫ F.map r = 𝟙 _
    rw [← F.map_comp, hr]
    exact F.map_id _
  intro x y hxy
  have hxy' := congrArg (fun z ↦ apm_t95J02_H1Map r z) hxy
  have hx := congrArg
    (fun q : apm_t95J02_H1 t95J02CircleB ⟶
        apm_t95J02_H1 t95J02CircleB ↦ q x) hcomp
  have hy := congrArg
    (fun q : apm_t95J02_H1 t95J02CircleB ⟶
        apm_t95J02_H1 t95J02CircleB ↦ q y) hcomp
  simpa only [CategoryTheory.comp_apply, CategoryTheory.id_apply] using
    hx.symm.trans (hxy'.trans hy)

theorem apm_t95j02 :
    HasT95J02Retraction t95J02InclusionA ∧
    ¬HasT95J02Retraction t95J02InclusionB := by
  constructor
  · exact ⟨t95J02RetractionA, t95J02RetractionA_comp_inclusion⟩
  · intro hret
    obtain ⟨gamma, hgamma, hzero⟩ := apm_t95J02_bridge_vertical_H1_kernel
    apply hgamma
    apply apm_t95J02_bridge_retraction_injective hret
    simpa using hzero
