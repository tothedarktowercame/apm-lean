import Mathlib

/-!
# APM t00J03

## Statement repairs

The final occurrence of `ℝ²` in the source is read as `ℝ² \ {0}`, the domain
of the quotient map and of the displayed angle form. At the origin its
denominator vanishes, so the unrepaired wording is not meaningful.

The former conclusion used opaque one-form, pullback, and integral constants.
They are replaced by a concrete quotient of tangent representatives and
ordinary interval integrals along the two orientations of an explicit
half-circle parametrization of the actual real projective line.
-/

open Set
open scoped Interval
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t00j03_Plane := Fin 2 → ℝ
abbrev apm_t00j03_PuncturedPlane := {x : apm_t00j03_Plane // x ≠ 0}
abbrev apm_t00j03_RP1 := Projectivization ℝ apm_t00j03_Plane

noncomputable instance : TopologicalSpace apm_t00j03_RP1 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ apm_t00j03_Plane)))

def apm_t00j03_projectivize (x : apm_t00j03_PuncturedPlane) : apm_t00j03_RP1 :=
  Projectivization.mk' ℝ x

/-- Changing a projective tangent representative permits rescaling both
components and adding a radial vector to the tangent component. -/
inductive apm_t00j03_tangentRel :
    (apm_t00j03_PuncturedPlane × apm_t00j03_Plane) →
      (apm_t00j03_PuncturedPlane × apm_t00j03_Plane) → Prop
  | change (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane)
      (lam a : ℝ) (hlam : lam ≠ 0) :
      apm_t00j03_tangentRel (x, v)
        (⟨lam • x.1, smul_ne_zero hlam x.2⟩, lam • v + a • x.1)

def apm_t00j03_ProjectiveTangent :=
  Quotient (Relation.EqvGen.setoid apm_t00j03_tangentRel)

/-- The angle form `(x⁰ dx¹ - x¹ dx⁰) / ((x⁰)² + (x¹)²)`. -/
def apm_t00j03_angleFormValue
    (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane) : ℝ :=
  (x.1 0 * v 1 - x.1 1 * v 0) / (x.1 0 ^ 2 + x.1 1 ^ 2)

def apm_t00j03_circlePoint (θ : ℝ) : apm_t00j03_PuncturedPlane :=
  ⟨![Real.cos θ, Real.sin θ], by
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    nlinarith [Real.sin_sq_add_cos_sq θ]⟩

def apm_t00j03_circleVelocity (θ : ℝ) : apm_t00j03_Plane :=
  ![-Real.sin θ, Real.cos θ]

def apm_t00j03_tangentClass (θ : ℝ) : apm_t00j03_ProjectiveTangent :=
  Quotient.mk _ (apm_t00j03_circlePoint θ, apm_t00j03_circleVelocity θ)

lemma apm_t00j03_projectivize_surjective :
    Function.Surjective apm_t00j03_projectivize := by
  intro p
  refine ⟨⟨p.rep, p.rep_nonzero⟩, ?_⟩
  exact p.mk_rep

/-- The angle form evaluates to one on the unit half-circle and its velocity. -/
lemma apm_t00j03_angleFormValue_circle (θ : ℝ) :
    apm_t00j03_angleFormValue (apm_t00j03_circlePoint θ)
      (apm_t00j03_circleVelocity θ) = 1 := by
  simp [apm_t00j03_angleFormValue, apm_t00j03_circlePoint,
    apm_t00j03_circleVelocity]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma apm_t00j03_integral_angleFormValue_circle :
    (∫ θ in (0 : ℝ)..Real.pi,
      apm_t00j03_angleFormValue (apm_t00j03_circlePoint θ)
        (apm_t00j03_circleVelocity θ)) = Real.pi := by
  simp [apm_t00j03_angleFormValue_circle]

lemma apm_t00j03_integral_angleFormValue_circle_reverse :
    (∫ θ in Real.pi..(0 : ℝ),
      apm_t00j03_angleFormValue (apm_t00j03_circlePoint θ)
        (apm_t00j03_circleVelocity θ)) = -Real.pi := by
  simp [apm_t00j03_angleFormValue_circle]

/-- The angle form is unchanged by each generating change of projective
tangent representative. -/
lemma apm_t00j03_angleFormValue_change
    (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane)
    (lam a : ℝ) (hlam : lam ≠ 0) :
    apm_t00j03_angleFormValue
      ⟨lam • x.1, smul_ne_zero hlam x.2⟩ (lam • v + a • x.1) =
      apm_t00j03_angleFormValue x v := by
  have hden : x.1 0 ^ 2 + x.1 1 ^ 2 ≠ 0 := by
    intro h
    have hx0 : x.1 0 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    have hx1 : x.1 1 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    apply x.2
    funext i
    fin_cases i <;> simp [hx0, hx1]
  simp only [apm_t00j03_angleFormValue, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply]
  field_simp
  ring

/-- Superseded because its interval integral did not state that the half-circle
projects to the loop in `RP¹` over which the descended form is integrated. -/
theorem apm_t00j03_previous_encoding :
    Function.Surjective apm_t00j03_projectivize ∧
    ∃ eta : apm_t00j03_ProjectiveTangent → ℝ,
      (∀ (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane),
        eta (Quotient.mk _ (x, v)) = apm_t00j03_angleFormValue x v) ∧
      (∫ θ in (0 : ℝ)..Real.pi, eta (apm_t00j03_tangentClass θ)) = Real.pi ∧
      (∫ θ in Real.pi..(0 : ℝ), eta (apm_t00j03_tangentClass θ)) = -Real.pi := by
  -- Desk research: `Projectivization.mk_rep` supplies surjectivity, while
  -- `Relation.EqvGen.rec` (the same recursor used by `Quot.eqvGen_sound` in
  -- Mathlib) transports generator invariance through the quotient relation.
  refine ⟨apm_t00j03_projectivize_surjective, ?_⟩
  let F : apm_t00j03_PuncturedPlane × apm_t00j03_Plane → ℝ :=
    fun p ↦ apm_t00j03_angleFormValue p.1 p.2
  have hinv : ∀ p q,
      Relation.EqvGen apm_t00j03_tangentRel p q → F p = F q := by
    intro p q h
    exact Relation.EqvGen.rec
      (fun _ _ hrel ↦ by
        rcases hrel with ⟨x, v, lam, a, hlam⟩
        exact (apm_t00j03_angleFormValue_change x v lam a hlam).symm)
      (fun _ ↦ rfl)
      (fun _ _ _ ih ↦ ih.symm)
      (fun _ _ _ _ _ ih₁ ih₂ ↦ ih₁.trans ih₂) h
  let eta : apm_t00j03_ProjectiveTangent → ℝ :=
    Quotient.lift F (fun p q h ↦ hinv p q h)
  refine ⟨eta, ?_, ?_, ?_⟩
  · intro x v
    rfl
  · simpa [eta, apm_t00j03_tangentClass, F] using
      apm_t00j03_integral_angleFormValue_circle
  · simpa [eta, apm_t00j03_tangentClass, F] using
      apm_t00j03_integral_angleFormValue_circle_reverse

/-- The standard positively oriented loop in `RP¹`, obtained by projecting a
half-circle; its endpoints agree because antipodal vectors define one line. -/
def apm_t00j03_projectiveLoop (θ : ℝ) : apm_t00j03_RP1 :=
  apm_t00j03_projectivize (apm_t00j03_circlePoint θ)

/-- Integration of a descended one-form along the standard projective loop. -/
def apm_t00j03_projectiveLoopIntegral
    (eta : apm_t00j03_ProjectiveTangent → ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, eta (apm_t00j03_tangentClass θ)

/-- Continuity of the projected half-circle, stated separately from its
fundamental-domain properties so the two topology tasks are independent. -/
theorem apm_t00j03_projectiveLoop_continuous :
    Continuous apm_t00j03_projectiveLoop := by
  unfold apm_t00j03_projectiveLoop apm_t00j03_projectivize
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin

/-- The half-open half-circle is a set of unique representatives for `RP¹`,
and its two missing/added endpoints project to the same line. -/
lemma apm_t00j03_projectiveLoop_fundamentalDomain_aux_endpoints :
    apm_t00j03_projectiveLoop 0 = apm_t00j03_projectiveLoop Real.pi := by
  unfold apm_t00j03_projectiveLoop apm_t00j03_projectivize
  change Projectivization.mk ℝ (apm_t00j03_circlePoint 0).1 _ =
    Projectivization.mk ℝ (apm_t00j03_circlePoint Real.pi).1 _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨(-1 : ℝ), ?_⟩
  ext i
  fin_cases i <;> simp [apm_t00j03_circlePoint]

lemma apm_t00j03_projectiveLoop_fundamentalDomain_aux_injective :
    Set.InjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) := by
  intro θ hθ φ hφ heq
  unfold apm_t00j03_projectiveLoop apm_t00j03_projectivize at heq
  change Projectivization.mk ℝ (apm_t00j03_circlePoint θ).1 _ =
    Projectivization.mk ℝ (apm_t00j03_circlePoint φ).1 _ at heq
  rw [Projectivization.mk_eq_mk_iff'] at heq
  obtain ⟨a, ha⟩ := heq
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [apm_t00j03_circlePoint] at h0 h1
  have hs : Real.sin (θ - φ) = 0 := by
    rw [Real.sin_sub]
    rw [← h1, ← h0]
    ring
  have hdlo : -Real.pi < θ - φ := by linarith [hθ.1, hφ.2]
  have hdhi : θ - φ < Real.pi := by linarith [hθ.2, hφ.1]
  exact sub_eq_zero.mp ((Real.sin_eq_zero_iff_of_lt_of_lt hdlo hdhi).mp hs)

-- BEGIN SEAT AREA
lemma apm_t00j03_projectiveLoop_fundamentalDomain_aux_surjective :
    Set.SurjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) Set.univ := by
  intro p hp
  let z : ℂ := ⟨p.rep 0, p.rep 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply p.rep_nonzero
    funext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : Real.cos z.arg = p.rep 0 / ‖z‖ := by
    simpa [z] using Complex.cos_arg hz
  have hs : Real.sin z.arg = p.rep 1 / ‖z‖ := by
    simpa [z] using Complex.sin_arg z
  by_cases hneg : z.arg < 0
  · refine ⟨z.arg + Real.pi, ⟨by linarith [Complex.neg_pi_lt_arg z], ?_⟩, ?_⟩
    · linarith [Real.pi_pos]
    · unfold apm_t00j03_projectiveLoop apm_t00j03_projectivize
      rw [← p.mk_rep]
      change Projectivization.mk ℝ (apm_t00j03_circlePoint (z.arg + Real.pi)).1 _ =
        Projectivization.mk ℝ p.rep _
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨-(‖z‖⁻¹), ?_⟩
      ext i
      fin_cases i
      · simp [apm_t00j03_circlePoint, Real.cos_add_pi]
        rw [hc]
        field_simp [hn]
      · simp [apm_t00j03_circlePoint, Real.sin_add_pi]
        rw [hs]
        field_simp [hn]
  · by_cases hpi : z.arg = Real.pi
    · refine ⟨0, ⟨le_rfl, Real.pi_pos⟩, ?_⟩
      unfold apm_t00j03_projectiveLoop apm_t00j03_projectivize
      rw [← p.mk_rep]
      change Projectivization.mk ℝ (apm_t00j03_circlePoint 0).1 _ =
        Projectivization.mk ℝ p.rep _
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨-(‖z‖⁻¹), ?_⟩
      ext i
      fin_cases i
      · simp [apm_t00j03_circlePoint]
        have hc' := hc
        rw [hpi] at hc'
        simp at hc'
        field_simp [hn] at hc' ⊢
        linarith
      · simp [apm_t00j03_circlePoint]
        have hs' := hs
        rw [hpi] at hs'
        simp at hs'
        have hv1 : p.rep 1 = 0 := by
          exact ((div_eq_zero_iff.mp hs'.symm).resolve_right hn)
        simp [hv1]
    · refine ⟨z.arg, ⟨le_of_not_gt hneg, lt_of_le_of_ne (Complex.arg_le_pi z) hpi⟩, ?_⟩
      unfold apm_t00j03_projectiveLoop apm_t00j03_projectivize
      rw [← p.mk_rep]
      change Projectivization.mk ℝ (apm_t00j03_circlePoint z.arg).1 _ =
        Projectivization.mk ℝ p.rep _
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨‖z‖⁻¹, ?_⟩
      ext i
      fin_cases i
      · simp [apm_t00j03_circlePoint]
        rw [hc]
        field_simp [hn]
      · simp [apm_t00j03_circlePoint]
        rw [hs]
        field_simp [hn]
-- END SEAT AREA

theorem apm_t00j03_projectiveLoop_fundamentalDomain :
    Set.SurjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) Set.univ ∧
    Set.InjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) ∧
    apm_t00j03_projectiveLoop 0 = apm_t00j03_projectiveLoop Real.pi := by
  exact ⟨apm_t00j03_projectiveLoop_fundamentalDomain_aux_surjective,
    apm_t00j03_projectiveLoop_fundamentalDomain_aux_injective,
    apm_t00j03_projectiveLoop_fundamentalDomain_aux_endpoints⟩

/-- The displayed angle form descends to `RP¹`; with the orientation induced
by the projected half-circle its integral is `π`, and reversing orientation
changes the sign. -/
theorem apm_t00j03 :
    Continuous apm_t00j03_projectiveLoop ∧
    Set.SurjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) Set.univ ∧
    Set.InjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) ∧
    apm_t00j03_projectiveLoop 0 = apm_t00j03_projectiveLoop Real.pi ∧
    ∃ eta : apm_t00j03_ProjectiveTangent → ℝ,
      (∀ (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane),
        eta (Quotient.mk _ (x, v)) = apm_t00j03_angleFormValue x v) ∧
      apm_t00j03_projectiveLoopIntegral eta = Real.pi ∧
      (∫ θ in Real.pi..(0 : ℝ), eta (apm_t00j03_tangentClass θ)) =
        -Real.pi := by
  rcases apm_t00j03_projectiveLoop_fundamentalDomain with
    ⟨hsurj, hinj, hend⟩
  rcases apm_t00j03_previous_encoding with ⟨_, eta, heta, hpos, hneg⟩
  exact ⟨apm_t00j03_projectiveLoop_continuous, hsurj, hinj, hend,
    eta, heta, hpos, hneg⟩

#print axioms apm_t00j03
