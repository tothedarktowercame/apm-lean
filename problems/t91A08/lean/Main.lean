import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Covering.AddCircle
import ConstructionTargets.PeriodicCircleHomotopyWinding
import ConstructionTargets.CircleExponentialPathLift

/-!
# APM t91A08 — a two-form on the torus

The torus is the genuine quotient `(ℝ/ℤ)²`, equipped with its normalized Haar
measure.  Forms are continuous fields of alternating continuous multilinear
maps on the standard tangent model.  Descent is expressed along the quotient
map, pullback uses the actual derivative matrix, and integration is a Haar
integral over the torus.

## Statement repairs

None.

## Encoding questions

The tangent bundle of the quotient Lie group is represented in its canonical
translation trivialization by `ℝ²`; this is why every fiber below has the same
model vector space.

The alternating-form and Haar-integral encoding follows `t01J06`.
-/

open MeasureTheory
open scoped LinearAlgebra

noncomputable section

abbrev T91A08Torus := UnitAddCircle × UnitAddCircle
abbrev T91A08R2 := EuclideanSpace ℝ (Fin 2)
abbrev T91A08Alt2 := T91A08R2 [⋀^Fin 2]→L[ℝ] ℝ
abbrev T91A08Form2 := C(T91A08Torus, T91A08Alt2)

/-- The quotient covering `ℝ² → (ℝ/ℤ)²`. -/
def t91A08Cover (x : T91A08R2) : T91A08Torus :=
  (x 0, x 1)

/-- Pointwise descent of `3 dx ∧ dy` along the quotient covering. -/
def t91A08IsInduced (beta : T91A08Form2) : Prop :=
  ∀ (x : T91A08R2) (v : Fin 2 → T91A08R2),
    beta (t91A08Cover x) v =
      3 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def t91A08Linear (u : T91A08R2) : T91A08R2 :=
  WithLp.toLp 2 ![5 * u 0 + 2 * u 1, 4 * u 0 + 3 * u 1]

/-- The torus map induced by the integer matrix `[[5,2],[4,3]]`. -/
def t91A08g : C(T91A08Torus, T91A08Torus) :=
  ⟨fun p ↦ (5 • p.1 + 2 • p.2, 4 • p.1 + 3 • p.2), by fun_prop⟩

/-- `gamma` is the pullback of `beta` by `g`, in translation-trivialized
tangent coordinates. -/
def t91A08IsPullback (gamma beta : T91A08Form2) : Prop :=
  ∀ (p : T91A08Torus) (v : Fin 2 → T91A08R2),
    gamma p v = beta (t91A08g p) (fun i ↦ t91A08Linear (v i))

/-- Integral of a top-degree form against normalized Haar measure, using the
standard oriented translation-invariant frame. -/
def t91A08Integral (beta : T91A08Form2) : ℝ :=
  ∫ p : T91A08Torus,
    beta p ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]

lemma t91A08Cover_surjective : Function.Surjective t91A08Cover := by
  rintro ⟨p, q⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) p
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) q
  refine ⟨WithLp.toLp 2 ![x, y], ?_⟩
  ext <;> simp [t91A08Cover]

lemma t91A08Integral_induced (beta : T91A08Form2)
    (hbeta : t91A08IsInduced beta) : t91A08Integral beta = 3 := by
  have hconst (p : T91A08Torus) :
      beta p ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1] = 3 := by
    obtain ⟨x, rfl⟩ := t91A08Cover_surjective p
    simpa [EuclideanSpace.single_apply] using
      hbeta x ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]
  simp_rw [t91A08Integral, hconst]
  rw [integral_const]
  norm_num [Measure.real, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod,
    AddCircle.measure_univ]

lemma t91A08Integral_pullback (beta gamma : T91A08Form2)
    (hbeta : t91A08IsInduced beta)
    (hgamma : t91A08IsPullback gamma beta) : t91A08Integral gamma = 21 := by
  have hconst (p : T91A08Torus) :
      gamma p ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1] = 21 := by
    rw [hgamma p]
    obtain ⟨x, hx⟩ := t91A08Cover_surjective (t91A08g p)
    rw [← hx]
    rw [hbeta x]
    norm_num [t91A08Linear, EuclideanSpace.single_apply]
  simp_rw [t91A08Integral, hconst]
  rw [integral_const]
  norm_num [Measure.real, Measure.volume_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod,
    AddCircle.measure_univ]

def t91A08FirstCircle : C(UnitAddCircle, T91A08Torus) :=
  ⟨fun z ↦ (z, 0), by fun_prop⟩

def t91A08FirstProjection : C(T91A08Torus, UnitAddCircle) :=
  ⟨Prod.fst, continuous_fst⟩

def t91A08TimesFive : C(UnitAddCircle, UnitAddCircle) :=
  ⟨fun z ↦ 5 • z, by fun_prop⟩

lemma t91A08_timesFive_homotopic_of_g_homotopic
    (h : ContinuousMap.Homotopic t91A08g (ContinuousMap.id T91A08Torus)) :
    ContinuousMap.Homotopic t91A08TimesFive
      (ContinuousMap.id UnitAddCircle) := by
  have hpost := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl t91A08FirstProjection) h
  have hpre := ContinuousMap.Homotopic.comp hpost
    (ContinuousMap.Homotopic.refl t91A08FirstCircle)
  convert hpre using 1 <;>
    ext z <;>
    simp [t91A08FirstProjection, t91A08FirstCircle, t91A08TimesFive, t91A08g]

/-- The degree-five circle map is the quotient covering by its five-torsion
kernel.  This records the exact covering structure implicated by the remaining
homotopy obstruction. -/
lemma t91A08_timesFive_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap (5 • · : UnitAddCircle → UnitAddCircle)
      (nsmulAddMonoidHom (α := UnitAddCircle) 5).ker := by
  exact AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 5

/-- The covering is genuinely nontrivial: the class of `1/5` is a nonzero
element killed by multiplication by five. -/
lemma t91A08_timesFive_not_injective :
    ¬Function.Injective (5 • · : UnitAddCircle → UnitAddCircle) := by
  let u : UnitAddCircle := ((1 / 5 : ℝ) : UnitAddCircle)
  have hu5 : 5 • u = 0 := by
    apply (AddCircle.nsmul_eq_zero_iff (p := (1 : ℝ)) (by norm_num : 0 < 5)).2
    refine ⟨1, by norm_num, ?_⟩
    simp [u]
  have hu0 : u ≠ 0 := by
    intro hu
    have hord : addOrderOf u = 5 := by
      simpa [u] using
        (AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℝ))
          (m := 1) (n := 5) (by norm_num) (by norm_num))
    rw [hu] at hord
    norm_num at hord
  intro hinj
  apply hu0
  apply hinj
  simpa using hu5

/-! ## Circle power-map prototype (banked declarations only) -/

open scoped unitInterval
open ConstructionTargets.PeriodicCircleHomotopyWinding
open ConstructionTargets.CircleWindingUniqueness

/-- The power map `z ↦ z ^ n` on the circle. -/
noncomputable def powMap (n : ℕ) : C(Circle, Circle) where
  toFun z := z ^ n
  continuous_toFun := by fun_prop

/-- The standard generator loop, as a map `I → Circle`. -/
noncomputable def genLoop : C(I, Circle) where
  toFun t := Circle.exp ((2 * Real.pi : ℝ) * t)
  continuous_toFun := by fun_prop

theorem exp_one_eq : Circle.exp (2 * Real.pi : ℝ) = 1 := by
  simp

theorem genLoop_zero : genLoop 0 = 1 := by simp [genLoop, Circle.exp_zero]

theorem genLoop_one : genLoop 1 = 1 := by simp [genLoop]

theorem exp_pow (a : ℝ) (k : ℕ) :
    (Circle.exp a) ^ k = Circle.exp (a * (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Circle.exp_add]
      congr 1
      push_cast
      ring

theorem exp_pow_slice (n : ℕ) (t : I) :
    (genLoop t) ^ n = Circle.exp ((n : ℝ) * (2 * Real.pi : ℝ) * t) := by
  show Circle.exp ((2 * Real.pi : ℝ) * (t : ℝ)) ^ n
      = Circle.exp ((n : ℝ) * (2 * Real.pi : ℝ) * (t : ℝ))
  rw [exp_pow]
  congr 1
  ring

/-- The explicit affine lift of the `n`-th power of the generator loop. -/
noncomputable def sliceLift (n : ℕ) (b : ℝ) : C(I, ℝ) where
  toFun t := b + (n : ℝ) * (2 * Real.pi : ℝ) * t
  continuous_toFun := by fun_prop

theorem sliceLift_zero (n : ℕ) (b : ℝ) : sliceLift n b 0 = b := by
  simp [sliceLift]

/-- If a slice of the lifted square projects to the `n`-th power of the
generator loop and starts at `b`, it is the explicit affine lift. -/
theorem slice_of_pow (K : C(I × I, Circle)) (h0 : K (0, 0) = Circle.exp 0)
    (n : ℕ) (s : I) (b : ℝ) (hs : ∀ t : I, K (t, s) = (genLoop t) ^ n)
    (hb : liftedSquare K 0 h0 (0, s) = b)
    (hbexp : Circle.exp b = 1) (t : I) :
    liftedSquare K 0 h0 (t, s) = b + (n : ℝ) * (2 * Real.pi : ℝ) * t := by
  set γ : C(I, Circle) := ⟨fun t => (genLoop t) ^ n, by fun_prop⟩ with hγ
  have hγ1 : γ 0 = 1 := by
    show (genLoop 0) ^ n = 1
    simp [genLoop, Circle.exp_zero]
  have hγ0 : γ 0 = Circle.exp b := by
    rw [hγ1, hbexp]
  have hΓeq : (⟨fun t => liftedSquare K 0 h0 (t, s), by
      exact (liftedSquare K 0 h0).continuous.comp
        (continuous_id.prodMk continuous_const)⟩ : C(I, ℝ))
      = Circle.isCoveringMap_exp.liftPath γ b hγ0 := by
    refine ((Circle.isCoveringMap_exp.eq_liftPath_iff' hγ0).mpr ⟨?_, hb⟩)
    funext t
    show Circle.exp (liftedSquare K 0 h0 (t, s)) = γ t
    rw [exp_liftedSquare K 0 h0, hs t]
    rfl
  have hLiftEq : sliceLift n b = Circle.isCoveringMap_exp.liftPath γ b hγ0 := by
    refine ((Circle.isCoveringMap_exp.eq_liftPath_iff' hγ0).mpr ⟨?_, sliceLift_zero n b⟩)
    funext t
    show Circle.exp (b + (n : ℝ) * (2 * Real.pi : ℝ) * t) = (genLoop t) ^ n
    rw [Circle.exp_add, hbexp, one_mul, exp_pow_slice n t]
  have := congrFun (congrArg DFunLike.coe (hΓeq.trans hLiftEq.symm)) t
  simpa [sliceLift] using this

/-- No free homotopy joins the fifth-power map to the identity on `Circle`. -/
theorem pow_five_not_homotopic_id :
    ¬ ContinuousMap.Homotopic (powMap 5) (ContinuousMap.id Circle) := by
  rintro ⟨H⟩
  set K : C(I × I, Circle) :=
    ⟨fun p => H (p.2, genLoop p.1), by
      apply H.continuous.comp
      apply Continuous.prodMk continuous_snd
      exact genLoop.continuous.comp continuous_fst⟩ with hK
  have hloop : ∀ s : I, K (1, s) = K (0, s) := by
    intro s
    show H (s, genLoop 1) = H (s, genLoop 0)
    rw [genLoop_one, genLoop_zero]
  have h0lift : K (0, 0) = Circle.exp 0 := by
    show H.toFun (0, genLoop 0) = Circle.exp 0
    have hz := H.map_zero_left (genLoop 0)
    rw [hz, genLoop_zero]
    simp [powMap, Circle.exp_zero]
  have hcorner : liftedSquare K 0 h0lift (0, 0) = 0 := by
    rw [liftedSquare_zero K 0 h0lift]
    exact Circle.isCoveringMap_exp.liftPath_zero _ _ _
  have hs0 : ∀ t : I, K (t, 0) = (genLoop t) ^ (5 : ℕ) := by
    intro t
    have hz : H.toFun (0, genLoop t) = (powMap 5) (genLoop t) :=
      H.map_zero_left _
    show H (0, genLoop t) = (genLoop t) ^ (5 : ℕ)
    simpa [powMap] using hz
  have hs1 : ∀ t : I, K (t, 1) = (genLoop t) ^ (1 : ℕ) := by
    intro t
    show H (1, genLoop t) = (genLoop t) ^ (1 : ℕ)
    simp
  have hm : IsEndpointWinding (liftedSquare K 0 h0lift (1, 0))
      (liftedSquare K 0 h0lift (0, 0)) 5 := by
    unfold IsEndpointWinding
    rw [slice_of_pow K h0lift 5 0 0 hs0 hcorner (by simp [Circle.exp_zero]) 1,
      hcorner]
    ring_nf
    norm_num
  set b1 : ℝ := liftedSquare K 0 h0lift (0, 1) with hb1
  have hb1exp : Circle.exp b1 = 1 := by
    rw [hb1, exp_liftedSquare K 0 h0lift, hs1 0]
    simp [genLoop]
  have hn : IsEndpointWinding (liftedSquare K 0 h0lift (1, 1))
      (liftedSquare K 0 h0lift (0, 1)) 1 := by
    unfold IsEndpointWinding
    rw [slice_of_pow K h0lift 1 1 b1 hs1 hb1 hb1exp 1, hb1]
    ring_nf
    norm_num
  have hcontr := uniqueEndpointWinding_agrees K 0 h0lift hloop hm hn
  norm_num at hcontr

/-! ## UnitAddCircle transport through `AddCircle.homeomorphCircle` (T = 1) -/

theorem apm_t91A08_bridge_1 :
    ¬ ContinuousMap.Homotopic t91A08TimesFive
      (ContinuousMap.id UnitAddCircle) := by
  intro h
  have hsymm : ∀ x : UnitAddCircle,
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm
          (AddCircle.toCircle x) = x := by
    intro x
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm_apply_apply x
  -- Forward conjugation: the fifth-power map on `Circle` is exactly
  -- `e ∘ t91A08TimesFive ∘ e.symm` for the canonical period-one
  -- homeomorphism `e := AddCircle.homeomorphCircle one_ne_zero`, since
  -- `AddCircle.toCircle_nsmul : toCircle (n • x) = toCircle x ^ n`.
  have hpow : (powMap (5 : ℕ) : C(Circle, Circle))
      = ((⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)),
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous⟩ : C(UnitAddCircle, Circle)).comp
        (t91A08TimesFive.comp (⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm,
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous⟩ : C(Circle, UnitAddCircle)))) := by
    ext z
    obtain ⟨x, hx⟩ : ∃ x : UnitAddCircle, z = AddCircle.toCircle x :=
      ⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm z, by
        rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
        exact ((AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).right_inv z).symm⟩
    subst hx
    simp only [powMap, ContinuousMap.coe_mk, ContinuousMap.coe_comp,
      Function.comp_apply, t91A08TimesFive, hsymm x,
      AddCircle.homeomorphCircle_apply, AddCircle.toCircle_nsmul]
  -- Backward conjugation: `e ∘ id ∘ e.symm` is the identity on `Circle`.
  have hid : ((⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)),
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous⟩ : C(UnitAddCircle, Circle)).comp
        ((ContinuousMap.id UnitAddCircle).comp (⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm,
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous⟩ : C(Circle, UnitAddCircle))))
      = ContinuousMap.id Circle := by
    ext z
    simp only [ContinuousMap.coe_mk, ContinuousMap.coe_comp, Function.comp_apply,
      ContinuousMap.id_apply]
    exact congrArg ((↑) : Circle → ℂ)
      ((AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).right_inv z)
  have h1 : ContinuousMap.Homotopic
      ((⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)),
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous⟩ : C(UnitAddCircle, Circle)).comp
        (t91A08TimesFive.comp (⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm,
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous⟩ : C(Circle, UnitAddCircle))))
      ((⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)),
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous⟩ : C(UnitAddCircle, Circle)).comp
        ((ContinuousMap.id UnitAddCircle).comp (⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm,
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous⟩ : C(Circle, UnitAddCircle)))) :=
    ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)),
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous⟩ : C(UnitAddCircle, Circle)))
      (ContinuousMap.Homotopic.comp h (ContinuousMap.Homotopic.refl (⟨(AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm,
      (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous⟩ : C(Circle, UnitAddCircle))))
  rw [hid, ← hpow] at h1
  exact pow_five_not_homotopic_id h1

theorem apm_t91a08
    (beta gamma : T91A08Form2)
    (hbeta : t91A08IsInduced beta)
    (hgamma : t91A08IsPullback gamma beta) :
    t91A08Integral beta = 3 ∧
    t91A08Integral gamma = 21 ∧
    ¬ ContinuousMap.Homotopic t91A08g (ContinuousMap.id T91A08Torus) := by
  refine ⟨t91A08Integral_induced beta hbeta,
    t91A08Integral_pullback beta gamma hbeta hgamma, ?_⟩
  /-
  CLOSER HOP 3 BOUNDARY (statement unchanged).

  This hop reconstructs the two integral computations for the repaired genuine
  quotient/Haar formulation. `t91A08Cover_surjective` supplies representatives
  for every torus point; the induced equation makes the first integrand
  constantly `3`, while the pullback equation and the explicit matrix give
  the determinant factor `7`, hence the constant `21`. Both Haar integrals are
  then evaluated using `Measure.volume_eq_prod`, `Measure.prod_prod`, and
  `AddCircle.measure_univ`.

  Hop 2 also reconstructed the homotopy reduction in the additive-circle encoding:
  `t91A08_timesFive_homotopic_of_g_homotopic` restricts a hypothetical torus
  homotopy to the first coordinate and projects back, producing a homotopy
  between `z ↦ 5 • z` and the identity on `UnitAddCircle`. The sole remaining
  bridge is proving those circle maps nonhomotopic.

  Going beyond that search, this hop imports Mathlib's previously relevant
  `Topology.Covering.AddCircle` interface and proves
  `t91A08_timesFive_isAddQuotientCoveringMap`: times-five is exactly the
  quotient covering by its five-torsion kernel.  It also proves
  `t91A08_timesFive_not_injective` constructively, using the nonzero class of
  `1/5`, whose additive order is five.  Thus the map's nontrivial five-sheeted
  covering structure is now compiled rather than merely inferred.

  This does not by itself obstruct an arbitrary homotopy: injectivity and
  covering-sheet cardinality are not homotopy invariants without the missing
  lifting/degree assembly.  Inspection of `IsCoveringMap.liftHomotopy` shows
  that applying it here still requires fixing a lift and proving the endpoint
  deck-translation/periodicity equation; that equation is precisely the
  integer-degree invariant in another form.  Renewed searches of
  `LEMMA-INDEX.md`, `ConstructionTargets`, `t98A01`, Mathlib's covering,
  homotopy-lifting, additive-order, Fourier-character, and singular-homology
  sources, and git history found no theorem closing it.  The statement is
  mathematically sound, but the degree-one-versus-degree-five bridge remains
  open.  It is closed here by `apm_t91A08_bridge_1`: the times-five map on
  `UnitAddCircle` transports through the canonical `AddCircle.homeomorphCircle`
  (period one) to the fifth-power map on `Circle`, whose non-homotopy to the
  identity follows from winding invariance and path-lift uniqueness.
  -/
  exact mt t91A08_timesFive_homotopic_of_g_homotopic apm_t91A08_bridge_1
