import Mathlib

/-!
# APM m96A06

## Statement repairs

None.

## Encoding notes

Mathlib does not currently provide a packaged Sobolev-space type.  The type
`H` below is therefore an abstract Hilbert realization of the genuine graph
of the distributional derivative on `L²([0,1])`: the hypothesis `hH` says
exactly that its value/derivative pairs are all and only the weak-derivative
pairs.  This preserves the problem's central `H¹` object and its graph norm.

The Sturm–Liouville problem is stated in its standard weak Neumann form.  The
natural boundary conditions are encoded by allowing all `H¹` test functions,
including those with nonzero boundary traces.
-/

open MeasureTheory Set
open scoped ContDiff

def apm_m96a06_IsWeakDerivative
    (v w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Function.support φ ⊆ Ioo 0 1 →
      ∫ t, v t * deriv φ t ∂(volume.restrict (Icc (0 : ℝ) 1)) =
        -∫ t, w t * φ t ∂(volume.restrict (Icc (0 : ℝ) 1))

noncomputable def apm_m96a06_energy
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (value weakDeriv : H →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (a b : ℝ → ℝ) (u : H) : ℝ :=
  ∫ t, (weakDeriv u t) ^ 2 + a t * (value u t) ^ 2 - 2 * b t * value u t
    ∂(volume.restrict (Icc (0 : ℝ) 1))

def apm_m96a06_IsWeakNeumannSturmLiouville
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (value weakDeriv : H →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (a b : ℝ → ℝ) (u : H) : Prop :=
  ∀ h : H,
    ∫ t, weakDeriv u t * weakDeriv h t + a t * value u t * value h t
        ∂(volume.restrict (Icc (0 : ℝ) 1)) =
      ∫ t, b t * value h t ∂(volume.restrict (Icc (0 : ℝ) 1))

/-- Products of two concrete `L²` representatives are integrable. -/
lemma apm_m96a06_integrable_pair
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : Lp ℝ 2 μ) :
    Integrable (fun t => f t * g t) μ := by
  exact MemLp.integrable_mul (Lp.memLp f) (Lp.memLp g)

/-- The forcing term is integrable by the `L²` Hölder pairing. -/
lemma apm_m96a06_integrable_force
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b : α → ℝ) (hb : MemLp b 2 μ) (g : Lp ℝ 2 μ) :
    Integrable (fun t => b t * g t) μ := by
  exact MemLp.integrable_mul hb (Lp.memLp g)

/-- An `L∞` coefficient times two concrete `L²` representatives is
integrable; this is the Hölder estimate underlying the weighted form. -/
lemma apm_m96a06_integrable_weighted_pair
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (ha : MemLp a ⊤ μ) (f g : Lp ℝ 2 μ) :
    Integrable (fun t => a t * f t * g t) μ := by
  have haf : MemLp (fun t => a t * f t) 2 μ := by
    simpa only using (Lp.memLp f).mul' ha
  exact MemLp.integrable_mul haf (Lp.memLp g)

/-- Quantitative `L∞ × L² → L²` control for the representative-level
multiplier occurring in the weighted bilinear form. -/
lemma apm_m96a06_eLpNorm_weighted_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (f : Lp ℝ 2 μ) :
    eLpNorm (fun t ↦ a t * f t) 2 μ ≤
      eLpNorm a ⊤ μ * eLpNorm (fun t ↦ f t) 2 μ := by
  have h := eLpNorm_le_eLpNorm_top_mul_eLpNorm
    (p := (2 : ENNReal)) a (Lp.memLp f).1 (fun x y : ℝ ↦ x * y) 1
    (Filter.Eventually.of_forall fun t ↦ by simp [nnnorm_mul])
  simpa using h

/-- Multiplication by a raw `L∞` coefficient, descended to quotient `Lp` via
`MemLp.toLp` and heterogeneous `Lp` scalar multiplication. -/
noncomputable def apm_m96a06_multiplier
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (ha : MemLp a ⊤ μ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ha.toLp a • f

/-- The descended multiplier agrees almost everywhere with pointwise
multiplication by the original raw coefficient. -/
lemma apm_m96a06_multiplier_apply
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (ha : MemLp a ⊤ μ) (f : Lp ℝ 2 μ) :
    (apm_m96a06_multiplier a ha f : α → ℝ) =ᵐ[μ]
      fun t ↦ a t * f t := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (ha.toLp a) f,
    MemLp.coeFn_toLp ha] with t hmul haeq
  simpa [apm_m96a06_multiplier, haeq] using hmul

/-- Hölder supplies the quotient norm bound for the descended multiplier. -/
lemma apm_m96a06_norm_multiplier_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (ha : MemLp a ⊤ μ) (f : Lp ℝ 2 μ) :
    ‖apm_m96a06_multiplier a ha f‖ ≤ ‖ha.toLp a‖ * ‖f‖ := by
  exact Lp.norm_smul_le (r := 2) (ha.toLp a) f

/-- Multiplication by a fixed raw `L∞` coefficient as a bounded operator on
quotient `L²`.  This is Mathlib's Hölder bilinear map with its first argument
fixed after descending the coefficient via `MemLp.toLp`. -/
noncomputable def apm_m96a06_multiplierCLM
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (ha : MemLp a ⊤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ⊤ 2 2 (ha.toLp a)

lemma apm_m96a06_multiplierCLM_apply
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℝ) (ha : MemLp a ⊤ μ) (f : Lp ℝ 2 μ) :
    apm_m96a06_multiplierCLM a ha f = apm_m96a06_multiplier a ha f := by
  rfl

/-- The right-hand side pairing with an `L²` forcing term, packaged directly
as a continuous linear functional on quotient `Lp`. -/
noncomputable def apm_m96a06_forceCLM
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b : α → ℝ) (hb : MemLp b 2 μ) : Lp ℝ 2 μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2 (hb.toLp b)

/-- Evaluation of the packaged forcing functional is the representative-level
integral appearing in the frozen weak equation. -/
lemma apm_m96a06_forceCLM_apply
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b : α → ℝ) (hb : MemLp b 2 μ) (g : Lp ℝ 2 μ) :
    apm_m96a06_forceCLM b hb g = ∫ t, b t * g t ∂μ := by
  rw [apm_m96a06_forceCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hb] with t ht
  simp [ht]

/-- The weak forcing term transported along the Sobolev value map. -/
noncomputable def apm_m96a06_forceOnH
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (value : H →L[ℝ] Lp ℝ 2 μ) (b : α → ℝ) (hb : MemLp b 2 μ) :
    H →L[ℝ] ℝ :=
  apm_m96a06_forceCLM b hb ∘L value

lemma apm_m96a06_forceOnH_apply
    {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (value : H →L[ℝ] Lp ℝ 2 μ) (b : α → ℝ) (hb : MemLp b 2 μ) (h : H) :
    apm_m96a06_forceOnH value b hb h = ∫ t, b t * value h t ∂μ := by
  exact apm_m96a06_forceCLM_apply b hb (value h)

/-- Why this unblocks `apm_m96a06`: it constructs the bounded bilinear form
from the two `L²` pairings and the descended `L∞` multiplier, and records the
coercivity estimate needed by Lax--Milgram. -/
theorem apm_m96A06_bridge_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (value weakDeriv : H →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (hnorm : ∀ u : H, ‖u‖ ^ 2 =
      ∫ t, (value u t) ^ 2 + (weakDeriv u t) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) 1)))
    (a : ℝ → ℝ)
    (ha : MemLp a ⊤ (volume.restrict (Icc (0 : ℝ) 1)))
    (ε : ℝ) (hε : 0 < ε)
    (ha_lower : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ε ≤ a t) :
    ∃ B : H →L[ℝ] H →L[ℝ] ℝ,
      (∀ u h : H, B u h =
        ∫ t, weakDeriv u t * weakDeriv h t +
          a t * value u t * value h t
          ∂(volume.restrict (Icc (0 : ℝ) 1))) ∧
      0 < min 1 ε ∧
      ∀ u : H, min 1 ε * ‖u‖ ^ 2 ≤ B u u := by
  sorry

/-- Why this unblocks the first two conjuncts of `apm_m96a06`: the exact
quadratic expansion has a remainder bounded by `O(‖h‖²)`, yielding the stated
Fréchet derivative; uniqueness of derivatives then identifies its vanishing
with the weak Sturm--Liouville equation. -/
theorem apm_m96A06_bridge_2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (value weakDeriv : H →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (hnorm : ∀ u : H, ‖u‖ ^ 2 =
      ∫ t, (value u t) ^ 2 + (weakDeriv u t) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) 1)))
    (a b : ℝ → ℝ)
    (ha : MemLp a ⊤ (volume.restrict (Icc (0 : ℝ) 1)))
    (hb : MemLp b 2 (volume.restrict (Icc (0 : ℝ) 1))) :
    (∀ u : H, ∃ L : H →L[ℝ] ℝ,
      HasFDerivAt (apm_m96a06_energy value weakDeriv a b) L u ∧
      ∀ h : H, L h = 2 *
        (∫ t, weakDeriv u t * weakDeriv h t + a t * value u t * value h t -
          b t * value h t ∂(volume.restrict (Icc (0 : ℝ) 1)))) ∧
    ∀ u : H,
      (∃ L : H →L[ℝ] ℝ,
        HasFDerivAt (apm_m96a06_energy value weakDeriv a b) L u ∧ L = 0) ↔
      apm_m96a06_IsWeakNeumannSturmLiouville value weakDeriv a b u := by
  sorry

/-- Why this unblocks the final conjunct of `apm_m96a06`: coercivity of the
weighted Sobolev form and continuity of the forcing functional give the
unique weak Neumann solution by the real Hilbert-space Lax--Milgram theorem. -/
theorem apm_m96A06_bridge_3
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (value weakDeriv : H →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (hnorm : ∀ u : H, ‖u‖ ^ 2 =
      ∫ t, (value u t) ^ 2 + (weakDeriv u t) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) 1)))
    (a b : ℝ → ℝ)
    (ha : MemLp a ⊤ (volume.restrict (Icc (0 : ℝ) 1)))
    (hb : MemLp b 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (ε : ℝ) (hε : 0 < ε)
    (ha_lower : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ε ≤ a t) :
    ∃! u : H,
      apm_m96a06_IsWeakNeumannSturmLiouville value weakDeriv a b u := by
  sorry

theorem apm_m96a06
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (value weakDeriv : H →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (hH : ∀ v w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)),
      apm_m96a06_IsWeakDerivative v w ↔
        ∃! u : H, value u = v ∧ weakDeriv u = w)
    (hnorm : ∀ u : H, ‖u‖ ^ 2 =
      ∫ t, (value u t) ^ 2 + (weakDeriv u t) ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) 1)))
    (a b : ℝ → ℝ)
    (ha : MemLp a ⊤ (volume.restrict (Icc (0 : ℝ) 1)))
    (hb : MemLp b 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (ε : ℝ) (hε : 0 < ε)
    (ha_lower : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ε ≤ a t) :
    (∀ u : H, ∃ L : H →L[ℝ] ℝ,
      HasFDerivAt (apm_m96a06_energy value weakDeriv a b) L u ∧
      ∀ h : H, L h = 2 *
        (∫ t, weakDeriv u t * weakDeriv h t + a t * value u t * value h t -
          b t * value h t ∂(volume.restrict (Icc (0 : ℝ) 1)))) ∧
    (∀ u : H,
      (∃ L : H →L[ℝ] ℝ,
        HasFDerivAt (apm_m96a06_energy value weakDeriv a b) L u ∧ L = 0) ↔
      apm_m96a06_IsWeakNeumannSturmLiouville value weakDeriv a b u) ∧
    ∃! u : H, apm_m96a06_IsWeakNeumannSturmLiouville value weakDeriv a b u := by
  /-
  PARTIAL (closer hop 1, concrete `Lp` bilinear-form boundary).
  `apm_m96a06_eLpNorm_weighted_le` now compiles the quantitative multiplier
  estimate `‖a * f‖₂ ≤ ‖a‖∞ * ‖f‖₂` directly from Mathlib's
  `eLpNorm_le_eLpNorm_top_mul_eLpNorm`.  Together with the three integrability
  lemmas from the original pass, this closes both membership and norm control
  for the raw `L∞ × L² → L²` multiplication step.  The remaining interface is
  to turn it into a continuous linear multiplier on quotient `Lp`, compose it
  with `ContinuousLinearMap.lpPairing`, and identify evaluation with the
  frozen triple integral.

  Current Mathlib does contain
  the abstract real Hilbert-space Lax--Milgram theorem in
  `Analysis.InnerProductSpace.LaxMilgram`: for a bounded bilinear map
  `B : H →L[ℝ] H →L[ℝ] ℝ`, `IsCoercive.continuousLinearEquivOfBilin`
  provides the unique solution.  Thus the blocker is not the abstract theorem
  itself, but constructing its input from this frozen representative-level
  encoding.

  In detail, one must bundle
  `∫ (weakDeriv u * weakDeriv h + a * value u * value h)` as a continuous
  bilinear map on `H`.  This requires connecting the displayed pointwise
  integrals of Mathlib's chosen `Lp` representatives to
  `ContinuousLinearMap.lpPairing`, proving the
  `L∞ × L² × L² → L¹` weighted estimate from `ha`, and transporting the two
  `L²` bounds through `value` and `weakDeriv`.  The three local lemmas above
  now prove integrability of the derivative pairing, forcing pairing, and
  weighted value pairing using `MemLp.integrable_mul` and `MemLp.mul'`; this
  closes the prerequisites for `integral_add`/`integral_sub`.  Bundling their
  quantitative norm estimates as continuous bilinear maps remains open.
  Coercivity then needs the a.e.
  lower bound `ha_lower`, monotonicity of the integral, and `hnorm` to prove
  `min 1 ε * ‖u‖² ≤ B u u`.  The forcing term similarly needs to be bundled
  from `hb` by the `L²` pairing.

  The Fréchet-derivative conjunct additionally requires expanding the three
  representative-level integrals under `u + h`, identifying the linear part
  with the bundled functional, and bounding the exact quadratic remainder by
  `O(‖h‖²)` before applying `HasFDerivAt`.  Once that is done, the middle
  equivalence is algebraic and Lax--Milgram closes existence and uniqueness.

  `LEMMA-INDEX.md` exposed `ConstructionTargets.LpRepresentative` helpers,
  and completed sibling `a03J03` demonstrates `lpPairing_eq_integral`; neither
  provides multiplication by an arbitrary `L∞` coefficient as the needed
  bilinear operator.  `ConstructionTargets.LpRepresentative` concerns
  commuting representatives with Bochner integration, not this weighted
  form.  Partial siblings `m95A05`, `m03J05`, and `m00A04` do not supply the
  construction: the first predates Mathlib's packaged Lax--Milgram API, while
  the latter two stop at custom Sobolev/operator assembly boundaries.  The
  fully closed artifact scan, the remaining `ConstructionTargets/` modules,
  and `YoungL2.lean` yielded no closer reusable theorem.  The frozen statement
  appears sound, but this analytic interface was not completed in the pass.

  CLOSER HOP 2 goes beyond representative-level bounds by constructing the
  quotient-level forcing functional. `apm_m96a06_forceCLM` specializes
  Mathlib's `ContinuousLinearMap.lpPairing` to `hb.toLp b`, and
  `apm_m96a06_forceCLM_apply` transports its value back to the exact frozen
  integral using `MemLp.coeFn_toLp`. `apm_m96a06_forceOnH` then composes this
  functional with `value`, so the complete right-hand side of the weak problem
  is now a continuous linear functional on `H`, with a compiled evaluation
  theorem. This eliminates the forcing-side quotient descent entirely.

  The live boundary is now the left-hand bilinear form: multiplication by the
  arbitrary raw `L∞` coefficient must descend to quotient `Lp` (or the
  weighted triple pairing must be bundled directly), after which coercivity,
  Lax--Milgram, and the quadratic Fréchet remainder remain. Searches of the
  `Lp` multiplier/smul APIs found no constructor accepting a raw `MemLp a ⊤`
  coefficient, so this portion remains honestly open.

  CLOSER HOP 3 finds and compiles the missing quotient descent by composing
  APIs already present in Mathlib: `ha.toLp a` turns the raw coefficient into
  `Lp ℝ ⊤ μ`, and heterogeneous `Lp` scalar multiplication realizes
  `L∞ × L² → L²`. `apm_m96a06_multiplier` packages the result,
  `apm_m96a06_multiplier_apply` proves its exact a.e. representative using
  `Lp.coeFn_lpSMul` and `MemLp.coeFn_toLp`, and
  `apm_m96a06_norm_multiplier_le` supplies the quotient norm estimate.
  `apm_m96a06_multiplierCLM` further packages this operation as a continuous
  linear map by specializing Mathlib's `holderL`; thus it also closes the
  operator-packaging boundary left by hop 2. What remains is to compose this
  with `lpPairing` into the bilinear form, prove coercivity, and
  complete Lax--Milgram and the quadratic Frechet remainder. No unproved
  assertion was introduced; the frozen statement is unchanged.
  -/
  sorry
