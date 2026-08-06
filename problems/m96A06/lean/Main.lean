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
  SKIPPED (concrete `Lp` bilinear-form boundary).  Current Mathlib does contain
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
  `L²` bounds through `value` and `weakDeriv`.  Coercivity then needs the a.e.
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
  -/
  sorry
