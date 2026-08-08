import Mathlib

/-!
# APM a97J08

## Statement repairs

None.

## Encoding questions

Mathlib has no single bundled type for a rectifiable Jordan curve. The source's
condition is encoded without weakening as continuity and bounded variation on
`[0,1]`, equality of the endpoints, and injectivity on `[0,1)`. The interior is
the union of the bounded connected components of the complement of the curve.
Zero counts use the positive part of the meromorphic divisor, hence count
multiplicity rather than merely distinct zero locations.
-/

open Filter Metric Set
open scoped Topology

noncomputable section

/-- The image `Γ` of a parametrized closed curve. -/
def apm_a97j08_curveImage (γ : ℝ → ℂ) : Set ℂ :=
  γ '' Icc (0 : ℝ) 1

/-- The bounded side of a Jordan curve: the bounded connected components of
its complement. -/
def apm_a97j08_curveInterior (γ : ℝ → ℂ) : Set ℂ :=
  {z | z ∉ apm_a97j08_curveImage γ ∧
    Bornology.IsBounded
      (connectedComponentIn (apm_a97j08_curveImage γ)ᶜ z)}

/-- The number of zeros in `U`, counted with multiplicity by the positive
part of the divisor. -/
def apm_a97j08_zeroCount (f : ℂ → ℂ) (U : Set ℂ) : ℤ :=
  ∑ᶠ z : ℂ, max (MeromorphicOn.divisor f U z) 0

lemma apm_a97j08_curveImage_compact {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    IsCompact (apm_a97j08_curveImage γ) := by
  exact isCompact_Icc.image_of_continuousOn hγ_cont

lemma apm_a97j08_limit_continuousOn_curve
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D) :
    ContinuousOn g (apm_a97j08_curveImage γ) := by
  apply (hF_tendsto.continuousOn ?_).mono hγD
  exact Frequently.of_forall fun n ↦ (hF_analytic n).continuousOn

/-- Weierstrass' theorem supplies analyticity of the locally uniform limit. -/
lemma apm_a97j08_limit_differentiableOn
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D) :
    DifferentiableOn ℂ g D := by
  exact hF_tendsto.differentiableOn
    (Eventually.of_forall hF_analytic) hD_open

/-- Nonvanishing of the limit on the compact curve gives the quantitative
margin needed for the eventual Rouché inequality. -/
lemma apm_a97j08_exists_boundary_margin
    {γ : ℝ → ℂ} {g : ℂ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hg_cont : ContinuousOn g (apm_a97j08_curveImage γ))
    (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ apm_a97j08_curveImage γ, ε ≤ ‖g z‖ := by
  have hK := apm_a97j08_curveImage_compact hγ_cont
  have hKne : (apm_a97j08_curveImage γ).Nonempty := by
    refine ⟨γ 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hKne hg_cont.norm
  refine ⟨‖g z‖, norm_pos_iff.mpr (hg_ne z hz), ?_⟩
  intro w hw
  exact hmin hw

/-- Local uniform convergence gives the eventual strict Rouché inequality on
the whole compact curve.  This completes the analytic boundary reduction; the
remaining main-theorem gap is the arbitrary-Jordan-domain zero-count transfer. -/
lemma apm_a97j08_eventually_boundary_rouche
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ apm_a97j08_curveImage γ,
      ‖F n z - g z‖ < ‖g z‖ := by
  have hg_cont := apm_a97j08_limit_continuousOn_curve hγD hF_analytic hF_tendsto
  obtain ⟨ε, hε, hεg⟩ :=
    apm_a97j08_exists_boundary_margin hγ_cont hg_cont hg_ne
  have hcompact := apm_a97j08_curveImage_compact hγ_cont
  have huniform : TendstoUniformlyOn F g atTop (apm_a97j08_curveImage γ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).mp hF_tendsto
      _ hγD hcompact
  have heventually : ∀ᶠ n in atTop, ∀ z ∈ apm_a97j08_curveImage γ,
      dist (g z) (F n z) < ε :=
    (tendstoUniformlyOn_iff.mp huniform) ε hε
  rw [eventually_atTop] at heventually
  obtain ⟨N, hN⟩ := heventually
  refine ⟨N, fun n hn z hz ↦ ?_⟩
  rw [norm_sub_rev]
  exact lt_of_lt_of_le (by simpa [dist_eq_norm] using hN n hn z hz) (hεg z hz)

/-! ## Blocker analysis

This is the Hurwitz/Rouché theorem: zeros are stable under locally uniform
convergence. The proof requires:

1. **Weierstrass convergence theorem**: g is analytic (limit of analytic f_n).
   - Mathlib has `TendstoLocallyUniformlyOn` but no pre-packaged theorem that
     the locally uniform limit of holomorphic functions is holomorphic.

2. **Jordan curve theorem**: the interior of a Jordan curve is well-defined.
   - Mathlib has NO Jordan curve theorem. `apm_a97j08_curveInterior` is defined
     via `connectedComponentIn` and `Bornology.IsBounded`, but there is no
     theorem that a simple closed curve bounds a unique bounded region.

3. **Rouché's theorem / argument principle**: zero-counting via contour integrals.
   - Mathlib (v4.29.0-rc8) has NO Rouché's theorem, NO argument principle
     (`(1/2πi)∮ f'/f dz = number of zeros`), NO winding number.
   - Available: `Complex.circleIntegral_sub_inv_smul` (Cauchy integral formula),
     `MeromorphicOn.divisor` (divisor function), `MeromorphicOn.extract_zeros_poles`
   - But no theorem connecting contour integrals to zero counts.

4. **Homotopy invariance of zero count**: integer-valued continuous function is
   eventually constant — the key mechanism behind Rouché.

The statement is TRUE as stated. The blocker is a fundamental Mathlib
infrastructure gap: the entire argument-principle / Rouché / Hurwitz pipeline
is absent. This is the same gap that blocks a94A09. -/

theorem apm_a97j08 (D : Set ℂ) (γ : ℝ → ℂ) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_closed : γ 0 = γ 1)
    (hγ_simple : Set.InjOn γ (Ico (0 : ℝ) 1))
    (hγ_rectifiable : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      apm_a97j08_zeroCount (F n) (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  /-
  Boundary (closer hops 1--2): four helpers above now compile the quantitative
  boundary setup.  `apm_a97j08_curveImage_compact` proves compactness of the
  actual image, `apm_a97j08_limit_continuousOn_curve` obtains continuity of
  `g` there directly from locally uniform convergence, and
  `apm_a97j08_exists_boundary_margin` produces `ε > 0` with
  `ε ≤ ‖g z‖` on the whole curve.  Thus the remaining convergence step can use
  `apm_a97j08_eventually_boundary_rouche` now also performs the compact-set
  uniform-convergence step and obtains one `N` such that
  `‖F n z - g z‖ < ‖g z‖` on the entire boundary whenever `n ≥ N`.

  The reusable `ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq` now
  supplies Rouché zero-count transfer, but only for round disks and a divisor
  restricted to their closed balls.  The frozen theorem uses an arbitrary
  rectifiable Jordan curve and the set
  `apm_a97j08_curveInterior γ`.  Searches of `LEMMA-INDEX.md`, all
  `ConstructionTargets/`, Mathlib's connected-component/Jordan, locally
  uniform convergence, divisor, and contour-integration sources, prior
  Rouché users `a92J05` and `a97A08`, and git history found no Jordan curve
  theorem, no proof that this encoded interior has compact closure contained
  in simply connected `D`, and no arbitrary-contour argument principle that
  equates its divisor sum with a winding integral.

  Closure therefore still requires the topology bridge for this concrete
  interior plus a generalization of the disk Rouché theorem to rectifiable
  Jordan curves (or a homeomorphic/conformal reduction preserving divisors).

  CLOSER HOP 3: Mathlib's
  `TendstoLocallyUniformlyOn.differentiableOn` exactly matches the frozen
  hypotheses; `apm_a97j08_limit_differentiableOn` above now compiles
  `DifferentiableOn ℂ g D`, closing the original Weierstrass blocker.

  I also checked a route avoiding arbitrary-contour Rouché. Once the closure
  of the encoded interior is compact and contained in `D`, isolate the finite
  zeros of `g` by disjoint closed disks, apply the reusable disk Rouché theorem
  on each, and use uniform nonvanishing on the compact remainder. The missing
  interfaces are now Jordan compact-closure/containment and divisor
  finiteness, isolation, and additivity of the frozen `finsum` over this finite
  decomposition. No packaged declarations for them were found. The statement
  is unchanged.

  HOP 4 rechecked `ConstructionTargets.Rouche`, Mathlib's locally finite
  divisor support, connected-component, frontier, and simply-connected APIs.
  Disk Rouché is available, but there remains no theorem relating the bounded
  connected components in `apm_a97j08_curveInterior` to the curve image.

  The exact missing topological lemma is:

    `∀ (D : Set ℂ) (γ : ℝ → ℂ),
      IsOpen D → IsSimplyConnected D →
      ContinuousOn γ (Icc (0 : ℝ) 1) → γ 0 = γ 1 →
      Set.InjOn γ (Ico (0 : ℝ) 1) →
      apm_a97j08_curveImage γ ⊆ D →
      IsCompact (closure (apm_a97j08_curveInterior γ)) ∧
      closure (apm_a97j08_curveInterior γ) ⊆ D ∧
      frontier (apm_a97j08_curveInterior γ) =
        apm_a97j08_curveImage γ`.

  The exact analytic lemma that then closes the frozen theorem is:

    `∀ (D : Set ℂ) (γ : ℝ → ℂ) (f g : ℂ → ℂ),
      IsOpen D → IsSimplyConnected D →
      ContinuousOn γ (Icc (0 : ℝ) 1) → γ 0 = γ 1 →
      Set.InjOn γ (Ico (0 : ℝ) 1) →
      BoundedVariationOn γ (Icc (0 : ℝ) 1) →
      apm_a97j08_curveImage γ ⊆ D →
      DifferentiableOn ℂ f D → DifferentiableOn ℂ g D →
      (∀ z ∈ apm_a97j08_curveImage γ, ‖f z - g z‖ < ‖g z‖) →
      apm_a97j08_zeroCount f (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ)`.

  The second is the arbitrary-Jordan Rouché theorem in precisely the frozen
  divisor representation. Applying it to the already compiled eventual
  boundary inequality and limit differentiability is immediate. Neither
  proposition is available in the searched corpus, and proving them requires
  the absent Jordan separation/argument-principle infrastructure. The frozen
  statement remains unchanged.
  -/
  sorry
