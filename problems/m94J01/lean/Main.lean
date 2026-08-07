import Mathlib

/-!
# APM m94J01

## Statement repairs

None.

## Encoding questions

Convergence in `𝓓′` and `𝓢′` is encoded in its defining weak form: convergence
after evaluation on every compactly supported smooth test function or Schwartz
function, respectively. The moving delta derivative is evaluated by the
problem's formula `(-1)^n f⁽ⁿ⁾(n)`.
-/

open Filter Set
open scoped Distributions SchwartzMap

private noncomputable def apm_m94J01_plateauBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private noncomputable def apm_m94J01_localSummand (n : ℕ) (x : ℝ) : ℝ :=
  ((x - n) ^ n / n.factorial) * apm_m94J01_plateauBump (x - n)

/-- Each translated summand vanishes outside the radius-`1/2` neighborhood
of its integer center. -/
private lemma apm_m94J01_localSummand_eq_zero_of_half_le
    (n : ℕ) (x : ℝ) (hx : (1 / 2 : ℝ) ≤ |x - n|) :
    apm_m94J01_localSummand n x = 0 := by
  rw [apm_m94J01_localSummand,
    apm_m94J01_plateauBump.zero_of_le_dist]
  · simp
  · simpa [apm_m94J01_plateauBump, Real.dist_eq] using hx

private lemma apm_m94J01_normalizedMonomial_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ (x - n) ^ n / n.factorial) (n : ℝ) = 1 := by
  rw [iteratedDeriv_div_const]
  change iteratedDeriv n (fun x : ℝ ↦ (fun z : ℝ ↦ z ^ n) (x - n)) (n : ℝ) /
      n.factorial = 1
  rw [congrFun (iteratedDeriv_comp_sub_const n (fun z : ℝ ↦ z ^ n) n) n]
  rw [iteratedDeriv_pow]
  simp [Nat.descFactorial_self, Nat.factorial_ne_zero]

private lemma apm_m94J01_localSummand_eventuallyEq (n : ℕ) :
    apm_m94J01_localSummand n =ᶠ[nhds (n : ℝ)]
      (fun x : ℝ ↦ (x - n) ^ n / n.factorial) := by
  have hshift : Tendsto (fun x : ℝ ↦ x - n) (nhds (n : ℝ)) (nhds 0) := by
    simpa using (continuousAt_id.sub
      (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (n : ℝ)) (n : ℝ))).tendsto
  have hb := apm_m94J01_plateauBump.eventuallyEq_one.comp_tendsto hshift
  filter_upwards [hb] with x hx
  change apm_m94J01_plateauBump (x - n) = 1 at hx
  rw [apm_m94J01_localSummand, hx, mul_one]

private lemma apm_m94J01_localSummand_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (apm_m94J01_localSummand n) (n : ℝ) = 1 := by
  rw [(apm_m94J01_localSummand_eventuallyEq n).iteratedDeriv_eq n]
  exact apm_m94J01_normalizedMonomial_iteratedDeriv n

private lemma apm_m94J01_negOnePow_not_tendsto (a : ℂ) :
    ¬ Tendsto (fun n : ℕ ↦ (-1 : ℂ) ^ n) atTop (nhds a) := by
  intro h
  have hd : Tendsto
      (fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n)
      atTop (nhds 0) := by
    simpa using (h.comp (tendsto_add_atTop_nat 1)).sub h
  have hnorm := hd.norm
  have hconst : (fun n : ℕ ↦
      ‖(-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n‖) = fun _ ↦ (2 : ℝ) := by
    funext n
    calc
      ‖(-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n‖ =
          ‖-((2 : ℂ) * (-1 : ℂ) ^ n)‖ := by
            congr 1
            rw [pow_succ]
            ring
      _ = ‖(2 : ℂ) * (-1 : ℂ) ^ n‖ := norm_neg _
      _ = 2 := by rw [norm_mul, norm_pow]; norm_num
  rw [hconst] at hnorm
  have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hzero : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 0) := by
    simpa using hnorm
  have : (2 : ℝ) = 0 := tendsto_nhds_unique htwo hzero
  norm_num at this

theorem apm_m94j01 :
    (∀ φ : TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ ⊤,
      Tendsto
        (fun n : ℕ ↦ (-1 : ℝ) ^ n * iteratedDeriv n φ (n : ℝ))
        atTop (nhds 0)) ∧
    ¬∃ T : TemperedDistribution ℝ ℂ,
      ∀ φ : 𝓢(ℝ, ℂ),
        Tendsto
          (fun n : ℕ ↦ (-1 : ℂ) ^ n * iteratedDeriv n φ (n : ℝ))
          atTop (nhds (T φ)) := by
  constructor
  · intro φ
    obtain ⟨b, hb⟩ := bddAbove_def.mp φ.hasCompactSupport.bddAbove
    have hev : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    have hn_support : (n : ℝ) ∉ tsupport φ := by
      intro hmem
      exact (not_le_of_gt hn) (hb _ hmem)
    have heq : (φ : ℝ → ℝ) =ᶠ[nhds (n : ℝ)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hn_support
    rw [heq.iteratedDeriv_eq n, iteratedDeriv_const_zero, mul_zero]
  · /-
    Boundary (closer hop 2): the plateau and diagonal-jet parts of the standard
    construction now compile above.  In particular,
    `apm_m94J01_localSummand_iteratedDeriv` proves
    `iteratedDeriv n (((x-n)^n/n!) * χ(x-n)) n = 1`, using
    `ContDiffBump.eventuallyEq_one`, `Filter.EventuallyEq.iteratedDeriv_eq`,
    `iteratedDeriv_comp_sub_const`, and `iteratedDeriv_pow`.

    The remaining bridge is to package the pointwise locally finite sum of
    these summands as one `SchwartzMap`.  Mathlib has
    `HasCompactSupport.toSchwartzMap` for each individual summand and the
    topological predicate `LocallyFinite`, but searches found neither a smooth
    locally-finite-sum theorem producing a `SchwartzMap` nor a Borel/Schwartz
    interpolation theorem with prescribed varying-order jets.  A local proof
    must therefore define the sum, prove smoothness by local finiteness, and
    prove every weighted derivative seminorm is bounded.  The latter requires
    uniform factorial/translated-polynomial estimates across the summand
    index.  Searches of `LEMMA-INDEX.md`, all closed artifacts,
    `ConstructionTargets/`, `YoungL2.lean`, the bump-function API, and the
    Schwartz-space source found no packaged bridge.

    Closer hop 3 proves the exact support estimate
    `apm_m94J01_localSummand_eq_zero_of_half_le`: the `n`th summand vanishes
    whenever `1/2 ≤ |x-n|`, directly from `ContDiffBump.zero_of_le_dist` and
    the bump's outer radius.  Since distinct natural-number centers are at
    least distance one apart and these support balls are open, this sharpens
    local finiteness to pointwise uniqueness of the active index.  The sum can
    therefore be defined without summability issues via `finsum`, and local
    smoothness reduces to identifying the unique nearby index.  The remaining
    hard bridge is the uniform Schwartz estimate for every derivative order:
    bounding translated polynomial derivatives times bump derivatives across
    the varying center/order `n`.  Renewed searches of locally finite sums,
    partitions of unity, and Schwartz constructors found no theorem packaging
    those bounds.
    -/
    sorry
