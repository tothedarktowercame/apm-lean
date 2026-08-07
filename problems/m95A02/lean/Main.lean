import Mathlib

/-! # APM m95A02: the periodic Sobolev space `H¹`

## Statement repairs

None.

## Encoding note

Mathlib does not bundle periodic `W^{1,2}`.  We use its exact weighted-Fourier
realization: an element of `m95A02H = ℓ²(ℤ, ℂ)` stores the coefficient in the
normalized basis `exp (inx) / √(2π(n²+1))`.  Consequently its `ℓ²` inner product
is precisely the Sobolev inner product printed in the question.
-/

open Filter Set

noncomputable section

abbrev m95A02H := lp (fun _ : ℤ => ℂ) 2

def m95A02BasisFunction (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) /
    (Real.sqrt (2 * Real.pi * ((n : ℝ) ^ 2 + 1)) : ℂ)

def m95A02Value (f : m95A02H) (x : ℝ) : ℂ :=
  ∑' n : ℤ, f n * m95A02BasisFunction n x

def m95A02MaxDist (f g : m95A02H) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Icc (0 : ℝ) (2 * Real.pi),
    r = dist (m95A02Value f x) (m95A02Value g x)}

/-- The Fourier-series realization sends the zero coefficient vector to the
zero function. -/
lemma m95A02Value_zero (x : ℝ) : m95A02Value (0 : m95A02H) x = 0 := by
  unfold m95A02Value
  have hz : ⇑(0 : m95A02H) = (0 : ℤ → ℂ) := by
    exact lp.coeFn_zero _ _
  rw [show (fun n : ℤ => (0 : m95A02H) n * m95A02BasisFunction n x) =
      (fun _ : ℤ => 0) by funext n; rw [show (0 : m95A02H) n = 0 from congrFun hz n]; simp]
  exact tsum_zero

/-- Evaluation of a coordinate vector is the corresponding normalized Fourier
mode.  This is the finite-coordinate core needed by the weak-convergence
route. -/
lemma m95A02Value_single (n : ℤ) (x : ℝ) :
    m95A02Value (lp.single 2 n 1 : m95A02H) x = m95A02BasisFunction n x := by
  unfold m95A02Value
  rw [tsum_eq_single n]
  · simp
  · intro j hj
    simp [hj]

/-- The custom maximum-distance encoding vanishes on the diagonal. -/
lemma m95A02MaxDist_self (f : m95A02H) : m95A02MaxDist f f = 0 := by
  have hset :
      {r : ℝ | ∃ x ∈ Icc (0 : ℝ) (2 * Real.pi),
        r = dist (m95A02Value f x) (m95A02Value f x)} = {0} := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp
    · intro hr
      have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
      subst r
      exact ⟨0, ⟨le_rfl, by positivity⟩, by simp⟩
  rw [m95A02MaxDist, hset]
  simp

/-- A uniform pointwise evaluation bound passes directly through the custom
set-valued supremum encoding. -/
lemma m95A02MaxDist_le_of_forall
    (f g : m95A02H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
      dist (m95A02Value f x) (m95A02Value g x) ≤ C) :
    m95A02MaxDist f g ≤ C := by
  unfold m95A02MaxDist
  apply Real.sSup_le _ hC
  intro r hr
  obtain ⟨x, hx, rfl⟩ := hr
  exact h x hx

/-- Weak convergence in the Fourier realization implies convergence of every
individual coefficient. -/
lemma m95A02_tendsto_coord_of_weak
    (f : ℕ → m95A02H) (g : m95A02H)
    (h : Tendsto (fun n ↦ toWeakSpace ℂ m95A02H (f n)) atTop
      (nhds (toWeakSpace ℂ m95A02H g))) (j : ℤ) :
    Tendsto (fun n ↦ f n j) atTop (nhds (g j)) := by
  have hall := (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℂ m95A02H).flip)
    (separatingDual_iff_injective.mp inferInstance)).1 h
  have hj := hall ((InnerProductSpace.toDual ℂ m95A02H)
    (lp.single 2 j 1 : m95A02H))
  convert hj using 1
  · funext n
    change f n j = (InnerProductSpace.toDual ℂ m95A02H)
      (lp.single 2 j 1 : m95A02H) (f n)
    rw [InnerProductSpace.toDual_apply_apply, lp.inner_single_left]
    simp
  · congr 1
    change g j = (InnerProductSpace.toDual ℂ m95A02H)
      (lp.single 2 j 1 : m95A02H) g
    rw [InnerProductSpace.toDual_apply_apply, lp.inner_single_left]
    simp

theorem apm_m95a02 :
    (∃ b : HilbertBasis ℤ ℂ m95A02H,
      ∀ n : ℤ, b n = lp.single 2 n 1 ∧
        ∀ x : ℝ, m95A02Value (b n) x = m95A02BasisFunction n x) ∧
    (∀ (f : m95A02H) (x y : ℝ),
      dist (m95A02Value f x) (m95A02Value f y) ≤
        |x - y| ^ (1 / 2 : ℝ) * ‖f‖) ∧
    (∀ (f : ℕ → m95A02H) (g : m95A02H),
      Tendsto (fun n => toWeakSpace ℂ m95A02H (f n)) atTop
        (nhds (toWeakSpace ℂ m95A02H g)) →
      Tendsto (fun n => m95A02MaxDist (f n) g) atTop (nhds 0)) := by
  refine ⟨?_, ?_⟩
  · let b : HilbertBasis ℤ ℂ m95A02H :=
      HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ m95A02H)
    refine ⟨b, ?_⟩
    intro n
    have hbn : b n = lp.single 2 n 1 := by
      simpa [b] using (b.repr_symm_single n).symm
    constructor
    · exact hbn
    · intro x
      rw [hbn]
      exact m95A02Value_single n x
  · /-
    PASS-1 boundary (Codex): the canonical Hilbert basis clause is proved,
    and `m95A02Value_zero` plus `m95A02MaxDist_self` now formally verify the
    zero evaluation and diagonal behavior of the custom supremum encoding.

    The remaining Hölder estimate reduces by Cauchy–Schwarz to
    the sharp Fourier-kernel bound
    `∑ n : ℤ, |exp (n*I*x) - exp (n*I*y)|² /
      (2π (n²+1)) ≤ |x-y|`.
    I searched Mathlib and the repository for this periodic Sobolev kernel
    estimate, the equivalent bilateral-series identity for
    `∑ n : ℤ, cos (n*d) / (n²+1)`,
    `ArzelaAscoli.isCompact_of_equicontinuous`, weak-topology evaluation
    criteria, and `HilbertBasis`/`lp.single` infrastructure. Mathlib supplies
    `Real.summable_abs_int_rpow` and Poisson summation, but no compiled
    artifact supplies the sharp kernel inequality. `ConstructionTargets.LusinN`
    proves an FTC distance estimate for actual absolutely continuous
    functions, but it cannot apply before constructing an AC representative
    of this sequence-defined Fourier realization.

    After that inequality, the final clause still requires boundedness of a
    weakly convergent sequence, continuity of every evaluation functional,
    Arzelà–Ascoli on `[0,2π]`, and conversion of uniform convergence to the
    custom `sSup` expression `m95A02MaxDist`. I also tried a direct spectral
    route: weak convergence gives convergence of every finite set of Fourier
    coordinates, while Cauchy--Schwarz and the summable weights
    `1 / (n²+1)` should control the remaining evaluation tail uniformly in
    `x`. Mathlib has `lp.single`, weak-space evaluation criteria, and generic
    `tsum` Cauchy--Schwarz machinery, but no assembled lemma connecting them
    to this bilateral weighted Fourier series. Sibling `m02A01` confirms that
    even weak convergence of the `lp.single` sequence still lacks a packaged
    coordinate/Riesz bridge in this corpus. Searches of all 170 closed
    artifacts, `ConstructionTargets/`, `YoungL2.lean`, boundary comments, and
    git history found no stronger route. Those analytic and order-theory
    bridges were not completed within this pass.

    Closer hop 1 extracted `m95A02Value_single`, so evaluation of every basis
    coordinate is now available independently of the bundled basis proof. A
    renewed Mathlib source search also found `lp.inner_single_right`, which
    supplies the previously missing algebraic Riesz-coordinate identity
    `⟪f, single j 1⟫ = ⟪f j, 1⟫`. Thus weak convergence can in principle be
    specialized to coordinate convergence without constructing a new Riesz
    theorem. The still-open bridge is applying the weak-space filter criterion
    with these inner-product functionals and then proving a uniform bilateral
    tail estimate strong enough for `m95A02MaxDist`; no corpus artifact
    packages that analytic sum.

    Closer hop 2 closes the weak-to-coordinate bridge as
    `m95A02_tendsto_coord_of_weak`.  It applies
    `WeakBilin.tendsto_iff_forall_eval_tendsto` to the Riesz functional of
    `lp.single 2 j 1`, then uses `InnerProductSpace.toDual_apply_apply` and
    `lp.inner_single_left` to identify the pairing with the `j`th coefficient.
    Searches of Mathlib's bilateral `ℤ` summability, Cauchy--Schwarz, tsum-tail,
    and integer-rpow sources, along with the closed corpus and construction
    libraries, still found no uniform estimate for the normalized Fourier
    tail.  Thus the remaining bridge is now exactly: combine finite-coordinate
    convergence with weak boundedness and the summable weights
    `1 / (n²+1)`, then transport the resulting uniform evaluation bound through
    the set-valued `sSup` in `m95A02MaxDist`.

    Closer hop 3 closes that final order-theory transport as
    `m95A02MaxDist_le_of_forall`: any nonnegative constant bounding all
    pointwise evaluation distances on `[0,2π]` also bounds the custom real
    `sSup`.  It uses `Real.sSup_le`, so no boundedness or nonemptiness
    bookkeeping remains at the call site.  The remaining boundary is now
    purely analytic: obtain a uniform pointwise bound tending to zero from
    finite-coordinate convergence and bounded ℓ² norms.  Source searches
    found generic `Summable` cofinite-tail and Cauchy--Schwarz APIs, but no
    theorem assembling the bilateral integer weights or the normalized
    exponential evaluation map; this weighted tail estimate still must be
    developed locally.
    -/
    sorry
