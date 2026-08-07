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
      unfold m95A02Value
      rw [tsum_eq_single n]
      · simp
      · intro j hj
        simp [hj]
  · /-
    Boundary: the remaining Hölder estimate reduces by Cauchy–Schwarz to
    the sharp Fourier-kernel bound
    `∑ n : ℤ, |exp (n*I*x) - exp (n*I*y)|² /
      (2π (n²+1)) ≤ |x-y|`.
    I searched Mathlib and the repository for this periodic Sobolev kernel
    estimate, the equivalent bilateral-series identity for
    `∑ n : ℤ, cos (n*d) / (n²+1)`,
    `ArzelaAscoli.isCompact_of_equicontinuous`, weak-topology evaluation
    criteria, and `HilbertBasis`/`lp.single` infrastructure. The canonical
    Hilbert basis clause is proved above, but no compiled artifact supplies
    the sharp kernel inequality.

    After that inequality, the final clause still requires boundedness of a
    weakly convergent sequence, continuity of every evaluation functional,
    Arzelà–Ascoli on `[0,2π]`, and conversion of uniform convergence to the
    custom `sSup` expression `m95A02MaxDist`. I also tried a direct spectral
    route: weak convergence gives convergence of every finite set of Fourier
    coordinates, while Cauchy--Schwarz and the summable weights
    `1 / (n²+1)` should control the remaining evaluation tail uniformly in
    `x`. Mathlib has `lp.single`, weak-space evaluation criteria, and generic
    `tsum` Cauchy--Schwarz machinery, but no assembled lemma connecting them
    to this bilateral weighted Fourier series. Those analytic and order-
    theory bridges were not completed within this pass.
    -/
    sorry
