import Mathlib

/-!
# APM m02A02 — the periodic Poisson variational problem

## Statement repairs

The source omits the compatibility condition for the periodic Poisson equation.
We therefore assume that the forcing annihilates constants (`hrhs_mean`).

The rejected version quantified unrelated scalar “energies” and an unrelated
`weakPoisson` predicate.  This repair replaces them by a pinned Sobolev model:

* `embed` realizes the periodic `H¹` carrier in the actual `L²` space on
  `Ω = [0,1]²`;
* `gradX`, `gradY`, and `laplacian` are continuous linear operators, with their
  relation pinned by Green's identity;
* the mean is the `L²` pairing with the normalized constant mode;
* the Dirichlet form and forcing in the conclusion are the corresponding inner
  products, rather than independently quantified functions;
* compactness of the Sobolev embedding, the constant-kernel characterization,
  and completeness of the periodic Sobolev carrier are explicit structural
  hypotheses.  They are the standard Sobolev facts from which Poincaré and the
  variational result are derived, not scalar restatements of those conclusions.

Mathlib has no packaged periodic Sobolev space or weak-derivative construction,
so these operators are exposed as concrete, equation-pinned structure rather
than hidden behind an opaque predicate.
-/

open MeasureTheory Set
open scoped ENNReal

def apm_m02a02_domain : Set (ℝ × ℝ) :=
  Icc 0 1 ×ˢ Icc 0 1

theorem apm_m02a02
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (embed : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (gradX gradY : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (laplacian : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (one rhs : Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (u₀ : H)
    (hone : ‖one‖ = 1)
    (hembed_inj : Function.Injective embed)
    (hembed_compact : IsCompactOperator embed)
    (hh1_norm : ∀ u : H,
      ‖u‖ ^ 2 = ‖embed u‖ ^ 2 + ‖gradX u‖ ^ 2 + ‖gradY u‖ ^ 2)
    (hgrad_kernel : ∀ u : H,
      gradX u = 0 ∧ gradY u = 0 ↔ ∃ c : ℝ, embed u = c • one)
    (hgreen : ∀ u v : H,
      @inner ℝ _ _ (gradX u) (gradX v) +
          @inner ℝ _ _ (gradY u) (gradY v) =
        -@inner ℝ _ _ (laplacian u) (embed v))
    (hrhs_mean : @inner ℝ _ _ rhs one = 0)
    (hlaplacian_mean : ∀ u : H, @inner ℝ _ _ (laplacian u) one = 0)
    (htest_dense : ∀ w : Lp ℝ 2 (volume.restrict apm_m02a02_domain),
      @inner ℝ _ _ w one = 0 →
      (∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
        @inner ℝ _ _ w (embed v) = 0) → w = 0) :
    CompleteSpace {u : H // @inner ℝ _ _ (embed u) one = 0} ∧
    (∃ C : ℝ, 0 < C ∧ ∀ u : H,
      @inner ℝ _ _ (embed u) one = 0 →
      ‖embed u‖ ^ 2 ≤ C * (‖gradX u‖ ^ 2 + ‖gradY u‖ ^ 2)) ∧
    (∃! u : H,
      @inner ℝ _ _ (embed (u - u₀)) one = 0 ∧
      ∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
        @inner ℝ _ _ (gradX u) (gradX v) +
          @inner ℝ _ _ (gradY u) (gradY v) = @inner ℝ _ _ rhs (embed v)) ∧
    (∀ u : H, @inner ℝ _ _ (embed (u - u₀)) one = 0 →
      ((∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
          @inner ℝ _ _ (gradX u) (gradX v) +
            @inner ℝ _ _ (gradY u) (gradY v) = @inner ℝ _ _ rhs (embed v)) ↔
        -laplacian u = rhs)) := by
  sorry
