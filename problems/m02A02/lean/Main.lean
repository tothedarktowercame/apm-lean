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

/-- The mean-zero carrier is complete because it is the kernel of the
continuous mean functional. -/
lemma apm_m02a02_completeSpace_meanZero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (embed : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (one : Lp ℝ 2 (volume.restrict apm_m02a02_domain)) :
    CompleteSpace {u : H // @inner ℝ _ _ (embed u) one = 0} := by
  let mean : H →L[ℝ] ℝ := (innerSLFlip ℝ one).comp embed
  have hclosed : IsClosed {u : H | @inner ℝ _ _ (embed u) one = 0} := by
    simpa [mean, innerSLFlip_apply_apply] using mean.isClosed_ker
  exact hclosed.completeSpace_coe

/-- Green's identity and density of mean-zero tests identify the weak and
strong equations. -/
lemma apm_m02a02_weak_iff_strong
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (embed : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (gradX gradY : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (laplacian : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (one rhs : Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (hgreen : ∀ u v : H,
      @inner ℝ _ _ (gradX u) (gradX v) + @inner ℝ _ _ (gradY u) (gradY v) =
        -@inner ℝ _ _ (laplacian u) (embed v))
    (hrhs_mean : @inner ℝ _ _ rhs one = 0)
    (hlaplacian_mean : ∀ u : H, @inner ℝ _ _ (laplacian u) one = 0)
    (htest_dense : ∀ w : Lp ℝ 2 (volume.restrict apm_m02a02_domain),
      @inner ℝ _ _ w one = 0 →
      (∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
        @inner ℝ _ _ w (embed v) = 0) → w = 0)
    (u : H) :
    ((∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
        @inner ℝ _ _ (gradX u) (gradX v) +
          @inner ℝ _ _ (gradY u) (gradY v) = @inner ℝ _ _ rhs (embed v)) ↔
      -laplacian u = rhs) := by
  constructor
  · intro hweak
    have hw : -laplacian u - rhs = 0 := by
      apply htest_dense
      · calc
          @inner ℝ _ _ (-laplacian u - rhs) one =
              -@inner ℝ _ _ (laplacian u) one - @inner ℝ _ _ rhs one := by
                rw [inner_sub_left, inner_neg_left]
          _ = 0 := by rw [hlaplacian_mean u, hrhs_mean]; norm_num
      · intro v hv
        have h := hweak v hv
        rw [hgreen u v] at h
        simpa [inner_sub_left] using sub_eq_zero.mpr h
    exact sub_eq_zero.mp hw
  · intro hstrong v hv
    rw [hgreen u v, ← hstrong]
    simp

/-- On the mean-zero carrier, the two gradient components have trivial joint
kernel.  This is the nondegeneracy input for both the compactness proof of
Poincaré and the eventual Lax--Milgram form. -/
lemma apm_m02a02_grad_jointKernel_meanZero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (embed : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (gradX gradY : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (one : Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (hone : ‖one‖ = 1)
    (hembed_inj : Function.Injective embed)
    (hgrad_kernel : ∀ u : H,
      gradX u = 0 ∧ gradY u = 0 ↔ ∃ c : ℝ, embed u = c • one)
    (u : H) (hu : @inner ℝ _ _ (embed u) one = 0)
    (hgrad : gradX u = 0 ∧ gradY u = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := (hgrad_kernel u).mp hgrad
  have hc0 : c = 0 := by
    have : c * ‖one‖ ^ 2 = 0 := by
      calc
        c * ‖one‖ ^ 2 = @inner ℝ _ _ (c • one) one := by
          simp [inner_smul_left]
        _ = @inner ℝ _ _ (embed u) one := by rw [hc]
        _ = 0 := hu
    rw [hone] at this
    simpa using this
  apply hembed_inj
  rw [hc, hc0]
  simp

/-- The variational equation has at most one solution on a prescribed affine
mean slice. -/
lemma apm_m02a02_weak_unique
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (embed : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (gradX gradY : H →L[ℝ] Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (one rhs : Lp ℝ 2 (volume.restrict apm_m02a02_domain))
    (u₀ : H) (hone : ‖one‖ = 1) (hembed_inj : Function.Injective embed)
    (hgrad_kernel : ∀ u : H,
      gradX u = 0 ∧ gradY u = 0 ↔ ∃ c : ℝ, embed u = c • one)
    (u w : H)
    (hu_mean : @inner ℝ _ _ (embed (u - u₀)) one = 0)
    (hw_mean : @inner ℝ _ _ (embed (w - u₀)) one = 0)
    (hu : ∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
      @inner ℝ _ _ (gradX u) (gradX v) + @inner ℝ _ _ (gradY u) (gradY v) =
        @inner ℝ _ _ rhs (embed v))
    (hw : ∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
      @inner ℝ _ _ (gradX w) (gradX v) + @inner ℝ _ _ (gradY w) (gradY v) =
        @inner ℝ _ _ rhs (embed v)) : u = w := by
  let z : H := u - w
  have hzmean : @inner ℝ _ _ (embed z) one = 0 := by
    calc
      @inner ℝ _ _ (embed z) one =
          @inner ℝ _ _ (embed (u - u₀) - embed (w - u₀)) one := by
            congr 2
            simp [z]
      _ = 0 := by rw [inner_sub_left, hu_mean, hw_mean, sub_zero]
  have henergy :
      @inner ℝ _ _ (gradX z) (gradX z) +
        @inner ℝ _ _ (gradY z) (gradY z) = 0 := by
    calc
      @inner ℝ _ _ (gradX z) (gradX z) + @inner ℝ _ _ (gradY z) (gradY z) =
          (@inner ℝ _ _ (gradX u) (gradX z) + @inner ℝ _ _ (gradY u) (gradY z)) -
          (@inner ℝ _ _ (gradX w) (gradX z) + @inner ℝ _ _ (gradY w) (gradY z)) := by
            simp only [z, map_sub, inner_sub_left]
            ring
      _ = 0 := by rw [hu z hzmean, hw z hzmean, sub_self]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at henergy
  have hx : ‖gradX z‖ = 0 := by nlinarith [norm_nonneg (gradX z), norm_nonneg (gradY z)]
  have hy : ‖gradY z‖ = 0 := by nlinarith [norm_nonneg (gradX z), norm_nonneg (gradY z)]
  have hz : z = 0 := apm_m02a02_grad_jointKernel_meanZero embed gradX gradY one
    hone hembed_inj hgrad_kernel z hzmean ⟨norm_eq_zero.mp hx, norm_eq_zero.mp hy⟩
  exact sub_eq_zero.mp hz

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
  have hcomplete :
      CompleteSpace {u : H // @inner ℝ _ _ (embed u) one = 0} :=
    apm_m02a02_completeSpace_meanZero embed one
  have hcore :
      (∃ C : ℝ, 0 < C ∧ ∀ u : H,
        @inner ℝ _ _ (embed u) one = 0 →
        ‖embed u‖ ^ 2 ≤ C * (‖gradX u‖ ^ 2 + ‖gradY u‖ ^ 2)) ∧
      (∃ u : H,
        @inner ℝ _ _ (embed (u - u₀)) one = 0 ∧
        ∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
          @inner ℝ _ _ (gradX u) (gradX v) +
            @inner ℝ _ _ (gradY u) (gradY v) =
              @inner ℝ _ _ rhs (embed v)) := by
    /-
    CLOSER HOP 3 boundary. `LEMMA-INDEX.md`, all construction modules, the
    closed corpus, and git history contain no periodic-Sobolev compactness
    lemma reusable for these abstract operators. Mathlib does now contain
    `Analysis.InnerProductSpace.LaxMilgram`: after Poincaré supplies coercivity
    on the mean-zero subtype,
    `IsCoercive.continuousLinearEquivOfBilin` is the correct existence API.

    Hop 2 proved `apm_m02a02_grad_jointKernel_meanZero`. This final hop uses it
    in the compiled lemma `apm_m02a02_weak_unique`: subtract two weak
    equations, test with their difference, rewrite the two self-inner-products
    as squared norms, and conclude both gradients and hence the difference
    vanish. The `sorry` below has accordingly been narrowed from existence and
    uniqueness to Poincaré plus mere existence.

    I also investigated Mathlib's Fredholm shortcut
    `IsCompactOperator.antilipschitz_of_not_hasEigenvalue`.  Its source
    contains essentially the desired compactness/subsequence argument, but
    the theorem applies to a compact endomorphism `X → X` and bounds
    `T - μ • 1`.  Here `embed : H → L²` and the gradient pair have different
    codomains, so applying it requires first building a product-space
    endomorphism and transporting its lower bound; no existing helper does
    that reduction.

    The remaining first step is therefore still the contradiction proof of Poincaré from
    `hembed_compact`: normalize a sequence whose gradient energy tends to
    zero, extract a convergent embedded subsequence, use `hh1_norm` and
    `hgrad_kernel` to identify its limit with a constant mode, and use the
    mean-zero condition plus `hone` and `hembed_inj` to contradict unit norm.
    Packaging that sequence/subsequence argument, then defining the bounded
    bilinear form on the mean-zero subtype and transporting the affine mean
    specified by `u₀`, remains open. Inspection of `Compact.lean` found only
    compact-image lemmas, while `LaxMilgram.lean` begins after a bounded
    coercive bilinear form has already been assembled; neither closes this
    representation-specific bridge.

    This hop nevertheless closes two formerly implicit pieces outside this
    boundary: `apm_m02a02_completeSpace_meanZero` proves the first conjunct as
    a closed kernel, and `apm_m02a02_weak_iff_strong` proves the entire final
    equivalence using Green's identity and `htest_dense`.
    -/
    sorry
  have hex_unique :
      ∃! u : H,
        @inner ℝ _ _ (embed (u - u₀)) one = 0 ∧
        ∀ v : H, @inner ℝ _ _ (embed v) one = 0 →
          @inner ℝ _ _ (gradX u) (gradX v) +
            @inner ℝ _ _ (gradY u) (gradY v) =
              @inner ℝ _ _ rhs (embed v) := by
    obtain ⟨u, hu⟩ := hcore.2
    refine ⟨u, hu, ?_⟩
    intro w hw
    exact apm_m02a02_weak_unique embed gradX gradY one rhs u₀ hone hembed_inj
      hgrad_kernel w u hw.1 hu.1 hw.2 hu.2
  refine ⟨hcomplete, hcore.1, hex_unique, ?_⟩
  intro u hu
  exact apm_m02a02_weak_iff_strong embed gradX gradY laplacian one rhs
    hgreen hrhs_mean hlaplacian_mean htest_dense u
