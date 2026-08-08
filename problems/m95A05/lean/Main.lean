import Mathlib

open scoped NNReal

/-!
# APM m95A05: coercivity on a reflexive Banach space

## Statement repairs

None.

## Encoding questions

Mathlib does not package topological reflexivity as a typeclass. It is encoded
directly and without weakening as surjectivity of the canonical continuous
linear isometry `V → V''`.
-/

noncomputable section

/-- Coercivity bounds the operator from below.  This is the quantitative
input both for injectivity and for closedness of the range. -/
lemma apm_m95a05_norm_le_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) (v : V) :
    c * ‖v‖ ≤ ‖A v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have heval : A v v ≤ ‖A v‖ * ‖v‖ := by
    exact (le_abs_self (A v v)).trans (by
      simpa [Real.norm_eq_abs] using (A v).le_opNorm v)
  have hmul : (c * ‖v‖) * ‖v‖ ≤ ‖A v‖ * ‖v‖ := calc
    (c * ‖v‖) * ‖v‖ = c * ‖v‖ ^ 2 := by ring
    _ ≤ A v v := hcoercive v
    _ ≤ ‖A v‖ * ‖v‖ := heval
  nlinarith

lemma apm_m95a05_injective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) :
    Function.Injective A := by
  intro x y hxy
  have hzero : A (x - y) = 0 := by simpa using sub_eq_zero.mpr hxy
  have hbound := apm_m95a05_norm_le_apply A c hcoercive (x - y)
  rw [hzero, norm_zero] at hbound
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Coercivity makes the operator anti-Lipschitz, hence its range is closed
when the domain is complete. -/
lemma apm_m95a05_isClosed_range
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) :
    IsClosed (Set.range A) := by
  let cNN : ℝ≥0 := Real.toNNReal c⁻¹
  have hanti : AntilipschitzWith cNN A := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    change dist x y ≤ (cNN : ℝ) * dist (A x) (A y)
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), le_inv_mul_iff₀ hc]
    simpa [dist_eq_norm] using apm_m95a05_norm_le_apply A c hcoercive (x - y)
  exact hanti.isClosed_range A.uniformContinuous

/-- A linear functional bounded strictly above on an entire linear range must
vanish there: otherwise scalar rescaling makes its value arbitrarily large. -/
lemma apm_m95a05_separator_vanishes_on_range
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V)
    (F : StrongDual ℝ (StrongDual ℝ V)) (u : ℝ)
    (hF : ∀ y ∈ Set.range A, F y < u) (v : V) :
    F (A v) = 0 := by
  by_contra hne
  have hscaled := hF (A (((u + 1) / F (A v)) • v))
    ⟨_, rfl⟩
  simp only [map_smul, smul_eq_mul] at hscaled
  field_simp [hne] at hscaled
  linarith

theorem apm_m95a05
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (hrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V))
    (A : V →L[ℝ] StrongDual ℝ V)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (f : StrongDual ℝ V) :
    ∃! u : V, A u = f := by
  /-
  Boundary (closer hop 1): `apm_m95a05_norm_le_apply` now compiles the
  coercivity estimate `c * ‖v‖ ≤ ‖A v‖`, using the dual operator-norm bound,
  and `apm_m95a05_injective` derives uniqueness.  Thus the quantitative lower
  bound and the entire uniqueness half of the theorem are closed.

  Closer hop 2 proves `apm_m95a05_isClosed_range`.  Recasting the coercive
  estimate as an `AntilipschitzWith (Real.toNNReal c⁻¹) A` bound allows direct
  application of `AntilipschitzWith.isClosed_range`; consequently the complete
  closed-range step is now compiled rather than merely planned.

  The remaining existence argument is now the separation/reflexivity route:
  if the proved-closed range is proper, geometric Hahn--Banach must produce a
  nonzero member of `V''` annihilating the
  range; use `hrefl` to write it as evaluation at `w : V`, and contradict
  coercivity by testing at `A w`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets`, the closed-range Hilbert
  proof in `m96A03`, the dual-annihilator partial development in `m03J04`,
  Mathlib's Banach-operator, double-dual, and Hahn--Banach sources, and git
  history found no single packaged normed-Banach annihilator theorem.  A new
  inspection of `Analysis.LocallyConvex.Separation` found
  `geometric_hahn_banach_closed_point`, which supplies the separator but still
  requires a local scaling argument showing it vanishes on the linear range,
  followed by transport through `hrefl`. `m96A03` uses Hilbert orthogonal
  complements and therefore does not apply directly to `StrongDual`.

  Original boundary:
  SKIPPED: Lax-Milgram theorem on reflexive Banach space.
  -- A: V→V' coercive (⟨Av,v⟩ ≥ c‖v‖²), f∈V'. Show ∃! u: Au=f.
  -- Proof: coercivity ⟹ A injective; reflexivity + coercivity ⟹ A surjective
  -- (via bounded inverse / open mapping theorem). This is essentially Lax-Milgram.
  -- Blocker: requires Lax-Milgram theorem (NOT in Mathlib), open mapping theorem
  -- application, reflexivity hypothesis manipulation with double dual surjectivity.
  APIs: `NormedSpace.inclusionInDoubleDual`, `ContinuousLinearMap`, `StrongDual`.

  CLOSER HOP 3 (complete). The Hahn--Banach/reflexivity bridge is now fully
  compiled. `apm_m95a05_separator_vanishes_on_range` proves by scalar
  rescaling that a continuous functional strictly bounded above on the entire
  linear range must annihilate it. If the already-closed range were proper,
  `geometric_hahn_banach_closed_point` would provide such a separator. The
  reflexivity hypothesis represents it as evaluation at `w : V`; annihilation
  at `A w` gives `A w w = 0`, while coercivity forces `w = 0`. The separator
  is therefore zero, contradicting its strict separation of the target from
  the range. This proves surjectivity, and the hop-1 injectivity lemma supplies
  uniqueness. The frozen theorem is unchanged and contains no `sorry`.
  -/
  have hclosed := apm_m95a05_isClosed_range A c hc hcoercive
  have hsurj : Function.Surjective A := by
    intro g
    by_contra hg
    have hconv : Convex ℝ (Set.range A) := by
      change Convex ℝ (A.range : Set (StrongDual ℝ V))
      exact A.range.convex
    obtain ⟨F, r, hFrange, hFg⟩ :=
      geometric_hahn_banach_closed_point hconv hclosed hg
    obtain ⟨w, hw⟩ := hrefl F
    have hFw : F (A w) = 0 :=
      apm_m95a05_separator_vanishes_on_range A F r hFrange w
    have hAww : A w w = 0 := by
      calc
        A w w = (NormedSpace.inclusionInDoubleDual ℝ V w) (A w) := rfl
        _ = F (A w) := by rw [hw]
        _ = 0 := hFw
    have hwnorm : ‖w‖ = 0 := by
      have hcow := hcoercive w
      rw [hAww] at hcow
      apply le_antisymm
      · by_contra hn
        have hnpos : 0 < ‖w‖ := lt_of_not_ge hn
        have hprod : 0 < c * ‖w‖ ^ 2 := mul_pos hc (sq_pos_of_pos hnpos)
        linarith
      · exact norm_nonneg w
    have hwzero : w = 0 := norm_eq_zero.mp hwnorm
    have hFzero : F = 0 := by simpa [hwzero] using hw.symm
    have hzero_lt : (0 : ℝ) < r := by
      have := hFrange 0 ⟨0, by simp⟩
      simpa [hFzero] using this
    have hr_zero : r < 0 := by simpa [hFzero] using hFg
    linarith
  obtain ⟨u, hu⟩ := hsurj f
  refine ⟨u, hu, ?_⟩
  intro y hy
  exact apm_m95a05_injective A c hc hcoercive (hy.trans hu.symm)
