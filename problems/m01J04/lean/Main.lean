import Mathlib

/-!
# APM m01J04: Weak convergence and compensated compactness

## Statement repairs

Parts (b) and (c) use the compact embedding `H¹(Ω) ↪ L²(Ω)`, which is false
for an arbitrary domain (translations on an unbounded domain are a standard
counterexample). We therefore add the exact required hypothesis that `Ω` has
the Rellich compactness property. This covers, in particular, the bounded
Lipschitz domains intended by the supplied solution.

## Encoding questions

None. `H¹(Ω)` is represented by a function, its genuine weak gradient, and
their `L²` conditions. Weak convergence and strong `H⁻¹` convergence are
spelled out through their defining dual pairings on the actual domain.
-/

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

def apm_m01J04_weaklyConverges {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (f : ℕ → X) (x : X) : Prop :=
  ∀ g : X →L[ℝ] ℝ, Tendsto (fun n ↦ g (f n)) atTop (nhds (g x))

structure apm_m01J04_H1 (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) where
  val : EuclideanSpace ℝ (Fin d) → ℝ
  grad : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  val_memLp : MemLp val 2 (volume.restrict Ω)
  grad_memLp : MemLp grad 2 (volume.restrict Ω)
  weakGradient : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → Function.support φ ⊆ Ω →
      ∀ i : Fin d,
        (∫ x in Ω, val x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -(∫ x in Ω, grad x i * φ x)

def apm_m01J04_H1norm {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u : apm_m01J04_H1 d Ω) : ℝ :=
  (eLpNorm u.val 2 (volume.restrict Ω)).toReal +
    (eLpNorm u.grad 2 (volume.restrict Ω)).toReal

def apm_m01J04_H1dist {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u w : apm_m01J04_H1 d Ω) : ℝ :=
  (eLpNorm (fun x ↦ u.val x - w.val x) 2 (volume.restrict Ω)).toReal +
    (eLpNorm (fun x ↦ u.grad x - w.grad x) 2 (volume.restrict Ω)).toReal

/-- Componentwise `L²` convergence is exactly what is needed for convergence
in the custom `H1dist`.  This is the terminal interface for a mollifier
construction: value and genuine-gradient estimates can be proved separately. -/
lemma apm_m01J04_H1dist_tendsto_zero_of_components
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (a : ℕ → apm_m01J04_H1 d Ω) (f : apm_m01J04_H1 d Ω)
    (hval : Tendsto (fun n ↦
      (eLpNorm (fun x ↦ (a n).val x - f.val x) 2
        (volume.restrict Ω)).toReal) atTop (nhds 0))
    (hgrad : Tendsto (fun n ↦
      (eLpNorm (fun x ↦ (a n).grad x - f.grad x) 2
        (volume.restrict Ω)).toReal) atTop (nhds 0)) :
    Tendsto (fun n ↦ apm_m01J04_H1dist (a n) f) atTop (nhds 0) := by
  simpa [apm_m01J04_H1dist] using hval.add hgrad

/-- A field supported in a measurable subset of the restricted domain can be
viewed as a global `Lᵖ` field.  This is the measure-theoretic globalization
step needed before convolving a compactly localized Sobolev pair. -/
lemma apm_m01J04_memLp_volume_of_support_subset
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {Ω s : Set α} {u : α → E} {p : ℝ≥0∞}
    (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (hu : MemLp u p (μ.restrict Ω))
    (hsupp : Function.support u ⊆ s) : MemLp u p μ := by
  classical
  have hus : MemLp u p (μ.restrict s) :=
    MemLp.mono_measure (Measure.restrict_mono_set μ hsΩ) hu
  have hp : MemLp (s.piecewise u 0) p μ :=
    hus.piecewise hs MemLp.zero
  have heq : s.piecewise u 0 = u := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx]
    · have hux : u x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      simp [hx, hux]
  rwa [heq] at hp

/-- Almost-everywhere support is enough for the same globalization step.  This
is the form needed for weak derivatives, whose representatives may be nonzero
on a null part of the multiplier's zero set. -/
lemma apm_m01J04_memLp_of_ae_eq_zero_outside
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {Ω s : Set α} {u : α → E} {p : ℝ≥0∞}
    (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (hu : MemLp u p (μ.restrict Ω))
    (hu0 : ∀ᵐ x ∂μ, x ∉ s → u x = 0) : MemLp u p μ := by
  classical
  have hus : MemLp u p (μ.restrict s) :=
    MemLp.mono_measure (Measure.restrict_mono_set μ hsΩ) hu
  have hp : MemLp (s.piecewise u 0) p μ :=
    hus.piecewise hs MemLp.zero
  have heq : s.piecewise u 0 =ᵐ[μ] u := by
    filter_upwards [hu0] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs, hx hxs]
  refine ⟨hp.1.congr heq, ?_⟩
  rw [← eLpNorm_congr_ae heq]
  exact hp.2

/-- Scalar multiplication of the encoded weak-`H¹` record. -/
def apm_m01J04_H1smul {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (c : ℝ) (f : apm_m01J04_H1 d Ω) : apm_m01J04_H1 d Ω where
  val := c • f.val
  grad := c • f.grad
  val_memLp := f.val_memLp.const_smul c
  grad_memLp := f.grad_memLp.const_smul c
  weakGradient := by
    intro φ hφ hs hΩ i
    have h := congrArg (fun z : ℝ ↦ c * z) (f.weakGradient φ hφ hs hΩ i)
    simpa [Pi.smul_apply, mul_assoc, MeasureTheory.integral_const_mul] using h

@[simp] lemma apm_m01J04_H1smul_val
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (c : ℝ) (f : apm_m01J04_H1 d Ω) :
    (apm_m01J04_H1smul c f).val = c • f.val := rfl

@[simp] lemma apm_m01J04_H1smul_grad
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (c : ℝ) (f : apm_m01J04_H1 d Ω) :
    (apm_m01J04_H1smul c f).grad = c • f.grad := rfl

lemma apm_m01J04_H1norm_smul
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (c : ℝ) (f : apm_m01J04_H1 d Ω) :
    apm_m01J04_H1norm (apm_m01J04_H1smul c f) =
      |c| * apm_m01J04_H1norm f := by
  simp [apm_m01J04_H1norm, apm_m01J04_H1smul,
    eLpNorm_const_smul, ENNReal.toReal_mul, ← mul_add, Real.norm_eq_abs]

lemma apm_m01J04_H1dist_smul
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (c : ℝ) (f g : apm_m01J04_H1 d Ω) :
    apm_m01J04_H1dist (apm_m01J04_H1smul c f)
      (apm_m01J04_H1smul c g) = |c| * apm_m01J04_H1dist f g := by
  have hv : (fun x ↦ c • f.val x - c • g.val x) =
      c • (fun x ↦ f.val x - g.val x) := by
    funext x
    simp [Pi.smul_apply, mul_sub]
  have hg : (fun x ↦ c • f.grad x - c • g.grad x) =
      c • (fun x ↦ f.grad x - g.grad x) := by
    funext x
    simp [Pi.smul_apply, smul_sub]
  simp only [apm_m01J04_H1dist, apm_m01J04_H1smul, Pi.smul_apply]
  rw [hv, hg, eLpNorm_const_smul, eLpNorm_const_smul,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp [← mul_add, Real.norm_eq_abs]

def apm_m01J04_isH1Zero {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (h : apm_m01J04_H1 d Ω) : Prop :=
  ∃ approximant : ℕ → apm_m01J04_H1 d Ω,
    (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (approximant n).val ∧
      HasCompactSupport (approximant n).val ∧
      Function.support (approximant n).val ⊆ Ω) ∧
    Tendsto (fun n ↦ apm_m01J04_H1dist (approximant n) h) atTop (nhds 0)

lemma apm_m01J04_isH1Zero_smul
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (c : ℝ) (f : apm_m01J04_H1 d Ω)
    (hf : apm_m01J04_isH1Zero f) :
    apm_m01J04_isH1Zero (apm_m01J04_H1smul c f) := by
  obtain ⟨a, ha, hlim⟩ := hf
  refine ⟨fun n ↦ apm_m01J04_H1smul c (a n), ?_, ?_⟩
  · intro n
    refine ⟨(ha n).1.const_smul c, (ha n).2.1.smul_left, ?_⟩
    intro x hx
    apply (ha n).2.2
    contrapose! hx
    simp [Function.notMem_support.mp hx, Pi.smul_apply]
  · simp_rw [apm_m01J04_H1dist_smul]
    simpa using (tendsto_const_nhds.mul hlim : Tendsto
      (fun n ↦ |c| * apm_m01J04_H1dist (a n) f) atTop (nhds (|c| * 0)))

def apm_m01J04_H1WeaklyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u : ℕ → apm_m01J04_H1 d Ω) (w : apm_m01J04_H1 d Ω) : Prop :=
  (∀ q : EuclideanSpace ℝ (Fin d) → ℝ,
    MemLp q 2 (volume.restrict Ω) →
      Tendsto (fun n ↦ ∫ x in Ω, (u n).val x * q x) atTop
        (nhds (∫ x in Ω, w.val x * q x))) ∧
  (∀ q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    MemLp q 2 (volume.restrict Ω) →
      Tendsto (fun n ↦ ∫ x in Ω, inner ℝ ((u n).grad x) (q x)) atTop
        (nhds (∫ x in Ω, inner ℝ (w.grad x) (q x))))

def apm_m01J04_L2StronglyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u : ℕ → apm_m01J04_H1 d Ω) (w : apm_m01J04_H1 d Ω) : Prop :=
  Tendsto (fun n ↦
    (eLpNorm (fun x ↦ (u n).val x - w.val x) 2
      (volume.restrict Ω)).toReal) atTop (nhds 0)

/-- Strong scalar `L²` convergence is preserved after multiplication by a
fixed `L∞` vector field. -/
lemma apm_m01J04_L2StronglyConverges_smul
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hu : apm_m01J04_L2StronglyConverges u w)
    (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hq : MemLp q ⊤ (volume.restrict Ω)) :
    Tendsto (fun n ↦ (eLpNorm (fun x ↦
      ((u n).val x - w.val x) • q x) 2 (volume.restrict Ω)).toReal)
      atTop (nhds 0) := by
  let Q := (eLpNorm q ⊤ (volume.restrict Ω)).toReal
  have hQtop : eLpNorm q ⊤ (volume.restrict Ω) ≠ ⊤ := hq.eLpNorm_ne_top
  have hbound (n : ℕ) :
      (eLpNorm (fun x ↦ ((u n).val x - w.val x) • q x) 2
        (volume.restrict Ω)).toReal ≤
      (eLpNorm (fun x ↦ (u n).val x - w.val x) 2
        (volume.restrict Ω)).toReal * Q := by
    have herr : MemLp (fun x ↦ (u n).val x - w.val x) 2
        (volume.restrict Ω) := (u n).val_memLp.sub w.val_memLp
    have hle := eLpNorm_smul_le_mul_eLpNorm
      (p := 2) (q := ⊤) (r := 2) hq.1 herr.1
    calc
      (eLpNorm (fun x ↦ ((u n).val x - w.val x) • q x) 2
          (volume.restrict Ω)).toReal ≤
          (eLpNorm (fun x ↦ (u n).val x - w.val x) 2
            (volume.restrict Ω) * eLpNorm q ⊤
              (volume.restrict Ω)).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top herr.eLpNorm_ne_top hQtop) hle
      _ = (eLpNorm (fun x ↦ (u n).val x - w.val x) 2
            (volume.restrict Ω)).toReal * Q := by
        rw [ENNReal.toReal_mul]
  apply squeeze_zero (fun n ↦ ENNReal.toReal_nonneg) hbound
  simpa [Q] using (hu.mul tendsto_const_nhds : Tendsto
      (fun n ↦ (eLpNorm (fun x ↦ (u n).val x - w.val x) 2
        (volume.restrict Ω)).toReal * Q) atTop (nhds (0 * Q)))

def apm_m01J04_HasRellichProperty (d : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ u : ℕ → apm_m01J04_H1 d Ω,
    (∃ C : ℝ, ∀ n, apm_m01J04_H1norm (u n) ≤ C) →
      ∃ k : ℕ → ℕ, StrictMono k ∧
        ∃ w : apm_m01J04_H1 d Ω,
          apm_m01J04_H1WeaklyConverges (fun n ↦ u (k n)) w ∧
          apm_m01J04_L2StronglyConverges (fun n ↦ u (k n)) w

def apm_m01J04_L2WeaklyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ n, MemLp (v n) 2 (volume.restrict Ω)) ∧
  MemLp w 2 (volume.restrict Ω) ∧
  ∀ q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    MemLp q 2 (volume.restrict Ω) →
      Tendsto (fun n ↦ ∫ x in Ω, inner ℝ (v n x) (q x)) atTop
        (nhds (∫ x in Ω, inner ℝ (w x) (q x)))

def apm_m01J04_divStronglyConverges {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ h : apm_m01J04_H1 d Ω,
      apm_m01J04_isH1Zero h → apm_m01J04_H1norm h ≤ 1 →
      |∫ x in Ω, inner ℝ (v n x - w x) (h.grad x)| ≤ ε

lemma apm_m01J04_H1WeaklyConverges_subseq
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hu : apm_m01J04_H1WeaklyConverges u w)
    {k : ℕ → ℕ} (hk : StrictMono k) :
    apm_m01J04_H1WeaklyConverges (fun n ↦ u (k n)) w := by
  constructor
  · intro q hq
    exact (hu.1 q hq).comp hk.tendsto_atTop
  · intro q hq
    exact (hu.2 q hq).comp hk.tendsto_atTop

lemma apm_m01J04_L2StronglyConverges_subseq
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hu : apm_m01J04_L2StronglyConverges u w)
    {k : ℕ → ℕ} (hk : StrictMono k) :
    apm_m01J04_L2StronglyConverges (fun n ↦ u (k n)) w :=
  hu.comp hk.tendsto_atTop

/-- The custom real-valued strong `L²` predicate is genuine norm convergence
of the bundled `L²` representatives. -/
lemma apm_m01J04_L2StronglyConverges_toLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hu : apm_m01J04_L2StronglyConverges u w) :
    Tendsto (fun n ↦ (u n).val_memLp.toLp (u n).val) atTop
      (nhds (w.val_memLp.toLp w.val)) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n ↦ (u n).val) (fun n ↦ (u n).val_memLp) w.val w.val_memLp).2
  apply (ENNReal.tendsto_toReal_iff
    (fun n ↦ ((u n).val_memLp.sub w.val_memLp).eLpNorm_ne_top)
    ENNReal.zero_ne_top).1
  simpa [Pi.sub_apply] using hu

/-- The value half of custom weak `H¹` convergence is weak convergence of
the bundled scalar `L²` representatives. -/
lemma apm_m01J04_H1WeaklyConverges_val_toLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hu : apm_m01J04_H1WeaklyConverges u w) :
    apm_m01J04_weaklyConverges
      (fun n ↦ (u n).val_memLp.toLp (u n).val)
      (w.val_memLp.toLp w.val) := by
  intro g
  let q : EuclideanSpace ℝ (Fin d) →₂[volume.restrict Ω] ℝ :=
    (InnerProductSpace.toDual ℝ _).symm g
  have hraw := hu.1 (fun x ↦ q x) (Lp.memLp q)
  have heq (n : ℕ) :
      g ((u n).val_memLp.toLp (u n).val) =
        ∫ x in Ω, (u n).val x * q x := by
    rw [← InnerProductSpace.toDual_symm_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(u n).val_memLp.coeFn_toLp] with x hx
    rw [hx]
    simp [q, real_inner_eq_re_inner, RCLike.inner_apply]
  have heq_lim : g (w.val_memLp.toLp w.val) =
      ∫ x in Ω, w.val x * q x := by
    rw [← InnerProductSpace.toDual_symm_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [w.val_memLp.coeFn_toLp] with x hx
    rw [hx]
    simp [q, real_inner_eq_re_inner, RCLike.inner_apply]
  rw [heq_lim]
  exact hraw.congr' (Filter.Eventually.of_forall (fun n ↦ (heq n).symm))

/-- A strong value limit of an `H¹` sequence agrees in `L²` with its weak
value limit. -/
lemma apm_m01J04_L2Strong_weak_limit_unique
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {z w : apm_m01J04_H1 d Ω}
    (hs : apm_m01J04_L2StronglyConverges u z)
    (hw : apm_m01J04_H1WeaklyConverges u w) :
    z.val_memLp.toLp z.val = w.val_memLp.toLp w.val := by
  apply (NormedSpace.inclusionInDoubleDualLi (E :=
    EuclideanSpace ℝ (Fin d) →₂[volume.restrict Ω] ℝ) ℝ).injective
  ext g
  have hsLp := apm_m01J04_L2StronglyConverges_toLp hs
  have hsPair : Tendsto
      (fun n ↦ g ((u n).val_memLp.toLp (u n).val)) atTop
      (nhds (g (z.val_memLp.toLp z.val))) :=
    (g.continuous.tendsto _).comp hsLp
  have hwPair := apm_m01J04_H1WeaklyConverges_val_toLp hw g
  exact tendsto_nhds_unique hsPair hwPair

lemma apm_m01J04_L2StronglyConverges_congr_limit
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {z w : apm_m01J04_H1 d Ω}
    (hs : apm_m01J04_L2StronglyConverges u z)
    (hzw : z.val_memLp.toLp z.val = w.val_memLp.toLp w.val) :
    apm_m01J04_L2StronglyConverges u w := by
  have hae : z.val =ᵐ[volume.restrict Ω] w.val :=
    (MemLp.toLp_eq_toLp_iff z.val_memLp w.val_memLp).1 hzw
  unfold apm_m01J04_L2StronglyConverges at hs ⊢
  convert hs using 1
  funext n
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards [hae] with x hx
  rw [hx]

lemma apm_m01J04_L2WeaklyConverges_subseq
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v w)
    {k : ℕ → ℕ} (hk : StrictMono k) :
    apm_m01J04_L2WeaklyConverges (Ω := Ω) (fun n ↦ v (k n)) w := by
  refine ⟨fun n ↦ hv.1 (k n), hv.2.1, fun q hq ↦ ?_⟩
  exact (hv.2.2 q hq).comp hk.tendsto_atTop

lemma apm_m01J04_divStronglyConverges_subseq
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hv : apm_m01J04_divStronglyConverges (Ω := Ω) v w)
    {k : ℕ → ℕ} (hk : StrictMono k) :
    apm_m01J04_divStronglyConverges (Ω := Ω) (fun n ↦ v (k n)) w := by
  intro ε hε
  obtain ⟨N, hN⟩ := hv ε hε
  refine ⟨N, fun n hn h hh hnorm ↦ ?_⟩
  exact hN (k n) (le_trans hn (StrictMono.id_le hk n)) h hh hnorm

/-- The unit-ball definition of strong divergence convergence extends to any
fixed positive `H¹` radius. -/
lemma apm_m01J04_divStronglyConverges_on_ball
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hdiv : apm_m01J04_divStronglyConverges (Ω := Ω) v w)
    (B : ℝ) (hB : 0 < B) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : apm_m01J04_H1 d Ω,
        apm_m01J04_isH1Zero h → apm_m01J04_H1norm h ≤ B →
        |∫ x in Ω, inner ℝ (v n x - w x) (h.grad x)| ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hdiv (ε / B) (div_pos hε hB)
  refine ⟨N, fun n hn h hh hhnorm ↦ ?_⟩
  let hs := apm_m01J04_H1smul (1 / B) h
  have hs0 : apm_m01J04_isH1Zero hs :=
    apm_m01J04_isH1Zero_smul (1 / B) h hh
  have hsnorm : apm_m01J04_H1norm hs ≤ 1 := by
    rw [show hs = apm_m01J04_H1smul (1 / B) h by rfl,
      apm_m01J04_H1norm_smul, abs_of_pos (div_pos zero_lt_one hB)]
    exact (mul_le_mul_of_nonneg_left hhnorm (le_of_lt (div_pos zero_lt_one hB))).trans_eq
      (by field_simp)
  have hscaled := hN n hn hs hs0 hsnorm
  have heq : (∫ x in Ω, inner ℝ (v n x - w x) (hs.grad x)) =
      (1 / B) * ∫ x in Ω, inner ℝ (v n x - w x) (h.grad x) := by
    rw [show hs.grad = (1 / B) • h.grad by rfl,
      ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Pi.smul_apply, inner_smul_right]
  rw [heq, abs_mul, abs_of_pos (div_pos zero_lt_one hB)] at hscaled
  apply (div_le_div_iff_of_pos_right hB).mp
  simpa [div_eq_mul_inv, mul_comm] using hscaled

/-- Sequential form of bounded-ball divergence convergence, ready for the
Leibniz decomposition in the compensated-compactness clause. -/
lemma apm_m01J04_divStronglyConverges_pairing
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hdiv : apm_m01J04_divStronglyConverges (Ω := Ω) v w)
    (h : ℕ → apm_m01J04_H1 d Ω)
    (hh : ∀ n, apm_m01J04_isH1Zero (h n))
    (B : ℝ) (hB : 0 < B)
    (hhnorm : ∀ n, apm_m01J04_H1norm (h n) ≤ B) :
    Tendsto (fun n ↦ ∫ x in Ω,
      inner ℝ (v n x - w x) ((h n).grad x)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := apm_m01J04_divStronglyConverges_on_ball
    hdiv B hB (ε / 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
  exact (hN n hn (h n) (hh n) (hhnorm n)).trans_lt (by linarith)

def apm_m01J04_isTestFunction {d : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ Function.support φ ⊆ Ω

/-- The localized value has a genuine global `L²` representative, even when
the ambient domain itself is not assumed measurable.  Its measurable support
is the open nonzero set of the continuous test multiplier. -/
lemma apm_m01J04_test_mul_val_memLp_volume
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    MemLp (fun x ↦ f.val x * φ x) 2 volume := by
  have hφtop : MemLp φ ⊤ (volume.restrict Ω) :=
    hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  have hlocal : MemLp (fun x ↦ f.val x * φ x) 2
      (volume.restrict Ω) := by
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using
      f.val_memLp.smul hφtop
  apply apm_m01J04_memLp_volume_of_support_subset
    hφ.1.continuous.isOpen_support.measurableSet hφ.2.2 hlocal
  intro x hx
  contrapose! hx
  simp [Function.notMem_support.mp hx]

/-- Raw-function `L²` Cauchy--Schwarz, with the real `eLpNorm` presentation
used by the convergence predicates below. -/
lemma apm_m01J04_abs_integral_inner_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure α}
    (f g : α → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  let F : α →₂[μ] E := hf.toLp f
  let G : α →₂[μ] E := hg.toLp g
  have h := abs_real_inner_le_norm F G
  rw [MeasureTheory.L2.inner_def] at h
  have hfg : (∫ x, inner ℝ (F x) (G x) ∂μ) =
      ∫ x, inner ℝ (f x) (g x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
  rw [hfg] at h
  simpa [F, G, Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp,
    eLpNorm_congr_ae hg.coeFn_toLp] using h

lemma apm_m01J04_integrable_inner
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure α}
    (f g : α → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ inner ℝ (f x) (g x)) μ := by
  let F : α →₂[μ] E := hf.toLp f
  let G : α →₂[μ] E := hg.toLp g
  refine (L2.integrable_inner F G).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

lemma apm_m01J04_L2WeaklyConverges_sub_pairing
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v w)
    (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hq : MemLp q 2 (volume.restrict Ω)) :
    Tendsto (fun n ↦ ∫ x in Ω, inner ℝ (v n x - w x) (q x))
      atTop (nhds 0) := by
  have hconv := (hv.2.2 q hq).sub
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ ∫ x in Ω, inner ℝ (w x) (q x)) atTop
      (nhds (∫ x in Ω, inner ℝ (w x) (q x))))
  convert hconv using 1
  · funext n
    simp_rw [inner_sub_left]
    rw [MeasureTheory.integral_sub
      (apm_m01J04_integrable_inner _ _ (hv.1 n) hq)
      (apm_m01J04_integrable_inner _ _ hv.2.1 hq)]
  · simp

/-- Pointwise weak convergence in raw `L²` pairings supplies a uniform norm
bound, via Riesz representation and uniform boundedness. -/
lemma apm_m01J04_weak_L2_uniform_bound
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure α}
    (f : ℕ → α → E) (w : α → E)
    (hf : ∀ n, MemLp (f n) 2 μ)
    (hweak : ∀ q : α → E, MemLp q 2 μ →
      Tendsto (fun n ↦ ∫ x, inner ℝ (f n x) (q x) ∂μ) atTop
        (nhds (∫ x, inner ℝ (w x) (q x) ∂μ))) :
    ∃ C : ℝ, ∀ n, (eLpNorm (f n) 2 μ).toReal ≤ C := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : CompleteSpace (α →₂[μ] E) := MeasureTheory.Lp.instCompleteSpace
  let F : ℕ → α →₂[μ] E := fun n ↦ (hf n).toLp (f n)
  have hpoint : ∀ q : α →₂[μ] E, ∃ C : ℝ, ∀ n,
      ‖(innerSL ℝ (F n)) q‖ ≤ C := by
    intro q
    have ht := hweak (fun x ↦ q x) (Lp.memLp q)
    have heq (n : ℕ) : (innerSL ℝ (F n)) q =
        ∫ x, inner ℝ (f n x) (q x) ∂μ := by
      rw [innerSL_apply_apply, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hf n).coeFn_toLp] with x hx
      rw [show F n x = f n x by exact hx]
    have ht' : Tendsto (fun n ↦ (innerSL ℝ (F n)) q) atTop
        (nhds (∫ x, inner ℝ (w x) (q x) ∂μ)) :=
      ht.congr' (Filter.Eventually.of_forall (fun n ↦ (heq n).symm))
    obtain ⟨C, hC⟩ :=
      (Metric.isBounded_range_of_tendsto _ ht').exists_norm_le
    exact ⟨C, fun n ↦ hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun n ↦ innerSL ℝ (F n)) hpoint
  refine ⟨C, fun n ↦ ?_⟩
  have hn := hC n
  rw [innerSL_apply_norm] at hn
  simpa [F, Lp.norm_def, eLpNorm_congr_ae (hf n).coeFn_toLp] using hn

lemma apm_m01J04_H1WeaklyConverges_uniform_norm
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hf : apm_m01J04_H1WeaklyConverges f w) :
    ∃ C : ℝ, ∀ n, apm_m01J04_H1norm (f n) ≤ C := by
  obtain ⟨Cv, hCv⟩ := apm_m01J04_weak_L2_uniform_bound
    (fun n ↦ (f n).val) w.val (fun n ↦ (f n).val_memLp) (by
      intro q hq
      simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using hf.1 q hq)
  obtain ⟨Cg, hCg⟩ := apm_m01J04_weak_L2_uniform_bound
    (fun n ↦ (f n).grad) w.grad (fun n ↦ (f n).grad_memLp) hf.2
  refine ⟨Cv + Cg, fun n ↦ ?_⟩
  exact add_le_add (hCv n) (hCg n)

lemma apm_m01J04_L2WeaklyConverges_uniform_sub_norm
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v w) :
    ∃ C : ℝ, ∀ n,
      (eLpNorm (fun x ↦ v n x - w x) 2 (volume.restrict Ω)).toReal ≤ C := by
  obtain ⟨Cv, hCv⟩ := apm_m01J04_weak_L2_uniform_bound
    v w hv.1 hv.2.2
  let W := (eLpNorm w 2 (volume.restrict Ω)).toReal
  refine ⟨Cv + W, fun n ↦ ?_⟩
  have hle : eLpNorm (fun x ↦ v n x - w x) 2 (volume.restrict Ω) ≤
      eLpNorm (v n) 2 (volume.restrict Ω) +
        eLpNorm w 2 (volume.restrict Ω) := by
    simpa [Pi.sub_apply] using eLpNorm_sub_le
      (p := (2 : ℝ≥0∞)) (hv.1 n).1 hv.2.1.1 (by norm_num)
  calc
    (eLpNorm (fun x ↦ v n x - w x) 2
        (volume.restrict Ω)).toReal ≤
        (eLpNorm (v n) 2 (volume.restrict Ω) +
          eLpNorm w 2 (volume.restrict Ω)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨(hv.1 n).eLpNorm_ne_top, hv.2.1.eLpNorm_ne_top⟩) hle
    _ = (eLpNorm (v n) 2 (volume.restrict Ω)).toReal + W := by
      rw [ENNReal.toReal_add]
      · exact (hv.1 n).eLpNorm_ne_top
      · exact hv.2.1.eLpNorm_ne_top
    _ ≤ Cv + W := add_le_add (hCv n) le_rfl

lemma apm_m01J04_strong_value_weak_field_error
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : apm_m01J04_L2StronglyConverges f fLim)
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v vLim)
    (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hq : MemLp q ⊤ (volume.restrict Ω)) :
    Tendsto (fun n ↦ ∫ x in Ω,
      inner ℝ (v n x - vLim x) (((f n).val x - fLim.val x) • q x))
      atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := apm_m01J04_L2WeaklyConverges_uniform_sub_norm hv
  have hC0 : 0 ≤ C := le_trans ENNReal.toReal_nonneg (hC 0)
  have hstrong := apm_m01J04_L2StronglyConverges_smul hf q hq
  have hbound (n : ℕ) :
      |∫ x in Ω, inner ℝ (v n x - vLim x)
        (((f n).val x - fLim.val x) • q x)| ≤
      C * (eLpNorm (fun x ↦ ((f n).val x - fLim.val x) • q x) 2
        (volume.restrict Ω)).toReal := by
    have hvsub : MemLp (fun x ↦ v n x - vLim x) 2
        (volume.restrict Ω) := (hv.1 n).sub hv.2.1
    have hfq : MemLp (fun x ↦ ((f n).val x - fLim.val x) • q x) 2
        (volume.restrict Ω) := by
      simpa [smul_comm] using hq.smul ((f n).val_memLp.sub fLim.val_memLp)
    refine (apm_m01J04_abs_integral_inner_le _ _ hvsub hfq).trans ?_
    exact mul_le_mul_of_nonneg_right (hC n) ENNReal.toReal_nonneg
  rw [Metric.tendsto_atTop] at hstrong ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hstrong (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
  refine lt_of_le_of_lt (hbound n) ?_
  calc
    C * (eLpNorm (fun x ↦ ((f n).val x - fLim.val x) • q x) 2
        (volume.restrict Ω)).toReal ≤ C * (ε / (C + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact le_of_lt (by simpa [dist_eq_norm, Real.norm_eq_abs] using hN n hn)
    _ < ε := by
      calc
        C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one C) (by positivity)
        _ = ε := by field_simp

/-- Every subsequence of a weakly convergent `H¹` sequence has a Rellich
refinement converging strongly to the prescribed weak value limit. -/
lemma apm_m01J04_rellich_refine_subseq
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hrel : apm_m01J04_HasRellichProperty d Ω)
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    (hf : apm_m01J04_H1WeaklyConverges f fLim)
    {s : ℕ → ℕ} (hs : StrictMono s) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      apm_m01J04_L2StronglyConverges (fun n ↦ f (s (k n))) fLim := by
  obtain ⟨C, hC⟩ := apm_m01J04_H1WeaklyConverges_uniform_norm hf
  obtain ⟨k, hk, z, hweakz, hstrongz⟩ := hrel (fun n ↦ f (s n))
    ⟨C, fun n ↦ hC (s n)⟩
  have hweakLim : apm_m01J04_H1WeaklyConverges
      (fun n ↦ f (s (k n))) fLim :=
    apm_m01J04_H1WeaklyConverges_subseq
      (apm_m01J04_H1WeaklyConverges_subseq hf hs) hk
  have heq := apm_m01J04_L2Strong_weak_limit_unique hstrongz hweakLim
  exact ⟨k, hk, apm_m01J04_L2StronglyConverges_congr_limit hstrongz heq⟩

/-- Rellich compactness upgrades the refined strong-error estimate to the full
sequence by the subsequence criterion. -/
lemma apm_m01J04_variable_lower_order_tendsto_zero
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hrel : apm_m01J04_HasRellichProperty d Ω)
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : apm_m01J04_H1WeaklyConverges f fLim)
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v vLim)
    (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hq : MemLp q ⊤ (volume.restrict Ω)) :
    Tendsto (fun n ↦ ∫ x in Ω,
      inner ℝ (v n x - vLim x) (((f n).val x - fLim.val x) • q x))
      atTop (nhds 0) := by
  refine tendsto_of_subseq_tendsto (l := atTop) fun s hs ↦ ?_
  obtain ⟨r, hr, hsr⟩ := strictMono_subseq_of_tendsto_atTop hs
  obtain ⟨k, hk, hstrong⟩ :=
    apm_m01J04_rellich_refine_subseq hrel hf hsr
  refine ⟨r ∘ k, ?_⟩
  have hvsub := apm_m01J04_L2WeaklyConverges_subseq
    (apm_m01J04_L2WeaklyConverges_subseq hv hsr) hk
  simpa [Function.comp_apply] using
    apm_m01J04_strong_value_weak_field_error hstrong hvsub q hq

lemma apm_m01J04_abs_integral_mul_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using
    apm_m01J04_abs_integral_inner_le f g hf hg

/-- Each `L²` component is bounded by the encoded `H¹` norm bound. -/
lemma apm_m01J04_component_norm_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (f : apm_m01J04_H1 d Ω) {C : ℝ}
    (hf : apm_m01J04_H1norm f ≤ C) :
    (eLpNorm f.val 2 (volume.restrict Ω)).toReal ≤ C ∧
    (eLpNorm f.grad 2 (volume.restrict Ω)).toReal ≤ C := by
  unfold apm_m01J04_H1norm at hf
  constructor <;> nlinarith
    [ENNReal.toReal_nonneg (a := eLpNorm f.val 2 (volume.restrict Ω)),
      ENNReal.toReal_nonneg (a := eLpNorm f.grad 2 (volume.restrict Ω))]

/-- An encoded `H¹` bound supplies the uniform gradient bound used for the
strong-error term in the Rellich pairing. -/
lemma apm_m01J04_uniform_grad_norm
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω}
    (hu : ∃ C : ℝ, ∀ n, apm_m01J04_H1norm (u n) ≤ C) :
    ∃ C : ℝ, ∀ n,
      (eLpNorm (u n).grad 2 (volume.restrict Ω)).toReal ≤ C := by
  obtain ⟨C, hC⟩ := hu
  exact ⟨C, fun n ↦ (apm_m01J04_component_norm_le (u n) (hC n)).2⟩

/-- The fixed field occurring in the weak-gradient half of the Rellich
decomposition is an admissible `L²` test. -/
lemma apm_m01J04_val_smul_memLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (w : apm_m01J04_H1 d Ω)
    (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hq : MemLp q ⊤ (volume.restrict Ω)) :
    MemLp (fun x ↦ w.val x • q x) 2 (volume.restrict Ω) := by
  simpa [smul_comm] using hq.smul w.val_memLp

/-- The strong-value error in the Rellich nonlinear pairing vanishes against
any uniformly `L²`-bounded gradient sequence. -/
lemma apm_m01J04_rellich_error_tendsto_zero
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hu : apm_m01J04_L2StronglyConverges u w)
    (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hq : MemLp q ⊤ (volume.restrict Ω))
    (C : ℝ) (hC : ∀ n,
      (eLpNorm (u n).grad 2 (volume.restrict Ω)).toReal ≤ C) :
    Tendsto (fun n ↦ ∫ x in Ω,
      inner ℝ ((u n).grad x) (((u n).val x - w.val x) • q x))
      atTop (nhds 0) := by
  have hstrong := apm_m01J04_L2StronglyConverges_smul hu q hq
  have hC0 : 0 ≤ C := le_trans ENNReal.toReal_nonneg (hC 0)
  have hbound (n : ℕ) :
      |∫ x in Ω,
        inner ℝ ((u n).grad x) (((u n).val x - w.val x) • q x)| ≤
      C * (eLpNorm (fun x ↦ ((u n).val x - w.val x) • q x) 2
        (volume.restrict Ω)).toReal := by
    have herr : MemLp (fun x ↦ ((u n).val x - w.val x) • q x) 2
        (volume.restrict Ω) := by
      simpa [smul_comm] using hq.smul ((u n).val_memLp.sub w.val_memLp)
    refine (apm_m01J04_abs_integral_inner_le _ _ (u n).grad_memLp
      herr).trans ?_
    exact mul_le_mul_of_nonneg_right (hC n) ENNReal.toReal_nonneg
  rw [Metric.tendsto_atTop] at hstrong ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hstrong (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
  refine lt_of_le_of_lt (hbound n) ?_
  calc
    C * (eLpNorm (fun x ↦ ((u n).val x - w.val x) • q x) 2
        (volume.restrict Ω)).toReal ≤ C * (ε / (C + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact le_of_lt (by
        simpa [dist_eq_norm, Real.norm_eq_abs] using hN n hn)
    _ < ε := by
      calc
        C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) := by
          exact mul_lt_mul_of_pos_right (lt_add_one C) (by positivity)
        _ = ε := by field_simp

/-- Strong convergence of values plus weak convergence of gradients gives the
nonlinear Rellich pairing limit against a fixed bounded vector field. -/
lemma apm_m01J04_rellich_pairing
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → apm_m01J04_H1 d Ω} {w : apm_m01J04_H1 d Ω}
    (hweak : apm_m01J04_H1WeaklyConverges u w)
    (hstrong : apm_m01J04_L2StronglyConverges u w)
    (C : ℝ) (hC : ∀ n,
      (eLpNorm (u n).grad 2 (volume.restrict Ω)).toReal ≤ C)
    (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hq : MemLp q ⊤ (volume.restrict Ω)) :
    Tendsto (fun n ↦ ∫ x in Ω,
      (u n).val x * inner ℝ ((u n).grad x) (q x)) atTop
      (nhds (∫ x in Ω, w.val x * inner ℝ (w.grad x) (q x))) := by
  let qfixed := fun x ↦ w.val x • q x
  have hqfixed : MemLp qfixed 2 (volume.restrict Ω) :=
    apm_m01J04_val_smul_memLp w q hq
  have herr := apm_m01J04_rellich_error_tendsto_zero
    hstrong q hq C hC
  have hwk := hweak.2 qfixed hqfixed
  convert herr.add hwk using 1
  · funext n
    have he : Integrable (fun x ↦ inner ℝ ((u n).grad x)
        (((u n).val x - w.val x) • q x)) (volume.restrict Ω) :=
      apm_m01J04_integrable_inner _ _ (u n).grad_memLp (by
        simpa [smul_comm] using hq.smul ((u n).val_memLp.sub w.val_memLp))
    have hf : Integrable (fun x ↦ inner ℝ ((u n).grad x) (qfixed x))
        (volume.restrict Ω) :=
      apm_m01J04_integrable_inner _ _ (u n).grad_memLp hqfixed
    rw [← MeasureTheory.integral_add he hf]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [qfixed, inner_smul_right]
    ring
  · simp only [zero_add]
    apply congrArg nhds
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [qfixed, inner_smul_right]

/-- A test function in the custom encoding has a global pointwise bound.
This is the scalar multiplier bound needed in the `L²` part of the product
construction. -/
lemma apm_m01J04_isTestFunction_exists_abs_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |φ x| ≤ C := by
  have hb : BddAbove ((fun x ↦ |φ x|) '' tsupport φ) :=
    hφ.2.1.bddAbove_image hφ.1.continuous.abs.continuousOn
  obtain ⟨C, hC⟩ := bddAbove_def.mp hb
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  by_cases hx : x ∈ Function.support φ
  · exact (hC _ ⟨x, subset_closure hx, rfl⟩).trans (le_max_left _ _)
  · have hzero : φ x = 0 := Function.notMem_support.mp hx
    simp [hzero, le_max_right C 0]

/-- The full derivative field of a test function is globally bounded.  Keeping
the estimate at the operator-norm level avoids a separate compactness argument
for every coordinate and is the form needed by the multiplier construction. -/
lemma apm_m01J04_isTestFunction_exists_fderiv_norm_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (hφ.2.1.fderiv ℝ).exists_bound_of_continuous
      (hφ.1.continuous_fderiv (by simp))
  refine ⟨max C 0, le_max_right _ _, fun x ↦ (hC x).trans (le_max_left _ _)⟩

/-- Coordinate derivatives inherit the uniform operator-norm bound. -/
lemma apm_m01J04_isTestFunction_exists_fderiv_apply_abs_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x (i : Fin d),
      |fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := apm_m01J04_isTestFunction_exists_fderiv_norm_le hφ
  refine ⟨C, hC0, fun x i ↦ ?_⟩
  rw [← Real.norm_eq_abs]
  calc
    ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ≤
        ‖fderiv ℝ φ x‖ * ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin d))‖ :=
      (fderiv ℝ φ x).le_opNorm _
    _ = ‖fderiv ℝ φ x‖ := by simp
    _ ≤ C := hC x

/-- The coordinate presentation of the derivative used in `bridge_1` is an
`L²` field.  This packages continuity and compact support before the later
Hölder estimates. -/
lemma apm_m01J04_isTestFunction_fderivField_memLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ) (p : ℝ≥0∞) :
    MemLp (fun x ↦ WithLp.toLp 2
      (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) p
      (volume.restrict Ω) := by
  let D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x ↦ WithLp.toLp 2
      (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
  have hDcont : Continuous D := by
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp
      (continuous_pi fun i ↦
        (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDsupp : HasCompactSupport D := by
    apply (hφ.2.1.fderiv ℝ).mono'
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
    have hz : fderiv ℝ φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    ext i
    simp [D, hz]
  exact hDcont.memLp_of_hasCompactSupport hDsupp

/-- The complete lower-order term in the localized Leibniz rule vanishes:
Rellich handles the varying value error, and weak `L²` convergence handles
the fixed limit-value field. -/
lemma apm_m01J04_lower_order_tendsto_zero
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hrel : apm_m01J04_HasRellichProperty d Ω)
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : apm_m01J04_H1WeaklyConverges f fLim)
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v vLim)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    Tendsto (fun n ↦ ∫ x in Ω, inner ℝ (v n x - vLim x)
      ((f n).val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))))
      atTop (nhds 0) := by
  let D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x ↦ WithLp.toLp 2
      (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
  have hDtop : MemLp D ⊤ (volume.restrict Ω) :=
    apm_m01J04_isTestFunction_fderivField_memLp hφ ⊤
  have hfixed : MemLp (fun x ↦ fLim.val x • D x) 2
      (volume.restrict Ω) := by
    simpa [smul_comm] using hDtop.smul fLim.val_memLp
  have hvar := apm_m01J04_variable_lower_order_tendsto_zero
    hrel hf hv D hDtop
  have hconst := apm_m01J04_L2WeaklyConverges_sub_pairing hv _ hfixed
  convert hvar.add hconst using 1
  · funext n
    have hvsub : MemLp (fun x ↦ v n x - vLim x) 2
        (volume.restrict Ω) := (hv.1 n).sub hv.2.1
    have he : MemLp (fun x ↦ ((f n).val x - fLim.val x) • D x) 2
        (volume.restrict Ω) := by
      simpa [smul_comm] using hDtop.smul ((f n).val_memLp.sub fLim.val_memLp)
    rw [← MeasureTheory.integral_add
      (apm_m01J04_integrable_inner _ _ hvsub he)
      (apm_m01J04_integrable_inner _ _ hvsub hfixed)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [D]
    rw [← inner_add_right, ← add_smul]
    simp
  · simp

/-- Both fields prescribed for the product record in `bridge_1` satisfy its
raw `L²` requirements.  The key exponent choice is `L∞` for both smooth
test-function factors, so each may multiply one of the original `L²` fields. -/
lemma apm_m01J04_test_mul_fields_memLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    MemLp (fun x ↦ f.val x * φ x) 2 (volume.restrict Ω) ∧
    MemLp (fun x ↦
      φ x • f.grad x +
        f.val x • WithLp.toLp 2
          (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2
      (volume.restrict Ω) := by
  have hφtop : MemLp φ ⊤ (volume.restrict Ω) :=
    hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  have hDtop := apm_m01J04_isTestFunction_fderivField_memLp hφ ⊤
  constructor
  · simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using f.val_memLp.smul hφtop
  · exact (f.grad_memLp.smul hφtop).add (hDtop.smul f.val_memLp)

/-- The precise level-set regularity fact needed to globalize a localized
weak gradient.  It is stated for the bundled coordinate derivative field used
throughout this development. -/
def apm_m01J04_AEDerivativeZeroOnZeroSet {d : ℕ}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ᵐ x ∂volume, φ x = 0 →
    WithLp.toLp 2 (fun i ↦
      fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0

lemma apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet
    {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    apm_m01J04_AEDerivativeZeroOnZeroSet φ := by
  by_cases hd : d = 0
  · subst d
    filter_upwards [] with x
    intro hx
    exact Subsingleton.elim _ _
  · let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i0 1
    let s : Set (EuclideanSpace ℝ (Fin d)) := {x | φ x = 0}
    let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
      fun x ↦ φ x • e
    have hs : MeasurableSet s := by
      change MeasurableSet (φ ⁻¹' {0})
      exact hφ.continuous.measurable (measurableSet_singleton (0 : ℝ))
    have happ : ApproximatesLinearOn F
        (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) s 0 := by
      intro x hx y hy
      simp [F, s] at hx hy ⊢
      simp [hx, hy]
    have hder : ∀ x ∈ s, HasFDerivWithinAt F
        ((fderiv ℝ φ x).smulRight e) s x := by
      intro x hx
      exact ((hφ.differentiable (by simp) x).hasFDerivAt.smul_const e).hasFDerivWithinAt
    have hae := happ.norm_fderiv_sub_le volume hs
      (fun x ↦ (fderiv ℝ φ x).smulRight e) hder
    rw [MeasureTheory.ae_restrict_iff' hs] at hae
    filter_upwards [hae] with x hx
    intro hφx
    have hxs : x ∈ s := hφx
    have hnorm := hx hxs
    have hmap : (fderiv ℝ φ x).smulRight e = 0 := by
      apply nnnorm_eq_zero.mp
      exact le_antisymm (by simpa using hnorm) (zero_le _)
    rw [WithLp.toLp_eq_zero]
    funext i
    have happly := congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ]
        EuclideanSpace ℝ (Fin d) ↦ (L (EuclideanSpace.single i 1)) i0) hmap
    simpa [e, i0] using happly

/-- Once the derivative of the multiplier is known to vanish almost
everywhere on its zero set, the full Leibniz gradient globalizes to `L²`. -/
lemma apm_m01J04_test_mul_grad_memLp_volume_of_ae_zero
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    (hD0 : apm_m01J04_AEDerivativeZeroOnZeroSet φ) :
    MemLp (fun x ↦
      φ x • f.grad x + f.val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2 volume := by
  have hlocal := (apm_m01J04_test_mul_fields_memLp φ hφ f).2
  apply apm_m01J04_memLp_of_ae_eq_zero_outside
    hφ.1.continuous.isOpen_support.measurableSet hφ.2.2 hlocal
  filter_upwards [hD0] with x hx
  intro hxs
  have hφx : φ x = 0 := Function.notMem_support.mp hxs
  simp [hφx, hx hφx]

lemma apm_m01J04_test_mul_grad_memLp_volume
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    MemLp (fun x ↦
      φ x • f.grad x + f.val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2 volume :=
  apm_m01J04_test_mul_grad_memLp_volume_of_ae_zero φ hφ f
    (apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet hφ.1)

/-- The localized weak-Sobolev pair is globally square-integrable.  These are
the two raw fields to which one common approximate identity must be applied. -/
lemma apm_m01J04_test_mul_fields_memLp_volume
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    MemLp (fun x ↦ f.val x * φ x) 2 volume ∧
    MemLp (fun x ↦
      φ x • f.grad x + f.val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2 volume :=
  ⟨apm_m01J04_test_mul_val_memLp_volume φ hφ f,
    apm_m01J04_test_mul_grad_memLp_volume φ hφ f⟩

lemma apm_m01J04_test_mul_fields_locallyIntegrable
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    LocallyIntegrable (fun x ↦ f.val x * φ x) volume ∧
    LocallyIntegrable (fun x ↦
      φ x • f.grad x + f.val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) volume := by
  obtain ⟨hv, hg⟩ := apm_m01J04_test_mul_fields_memLp_volume φ hφ f
  exact ⟨hv.locallyIntegrable (by norm_num), hg.locallyIntegrable (by norm_num)⟩

/-- An integrand which vanishes almost everywhere off a measurable subset of
the domain has the same global and restricted integrals.  The intermediate
restriction to `s` avoids any measurability assumption on the ambient set
`Ω`, which is deliberately absent from the problem statement. -/
lemma apm_m01J04_integral_eq_restrict_of_ae_zero_outside
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure α} {Ω s : Set α} {u : α → E}
    (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (hu0 : ∀ᵐ x ∂μ, x ∉ s → u x = 0) :
    (∫ x, u x ∂μ) = ∫ x in Ω, u x ∂μ := by
  classical
  have hind : s.indicator u =ᵐ[μ] u := by
    filter_upwards [hu0] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs, hx hxs]
  calc
    (∫ x, u x ∂μ) = ∫ x, s.indicator u x ∂μ :=
      integral_congr_ae hind.symm
    _ = ∫ x in s, u x ∂μ := integral_indicator hs
    _ = ∫ x in Ω, s.indicator u x ∂μ := by
      rw [integral_indicator hs, Measure.restrict_restrict_of_subset hsΩ]
    _ = ∫ x in Ω, u x ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hind)

/-- The exact Leibniz gradient vanishes almost everywhere away from the
nonzero set of the compactly supported multiplier. -/
lemma apm_m01J04_test_mul_grad_ae_zero_outside
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    ∀ᵐ x ∂volume, x ∉ Function.support φ →
      φ x • f.grad x + f.val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 := by
  have hD0 := apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet hφ.1
  filter_upwards [hD0] with x hx
  intro hxs
  have hφx : φ x = 0 := Function.notMem_support.mp hxs
  simp [hφx, hx hφx]


/-- The bespoke test-function predicate is closed under multiplication.  The
support is routed through the second factor so its `Ω` containment is retained. -/
lemma apm_m01J04_isTestFunction_mul
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (hψ : apm_m01J04_isTestFunction Ω ψ) :
    apm_m01J04_isTestFunction Ω (fun x ↦ φ x * ψ x) := by
  refine ⟨hφ.1.mul hψ.1, hφ.2.1.mul_right, ?_⟩
  intro x hx
  apply hψ.2.2
  contrapose! hx
  simp [Function.notMem_support.mp hx]

/-- Multiplication retains the support of the first factor; hence the second
factor need only be smooth and compactly supported, not supported in `Ω`. -/
lemma apm_m01J04_isTestFunction_mul_right
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (hψdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψcompact : HasCompactSupport ψ) :
    apm_m01J04_isTestFunction Ω (fun x ↦ φ x * ψ x) := by
  refine ⟨hφ.1.mul hψdiff, hψcompact.mul_left, ?_⟩
  intro x hx
  apply hφ.2.2
  contrapose! hx
  simp [Function.notMem_support.mp hx]

/-- Coordinate form of the product rule, matching the exact derivative
presentation in `apm_m01J04_H1.weakGradient`. -/
lemma apm_m01J04_fderiv_mul_apply
    {d : ℕ} {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    fderiv ℝ (fun y ↦ φ y * ψ y) x (EuclideanSpace.single i 1) =
      φ x * fderiv ℝ ψ x (EuclideanSpace.single i 1) +
        ψ x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  have hprod : fderiv ℝ (fun y ↦ φ y * ψ y) x =
      φ x • fderiv ℝ ψ x + ψ x • fderiv ℝ φ x :=
    fderiv_fun_mul (x := x)
      (hφ.differentiable (by simp)).differentiableAt
      (hψ.differentiable (by simp)).differentiableAt
  have h := congrArg
    (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i 1))
    hprod
  simpa [ContinuousLinearMap.add_apply, smul_eq_mul] using h

/-- Every coordinate derivative of a test function belongs to every `L^p` on
the restricted domain.  This is the scalar interface used in the forthcoming
integral splitting. -/
lemma apm_m01J04_isTestFunction_fderiv_apply_memLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ) (p : ℝ≥0∞) (i : Fin d) :
    MemLp (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) p
      (volume.restrict Ω) := by
  simpa using
    (apm_m01J04_isTestFunction_fderivField_memLp hφ p).continuousLinearMap_comp
      (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d ↦ ℝ) i)

/-- Scalar coordinates of an encoded weak gradient retain its `L²` bound. -/
lemma apm_m01J04_H1_grad_apply_memLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (f : apm_m01J04_H1 d Ω) (i : Fin d) :
    MemLp (fun x ↦ f.grad x i) 2 (volume.restrict Ω) := by
  simpa using f.grad_memLp.continuousLinearMap_comp
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d ↦ ℝ) i)

/-- A test function belongs to every `L^p` on the restricted domain. -/
lemma apm_m01J04_isTestFunction_memLp
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : apm_m01J04_isTestFunction Ω φ) (p : ℝ≥0∞) :
    MemLp φ p (volume.restrict Ω) :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1

/-- Subtraction in the custom weak-Sobolev encoding. -/
noncomputable def apm_m01J04_H1sub {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u w : apm_m01J04_H1 d Ω) : apm_m01J04_H1 d Ω where
  val := fun x ↦ u.val x - w.val x
  grad := fun x ↦ u.grad x - w.grad x
  val_memLp := u.val_memLp.sub w.val_memLp
  grad_memLp := u.grad_memLp.sub w.grad_memLp
  weakGradient := by
    intro φ hφdiff hφcompact hφsupport i
    have hφ : apm_m01J04_isTestFunction Ω φ :=
      ⟨hφdiff, hφcompact, hφsupport⟩
    have hdφ2 := apm_m01J04_isTestFunction_fderiv_apply_memLp hφ 2 i
    have hφ2 := apm_m01J04_isTestFunction_memLp hφ 2
    have huD : Integrable (fun x ↦
        u.val x * fderiv ℝ φ x (EuclideanSpace.single i 1))
        (volume.restrict Ω) := memLp_one_iff_integrable.mp (by
      simpa [mul_comm] using u.val_memLp.mul' hdφ2)
    have hwD : Integrable (fun x ↦
        w.val x * fderiv ℝ φ x (EuclideanSpace.single i 1))
        (volume.restrict Ω) := memLp_one_iff_integrable.mp (by
      simpa [mul_comm] using w.val_memLp.mul' hdφ2)
    have huG : Integrable (fun x ↦ u.grad x i * φ x)
        (volume.restrict Ω) := memLp_one_iff_integrable.mp (by
      simpa [mul_comm] using (apm_m01J04_H1_grad_apply_memLp u i).mul' hφ2)
    have hwG : Integrable (fun x ↦ w.grad x i * φ x)
        (volume.restrict Ω) := memLp_one_iff_integrable.mp (by
      simpa [mul_comm] using (apm_m01J04_H1_grad_apply_memLp w i).mul' hφ2)
    rw [show (∫ x in Ω, (u.val x - w.val x) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (∫ x in Ω, u.val x * fderiv ℝ φ x (EuclideanSpace.single i 1)) -
        (∫ x in Ω, w.val x * fderiv ℝ φ x (EuclideanSpace.single i 1)) by
      rw [← MeasureTheory.integral_sub huD hwD]
      apply integral_congr_ae
      filter_upwards [] with x
      ring]
    rw [show (∫ x in Ω, (u.grad x - w.grad x) i * φ x) =
        (∫ x in Ω, u.grad x i * φ x) -
        (∫ x in Ω, w.grad x i * φ x) by
      rw [← MeasureTheory.integral_sub huG hwG]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.sub_apply]
      ring]
    rw [u.weakGradient φ hφdiff hφcompact hφsupport i,
      w.weakGradient φ hφdiff hφcompact hφsupport i]
    ring

@[simp] lemma apm_m01J04_H1sub_val
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u w : apm_m01J04_H1 d Ω) :
    (apm_m01J04_H1sub u w).val = fun x ↦ u.val x - w.val x := rfl

@[simp] lemma apm_m01J04_H1sub_grad
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u w : apm_m01J04_H1 d Ω) :
    (apm_m01J04_H1sub u w).grad = fun x ↦ u.grad x - w.grad x := rfl

lemma apm_m01J04_H1norm_sub_eq_dist
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (u w : apm_m01J04_H1 d Ω) :
    apm_m01J04_H1norm (apm_m01J04_H1sub u w) = apm_m01J04_H1dist u w := rfl

/-- The three terms occurring after expanding the weak derivative of `φ * ψ`
are integrable.  This is exactly the side-condition bundle required by
`integral_add` in the weak Leibniz proof. -/
lemma apm_m01J04_weakLeibniz_integrable
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (hψdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψcompact : HasCompactSupport ψ)
    (f : apm_m01J04_H1 d Ω) (i : Fin d) :
    Integrable (fun x ↦ f.val x *
      (φ x * fderiv ℝ ψ x (EuclideanSpace.single i 1)))
        (volume.restrict Ω) ∧
    Integrable (fun x ↦ f.val x *
      (ψ x * fderiv ℝ φ x (EuclideanSpace.single i 1)))
        (volume.restrict Ω) ∧
    Integrable (fun x ↦ f.grad x i * (φ x * ψ x))
        (volume.restrict Ω) := by
  have hφtop := apm_m01J04_isTestFunction_memLp hφ ⊤
  have hψU : apm_m01J04_isTestFunction Set.univ ψ :=
    ⟨hψdiff, hψcompact, Set.subset_univ _⟩
  have hψtopVol : MemLp ψ ⊤ volume := by
    simpa using apm_m01J04_isTestFunction_memLp hψU ⊤
  have hψtop : MemLp ψ ⊤ (volume.restrict Ω) :=
    hψtopVol.mono_measure Measure.restrict_le_self
  have hψ2Vol : MemLp ψ 2 volume := by
    simpa using apm_m01J04_isTestFunction_memLp hψU 2
  have hψ2 : MemLp ψ 2 (volume.restrict Ω) :=
    hψ2Vol.mono_measure Measure.restrict_le_self
  have hdφ2 := apm_m01J04_isTestFunction_fderiv_apply_memLp hφ 2 i
  have hdψ2Vol : MemLp (fun x ↦
      fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 volume := by
    simpa using apm_m01J04_isTestFunction_fderiv_apply_memLp hψU 2 i
  have hdψ2 : MemLp (fun x ↦
      fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) :=
    hdψ2Vol.mono_measure Measure.restrict_le_self
  have hφdψ2 : MemLp (fun x ↦ φ x *
      fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hdψ2.smul hφtop
  have hψdφ2 : MemLp (fun x ↦ ψ x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hdφ2.smul hψtop
  have hφψ2 : MemLp (fun x ↦ φ x * ψ x) 2 (volume.restrict Ω) := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      hψ2.smul hφtop
  refine ⟨memLp_one_iff_integrable.mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using f.val_memLp.mul' hφdψ2),
    memLp_one_iff_integrable.mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using f.val_memLp.mul' hψdφ2), ?_⟩
  exact memLp_one_iff_integrable.mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (apm_m01J04_H1_grad_apply_memLp f i).mul' hφψ2)

/-- Weak Leibniz identity in the exact scalar-coordinate form needed to fill
the `weakGradient` field of the product record. -/
lemma apm_m01J04_weakLeibniz
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (hψdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψcompact : HasCompactSupport ψ)
    (f : apm_m01J04_H1 d Ω) (i : Fin d) :
    (∫ x in Ω, (f.val x * φ x) *
      fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -(∫ x in Ω,
        (φ x * f.grad x i +
          f.val x * fderiv ℝ φ x (EuclideanSpace.single i 1)) * ψ x) := by
  obtain ⟨hA, hB, hC⟩ :=
    apm_m01J04_weakLeibniz_integrable φ ψ hφ hψdiff hψcompact f i
  have hweak := f.weakGradient (fun x ↦ φ x * ψ x)
    (apm_m01J04_isTestFunction_mul_right hφ hψdiff hψcompact).1
    (apm_m01J04_isTestFunction_mul_right hφ hψdiff hψcompact).2.1
    (apm_m01J04_isTestFunction_mul_right hφ hψdiff hψcompact).2.2 i
  have hleft :
      (∫ x in Ω, f.val x *
        fderiv ℝ (fun y ↦ φ y * ψ y) x (EuclideanSpace.single i 1)) =
      (∫ x in Ω, f.val x *
        (φ x * fderiv ℝ ψ x (EuclideanSpace.single i 1))) +
      (∫ x in Ω, f.val x *
        (ψ x * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    rw [← MeasureTheory.integral_add hA hB]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [apm_m01J04_fderiv_mul_apply hφ.1 hψdiff]
    ring
  have hright :
      (∫ x in Ω,
        (φ x * f.grad x i +
          f.val x * fderiv ℝ φ x (EuclideanSpace.single i 1)) * ψ x) =
      (∫ x in Ω, f.grad x i * (φ x * ψ x)) +
      (∫ x in Ω, f.val x *
        (ψ x * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    rw [← MeasureTheory.integral_add hC hB]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hleft] at hweak
  rw [hright]
  simp only [mul_assoc]
  linarith

/-- The localized product pair satisfies its weak-gradient identity on the
whole Euclidean space. -/
lemma apm_m01J04_test_mul_weakGradient_volume
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (hψdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψcompact : HasCompactSupport ψ)
    (f : apm_m01J04_H1 d Ω) (i : Fin d) :
    (∫ x, (f.val x * φ x) * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -(∫ x, (φ x * f.grad x i + f.val x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) * ψ x) := by
  let s := Function.support φ
  have hs : MeasurableSet s := hφ.1.continuous.isOpen_support.measurableSet
  have hsΩ : s ⊆ Ω := hφ.2.2
  have hleft0 : ∀ᵐ x ∂volume, x ∉ s → (f.val x * φ x) *
      fderiv ℝ ψ x (EuclideanSpace.single i 1) = 0 := by
    filter_upwards [] with x
    intro hxs
    simp [Function.notMem_support.mp hxs]
  have hright0 : ∀ᵐ x ∂volume, x ∉ s → (φ x * f.grad x i + f.val x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) * ψ x = 0 := by
    filter_upwards [apm_m01J04_test_mul_grad_ae_zero_outside φ hφ f] with x hx
    intro hxs
    have hc := congrArg (fun v : EuclideanSpace ℝ (Fin d) ↦ v i) (hx hxs)
    have hc' := congrArg (fun z : ℝ ↦ z * ψ x) hc
    simpa [Pi.smul_apply, smul_eq_mul] using hc'
  have hleft := apm_m01J04_integral_eq_restrict_of_ae_zero_outside hs hsΩ hleft0
  have hright := apm_m01J04_integral_eq_restrict_of_ae_zero_outside hs hsΩ hright0
  calc
    (∫ x, (f.val x * φ x) * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      ∫ x in Ω, (f.val x * φ x) *
        fderiv ℝ ψ x (EuclideanSpace.single i 1) := hleft
    _ = -(∫ x in Ω, (φ x * f.grad x i + f.val x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) * ψ x) :=
      apm_m01J04_weakLeibniz φ ψ hφ hψdiff hψcompact f i
    _ = -(∫ x, (φ x * f.grad x i + f.val x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) * ψ x) := by rw [← hright]

/-- The compactly localized pair as a global encoded `H¹` function. -/
noncomputable def apm_m01J04_globalLocalizedH1
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) : apm_m01J04_H1 d Set.univ :=
  { val := fun x ↦ f.val x * φ x
    grad := fun x ↦ φ x • f.grad x + f.val x • WithLp.toLp 2
      (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
    val_memLp := by simpa using (apm_m01J04_test_mul_fields_memLp_volume φ hφ f).1
    grad_memLp := by simpa using (apm_m01J04_test_mul_fields_memLp_volume φ hφ f).2
    weakGradient := by
      intro ψ hψdiff hψcompact hψsupport i
      simpa [Pi.smul_apply, smul_eq_mul] using
        apm_m01J04_test_mul_weakGradient_volume φ ψ hφ hψdiff hψcompact f i }

/-- The value field of the global localization is genuinely compactly
supported.  This is the support input for whole-space mollification; unlike
the weak gradient, no almost-everywhere qualification is needed. -/
lemma apm_m01J04_globalLocalizedH1_val_hasCompactSupport
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    HasCompactSupport (apm_m01J04_globalLocalizedH1 φ hφ f).val := by
  apply hφ.2.1.mono
  intro x hx
  contrapose! hx
  simp [apm_m01J04_globalLocalizedH1, Function.notMem_support.mp hx]

/-- Convolution of the compactly localized value with a smooth compact kernel
is smooth.  This records the regularity half of the eventual Friedrichs
mollifier construction independently of its `L²` convergence estimates. -/
lemma apm_m01J04_globalLocalizedH1_contDiff_convolution
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκcompact : HasCompactSupport κ) (hκsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (MeasureTheory.convolution κ
      (apm_m01J04_globalLocalizedH1 φ hφ f).val
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  have hloc : LocallyIntegrable
      (apm_m01J04_globalLocalizedH1 φ hφ f).val volume := by
    have hp : MemLp (apm_m01J04_globalLocalizedH1 φ hφ f).val 2 volume := by
      simpa only [MeasureTheory.Measure.restrict_univ] using
        (apm_m01J04_globalLocalizedH1 φ hφ f).val_memLp
    exact hp.locallyIntegrable (by norm_num)
  apply HasCompactSupport.contDiff_convolution_left (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.lsmul ℝ ℝ) (by assumption) (by assumption)
  exact hloc

/-- Both fields of the global localization admit independent smooth compactly
supported `L²` approximants.  The remaining Sobolev-density step is precisely
to choose these approximants compatibly, with the second field the genuine
gradient of the first. -/
lemma apm_m01J04_globalLocalizedH1_exists_smooth_fields
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin d) → ℝ)
      (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      eLpNorm ((apm_m01J04_globalLocalizedH1 φ hφ f).val - g) 2 volume ≤
        ENNReal.ofReal ε ∧
      HasCompactSupport G ∧ ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) G ∧
      eLpNorm ((apm_m01J04_globalLocalizedH1 φ hφ f).grad - G) 2 volume ≤
        ENNReal.ofReal ε := by
  have hval : MemLp (apm_m01J04_globalLocalizedH1 φ hφ f).val 2 volume := by
    simpa only [MeasureTheory.Measure.restrict_univ] using
      (apm_m01J04_globalLocalizedH1 φ hφ f).val_memLp
  have hgrad : MemLp (apm_m01J04_globalLocalizedH1 φ hφ f).grad 2 volume := by
    simpa only [MeasureTheory.Measure.restrict_univ] using
      (apm_m01J04_globalLocalizedH1 φ hφ f).grad_memLp
  obtain ⟨g, hgcompact, hgsmooth, hg⟩ :=
    hval.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
  obtain ⟨G, hGcompact, hGsmooth, hG⟩ :=
    hgrad.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
  exact ⟨g, G, hgcompact, hgsmooth, hg, hGcompact, hGsmooth, hG⟩

/-- Restriction of a globally encoded Sobolev function to an arbitrary set. -/
noncomputable def apm_m01J04_H1restrict
    {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (u : apm_m01J04_H1 d Set.univ) : apm_m01J04_H1 d Ω :=
  { val := u.val
    grad := u.grad
    val_memLp := u.val_memLp.mono_measure (by
      simpa using (Measure.restrict_le_self (μ := volume) (s := Ω)))
    grad_memLp := u.grad_memLp.mono_measure (by
      simpa using (Measure.restrict_le_self (μ := volume) (s := Ω)))
    weakGradient := by
      intro ψ hψdiff hψcompact hψsupport i
      let s := Function.support ψ
      have hs : MeasurableSet s := hψdiff.continuous.isOpen_support.measurableSet
      have hD0 := apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet hψdiff
      have hleft0 : ∀ᵐ x ∂volume, x ∉ s →
          u.val x * fderiv ℝ ψ x (EuclideanSpace.single i 1) = 0 := by
        filter_upwards [hD0] with x hx
        intro hxs
        have hψx : ψ x = 0 := Function.notMem_support.mp hxs
        have hc := congrArg (fun v : EuclideanSpace ℝ (Fin d) ↦ v i) (hx hψx)
        simpa using congrArg (fun z : ℝ ↦ u.val x * z) hc
      have hright0 : ∀ᵐ x ∂volume, x ∉ s → u.grad x i * ψ x = 0 := by
        filter_upwards [] with x
        intro hxs
        simp [Function.notMem_support.mp hxs]
      have hleft := apm_m01J04_integral_eq_restrict_of_ae_zero_outside
        hs hψsupport hleft0
      have hright := apm_m01J04_integral_eq_restrict_of_ae_zero_outside
        hs hψsupport hright0
      calc
        (∫ x in Ω, u.val x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
            ∫ x, u.val x * fderiv ℝ ψ x (EuclideanSpace.single i 1) := hleft.symm
        _ = -(∫ x, u.grad x i * ψ x) := by
          simpa using u.weakGradient ψ hψdiff hψcompact (Set.subset_univ _) i
        _ = -(∫ x in Ω, u.grad x i * ψ x) := by rw [← hright] }

@[simp] lemma apm_m01J04_H1restrict_val
    {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (u : apm_m01J04_H1 d Set.univ) :
    (apm_m01J04_H1restrict Ω u).val = u.val := rfl

@[simp] lemma apm_m01J04_H1restrict_grad
    {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (u : apm_m01J04_H1 d Set.univ) :
    (apm_m01J04_H1restrict Ω u).grad = u.grad := rfl

/-- Restriction contracts the custom `H1dist`. -/
lemma apm_m01J04_H1dist_restrict_le
    {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (u w : apm_m01J04_H1 d Set.univ) :
    apm_m01J04_H1dist (apm_m01J04_H1restrict Ω u)
      (apm_m01J04_H1restrict Ω w) ≤ apm_m01J04_H1dist u w := by
  apply add_le_add
  · exact ENNReal.toReal_mono (u.val_memLp.sub w.val_memLp).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (by
        simpa using (Measure.restrict_le_self (μ := volume) (s := Ω))))
  · exact ENNReal.toReal_mono (u.grad_memLp.sub w.grad_memLp).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (by
        simpa using (Measure.restrict_le_self (μ := volume) (s := Ω))))

/-- The actual `H¹` product record, before the zero-boundary and quantitative
norm properties required by `bridge_1`. -/
lemma apm_m01J04_test_mul_exists_H1
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    ∃ h : apm_m01J04_H1 d Ω,
      h.val = (fun x ↦ f.val x * φ x) ∧
      h.grad = (fun x ↦
        φ x • f.grad x +
          f.val x • WithLp.toLp 2
            (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
  obtain ⟨hval, hgrad⟩ := apm_m01J04_test_mul_fields_memLp φ hφ f
  let h : apm_m01J04_H1 d Ω :=
    { val := fun x ↦ f.val x * φ x
      grad := fun x ↦
        φ x • f.grad x +
          f.val x • WithLp.toLp 2
            (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      val_memLp := hval
      grad_memLp := hgrad
      weakGradient := by
        intro ψ hψdiff hψcompact hψsupport i
        have hψ : apm_m01J04_isTestFunction Ω ψ :=
          ⟨hψdiff, hψcompact, hψsupport⟩
        simpa [Pi.smul_apply, smul_eq_mul] using
          apm_m01J04_weakLeibniz φ ψ hφ hψdiff hψcompact f i }
  exact ⟨h, rfl, rfl⟩

noncomputable def apm_m01J04_H1mul
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) : apm_m01J04_H1 d Ω :=
  Classical.choose (apm_m01J04_test_mul_exists_H1 φ hφ f)

@[simp] lemma apm_m01J04_H1mul_val
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    (apm_m01J04_H1mul φ hφ f).val = fun x ↦ f.val x * φ x :=
  (Classical.choose_spec (apm_m01J04_test_mul_exists_H1 φ hφ f)).1

@[simp] lemma apm_m01J04_H1mul_grad
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    (apm_m01J04_H1mul φ hφ f).grad = fun x ↦
      φ x • f.grad x + f.val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
  (Classical.choose_spec (apm_m01J04_test_mul_exists_H1 φ hφ f)).2

/-- Restricting the packaged global localization gives exactly the local
product, as far as the custom distance (which only observes fields) is
concerned. -/
lemma apm_m01J04_H1dist_restrict_globalLocalized
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) (a : apm_m01J04_H1 d Set.univ) :
    apm_m01J04_H1dist (apm_m01J04_H1restrict Ω a)
      (apm_m01J04_H1mul φ hφ f) =
      apm_m01J04_H1dist (apm_m01J04_H1restrict Ω a)
        (apm_m01J04_H1restrict Ω (apm_m01J04_globalLocalizedH1 φ hφ f)) := by
  simp only [apm_m01J04_H1dist, apm_m01J04_H1restrict_val,
    apm_m01J04_H1restrict_grad, apm_m01J04_H1mul_val,
    apm_m01J04_H1mul_grad, apm_m01J04_globalLocalizedH1]

/-- Terminal whole-space density interface.  Once smooth compactly supported
global approximants stay inside `Ω`, distance contraction supplies the exact
zero-boundary approximating sequence required by the local product. -/
lemma apm_m01J04_localization_isH1Zero_of_globalApprox
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    (a : ℕ → apm_m01J04_H1 d Set.univ)
    (ha : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a n).val ∧ HasCompactSupport (a n).val ∧
      Function.support (a n).val ⊆ Ω)
    (hlim : Tendsto (fun n ↦ apm_m01J04_H1dist (a n)
      (apm_m01J04_globalLocalizedH1 φ hφ f)) atTop (nhds 0)) :
    apm_m01J04_isH1Zero (apm_m01J04_H1mul φ hφ f) := by
  refine ⟨fun n ↦ apm_m01J04_H1restrict Ω (a n), ?_, ?_⟩
  · intro n
    simpa using ha n
  · rw [show (fun n ↦ apm_m01J04_H1dist
        (apm_m01J04_H1restrict Ω (a n)) (apm_m01J04_H1mul φ hφ f)) =
        (fun n ↦ apm_m01J04_H1dist (apm_m01J04_H1restrict Ω (a n))
          (apm_m01J04_H1restrict Ω
            (apm_m01J04_globalLocalizedH1 φ hφ f))) by
      funext n
      exact apm_m01J04_H1dist_restrict_globalLocalized φ hφ f (a n)]
    apply squeeze_zero
      (fun n ↦ add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun n ↦ apm_m01J04_H1dist_restrict_le Ω (a n)
        (apm_m01J04_globalLocalizedH1 φ hφ f))
    exact hlim

/-- Positive level sets of a compactly supported smooth multiplier form
compact cores of its open nonzero set, with a uniform convolution margin. -/
lemma apm_m01J04_test_levelSet_exists_cthickening
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.cthickening δ {x | ε ≤ |φ x|} ⊆ Function.support φ ∧
      Metric.cthickening δ {x | ε ≤ |φ x|} ⊆ Ω := by
  have hclosed : IsClosed {x | ε ≤ |φ x|} :=
    isClosed_Ici.preimage hφ.1.continuous.abs
  have hcore : {x | ε ≤ |φ x|} ⊆ tsupport φ := by
    intro x hx
    apply subset_tsupport φ
    exact abs_pos.mp (hε.trans_le hx)
  have hcompact : IsCompact {x | ε ≤ |φ x|} :=
    hφ.2.1.of_isClosed_subset hclosed hcore
  have hinside : {x | ε ≤ |φ x|} ⊆ Function.support φ := by
    intro x hx
    exact abs_pos.mp (hε.trans_le hx)
  obtain ⟨δ, hδ, hthick⟩ := hcompact.exists_cthickening_subset_open
    hφ.1.continuous.isOpen_support hinside
  exact ⟨δ, hδ, hthick, hthick.trans hφ.2.2⟩

/-- A kernel supported in the radius-`δ` ball can enlarge the support of its
right convolution factor by at most the closed `δ`-thickening. -/
lemma apm_m01J04_support_convolution_subset_cthickening
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : EuclideanSpace ℝ (Fin d) → ℝ}
    {u : EuclideanSpace ℝ (Fin d) → E} {K : Set (EuclideanSpace ℝ (Fin d))}
    {δ : ℝ} (hκ : Function.support κ ⊆ Metric.closedBall 0 δ)
    (hu : Function.support u ⊆ K) :
    Function.support (MeasureTheory.convolution κ u
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
      Metric.cthickening δ K := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (MeasureTheory.support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx)
  apply Metric.closedBall_subset_cthickening (hu hb) δ
  have ha' := hκ ha
  simpa [Metric.mem_closedBall, dist_eq_norm] using ha'

/-- Exact support-safe convolution interface for a positive multiplier core. -/
lemma apm_m01J04_test_levelSet_convolution_support
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀
      (κ : EuclideanSpace ℝ (Fin d) → ℝ)
      (u : EuclideanSpace ℝ (Fin d) → E),
      Function.support κ ⊆ Metric.closedBall 0 δ →
      Function.support u ⊆ {x | ε ≤ |φ x|} →
      Function.support (MeasureTheory.convolution κ u
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ Ω := by
  obtain ⟨δ, hδ, hthick, hthickΩ⟩ :=
    apm_m01J04_test_levelSet_exists_cthickening φ hφ hε
  refine ⟨δ, hδ, fun κ u hκ hu ↦ ?_⟩
  exact (apm_m01J04_support_convolution_subset_cthickening hκ hu).trans hthickΩ

/-- Sharp extended-real multiplier estimates for the two fields of the product
record.  They are kept in `ENNReal` until the final finite-norm conversion. -/
lemma apm_m01J04_test_mul_eLpNorm_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    eLpNorm (fun x ↦ f.val x * φ x) 2 (volume.restrict Ω) ≤
        eLpNorm φ ⊤ (volume.restrict Ω) *
          eLpNorm f.val 2 (volume.restrict Ω) ∧
    eLpNorm (fun x ↦
      φ x • f.grad x +
        f.val x • WithLp.toLp 2
          (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2
        (volume.restrict Ω) ≤
      eLpNorm φ ⊤ (volume.restrict Ω) *
          eLpNorm f.grad 2 (volume.restrict Ω) +
        eLpNorm (fun x ↦ WithLp.toLp 2
          (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) ⊤
            (volume.restrict Ω) *
          eLpNorm f.val 2 (volume.restrict Ω) := by
  have hφtop := apm_m01J04_isTestFunction_memLp hφ ⊤
  have hDtop := apm_m01J04_isTestFunction_fderivField_memLp hφ ⊤
  constructor
  · simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (eLpNorm_smul_le_mul_eLpNorm (p := ⊤) (q := 2) (r := 2)
        f.val_memLp.1 hφtop.1 :
        eLpNorm (φ • f.val) 2 (volume.restrict Ω) ≤ _)
  · refine (eLpNorm_add_le (hφtop.1.smul f.grad_memLp.1)
      (f.val_memLp.1.smul hDtop.1) (by norm_num)).trans ?_
    have hfirst : eLpNorm (φ • f.grad) 2 (volume.restrict Ω) ≤
        eLpNorm φ ⊤ (volume.restrict Ω) *
          eLpNorm f.grad 2 (volume.restrict Ω) :=
      eLpNorm_smul_le_mul_eLpNorm (p := ⊤) (q := 2) (r := 2)
        f.grad_memLp.1 hφtop.1
    have hsecond : eLpNorm (f.val • fun x ↦ WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2
        (volume.restrict Ω) ≤
      eLpNorm (fun x ↦ WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) ⊤
          (volume.restrict Ω) * eLpNorm f.val 2 (volume.restrict Ω) :=
      by
        simpa [mul_comm] using
          (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := ⊤) (r := 2)
            hDtop.1 f.val_memLp.1)
    exact add_le_add hfirst hsecond

/-- Real-valued consolidation of the multiplier estimates, in the exact norm
shape consumed by `bridge_1`. -/
lemma apm_m01J04_test_mul_H1norm_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : apm_m01J04_H1 d Ω,
      (eLpNorm (fun x ↦ f.val x * φ x) 2
          (volume.restrict Ω)).toReal +
        (eLpNorm (fun x ↦
          φ x • f.grad x +
            f.val x • WithLp.toLp 2
              (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2
          (volume.restrict Ω)).toReal ≤ C * apm_m01J04_H1norm f := by
  let A := eLpNorm φ ⊤ (volume.restrict Ω)
  let D := eLpNorm (fun x ↦ WithLp.toLp 2
    (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) ⊤
      (volume.restrict Ω)
  have hAtop : A ≠ ⊤ :=
    (apm_m01J04_isTestFunction_memLp hφ ⊤).eLpNorm_ne_top
  have hDtop : D ≠ ⊤ :=
    (apm_m01J04_isTestFunction_fderivField_memLp hφ ⊤).eLpNorm_ne_top
  refine ⟨A.toReal + D.toReal, add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    fun f ↦ ?_⟩
  obtain ⟨hval, hgrad⟩ := apm_m01J04_test_mul_eLpNorm_le φ hφ f
  have hvalR :
      (eLpNorm (fun x ↦ f.val x * φ x) 2 (volume.restrict Ω)).toReal ≤
        A.toReal * (eLpNorm f.val 2 (volume.restrict Ω)).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hAtop f.val_memLp.eLpNorm_ne_top) hval
  have hgradR :
      (eLpNorm (fun x ↦ φ x • f.grad x +
        f.val x • WithLp.toLp 2
          (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2
          (volume.restrict Ω)).toReal ≤
        A.toReal * (eLpNorm f.grad 2 (volume.restrict Ω)).toReal +
          D.toReal * (eLpNorm f.val 2 (volume.restrict Ω)).toReal := by
    rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul,
      ← ENNReal.toReal_add
        (ENNReal.mul_ne_top hAtop f.grad_memLp.eLpNorm_ne_top)
        (ENNReal.mul_ne_top hDtop f.val_memLp.eLpNorm_ne_top)]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hAtop f.grad_memLp.eLpNorm_ne_top,
        ENNReal.mul_ne_top hDtop f.val_memLp.eLpNorm_ne_top⟩) hgrad
  unfold apm_m01J04_H1norm
  nlinarith [ENNReal.toReal_nonneg (a := A), ENNReal.toReal_nonneg (a := D),
    ENNReal.toReal_nonneg (a := eLpNorm f.val 2 (volume.restrict Ω)),
    ENNReal.toReal_nonneg (a := eLpNorm f.grad 2 (volume.restrict Ω))]

/-- Multiplication by a fixed test function is Lipschitz for the custom
`H1dist`.  This is the transport estimate needed to turn a local smooth
approximation of `f` into the defining approximation of `φ * f`. -/
lemma apm_m01J04_test_mul_H1dist_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a f : apm_m01J04_H1 d Ω,
      (eLpNorm (fun x ↦ a.val x * φ x - f.val x * φ x) 2
          (volume.restrict Ω)).toReal +
        (eLpNorm (fun x ↦
          (φ x • a.grad x + a.val x • WithLp.toLp 2
            (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) -
          (φ x • f.grad x + f.val x • WithLp.toLp 2
            (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)))) 2
          (volume.restrict Ω)).toReal ≤ C * apm_m01J04_H1dist a f := by
  obtain ⟨C, hC0, hC⟩ := apm_m01J04_test_mul_H1norm_le φ hφ
  refine ⟨C, hC0, fun a f ↦ ?_⟩
  have hb := hC (apm_m01J04_H1sub a f)
  rw [apm_m01J04_H1norm_sub_eq_dist] at hb
  simpa only [apm_m01J04_H1sub_val, apm_m01J04_H1sub_grad,
    Pi.sub_apply, sub_mul, smul_sub, sub_smul, sub_eq_add_neg,
    neg_smul, smul_neg, add_smul, smul_add, add_mul, neg_mul, neg_add_rev,
    add_assoc, add_left_comm, add_comm] using hb

lemma apm_m01J04_H1dist_mul_le
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a f : apm_m01J04_H1 d Ω,
      apm_m01J04_H1dist (apm_m01J04_H1mul φ hφ a)
        (apm_m01J04_H1mul φ hφ f) ≤ C * apm_m01J04_H1dist a f := by
  obtain ⟨C, hC0, hC⟩ := apm_m01J04_test_mul_H1dist_le φ hφ
  refine ⟨C, hC0, fun a f ↦ ?_⟩
  simpa [apm_m01J04_H1dist, apm_m01J04_H1mul_val,
    apm_m01J04_H1mul_grad] using hC a f

/-- Multiplication preserves the encoded zero-boundary closure whenever the
input already has such an approximation. -/
lemma apm_m01J04_isH1Zero_mul
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) (hf : apm_m01J04_isH1Zero f) :
    apm_m01J04_isH1Zero (apm_m01J04_H1mul φ hφ f) := by
  obtain ⟨a, ha, hlim⟩ := hf
  obtain ⟨C, hC0, hC⟩ := apm_m01J04_H1dist_mul_le φ hφ
  refine ⟨fun n ↦ apm_m01J04_H1mul φ hφ (a n), ?_, ?_⟩
  · intro n
    rw [apm_m01J04_H1mul_val]
    refine ⟨(ha n).1.mul hφ.1, hφ.2.1.mul_left, ?_⟩
    intro x hx
    apply hφ.2.2
    contrapose! hx
    simp [Function.notMem_support.mp hx]
  · apply squeeze_zero
      (fun n ↦ add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun n ↦ hC (a n) f)
    simpa using (tendsto_const_nhds.mul hlim :
      Tendsto (fun n ↦ C * apm_m01J04_H1dist (a n) f) atTop (nhds (C * 0)))

/-- Localization supplies the compact support and boundary condition, so a
global smooth `H¹` approximation is sufficient.  This separates the genuinely
analytic Meyers--Serrin input from all support bookkeeping. -/
lemma apm_m01J04_localization_isH1Zero_of_smoothApprox
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    (a : ℕ → apm_m01J04_H1 d Ω)
    (ha : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a n).val)
    (hlim : Tendsto (fun n ↦ apm_m01J04_H1dist (a n) f)
      atTop (nhds 0)) :
    apm_m01J04_isH1Zero (apm_m01J04_H1mul φ hφ f) := by
  obtain ⟨C, hC0, hC⟩ := apm_m01J04_H1dist_mul_le φ hφ
  refine ⟨fun n ↦ apm_m01J04_H1mul φ hφ (a n), ?_, ?_⟩
  · intro n
    rw [apm_m01J04_H1mul_val]
    refine ⟨(ha n).mul hφ.1, hφ.2.1.mul_left, ?_⟩
    intro x hx
    apply hφ.2.2
    contrapose! hx
    simp [Function.notMem_support.mp hx]
  · apply squeeze_zero
      (fun n ↦ add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun n ↦ hC (a n) f)
    simpa using (tendsto_const_nhds.mul hlim :
      Tendsto (fun n ↦ C * apm_m01J04_H1dist (a n) f) atTop (nhds (C * 0)))

/-- Epsilon-form smooth density suffices for localization.  This packages the
choice of approximants and the `1 / (n + 1)` convergence argument, leaving a
mollifier development only a single-error-tolerance obligation. -/
lemma apm_m01J04_localization_isH1Zero_of_forall_exists_smooth
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ a : apm_m01J04_H1 d Ω,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.val ∧ apm_m01J04_H1dist a f < ε) :
    apm_m01J04_isH1Zero (apm_m01J04_H1mul φ hφ f) := by
  let ε : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hε (n : ℕ) : 0 < ε n := by
    simp only [ε]
    positivity
  let a : ℕ → apm_m01J04_H1 d Ω := fun n ↦
    Classical.choose (hdense (ε n) (hε n))
  have ha (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a n).val :=
    (Classical.choose_spec (hdense (ε n) (hε n))).1
  have hdist (n : ℕ) : apm_m01J04_H1dist (a n) f ≤ ε n :=
    (Classical.choose_spec (hdense (ε n) (hε n))).2.le
  apply apm_m01J04_localization_isH1Zero_of_smoothApprox φ hφ f a ha
  apply squeeze_zero
    (fun n ↦ add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    hdist
  simpa only [ε] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0))

/-- Collar cutoff for the core approximation: `0` where `|φ| ≤ r`, `1` where
`|φ| ≥ √2 r`.  The rescaling by `r²` matters: as `r → 0` it tends to `1` on
`{φ ≠ 0}`, and the collar gradient carries a factor `φ/r²` that the factor `φ`
inside `globalLocalizedH1` cancels. -/
noncomputable def apm_m01J04_localization_core_approx_aux_cutoff
    {d : ℕ} (phi : EuclideanSpace ℝ (Fin d) → ℝ) (r : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x ↦ Real.smoothTransition (phi x ^ 2 / r ^ 2 - 1)

lemma apm_m01J04_localization_core_approx_aux_cutoff_contDiff
    {d : ℕ} {phi : EuclideanSpace ℝ (Fin d) → ℝ}
    (hphi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phi) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (apm_m01J04_localization_core_approx_aux_cutoff phi r) :=
  Real.smoothTransition.contDiff.comp
    (((hphi.pow 2).div_const _).sub contDiff_const)

lemma apm_m01J04_localization_core_approx_aux_cutoff_support
    {d : ℕ} {phi : EuclideanSpace ℝ (Fin d) → ℝ} {r : ℝ}
    (hr : 0 < r) :
    Function.support (apm_m01J04_localization_core_approx_aux_cutoff phi r) ⊆
      {x | r ≤ |phi x|} := by
  intro x hx
  have harg : 0 < phi x ^ 2 / r ^ 2 - 1 :=
    lt_of_not_ge (Real.smoothTransition.zero_iff_nonpos.not.mp hx)
  have hsquares : r ^ 2 < |phi x| ^ 2 := by
    have h1 : 1 < phi x ^ 2 / r ^ 2 := by linarith
    rw [one_lt_div (by positivity)] at h1
    simpa [sq_abs] using h1
  change r ≤ |phi x|
  nlinarith [abs_nonneg (phi x), sq_nonneg (r - |phi x|)]

lemma apm_m01J04_localization_core_approx_aux_cutoff_compact
    {d : ℕ} {Omega : Set (EuclideanSpace ℝ (Fin d))}
    {phi : EuclideanSpace ℝ (Fin d) → ℝ}
    (hphi : apm_m01J04_isTestFunction Omega phi) (r : ℝ) :
    HasCompactSupport
      (apm_m01J04_localization_core_approx_aux_cutoff phi r) := by
  apply hphi.2.1.mono
  intro x hx
  contrapose! hx
  have hz : phi x = 0 := Function.notMem_support.mp hx
  simp [apm_m01J04_localization_core_approx_aux_cutoff, hz]

lemma apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction
    {d : ℕ} {Omega : Set (EuclideanSpace ℝ (Fin d))}
    {phi : EuclideanSpace ℝ (Fin d) → ℝ}
    (hphi : apm_m01J04_isTestFunction Omega phi) (r : ℝ) :
    apm_m01J04_isTestFunction Set.univ
      (apm_m01J04_localization_core_approx_aux_cutoff phi r) :=
  ⟨apm_m01J04_localization_core_approx_aux_cutoff_contDiff hphi.1 r,
    apm_m01J04_localization_core_approx_aux_cutoff_compact hphi r,
    Set.subset_univ _⟩

/-- The gradient of the cutoff lives where the cutoff's closed support does. -/
lemma apm_m01J04_localization_core_approx_aux_cutoff_fderiv_support
    {d : ℕ} {phi : EuclideanSpace ℝ (Fin d) → ℝ}
    (hphi : Continuous phi) {r : ℝ} (hr : 0 < r) :
    Function.support (fun x ↦
      fderiv ℝ (apm_m01J04_localization_core_approx_aux_cutoff phi r) x) ⊆
      {x | r ≤ |phi x|} := by
  refine (support_fderiv_subset ℝ).trans ?_
  exact closure_minimal
    (apm_m01J04_localization_core_approx_aux_cutoff_support hr)
    (isClosed_le continuous_const (continuous_abs.comp hphi))

/-- Value part of the core convergence: `χ_{1/(n+1)} · (f φ) → f φ` in `L²`
(dominated convergence; `χ_r → 1` pointwise on `{φ ≠ 0}`, `|χ_r| ≤ 1`). -/
lemma apm_m01J04_localization_core_approx_aux_val_tendsto
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    Tendsto (fun n : ℕ ↦
      (eLpNorm (fun x ↦
        (apm_m01J04_H1mul
          (apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ)))
          (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ _)
          (apm_m01J04_globalLocalizedH1 φ hφ f)).val x -
        (apm_m01J04_globalLocalizedH1 φ hφ f).val x) 2
        (volume.restrict Set.univ)).toReal) atTop (nhds 0) := by
  let g := apm_m01J04_globalLocalizedH1 φ hφ f
  let c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n ↦
    apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ))
  let e : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n x ↦ c n x * g.val x - g.val x
  have he_mem (n : ℕ) : MemLp (e n) 2 (volume.restrict Set.univ) := by
    have h := (apm_m01J04_H1mul (c n)
      (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ _) g).val_memLp.sub
        g.val_memLp
    simpa [e, c, Pi.sub_apply, apm_m01J04_H1mul_val, mul_comm] using h
  have hbound (n : ℕ) : ∀ᵐ x ∂(volume.restrict Set.univ),
      ‖e n x‖ₑ ^ (2 : ℝ) ≤ ‖g.val x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [] with x
    have hc0 : 0 ≤ c n x := Real.smoothTransition.nonneg _
    have hc1 : c n x ≤ 1 := Real.smoothTransition.le_one _
    rw [show e n x = (c n x - 1) * g.val x by
      simp only [e]
      ring, enorm_mul]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    apply mul_le_of_le_one_left (by positivity)
    simp [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hc1), hc0]
  have hfin : (∫⁻ x, ‖g.val x‖ₑ ^ (2 : ℝ) ∂(volume.restrict Set.univ)) ≠ ∞ :=
    ne_of_lt (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      g.val_memLp.eLpNorm_lt_top)
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      Tendsto (fun n ↦ ‖e n x‖ₑ ^ (2 : ℝ)) atTop (nhds 0) := by
    by_cases hx : φ x = 0
    · have hgx : g.val x = 0 := by
        simp [g, apm_m01J04_globalLocalizedH1, apm_m01J04_H1mul_val, hx]
      simp [e, hgx]
    · obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Real.sqrt 2 / |φ x|)
      have hev : ∀ᶠ n : ℕ in atTop, e n x = 0 := by
        filter_upwards [eventually_atTop.2 ⟨N, fun _ hn ↦ hn⟩] with n hn
        have habs : Real.sqrt 2 < (n + 1 : ℝ) * |φ x| := by
          have hp : 0 < |φ x| := abs_pos.mpr hx
          apply (div_lt_iff₀ hp).mp
          exact lt_of_lt_of_le hN (by exact_mod_cast Nat.le_add_right_of_le hn)
        have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        have hsquares : (2 : ℝ) < (n + 1 : ℝ) ^ 2 * φ x ^ 2 := by
          have := (sq_lt_sq₀ hsqrt (mul_nonneg (by positivity) (abs_nonneg _))).2 habs
          rw [Real.sq_sqrt (by norm_num), mul_pow, sq_abs] at this
          exact this
        have harg : 1 ≤ φ x ^ 2 / (1 / (n + 1 : ℝ)) ^ 2 - 1 := by
          have hnpos : 0 < (n + 1 : ℝ) := by positivity
          field_simp
          nlinarith
        have hc : c n x = 1 := Real.smoothTransition.eq_one_iff_one_le.2 harg
        simp [e, hc]
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (nhds 0)).congr'
        (hev.mono fun n hn ↦ by simp [hn])
  have hlin : Tendsto
      (fun n ↦ ∫⁻ x, ‖e n x‖ₑ ^ (2 : ℝ) ∂(volume.restrict Set.univ))
      atTop (nhds 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun x ↦ ‖g.val x‖ₑ ^ (2 : ℝ))
      (fun n ↦ (he_mem n).1.enorm.pow_const _) hbound hfin
      (ae_of_all _ hpoint)
  have help : Tendsto (fun n ↦ eLpNorm (e n) 2 (volume.restrict Set.univ))
      atTop (nhds 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    norm_num
    have hc : Continuous (fun z : ℝ≥0∞ ↦ z ^ (1 / 2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hlin
  have hreal := (ENNReal.tendsto_toReal_iff
    (fun n ↦ (he_mem n).eLpNorm_ne_top) ENNReal.zero_ne_top).2
    help
  simpa [e, c, g, apm_m01J04_H1mul_val, mul_comm] using hreal

lemma apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_zeroSet
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∀ᵐ x ∂volume, φ x = 0 →
      WithLp.toLp 2 (fun i ↦
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 := by
  exact apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet hφ.1

/-- `smoothTransition` has bounded derivative (smooth, constant outside `[0,1]`). -/
lemma apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_deriv_bound :
    ∃ M : ℝ, ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M := by
  have hcont : Continuous (fun t : ℝ ↦ |deriv Real.smoothTransition t|) :=
    ((@Real.smoothTransition.contDiff 2).continuous_deriv (by norm_num)).abs
  obtain ⟨M, hM⟩ :=
    ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image
      hcont.continuousOn)
  have hM0 : 0 ≤ M := by
    have h := hM ⟨(0 : ℝ), by simp, rfl⟩
    exact (abs_nonneg _).trans h
  refine ⟨M, fun t ↦ ?_⟩
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · exact hM ⟨t, ht, rfl⟩
  · have hout : t < 0 ∨ 1 < t := by
      by_cases h0 : 0 ≤ t
      · exact Or.inr (lt_of_not_ge fun h1 ↦ ht ⟨h0, h1⟩)
      · exact Or.inl (lt_of_not_ge h0)
    rcases hout with hneg | hpos
    · have heq : Filter.EventuallyEq (nhds t) Real.smoothTransition (fun _ ↦ 0) := by
        filter_upwards [eventually_lt_nhds hneg] with x hx
        exact Real.smoothTransition.zero_of_nonpos hx.le
      rw [heq.deriv_eq]
      simpa using hM0
    · have heq : Filter.EventuallyEq (nhds t) Real.smoothTransition (fun _ ↦ 1) := by
        filter_upwards [eventually_gt_nhds hpos] with x hx
        exact Real.smoothTransition.one_of_one_le hx.le
      rw [heq.deriv_eq]
      simpa using hM0

/-- Bulk term: `χ_r • ∇(fφ) → ∇(fφ)` in `L²` (dominated convergence, `|χ_r| ≤ 1`,
`χ_r → 1` on `{φ ≠ 0}`, and `∇(fφ) = 0` a.e. on `{φ = 0}` by the banked
zero-set lemma). -/
lemma apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_bulk
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    Tendsto (fun n : ℕ ↦
      (eLpNorm (fun x ↦ apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ)) x • (apm_m01J04_globalLocalizedH1 φ hφ f).grad x -
          (apm_m01J04_globalLocalizedH1 φ hφ f).grad x) 2 volume).toReal) atTop (nhds 0) := by
  let g := apm_m01J04_globalLocalizedH1 φ hφ f
  let c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n ↦
    apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ))
  let e : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun n x ↦ c n x • g.grad x - g.grad x
  have hgmem : MemLp g.grad 2 volume := by
    simpa using g.grad_memLp
  have he_mem (n : ℕ) : MemLp (e n) 2 volume := by
    apply hgmem.of_le
    · have hcmeas : AEStronglyMeasurable (c n) volume :=
        (apm_m01J04_localization_core_approx_aux_cutoff_contDiff hφ.1 _).continuous.aestronglyMeasurable
      exact (hcmeas.smul hgmem.1).sub hgmem.1
    · filter_upwards [] with x
      rw [show e n x = (c n x - 1) • g.grad x by
        simp only [e]
        rw [sub_smul, one_smul], norm_smul]
      have hc0 : 0 ≤ c n x := Real.smoothTransition.nonneg _
      have hc1 : c n x ≤ 1 := Real.smoothTransition.le_one _
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hc1), neg_sub]
      apply mul_le_of_le_one_left (norm_nonneg _)
      linarith
  have hbound (n : ℕ) : ∀ᵐ x ∂volume,
      ‖e n x‖ₑ ^ (2 : ℝ) ≤ ‖g.grad x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [] with x
    have hc0 : 0 ≤ c n x := Real.smoothTransition.nonneg _
    have hc1 : c n x ≤ 1 := Real.smoothTransition.le_one _
    rw [show e n x = (c n x - 1) • g.grad x by
      simp only [e]
      rw [sub_smul, one_smul], enorm_smul]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    rw [Real.enorm_eq_ofReal_abs]
    apply mul_le_of_le_one_left (bot_le)
    rw [ENNReal.ofReal_le_one]
    simpa [abs_of_nonpos (sub_nonpos.mpr hc1)] using hc0
  have hfin : (∫⁻ x, ‖g.grad x‖ₑ ^ (2 : ℝ) ∂volume) ≠ ∞ :=
    ne_of_lt (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hgmem.eLpNorm_lt_top)
  have hgzero : ∀ᵐ x ∂volume, φ x = 0 → g.grad x = 0 := by
    filter_upwards
      [apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_zeroSet φ hφ]
      with x hx
    intro hφx
    simp [g, apm_m01J04_globalLocalizedH1, hφx, hx hφx]
  have hpoint : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ ‖e n x‖ₑ ^ (2 : ℝ)) atTop (nhds 0) := by
    filter_upwards [hgzero] with x hgx
    by_cases hx : φ x = 0
    · simp [e, hgx hx]
    · obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Real.sqrt 2 / |φ x|)
      have hev : ∀ᶠ n : ℕ in atTop, e n x = 0 := by
        filter_upwards [eventually_atTop.2 ⟨N, fun _ hn ↦ hn⟩] with n hn
        have habs : Real.sqrt 2 < (n + 1 : ℝ) * |φ x| := by
          have hp : 0 < |φ x| := abs_pos.mpr hx
          apply (div_lt_iff₀ hp).mp
          exact lt_of_lt_of_le hN (by exact_mod_cast Nat.le_add_right_of_le hn)
        have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        have hsquares : (2 : ℝ) < (n + 1 : ℝ) ^ 2 * φ x ^ 2 := by
          have := (sq_lt_sq₀ hsqrt (mul_nonneg (by positivity) (abs_nonneg _))).2 habs
          rw [Real.sq_sqrt (by norm_num), mul_pow, sq_abs] at this
          exact this
        have harg : 1 ≤ φ x ^ 2 / (1 / (n + 1 : ℝ)) ^ 2 - 1 := by
          have hnpos : 0 < (n + 1 : ℝ) := by positivity
          field_simp
          nlinarith
        have hc : c n x = 1 := Real.smoothTransition.eq_one_iff_one_le.2 harg
        simp [e, hc]
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (nhds 0)).congr'
        (hev.mono fun n hn ↦ by simp [hn])
  have hlin : Tendsto
      (fun n ↦ ∫⁻ x, ‖e n x‖ₑ ^ (2 : ℝ) ∂volume) atTop (nhds 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun x ↦ ‖g.grad x‖ₑ ^ (2 : ℝ))
      (fun n ↦ (he_mem n).1.enorm.pow_const _) hbound hfin hpoint
  have help : Tendsto (fun n ↦ eLpNorm (e n) 2 volume) atTop (nhds 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    norm_num
    have hc : Continuous (fun z : ℝ≥0∞ ↦ z ^ (1 / 2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hlin
  have hreal := (ENNReal.tendsto_toReal_iff
    (fun n ↦ (he_mem n).eLpNorm_ne_top) ENNReal.zero_ne_top).2 help
  simpa [e, c, g] using hreal

/-- Chain rule for the rescaled cutoff. -/
lemma apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_collar_fderiv
    {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (r : ℝ) (x) :
    fderiv ℝ (apm_m01J04_localization_core_approx_aux_cutoff φ r) x =
      (deriv Real.smoothTransition (φ x ^ 2 / r ^ 2 - 1)) •
        ((2 * φ x / r ^ 2) • fderiv ℝ φ x) := by
  have hφx : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (fun y ↦ φ y ^ 2 / r ^ 2 - 1)
      ((2 * φ x / r ^ 2) • fderiv ℝ φ x) x := by
    convert ((hφx.pow 2).const_smul (1 / r ^ 2)).sub_const 1 using 1 <;>
      ext z <;> simp <;> ring
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (φ x ^ 2 / r ^ 2 - 1))
      (φ x ^ 2 / r ^ 2 - 1) :=
    ((@Real.smoothTransition.contDiff 1).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hc := (hs.hasFDerivAt.comp x hi).fderiv
  convert hc using 1 <;>
    ext z <;>
    simp [apm_m01J04_localization_core_approx_aux_cutoff, Function.comp_def,
      smul_smul] <;> ring

/-- Collar term: `(fφ) • ∇χ_r → 0` in `L²`.  Pointwise
`(fφ) ∇χ_r = f · smoothTransition'(φ²/r² − 1) · 2(φ²/r²) ∇φ`, bounded by
`4M |f| |∇φ|` (on the collar `φ² ≤ 2r²`) and eventually `0` at each point. -/
lemma apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_collar_aux_fderiv
    {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (r : ℝ) (x) :
    fderiv ℝ (apm_m01J04_localization_core_approx_aux_cutoff φ r) x =
      (deriv Real.smoothTransition (φ x ^ 2 / r ^ 2 - 1)) •
        ((2 * φ x / r ^ 2) • fderiv ℝ φ x) := by
  have hφx : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (fun y ↦ φ y ^ 2 / r ^ 2 - 1)
      ((2 * φ x / r ^ 2) • fderiv ℝ φ x) x := by
    convert ((hφx.pow 2).const_smul (1 / r ^ 2)).sub_const 1 using 1 <;>
      ext z <;> simp <;> ring
  have hs : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (φ x ^ 2 / r ^ 2 - 1))
      (φ x ^ 2 / r ^ 2 - 1) :=
    ((@Real.smoothTransition.contDiff 1).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hc := (hs.hasFDerivAt.comp x hi).fderiv
  convert hc using 1 <;>
    ext z <;>
    simp [apm_m01J04_localization_core_approx_aux_cutoff, Function.comp_def,
      smul_smul] <;> ring

lemma apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_collar
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    {M : ℝ} (hM : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) :
    Tendsto (fun n : ℕ ↦
      (eLpNorm (fun x ↦ (apm_m01J04_globalLocalizedH1 φ hφ f).val x • WithLp.toLp 2 (fun i ↦
          fderiv ℝ (apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ))) x (EuclideanSpace.single i 1))) 2 volume).toReal) atTop (nhds 0) := by
  let D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x ↦
    WithLp.toLp 2 (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
  let e : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun n x ↦
    (apm_m01J04_globalLocalizedH1 φ hφ f).val x • WithLp.toLp 2 (fun i ↦
      fderiv ℝ (apm_m01J04_localization_core_approx_aux_cutoff φ
        (1 / (n + 1 : ℝ))) x (EuclideanSpace.single i 1))
  have hM0 : 0 ≤ M :=
    (abs_nonneg (deriv Real.smoothTransition 0)).trans (hM 0)
  have hprod : MemLp (fun x ↦ f.val x • D x) 2 volume := by
    have hlocal : MemLp (fun x ↦ f.val x • D x) 2 (volume.restrict Ω) := by
      exact (apm_m01J04_isTestFunction_fderivField_memLp hφ ⊤).smul f.val_memLp
    apply apm_m01J04_memLp_of_ae_eq_zero_outside
      hφ.1.continuous.isOpen_support.measurableSet hφ.2.2 hlocal
    filter_upwards
      [apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet hφ.1] with x hx
    intro hxs
    have hz : φ x = 0 := Function.notMem_support.mp hxs
    simp [D, hx hz]
  have he_meas (n : ℕ) : AEStronglyMeasurable (e n) volume := by
    have hc := (apm_m01J04_localization_core_approx_aux_cutoff_contDiff hφ.1
      (1 / (n + 1 : ℝ))).continuous
    have hD := apm_m01J04_isTestFunction_fderivField_memLp
      (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ
        (1 / (n + 1 : ℝ))) ⊤
    simpa [e] using
      (apm_m01J04_globalLocalizedH1 φ hφ f).val_memLp.1.smul hD.1
  have hnorm (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
      ‖e n x‖ ≤ ‖(4 * M) • (f.val x • D x)‖ := by
    let r : ℝ := 1 / (n + 1 : ℝ)
    let a : ℝ := φ x ^ 2 / r ^ 2 - 1
    have hr : 0 < r := by simp [r]; positivity
    simp only [e]
    rw [apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_collar_aux_fderiv
      φ hφ.1 r x]
    have hfield : WithLp.toLp 2 (fun i ↦
        ((deriv Real.smoothTransition a) •
          ((2 * φ x / r ^ 2) • fderiv ℝ φ x))
          (EuclideanSpace.single i 1)) =
        (deriv Real.smoothTransition a * (2 * φ x / r ^ 2)) • D x := by
      ext i
      simp [D, smul_smul]
    rw [hfield]
    change ‖(f.val x * φ x) •
      ((deriv Real.smoothTransition a * (2 * φ x / r ^ 2)) • D x)‖ ≤
        ‖(4 * M) • (f.val x • D x)‖
    simp only [smul_smul, norm_smul, Real.norm_eq_abs]
    by_cases ha : a ∈ Set.Icc (0 : ℝ) 1
    · have hratio : φ x ^ 2 / r ^ 2 ≤ 2 := by
        dsimp [a] at ha
        linarith [ha.2]
      have habsratio : |φ x * (2 * φ x / r ^ 2)| ≤ 4 := by
        have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
        calc
          |φ x * (2 * φ x / r ^ 2)| = 2 * (φ x ^ 2 / r ^ 2) := by
            rw [show φ x * (2 * φ x / r ^ 2) = 2 * (φ x ^ 2 / r ^ 2) by ring]
            exact abs_of_nonneg (by positivity)
          _ ≤ 4 := by linarith
      have hcoef :
          |φ x * (deriv Real.smoothTransition a * (2 * φ x / r ^ 2))| ≤
            |4 * M| := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hM0)]
        calc
          |φ x * (deriv Real.smoothTransition a * (2 * φ x / r ^ 2))| =
              |φ x * (2 * φ x / r ^ 2)| * |deriv Real.smoothTransition a| := by
                rw [abs_mul, abs_mul, abs_mul]
                ring
          _ ≤ 4 * M := mul_le_mul habsratio (hM a) (abs_nonneg _) (by norm_num)
      have hh := mul_le_mul_of_nonneg_left hcoef (abs_nonneg (f.val x))
      have hhh := mul_le_mul_of_nonneg_right hh (norm_nonneg (D x))
      simpa only [abs_mul, mul_assoc, mul_left_comm, mul_comm] using hhh
    · have hout : a < 0 ∨ 1 < a := by
        by_cases h0 : 0 ≤ a
        · exact Or.inr (lt_of_not_ge fun h1 ↦ ha ⟨h0, h1⟩)
        · exact Or.inl (lt_of_not_ge h0)
      have hd : deriv Real.smoothTransition a = 0 := by
        rcases hout with hneg | hpos
        · have heq : Filter.EventuallyEq (nhds a) Real.smoothTransition (fun _ ↦ 0) := by
            filter_upwards [eventually_lt_nhds hneg] with y hy
            exact Real.smoothTransition.zero_of_nonpos hy.le
          rw [heq.deriv_eq]
          simp
        · have heq : Filter.EventuallyEq (nhds a) Real.smoothTransition (fun _ ↦ 1) := by
            filter_upwards [eventually_gt_nhds hpos] with y hy
            exact Real.smoothTransition.one_of_one_le hy.le
          rw [heq.deriv_eq]
          simp
      simp [hd]
      positivity
  have he_mem (n : ℕ) : MemLp (e n) 2 volume :=
    (hprod.const_smul (4 * M)).of_le (he_meas n) (ae_of_all _ (hnorm n))
  have hbound (n : ℕ) : ∀ᵐ x ∂volume,
      ‖e n x‖ₑ ^ (2 : ℝ) ≤ ‖(4 * M) • (f.val x • D x)‖ₑ ^ (2 : ℝ) := by
    filter_upwards [] with x
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hnorm n x)
  have hfin : (∫⁻ x, ‖(4 * M) • (f.val x • D x)‖ₑ ^ (2 : ℝ) ∂volume) ≠ ∞ :=
    ne_of_lt (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (hprod.const_smul (4 * M)).eLpNorm_lt_top)
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      Tendsto (fun n ↦ ‖e n x‖ₑ ^ (2 : ℝ)) atTop (nhds 0) := by
    by_cases hx : φ x = 0
    · simp [e, apm_m01J04_globalLocalizedH1, apm_m01J04_H1mul_val, hx]
    · obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (Real.sqrt 2 / |φ x|)
      have hev : ∀ᶠ n : ℕ in atTop, e n x = 0 := by
        filter_upwards [eventually_atTop.2 ⟨N, fun _ hn ↦ hn⟩] with n hn
        have habs : Real.sqrt 2 < (n + 1 : ℝ) * |φ x| := by
          have hp : 0 < |φ x| := abs_pos.mpr hx
          apply (div_lt_iff₀ hp).mp
          exact lt_of_lt_of_le hN (by exact_mod_cast Nat.le_add_right_of_le hn)
        have hsquares : (2 : ℝ) < (n + 1 : ℝ) ^ 2 * φ x ^ 2 := by
          have := (sq_lt_sq₀ (Real.sqrt_nonneg 2)
            (mul_nonneg (by positivity) (abs_nonneg _))).2 habs
          rw [Real.sq_sqrt (by norm_num), mul_pow, sq_abs] at this
          exact this
        have harg : 1 < φ x ^ 2 / (1 / (n + 1 : ℝ)) ^ 2 - 1 := by
          have hnpos : 0 < (n + 1 : ℝ) := by positivity
          field_simp
          nlinarith
        have heq : Filter.EventuallyEq (nhds
            (φ x ^ 2 / (1 / (n + 1 : ℝ)) ^ 2 - 1))
            Real.smoothTransition (fun _ ↦ 1) := by
          filter_upwards [eventually_gt_nhds harg] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        have hd : deriv Real.smoothTransition
            (φ x ^ 2 / (1 / (n + 1 : ℝ)) ^ 2 - 1) = 0 := by
          rw [heq.deriv_eq]
          simp
        simp only [e]
        rw [apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_collar_aux_fderiv
          φ hφ.1]
        apply smul_eq_zero.mpr
        right
        rw [hd]
        rw [WithLp.toLp_eq_zero]
        funext i
        simp
      exact tendsto_const_nhds.congr' (hev.mono fun n hn ↦ by simp [hn])
  have hlin : Tendsto (fun n ↦ ∫⁻ x, ‖e n x‖ₑ ^ (2 : ℝ) ∂volume)
      atTop (nhds 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun x ↦ ‖(4 * M) • (f.val x • D x)‖ₑ ^ (2 : ℝ))
      (fun n ↦ (he_mem n).1.enorm.pow_const _) hbound hfin (ae_of_all _ hpoint)
  have help : Tendsto (fun n ↦ eLpNorm (e n) 2 volume) atTop (nhds 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    norm_num
    have hc : Continuous (fun z : ℝ≥0∞ ↦ z ^ (1 / 2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hlin
  have hreal := (ENNReal.tendsto_toReal_iff
    (fun n ↦ (he_mem n).eLpNorm_ne_top) ENNReal.zero_ne_top).2 help
  simpa [e] using hreal

/-- Triangle inequality: the product-rule gradient difference is the bulk term
plus the collar term (`apm_m01J04_H1mul_grad`). -/
lemma apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_split
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    (hbulk : Tendsto (fun n : ℕ ↦
      (eLpNorm (fun x ↦ apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ)) x • (apm_m01J04_globalLocalizedH1 φ hφ f).grad x -
          (apm_m01J04_globalLocalizedH1 φ hφ f).grad x) 2 volume).toReal) atTop (nhds 0))
    (hcollar : Tendsto (fun n : ℕ ↦
      (eLpNorm (fun x ↦ (apm_m01J04_globalLocalizedH1 φ hφ f).val x • WithLp.toLp 2 (fun i ↦
          fderiv ℝ (apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ))) x (EuclideanSpace.single i 1))) 2 volume).toReal) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      (eLpNorm (fun x ↦
        (apm_m01J04_H1mul
          (apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ)))
          (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ _)
          (apm_m01J04_globalLocalizedH1 φ hφ f)).grad x -
        (apm_m01J04_globalLocalizedH1 φ hφ f).grad x) 2
        (volume.restrict Set.univ)).toReal) atTop (nhds 0) := by
  let c (n : ℕ) :=
    apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ))
  let g := apm_m01J04_globalLocalizedH1 φ hφ f
  let bulk (n : ℕ) := fun x ↦ c n x • g.grad x - g.grad x
  let collar (n : ℕ) := fun x ↦ g.val x • WithLp.toLp 2 (fun i ↦
    fderiv ℝ (c n) x (EuclideanSpace.single i 1))
  have hbulk_mem (n : ℕ) : MemLp (bulk n) 2 volume := by
    have hc := apm_m01J04_isTestFunction_memLp
      (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ
        (1 / (n + 1 : ℝ))) ⊤
    simpa [bulk, c, g] using
      ((g.grad_memLp.smul hc).sub g.grad_memLp)
  have hcollar_mem (n : ℕ) : MemLp (collar n) 2 volume := by
    have hD := apm_m01J04_isTestFunction_fderivField_memLp
      (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ
        (1 / (n + 1 : ℝ))) ⊤
    simpa [collar, c, g, smul_comm] using hD.smul g.val_memLp
  have heq (n : ℕ) :
      (fun x ↦
        (apm_m01J04_H1mul (c n)
          (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ _)
          g).grad x - g.grad x) =
        fun x ↦ bulk n x + collar n x := by
    funext x
    rw [apm_m01J04_H1mul_grad]
    dsimp [bulk, collar]
    abel
  have hbound (n : ℕ) :
      (eLpNorm (fun x ↦
        (apm_m01J04_H1mul (c n)
          (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ _)
          g).grad x - g.grad x) 2 volume).toReal ≤
        (eLpNorm (bulk n) 2 volume).toReal +
          (eLpNorm (collar n) 2 volume).toReal := by
    rw [heq]
    have hle := eLpNorm_add_le (hbulk_mem n).1 (hcollar_mem n).1
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have htop : eLpNorm (bulk n) 2 volume + eLpNorm (collar n) 2 volume ≠ ⊤ :=
      ENNReal.add_ne_top.2
        ⟨(hbulk_mem n).eLpNorm_ne_top, (hcollar_mem n).eLpNorm_ne_top⟩
    calc
      _ ≤ (eLpNorm (bulk n) 2 volume + eLpNorm (collar n) 2 volume).toReal :=
        ENNReal.toReal_mono htop hle
      _ = _ := ENNReal.toReal_add
        (hbulk_mem n).eLpNorm_ne_top (hcollar_mem n).eLpNorm_ne_top
  have hresult : Tendsto (fun n ↦
      (eLpNorm (fun x ↦
        (apm_m01J04_H1mul (c n)
          (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ _)
          g).grad x - g.grad x) 2 volume).toReal) atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ ENNReal.toReal_nonneg) hbound
    simpa [bulk, collar, c, g] using hbulk.add hcollar
  simpa [c, g] using hresult

/-- Gradient part of the core convergence.  The product gradient is
`χ_r • ∇(fφ) + (fφ) • ∇χ_r`; the first term converges as in the value case,
and the collar term `f φ · smoothTransition'(φ²/r² − 1) · 2φ∇φ / r²` is
bounded by `4 M |f| |∇φ|` (since `φ² ≤ 2r²` on the collar) and tends to `0`
pointwise, so dominated convergence applies. -/
lemma apm_m01J04_localization_core_approx_aux_grad_tendsto
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    Tendsto (fun n : ℕ ↦
      (eLpNorm (fun x ↦
        (apm_m01J04_H1mul
          (apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ)))
          (apm_m01J04_localization_core_approx_aux_cutoff_isTestFunction hφ _)
          (apm_m01J04_globalLocalizedH1 φ hφ f)).grad x -
        (apm_m01J04_globalLocalizedH1 φ hφ f).grad x) 2
        (volume.restrict Set.univ)).toReal) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ :=
    apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_deriv_bound
  exact apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_split φ hφ f
    (apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_bulk φ hφ f)
    (apm_m01J04_localization_core_approx_aux_grad_tendsto_aux_collar φ hφ f hM)

/-- The remaining local Meyers--Serrin interface.  Unlike
`apm_m01J04_isH1Zero_mul`, the input is an arbitrary encoded `H¹` function;
compact localization by `φ` is what must produce the zero-boundary
approximation. -/
lemma apm_m01J04_localization_core_approx
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) {eta : ℝ} (heta : 0 < eta) :
    ∃ (epsilon : ℝ) (u : apm_m01J04_H1 d Set.univ),
      0 < epsilon ∧
      Function.support u.val ⊆ {x | epsilon ≤ |φ x|} ∧
      Function.support u.grad ⊆ {x | epsilon ≤ |φ x|} ∧
      apm_m01J04_H1dist u (apm_m01J04_globalLocalizedH1 φ hφ f) < eta := by
  set g := apm_m01J04_globalLocalizedH1 φ hφ f
  have hT := apm_m01J04_H1dist_tendsto_zero_of_components _ g
    (apm_m01J04_localization_core_approx_aux_val_tendsto φ hφ f)
    (apm_m01J04_localization_core_approx_aux_grad_tendsto φ hφ f)
  obtain ⟨n, hn⟩ := ((hT.eventually (gt_mem_nhds heta))).exists
  have hr : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  refine ⟨1 / (n + 1 : ℝ), _, hr, ?_, ?_, hn⟩
  · rw [apm_m01J04_H1mul_val]
    intro x hx
    exact apm_m01J04_localization_core_approx_aux_cutoff_support hr
      (Function.support_mul_subset_right _ _ hx)
  · rw [apm_m01J04_H1mul_grad]
    intro x hx
    by_contra hxr
    have h0 : apm_m01J04_localization_core_approx_aux_cutoff φ (1 / (n + 1 : ℝ)) x = 0 :=
      Function.notMem_support.mp fun h ↦ hxr
        (apm_m01J04_localization_core_approx_aux_cutoff_support hr h)
    have h1 : fderiv ℝ (apm_m01J04_localization_core_approx_aux_cutoff φ
        (1 / (n + 1 : ℝ))) x = 0 :=
      Function.notMem_support.mp fun h ↦ hxr
        (apm_m01J04_localization_core_approx_aux_cutoff_fderiv_support
          hφ.1.continuous hr h)
    exact hx (by simp only [h0, h1]; simp; right; rfl)

noncomputable def apm_m01J04_mollify_exists_compact_core_aux_bump
    {d : ℕ} (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨n + 1, 2 * (n + 1), by positivity, by
    have h : (0 : ℝ) < n + 1 := by positivity
    linarith⟩

noncomputable def apm_m01J04_mollify_exists_compact_core_aux_cutoff
    {d : ℕ} (n : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x ↦ (apm_m01J04_mollify_exists_compact_core_aux_bump n).toFun x

lemma apm_m01J04_mollify_exists_compact_core_aux_test
    {d : ℕ} (n : ℕ) :
    apm_m01J04_isTestFunction (Set.univ : Set (EuclideanSpace ℝ (Fin d)))
      (apm_m01J04_mollify_exists_compact_core_aux_cutoff n) := by
  unfold apm_m01J04_mollify_exists_compact_core_aux_cutoff
  exact ⟨ContDiffBump.contDiff _, ContDiffBump.hasCompactSupport _, Set.subset_univ _⟩

/-- Leaf: multiplication by the expanding bumps (`rIn = n+1`, `rOut = 2(n+1)`,
so `‖∇b_n‖∞ = O(1/n)` since the ratio is fixed) converges to the identity in
`H1dist`: value and bulk-gradient terms by dominated convergence, the
`u.val • ∇b_n` term by the `O(1/n)` bound. -/
lemma apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_scale
    {d : ℕ} (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    apm_m01J04_mollify_exists_compact_core_aux_cutoff n x =
      apm_m01J04_mollify_exists_compact_core_aux_cutoff 0
        ((n + 1 : ℝ)⁻¹ • x) := by
  have hr : 2 * (n + 1 : ℝ) / (n + 1) = 2 := by
    field_simp
  unfold apm_m01J04_mollify_exists_compact_core_aux_cutoff
    apm_m01J04_mollify_exists_compact_core_aux_bump
  rw [ContDiffBump.apply, ContDiffBump.apply]
  dsimp only
  rw [hr]
  norm_num

lemma apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_fderiv
    {d : ℕ} (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (apm_m01J04_mollify_exists_compact_core_aux_cutoff n) x =
      (n + 1 : ℝ)⁻¹ • fderiv ℝ
        (apm_m01J04_mollify_exists_compact_core_aux_cutoff 0)
        ((n + 1 : ℝ)⁻¹ • x) := by
  have heq : apm_m01J04_mollify_exists_compact_core_aux_cutoff (d := d) n =
      apm_m01J04_mollify_exists_compact_core_aux_cutoff 0 ∘
        fun x ↦ (n + 1 : ℝ)⁻¹ • x := by
    funext y
    exact apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_scale n y
  rw [heq, fderiv_comp]
  · ext y
    have hs : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) ↦
        (n + 1 : ℝ)⁻¹ • z) x =
        (n + 1 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ
          (EuclideanSpace ℝ (Fin d)) := by
      simpa using fderiv_const_smul (𝕜 := ℝ)
        (x := x) differentiableAt_id (n + 1 : ℝ)⁻¹
    rw [hs]
    simp
  · exact (apm_m01J04_mollify_exists_compact_core_aux_test (d := d) 0).1.differentiable
      (by simp) _
  · fun_prop

lemma apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_eventually_one
    {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ∀ᶠ n : ℕ in atTop,
      apm_m01J04_mollify_exists_compact_core_aux_cutoff n x = 1 := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_atTop.2 ⟨N, fun _ hn ↦ hn⟩] with n hn
  apply (apm_m01J04_mollify_exists_compact_core_aux_bump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ (n + 1 : ℝ)
  exact hN.le.trans (by exact_mod_cast Nat.le_add_right_of_le hn)

lemma apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_mul
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume) :
    Tendsto (fun n ↦ (eLpNorm (fun x ↦
      apm_m01J04_mollify_exists_compact_core_aux_cutoff n x • f x - f x)
      2 volume).toReal) atTop (nhds 0) := by
  let b : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n ↦
    apm_m01J04_mollify_exists_compact_core_aux_cutoff n
  let e : ℕ → EuclideanSpace ℝ (Fin d) → E := fun n x ↦ b n x • f x - f x
  have he_mem (n : ℕ) : MemLp (e n) 2 volume := by
    apply hf.of_le
    · exact ((((apm_m01J04_mollify_exists_compact_core_aux_test n).1.continuous
          ).aestronglyMeasurable.smul hf.1).sub hf.1)
    · filter_upwards [] with x
      rw [show e n x = (b n x - 1) • f x by simp [e, b, sub_smul], norm_smul]
      have h0 := (apm_m01J04_mollify_exists_compact_core_aux_bump n).nonneg' x
      have h1 := (apm_m01J04_mollify_exists_compact_core_aux_bump n).le_one (x := x)
      apply mul_le_of_le_one_left (norm_nonneg _)
      simpa [b, apm_m01J04_mollify_exists_compact_core_aux_cutoff,
        Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr h1)] using h0
  have hbound (n : ℕ) : ∀ᵐ x ∂volume,
      ‖e n x‖ₑ ^ (2 : ℝ) ≤ ‖f x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [] with x
    rw [show e n x = (b n x - 1) • f x by simp [e, b, sub_smul], enorm_smul]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply mul_le_of_le_one_left (bot_le)
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
    have h0 := (apm_m01J04_mollify_exists_compact_core_aux_bump n).nonneg' x
    have h1 := (apm_m01J04_mollify_exists_compact_core_aux_bump n).le_one (x := x)
    simpa [b, apm_m01J04_mollify_exists_compact_core_aux_cutoff,
      abs_of_nonpos (sub_nonpos.mpr h1)] using h0
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume) ≠ ∞ :=
    ne_of_lt (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hf.eLpNorm_lt_top)
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      Tendsto (fun n ↦ ‖e n x‖ₑ ^ (2 : ℝ)) atTop (nhds 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (nhds 0)).congr'
    filter_upwards [apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_eventually_one x]
      with n hn
    simp [e, b, hn]
  have hlin : Tendsto (fun n ↦ ∫⁻ x, ‖e n x‖ₑ ^ (2 : ℝ) ∂volume)
      atTop (nhds 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun x ↦ ‖f x‖ₑ ^ (2 : ℝ))
      (fun n ↦ (he_mem n).1.enorm.pow_const _) hbound hfin (ae_of_all _ hpoint)
  have help : Tendsto (fun n ↦ eLpNorm (e n) 2 volume) atTop (nhds 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    norm_num
    have hc : Continuous (fun z : ℝ≥0∞ ↦ z ^ (1 / 2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa [Function.comp_def] using hc.continuousAt.tendsto.comp hlin
  have hreal := (ENNReal.tendsto_toReal_iff
    (fun n ↦ (he_mem n).eLpNorm_ne_top) ENNReal.zero_ne_top).2 help
  simpa [e, b] using hreal

lemma apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_lower
    {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : MemLp f 2 volume) :
    Tendsto (fun n ↦ (eLpNorm (fun x ↦ f x • WithLp.toLp 2
      (fun i ↦ fderiv ℝ
        (apm_m01J04_mollify_exists_compact_core_aux_cutoff n) x
          (EuclideanSpace.single i 1))) 2 volume).toReal) atTop (nhds 0) := by
  let D : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun n x ↦
    WithLp.toLp 2 (fun i ↦ fderiv ℝ
      (apm_m01J04_mollify_exists_compact_core_aux_cutoff n) x
        (EuclideanSpace.single i 1))
  have hDcont (n : ℕ) : Continuous (D n) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp
      (continuous_pi fun i ↦
        ((apm_m01J04_mollify_exists_compact_core_aux_test n).1.continuous_fderiv
          (by simp)).clm_apply continuous_const)
  have hD0supp : HasCompactSupport (D 0) := by
    apply ((apm_m01J04_mollify_exists_compact_core_aux_test (d := d) 0).2.1.fderiv ℝ).mono'
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
    have hz : fderiv ℝ (apm_m01J04_mollify_exists_compact_core_aux_cutoff 0) x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    ext i
    simp [D, hz]
  obtain ⟨C, hC⟩ := hD0supp.exists_bound_of_continuous (hDcont 0)
  let s : ℕ → ℝ := fun n ↦ (n + 1 : ℝ)⁻¹
  have hDs (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
      D n x = s n • D 0 (s n • x) := by
    ext i
    change fderiv ℝ (apm_m01J04_mollify_exists_compact_core_aux_cutoff n) x
        (EuclideanSpace.single i 1) = _
    rw [apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_fderiv]
    simp [D, s]
  have hDnorm (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
      ‖D n x‖ ≤ s n * |C| := by
    rw [hDs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ s n)]
    exact mul_le_mul_of_nonneg_left ((hC _).trans (le_abs_self C)) (by positivity)
  have hDtop (n : ℕ) : eLpNorm (D n) ⊤ volume ≤ ENNReal.ofReal (s n * |C|) := by
    have h := eLpNorm_le_of_ae_bound (p := (⊤ : ℝ≥0∞))
      (μ := volume) (ae_of_all volume (hDnorm n))
    simpa using h
  have hle (n : ℕ) : eLpNorm (fun x ↦ f x • D n x) 2 volume ≤
      eLpNorm f 2 volume * ENNReal.ofReal (s n * |C|) := by
    exact (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := ⊤) (r := 2)
      (hDcont n).aestronglyMeasurable hf.1).trans
        (mul_le_mul_left' (hDtop n) _)
  have hreal (n : ℕ) : (eLpNorm (fun x ↦ f x • D n x) 2 volume).toReal ≤
      (eLpNorm f 2 volume).toReal * (s n * |C|) := by
    have htop : eLpNorm f 2 volume * ENNReal.ofReal (s n * |C|) ≠ ⊤ :=
      ENNReal.mul_ne_top hf.eLpNorm_ne_top ENNReal.ofReal_ne_top
    calc
      _ ≤ (eLpNorm f 2 volume * ENNReal.ofReal (s n * |C|)).toReal :=
        ENNReal.toReal_mono htop (hle n)
      _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  apply squeeze_zero (fun n ↦ ENNReal.toReal_nonneg) hreal
  have hs : Tendsto s atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))
  convert
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (eLpNorm f 2 volume).toReal)
      atTop (nhds (eLpNorm f 2 volume).toReal)).mul
      (hs.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ |C|) atTop (nhds |C|))) : Tendsto
      (fun n ↦ (eLpNorm f 2 volume).toReal * (s n * |C|))
        atTop (nhds ((eLpNorm f 2 volume).toReal * (0 * |C|)))) using 1 <;> simp

lemma apm_m01J04_mollify_exists_compact_core_aux_tendsto
    {d : ℕ} (u : apm_m01J04_H1 d Set.univ) :
    Tendsto (fun n ↦ apm_m01J04_H1dist
      (apm_m01J04_H1mul
        (apm_m01J04_mollify_exists_compact_core_aux_cutoff n)
        (apm_m01J04_mollify_exists_compact_core_aux_test n) u) u)
      atTop (nhds 0) := by
  let b : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n ↦
    apm_m01J04_mollify_exists_compact_core_aux_cutoff n
  let hb (n : ℕ) := apm_m01J04_mollify_exists_compact_core_aux_test (d := d) n
  let a (n : ℕ) := apm_m01J04_H1mul (b n) (hb n) u
  have hval : Tendsto (fun n ↦
      (eLpNorm (fun x ↦ (a n).val x - u.val x) 2 volume).toReal)
      atTop (nhds 0) := by
    simpa [a, b, hb, apm_m01J04_H1mul_val, mul_comm] using
      apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_mul u.val
        (by simpa using u.val_memLp)
  let bulk : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun n x ↦ b n x • u.grad x - u.grad x
  let lower : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun n x ↦ u.val x • WithLp.toLp 2 (fun i ↦
      fderiv ℝ (b n) x (EuclideanSpace.single i 1))
  have hbulk : Tendsto (fun n ↦ (eLpNorm (bulk n) 2 volume).toReal)
      atTop (nhds 0) := by
    simpa [bulk, b] using
      apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_mul u.grad
        (by simpa using u.grad_memLp)
  have hlower : Tendsto (fun n ↦ (eLpNorm (lower n) 2 volume).toReal)
      atTop (nhds 0) := by
    simpa [lower, b] using
      apm_m01J04_mollify_exists_compact_core_aux_tendsto_aux_lower u.val
        (by simpa using u.val_memLp)
  have heq (n : ℕ) : (fun x ↦ (a n).grad x - u.grad x) =
      fun x ↦ bulk n x + lower n x := by
    funext x
    simp only [a, b, bulk, lower, apm_m01J04_H1mul_grad]
    abel
  have hlower_mem (n : ℕ) : MemLp (lower n) 2 volume := by
    have hD := apm_m01J04_isTestFunction_fderivField_memLp (hb n) ⊤
    simpa [lower, b, smul_comm] using hD.smul u.val_memLp
  have hbulk_mem (n : ℕ) : MemLp (bulk n) 2 volume := by
    have ha : MemLp (a n).grad 2 volume := by simpa using (a n).grad_memLp
    have hu : MemLp u.grad 2 volume := by simpa using u.grad_memLp
    have h := (ha.sub hu).sub (hlower_mem n)
    convert h using 1
    funext x
    have hx := congrFun (heq n) x
    simp only [Pi.sub_apply]
    rw [hx]
    abel
  have hbound (n : ℕ) :
      (eLpNorm (fun x ↦ (a n).grad x - u.grad x) 2 volume).toReal ≤
        (eLpNorm (bulk n) 2 volume).toReal +
          (eLpNorm (lower n) 2 volume).toReal := by
    rw [heq]
    have hle := eLpNorm_add_le (hbulk_mem n).1 (hlower_mem n).1
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have htop : eLpNorm (bulk n) 2 volume + eLpNorm (lower n) 2 volume ≠ ⊤ :=
      ENNReal.add_ne_top.2
        ⟨(hbulk_mem n).eLpNorm_ne_top, (hlower_mem n).eLpNorm_ne_top⟩
    calc
      _ ≤ (eLpNorm (bulk n) 2 volume + eLpNorm (lower n) 2 volume).toReal :=
        ENNReal.toReal_mono htop hle
      _ = _ := ENNReal.toReal_add (hbulk_mem n).eLpNorm_ne_top
        (hlower_mem n).eLpNorm_ne_top
  have hgrad : Tendsto (fun n ↦
      (eLpNorm (fun x ↦ (a n).grad x - u.grad x) 2 volume).toReal)
      atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ ENNReal.toReal_nonneg) hbound
    simpa using hbulk.add hlower
  have hval' : Tendsto (fun n ↦
      (eLpNorm (fun x ↦ (a n).val x - u.val x) 2
        (volume.restrict Set.univ)).toReal) atTop (nhds 0) := by simpa using hval
  have hgrad' : Tendsto (fun n ↦
      (eLpNorm (fun x ↦ (a n).grad x - u.grad x) 2
        (volume.restrict Set.univ)).toReal) atTop (nhds 0) := by simpa using hgrad
  simpa [a, b, hb] using
    apm_m01J04_H1dist_tendsto_zero_of_components a u hval' hgrad'

/-- Spatial truncation reduces the general auxiliary statement to a genuinely
compactly supported global Sobolev pair.  The compact carrier lies in
`closure K`; closed thickening is unchanged on replacing a set by its closure. -/
lemma apm_m01J04_mollify_exists_compact_core
    {d : ℕ} (u : apm_m01J04_H1 d Set.univ)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (huval : Function.support u.val ⊆ K)
    (hugrad : Function.support u.grad ⊆ K)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ (w : apm_m01J04_H1 d Set.univ)
      (C : Set (EuclideanSpace ℝ (Fin d))),
      IsCompact C ∧ C ⊆ closure K ∧
      Function.support w.val ⊆ C ∧ Function.support w.grad ⊆ C ∧
      apm_m01J04_H1dist w u < eta := by
  have hlim := apm_m01J04_mollify_exists_compact_core_aux_tendsto u
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds heta)).exists
  let b := apm_m01J04_mollify_exists_compact_core_aux_cutoff (d := d) n
  let hb := apm_m01J04_mollify_exists_compact_core_aux_test (d := d) n
  let w := apm_m01J04_H1mul b hb u
  let C := tsupport b ∩ closure K
  refine ⟨w, C, ?_, inter_subset_right, ?_, ?_, ?_⟩
  · exact hb.2.1.inter_right isClosed_closure
  · rw [apm_m01J04_H1mul_val]
    intro x hx
    refine ⟨subset_tsupport _ (Function.support_mul_subset_right _ _ hx), ?_⟩
    exact subset_closure (huval (Function.support_mul_subset_left _ _ hx))
  · rw [apm_m01J04_H1mul_grad]
    intro x hx
    by_contra hxc
    rcases not_and_or.mp hxc with hxb | hxK
    · have hb0 : b x = 0 := Function.notMem_support.mp fun h ↦
        hxb (subset_tsupport b h)
      have hdb0 : fderiv ℝ b x = 0 := Function.notMem_support.mp fun h ↦
        hxb (support_fderiv_subset ℝ h)
      have hvec : WithLp.toLp 2
          (fun i ↦ fderiv ℝ b x (EuclideanSpace.single i 1)) = 0 := by
        rw [hdb0]
        rfl
      exact hx (by simp [hb0, hvec])
    · have huv0 : u.val x = 0 := Function.notMem_support.mp fun h ↦
        hxK (subset_closure (huval h))
      have hug0 : u.grad x = 0 := Function.notMem_support.mp fun h ↦
        hxK (subset_closure (hugrad h))
      exact hx (by simp [huv0, hug0])
  · simpa [w, b, hb] using hn

lemma apm_m01J04_mollify_exists_L2_kernel_aux_kernel
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta) :
    ∃ κ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ ∧
      HasCompactSupport κ ∧
      Function.support κ ⊆ Metric.closedBall 0 delta ∧
      (∀ x, 0 ≤ κ x) ∧ (∫ x, κ x ∂volume) = 1 := by
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨delta / 2, delta, half_pos hdelta, half_lt_self hdelta⟩
  refine ⟨φ.normed volume, φ.contDiff_normed, φ.hasCompactSupport_normed,
    ?_, φ.nonneg_normed, φ.integral_normed⟩
  rw [φ.support_normed_eq]
  exact Metric.ball_subset_closedBall

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_integrable
    {d : ℕ} (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκ : ∀ x, 0 ≤ κ x) (hint : (∫ x, κ x ∂volume) = 1) :
    Integrable κ volume := by
  exact integrable_of_integral_eq_one hint

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_L1
    {d : ℕ} (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκ : ∀ x, 0 ≤ κ x) (hint : (∫ x, κ x ∂volume) = 1) :
    eLpNorm κ 1 volume = 1 := by
  have hi : Integrable κ volume :=
    apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_integrable κ hκ hint
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hκ _), hint, ENNReal.ofReal_one]

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_smooth_dense
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume)
    {a : ℝ} (ha : 0 < a) :
    ∃ g : EuclideanSpace ℝ (Fin d) → E,
      HasCompactSupport g ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (eLpNorm (f - g) 2 volume).toReal ≤ a := by
  obtain ⟨g, hgK, hgS, hg⟩ := hf.exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2) ha
  refine ⟨g, hgK, hgS, ?_⟩
  calc
    (eLpNorm (f - g) 2 volume).toReal
        ≤ (ENNReal.ofReal a).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
    _ = a := ENNReal.toReal_ofReal ha.le

/-- `L²` continuity of translation. -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_translate
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ ρ0 →
      (eLpNorm (fun x ↦ f (x - y) - f x) 2 volume).toReal ≤ ε := by
  obtain ⟨g, hgK, hgC, hfg⟩ :=
    apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_smooth_dense
      f hf (by positivity : (0 : ℝ) < ε / 4)
  obtain ⟨r, hr, hKr⟩ := hgK.exists_isCompact_cthickening
  let A : ℝ := (volume (Metric.cthickening r (tsupport g)) ^ (1 / 2 : ℝ)).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hgU : UniformContinuous g :=
    hgK.uniformContinuous_of_continuous hgC.continuous
  obtain ⟨δ, hδ, hgδ⟩ := (Metric.uniformContinuous_iff.1 hgU)
    (ε / (2 * (A + 1))) (by positivity)
  refine ⟨min r (δ / 2), lt_min hr (half_pos hδ), fun y hy ↦ ?_⟩
  have hyr : ‖y‖ ≤ r := hy.trans (min_le_left _ _)
  have hyδ : ‖y‖ < δ :=
    (hy.trans (min_le_right _ _)).trans_lt (half_lt_self hδ)
  let G : EuclideanSpace ℝ (Fin d) → E := fun x ↦ g (x - y) - g x
  have hGsupp : Function.support G ⊆ Metric.cthickening r (tsupport g) := by
    intro x hx
    by_contra hxK
    have hg0 : g x = 0 := Function.notMem_support.mp fun hxg ↦
      hxK (Metric.mem_cthickening_of_dist_le x x r _ (subset_tsupport g hxg) (by simp [hr.le]))
    have hgy0 : g (x - y) = 0 := Function.notMem_support.mp fun hxyg ↦
      hxK (Metric.mem_cthickening_of_dist_le x (x - y) r _
        (subset_tsupport g hxyg) (by simpa [dist_eq_norm] using hyr))
    exact hx (by simp [G, hg0, hgy0])
  have hGmeas : AEStronglyMeasurable G volume :=
    ((hgC.continuous.comp (continuous_id.sub continuous_const)).sub hgC.continuous).aestronglyMeasurable
  have hGtop : eLpNorm G ⊤ volume ≤ ENNReal.ofReal (ε / (2 * (A + 1))) := by
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [] with x
    have hxy : dist (x - y) x < δ := by simpa [dist_eq_norm] using hyδ
    simpa [G, dist_eq_norm] using le_of_lt (hgδ hxy)
  have hG2 : (eLpNorm G 2 volume).toReal ≤ ε / 2 := by
    have hres : eLpNorm G 2 volume =
        eLpNorm G 2 (volume.restrict (Metric.cthickening r (tsupport g))) := by
      set_option maxHeartbeats 800000 in
        exact eLpNorm_restrict_eq_of_support_subset
          (f := G) (s := Metric.cthickening r (tsupport g))
          (p := (2 : ℝ≥0∞)) (μ := volume) hGsupp |>.symm
    rw [hres]
    have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict (Metric.cthickening r (tsupport g)))
      (show (2 : ℝ≥0∞) ≤ ⊤ by simp)
      hGmeas.restrict
    have hpow : (volume.restrict (Metric.cthickening r (tsupport g)) Set.univ) ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / (⊤ : ℝ≥0∞).toReal) =
        volume (Metric.cthickening r (tsupport g)) ^ (1 / 2 : ℝ) := by
      simp [hKr.measurableSet]
    rw [hpow] at hle
    have htop' : eLpNorm G ⊤ (volume.restrict (Metric.cthickening r (tsupport g))) ≤
        ENNReal.ofReal (ε / (2 * (A + 1))) := by
      exact (eLpNorm_mono_measure (p := (⊤ : ℝ≥0∞)) G
        Measure.restrict_le_self).trans hGtop
    set_option maxHeartbeats 1000000 in
     calc
      (eLpNorm G 2 (volume.restrict (Metric.cthickening r (tsupport g)))).toReal
          ≤ (ENNReal.ofReal (ε / (2 * (A + 1))) *
              volume (Metric.cthickening r (tsupport g)) ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKr.measure_ne_top))
          (hle.trans (mul_le_mul_right' htop' _))
      _ = ε / (2 * (A + 1)) * A := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      _ ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), div_mul_eq_mul_div]
        nlinarith
  have htrans : (eLpNorm (fun x ↦ (f - g) (x - y)) 2 volume).toReal =
      (eLpNorm (f - g) 2 volume).toReal := by
    have hm := measurePreserving_sub_right volume y
    simpa [Function.comp_def] using congrArg ENNReal.toReal
      (eLpNorm_comp_measurePreserving
        (hf.sub (hgC.continuous.memLp_of_hasCompactSupport hgK
          (p := (2 : ℝ≥0∞)) (μ := volume))).1 hm)
  have hfgmem : MemLp (f - g) 2 volume :=
    hf.sub (hgC.continuous.memLp_of_hasCompactSupport hgK
      (p := (2 : ℝ≥0∞)) (μ := volume))
  have hm := measurePreserving_sub_right volume y
  have htrmeas : AEStronglyMeasurable (fun x ↦ (f - g) (x - y)) volume :=
    hfgmem.1.comp_quasiMeasurePreserving hm.quasiMeasurePreserving
  have hgfmeas : AEStronglyMeasurable (fun x ↦ g x - f x) volume :=
    (hgC.continuous.aestronglyMeasurable.sub hf.1)
  have htri := eLpNorm_add_le htrmeas (hGmeas.add hgfmeas) (p := (2 : ℝ≥0∞))
  have htri2 := eLpNorm_add_le hGmeas hgfmeas (p := (2 : ℝ≥0∞))
  have htrmem : MemLp (fun x ↦ (f - g) (x - y)) 2 volume :=
    hfgmem.comp_measurePreserving hm
  have hGc : Continuous G :=
    (hgC.continuous.comp (continuous_id.sub continuous_const)).sub hgC.continuous
  have hGmem : MemLp G 2 volume :=
    hGc.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hKr hGsupp)
      (p := (2 : ℝ≥0∞)) (μ := volume)
  have hgfmem : MemLp (fun x ↦ g x - f x) 2 volume :=
    (hgC.continuous.memLp_of_hasCompactSupport hgK
      (p := (2 : ℝ≥0∞)) (μ := volume)).sub hf
  have hfinite : eLpNorm (fun x ↦ (f - g) (x - y)) 2 volume +
      (eLpNorm G 2 volume + eLpNorm (fun x ↦ g x - f x) 2 volume) ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨htrmem.eLpNorm_ne_top,
      ENNReal.add_ne_top.2 ⟨hGmem.eLpNorm_ne_top, hgfmem.eLpNorm_ne_top⟩⟩
  have hmain : eLpNorm (fun x ↦ f (x - y) - f x) 2 volume ≤
      eLpNorm (fun x ↦ (f - g) (x - y)) 2 volume +
        (eLpNorm G 2 volume + eLpNorm (fun x ↦ g x - f x) 2 volume) := by
    have heq : (fun x ↦ f (x - y) - f x) =
        (fun x ↦ (f - g) (x - y)) + (fun x ↦ G x + (g x - f x)) := by
      funext x
      simp [G]
    rw [heq]
    exact (htri (by norm_num)).trans
      (add_le_add_right (htri2 (by norm_num)) _)
  calc
    (eLpNorm (fun x ↦ f (x - y) - f x) 2 volume).toReal
        ≤ (eLpNorm (fun x ↦ (f - g) (x - y)) 2 volume +
          (eLpNorm G 2 volume + eLpNorm (fun x ↦ g x - f x) 2 volume)).toReal :=
      ENNReal.toReal_mono hfinite hmain
    _ = (eLpNorm (fun x ↦ (f - g) (x - y)) 2 volume).toReal +
          ((eLpNorm G 2 volume).toReal + (eLpNorm (fun x ↦ g x - f x) 2 volume).toReal) := by
      rw [ENNReal.toReal_add, ENNReal.toReal_add]
      · exact hGmem.eLpNorm_ne_top
      · exact hgfmem.eLpNorm_ne_top
      · exact htrmem.eLpNorm_ne_top
      · exact ENNReal.add_ne_top.2 ⟨hGmem.eLpNorm_ne_top, hgfmem.eLpNorm_ne_top⟩
    _ ≤ ε := by
      rw [htrans]
      have hgf : (eLpNorm (fun x ↦ g x - f x) 2 volume).toReal =
          (eLpNorm (f - g) 2 volume).toReal := by
        have he : (fun x ↦ g x - f x) = -(f - g) := by
          funext x
          simp
        rw [he, eLpNorm_neg]
      rw [hgf]
      linarith

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_integrable
    {d : ℕ} (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκ0 : ∀ x, 0 ≤ κ x) (hκ1 : (∫ x, κ x ∂volume) = 1) :
    Integrable κ volume := by
  exact integrable_of_integral_eq_one hκ1

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_translate
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume)
    (y : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun x ↦ f (x - y)) 2 volume ∧
      eLpNorm (fun x ↦ f (x - y)) 2 volume = eLpNorm f 2 volume := by
  have hmp := measurePreserving_sub_right volume y
  have hc : (fun x ↦ f (x - y)) = f ∘ (fun x ↦ x - y) := rfl
  rw [hc]
  exact ⟨hf.comp_measurePreserving hmp,
    eLpNorm_comp_measurePreserving hf.1 hmp⟩

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_support
    {d : ℕ} {ρ : ℝ} (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκs : Function.support κ ⊆ Metric.closedBall 0 ρ) :
    ∀ y, κ y ≠ 0 → ‖y‖ ≤ ρ := by
  intro y hy
  simpa [Metric.mem_closedBall, dist_zero_right] using hκs hy

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_bound
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume)
    {ρ ε : ℝ} (hε : 0 ≤ ε)
    (htr : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ ρ →
      (eLpNorm (fun x ↦ f (x - y) - f x) 2 volume).toReal ≤ ε) :
    ∀ y, ‖y‖ ≤ ρ →
      eLpNorm (fun x ↦ f (x - y) - f x) 2 volume ≤ ENNReal.ofReal ε := by
  intro y hy
  have htrans :=
    apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_translate
      f hf y
  have hmem : MemLp (fun x ↦ f (x - y) - f x) 2 volume := htrans.1.sub hf
  rw [← ENNReal.toReal_le_toReal hmem.eLpNorm_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε]
  exact htr y hy

/-- The mollification error is the kernel average of translation errors
(pointwise; all integrands are integrable since `κ` is continuous with compact
support and `f` is locally integrable). -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_identify
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume) {ρ : ℝ}
    (κ : EuclideanSpace ℝ (Fin d) → ℝ) (hκ : Continuous κ)
    (hκ1 : (∫ x, κ x ∂volume) = 1)
    (hκs : Function.support κ ⊆ Metric.closedBall 0 ρ) :
    (MeasureTheory.convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) =
      fun x ↦ ∫ y, κ y • (f (x - y) - f x) ∂volume := by
  have hκK : HasCompactSupport κ :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) ρ) hκs
  have hκLp : MemLp κ 2 volume :=
    hκ.memLp_of_hasCompactSupport hκK
      (p := (2 : ℝ≥0∞)) (μ := volume)
  funext x
  have hfx : MemLp (fun y ↦ f (x - y)) 2 volume := by
    have hmp := volume.measurePreserving_sub_left x
    exact hf.comp_measurePreserving hmp
  have hprod : Integrable (fun y ↦ κ y • f (x - y)) volume := by
    exact memLp_one_iff_integrable.mp
      (hfx.smul hκLp : MemLp (fun y ↦ κ y • f (x - y)) 1 volume)
  have hconst : Integrable (fun y ↦ κ y • f x) volume :=
    (hκ.integrable_of_hasCompactSupport hκK).smul_const (f x)
  simp only [Pi.sub_apply]
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply]
  have hfxavg : (∫ y, κ y • f x ∂volume) = f x := by
    rw [integral_smul_const, hκ1, one_smul]
  calc
    (∫ y, κ y • f (x - y) ∂volume) - f x =
        (∫ y, κ y • f (x - y) ∂volume) -
          (∫ y, κ y • f x ∂volume) := congrArg
            (fun z ↦ (∫ y, κ y • f (x - y) ∂volume) - z) hfxavg.symm
    _ = ∫ y, (κ y • f (x - y) - κ y • f x) ∂volume :=
      (integral_sub hprod hconst).symm
    _ = ∫ y, κ y • (f (x - y) - f x) ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦
        (smul_sub (κ y) (f (x - y)) (f x)).symm

/-- Joint measurability of the translation-error family. -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_joint_meas
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume) :
    AEStronglyMeasurable
      (Function.uncurry fun (y x : EuclideanSpace ℝ (Fin d)) ↦ f (x - y) - f x)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume
  have hshear : MeasurePreserving
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        (z.1, z.2 - z.1)) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_sub μ μ
  have hsub : Measure.QuasiMeasurePreserving
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        z.2 - z.1) (μ.prod μ) μ := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd.comp hshear.quasiMeasurePreserving)
  have h₁ : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        f (z.2 - z.1)) (μ.prod μ) :=
    hf.1.comp_quasiMeasurePreserving hsub
  have h₂ : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
        f z.2) (μ.prod μ) :=
    hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  simpa [μ, Function.uncurry] using h₁.sub h₂

lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound_aux_weighted
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : EuclideanSpace ℝ (Fin d) → ℝ) (hκ0 : ∀ x, 0 ≤ κ x)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → E)
    {C : ℝ≥0∞} (hC : ∀ y, κ y ≠ 0 → eLpNorm (G y) 2 volume ≤ C) :
    ∀ y, eLpNorm (fun x ↦ κ y • G y x) 2 volume ≤ ENNReal.ofReal (κ y) * C := by
  intro y
  by_cases hy : κ y = 0
  · simp [hy]
  · rw [show (fun x ↦ κ y • G y x) = κ y • G y by rfl,
      eLpNorm_const_smul]
    simpa [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (hκ0 y)] using
      mul_le_mul_left' (hC y hy) (ENNReal.ofReal (κ y))

/-- Jensen for the probability kernel `κ` (pointwise in `x`). -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound_aux_pointwise
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (κ : EuclideanSpace ℝ (Fin d) → ℝ) (hκ0 : ∀ x, 0 ≤ κ x) (hκint : Integrable κ volume)
    (hκ1 : (∫ x, κ x ∂volume) = 1)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → E) (x : EuclideanSpace ℝ (Fin d)) :
    ‖∫ y, κ y • G y x ∂volume‖ₑ ^ 2 ≤
      ∫⁻ y, ENNReal.ofReal (κ y) * ‖G y x‖ₑ ^ 2 ∂volume := by
  let w : EuclideanSpace ℝ (Fin d) → NNReal := fun y ↦ Real.toNNReal (κ y)
  have hw0 : AEMeasurable w volume := hκint.1.aemeasurable.real_toNNReal
  let wm : EuclideanSpace ℝ (Fin d) → NNReal := hw0.mk w
  have hwm : Measurable wm := hw0.measurable_mk
  have hw_eq : ∀ᵐ y ∂volume, (wm y : ℝ) = κ y := by
    filter_upwards [hw0.ae_eq_mk] with y hy
    simp only [wm]
    rw [← hy]
    simp [w, hκ0 y]
  have hwmint : Integrable (fun y ↦ (wm y : ℝ)) volume := hκint.congr (by
    filter_upwards [hw_eq] with y hy
    exact hy.symm)
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity fun y ↦ (wm y : ℝ≥0∞)
  letI : IsProbabilityMeasure ν := by
    rw [isProbabilityMeasure_iff]
    simp only [ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [lintegral_coe_eq_integral wm hwmint]
    rw [integral_congr_ae hw_eq]
    simp [hκ1]
  have hint : (∫ y, G y x ∂ν) = ∫ y, κ y • G y x ∂volume := by
    rw [show ν = volume.withDensity (fun y ↦ (wm y : ℝ≥0∞)) from rfl,
      integral_withDensity_eq_integral_smul hwm]
    apply integral_congr_ae
    filter_upwards [hw_eq] with y hy
    simp [NNReal.smul_def, hy]
  rw [← hint]
  by_cases hG : AEStronglyMeasurable (fun y ↦ G y x) ν
  · have h12 : eLpNorm (fun y ↦ G y x) 1 ν ≤
        eLpNorm (fun y ↦ G y x) 2 ν :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hG
    have hi : ‖∫ y, G y x ∂ν‖ₑ ≤ eLpNorm (fun y ↦ G y x) 2 ν := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      simpa [eLpNorm_one_eq_lintegral_enorm] using h12
    refine (pow_le_pow_left' hi 2).trans_eq ?_
    have hep := eLpNorm_nnreal_pow_eq_lintegral
      (f := fun y ↦ G y x) (p := (2 : NNReal)) (μ := ν) (by norm_num)
    rw [show eLpNorm (fun y ↦ G y x) 2 ν ^ 2 =
        ∫⁻ y, ‖G y x‖ₑ ^ 2 ∂ν by simpa [ENNReal.rpow_two] using hep]
    simp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul₀' hwm.coe_nnreal_ennreal.aemeasurable
      (hG.enorm.pow_const 2)]
    apply lintegral_congr_ae
    filter_upwards [hw_eq] with y hy
    rw [← hy, ENNReal.ofReal_coe_nnreal]
    simp [ENNReal.rpow_two, pow_two]
  · have hni : ¬ Integrable (fun y ↦ G y x) ν := fun h ↦ hG h.1
    rw [integral_undef hni]
    simp

/-- Tonelli: integrate the Jensen bound in `x` and use the section bound. -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound_aux_tonelli
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (κ : EuclideanSpace ℝ (Fin d) → ℝ) (hκ0 : ∀ x, 0 ≤ κ x) (hκint : Integrable κ volume)
    (hκ1 : (∫ x, κ x ∂volume) = 1)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → E)
    (hG : AEStronglyMeasurable (Function.uncurry G)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume))
    {C : ℝ≥0∞} (hC : ∀ y, κ y ≠ 0 → eLpNorm (G y) 2 volume ≤ C) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (κ y) * ‖G y x‖ₑ ^ 2 ∂volume ∂volume ≤ C ^ 2 := by
  have hκm : AEMeasurable κ volume := hκint.aestronglyMeasurable.aemeasurable
  have hm : AEMeasurable
      (Function.uncurry fun (x y : EuclideanSpace ℝ (Fin d)) ↦
        ENNReal.ofReal (κ y) * ‖G y x‖ₑ ^ 2)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    exact (hκm.ennreal_ofReal.comp_snd).mul
      (hG.prod_swap.enorm.pow_const 2)
  rw [lintegral_lintegral_swap hm]
  calc
    (∫⁻ y, ∫⁻ x, ENNReal.ofReal (κ y) * ‖G y x‖ₑ ^ 2 ∂volume ∂volume)
        = ∫⁻ y, ENNReal.ofReal (κ y) * eLpNorm (G y) 2 volume ^ 2 ∂volume := by
          apply lintegral_congr
          intro y
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          simpa using
            (eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := G y)
              (p := (2 : NNReal)) (by norm_num : (2 : NNReal) ≠ 0)).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (κ y) * C ^ 2 ∂volume := by
      apply lintegral_mono
      intro y
      by_cases hy : κ y = 0
      · simp [hy]
      · exact mul_le_mul_left' (pow_le_pow_left' (hC y hy) 2) _
    _ = (∫⁻ y, ENNReal.ofReal (κ y) ∂volume) * C ^ 2 := by
      rw [lintegral_mul_const'' _ hκm.ennreal_ofReal]
    _ = C ^ 2 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hκint
        (Filter.Eventually.of_forall hκ0), hκ1]
      simp

/-- An `L²` bound from a bound on the integral of the squared norm. -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound_aux_from_sq
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : EuclideanSpace ℝ (Fin d) → E) {C : ℝ≥0∞}
    (h : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂volume ≤ C ^ 2) :
    eLpNorm F 2 volume ≤ C := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  have heq : eLpNorm F 2 volume ^ (2 : ℕ) =
      ∫⁻ x, ‖F x‖ₑ ^ 2 ∂volume := by
    simpa [ENNReal.rpow_two] using
      (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
        (f := F) (p := (2 : NNReal)) (by norm_num))
  rwa [heq]

/-- Minkowski's integral inequality for a probability kernel: the `L²` norm of
a kernel average is at most the worst `L²` norm on the kernel's support. -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (κ : EuclideanSpace ℝ (Fin d) → ℝ) (hκ0 : ∀ x, 0 ≤ κ x) (hκint : Integrable κ volume)
    (hκ1 : (∫ x, κ x ∂volume) = 1)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → E)
    (hG : AEStronglyMeasurable (Function.uncurry G)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume))
    {C : ℝ≥0∞} (hC : ∀ y, κ y ≠ 0 → eLpNorm (G y) 2 volume ≤ C) :
    eLpNorm (fun x ↦ ∫ y, κ y • G y x ∂volume) 2 volume ≤ C := by
  apply apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound_aux_from_sq
  calc ∫⁻ x, ‖∫ y, κ y • G y x ∂volume‖ₑ ^ 2 ∂volume
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (κ y) * ‖G y x‖ₑ ^ 2 ∂volume ∂volume :=
        lintegral_mono fun x => apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound_aux_pointwise κ hκ0 hκint hκ1 G x
    _ ≤ C ^ 2 := apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound_aux_tonelli κ hκ0 hκint hκ1 G hG hC

/-- Minkowski's integral inequality for a probability kernel supported in the
`ρ`-ball: the mollification error is at most the worst translation error. -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume)
    {ρ ε : ℝ} (hε : 0 ≤ ε)
    (htr : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ ρ →
      (eLpNorm (fun x ↦ f (x - y) - f x) 2 volume).toReal ≤ ε)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (hκ1 : (∫ x, κ x ∂volume) = 1)
    (hκs : Function.support κ ⊆ Metric.closedBall 0 ρ) :
    (eLpNorm (MeasureTheory.convolution κ f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) 2 volume).toReal ≤ ε := by
  have htsupp : tsupport κ ⊆ Metric.closedBall 0 ρ :=
    closure_minimal hκs Metric.isClosed_closedBall
  have hκc : HasCompactSupport κ :=
    (isCompact_closedBall 0 ρ).of_isClosed_subset (isClosed_tsupport _) htsupp
  have hκint : Integrable κ volume := hκ.integrable_of_hasCompactSupport hκc
  rw [apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_identify f hf κ hκ hκ1 hκs]
  have hle := apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_avg_bound κ hκ0 hκint hκ1
    (fun y x ↦ f (x - y) - f x) (apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_joint_meas f hf)
    (C := ENNReal.ofReal ε) (fun y hy ↦
      apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_bound f hf hε htr y
        (apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski_aux_support κ hκs y hy))
  exact ENNReal.toReal_le_of_le_ofReal hε hle

/-- Approximate identity in `L²`, uniformly over normalised nonnegative
kernels supported in small balls: `‖κ ⋆ f - f‖₂ ≤ sup_{|y| ≤ ρ} ‖τ_y f - f‖₂`
(Minkowski's integral inequality) and translation is continuous in `L²`. -/
lemma apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : EuclideanSpace ℝ (Fin d) → E) (hf : MemLp f 2 volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
      ∀ κ : EuclideanSpace ℝ (Fin d) → ℝ, Continuous κ → (∀ x, 0 ≤ κ x) →
        (∫ x, κ x ∂volume) = 1 → Function.support κ ⊆ Metric.closedBall 0 ρ →
        (eLpNorm (MeasureTheory.convolution κ f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) 2 volume).toReal ≤ ε := by
  obtain ⟨ρ0, hρ0, htr⟩ := apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_translate f hf hε
  refine ⟨ρ0, hρ0, fun ρ hρ hρρ0 κ hκ hκ0 hκ1 hκs => ?_⟩
  exact apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity_minkowski f hf hε.le
    (fun y hy => htr y (hy.trans hρρ0)) κ hκ hκ0 hκ1 hκs

/-- Simultaneous `L²` approximate-identity estimate for the value and weak
gradient fields.  This leaf contains no differentiation or `H¹` packaging. -/
lemma apm_m01J04_mollify_exists_L2_kernel
    {d : ℕ} (w : apm_m01J04_H1 d Set.univ)
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 < eta) :
    ∃ κ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ ∧
      HasCompactSupport κ ∧
      Function.support κ ⊆ Metric.closedBall 0 delta ∧
      (eLpNorm (MeasureTheory.convolution κ w.val
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - w.val) 2 volume).toReal +
        (eLpNorm (MeasureTheory.convolution κ w.grad
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - w.grad) 2 volume).toReal < eta := by
  have hval : MemLp w.val 2 volume := by simpa using w.val_memLp
  have hgrad : MemLp w.grad 2 volume := by simpa using w.grad_memLp
  obtain ⟨ρ1, hρ1, h1⟩ := apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity
    w.val hval (by positivity : (0 : ℝ) < eta / 3)
  obtain ⟨ρ2, hρ2, h2⟩ := apm_m01J04_mollify_exists_L2_kernel_aux_approx_identity
    w.grad hgrad (by positivity : (0 : ℝ) < eta / 3)
  set ρ := min (min ρ1 ρ2) delta with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ1 hρ2) hdelta
  obtain ⟨κ, hs, hc, hsupp, hnn, hint⟩ :=
    apm_m01J04_mollify_exists_L2_kernel_aux_kernel (d := d) hρ
  refine ⟨κ, hs, hc, hsupp.trans
    (Metric.closedBall_subset_closedBall (min_le_right _ _)), ?_⟩
  have a := h1 ρ hρ ((min_le_left _ _).trans (min_le_left _ _)) κ hs.continuous
    hnn hint hsupp
  have b := h2 ρ hρ ((min_le_left _ _).trans (min_le_right _ _)) κ hs.continuous
    hnn hint hsupp
  linarith

/-- Convolution commutes with the encoded weak gradient.  This is the
integration-by-parts leaf and is independent of approximate-identity
convergence. -/
lemma apm_m01J04_mollify_convolution_weakGradient_aux_pointwise
    {d : ℕ} (w : apm_m01J04_H1 d Set.univ)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hκcompact : HasCompactSupport κ) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin d) :
    MeasureTheory.convolution (fderiv ℝ κ) w.val
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin d))) volume x (EuclideanSpace.single i 1) =
      MeasureTheory.convolution κ w.grad
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x i := by
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  let φ : EuclideanSpace ℝ (Fin d) → ℝ := fun y ↦ κ (x - y)
  have hφsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
    exact hκsmooth.comp (contDiff_const.sub contDiff_id)
  have hφcompact : HasCompactSupport φ := by
    exact hκcompact.comp_homeomorph (Homeomorph.subLeft x)
  have hweak := w.weakGradient φ hφsmooth hφcompact (Set.subset_univ _) i
  have hfderiv (y : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ φ y e = -(fderiv ℝ κ (x - y) e) := by
    have h := (hκsmooth.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change (fderiv ℝ (κ ∘ fun z ↦ x - z) y) e = _
    rw [show fderiv ℝ (κ ∘ fun z ↦ x - z) y =
        (fderiv ℝ κ (x - y)).comp
          (0 - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) by
      convert h.fderiv using 1 <;> simp]
    simp [e]
  have hwloc : LocallyIntegrable w.val volume := by
    simpa only [Measure.restrict_univ] using w.val_memLp.locallyIntegrable (by norm_num)
  have hwgloc : LocallyIntegrable w.grad volume := by
    simpa only [Measure.restrict_univ] using w.grad_memLp.locallyIntegrable (by norm_num)
  have hleft := (hκcompact.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (EuclideanSpace ℝ (Fin d)))
    (hκsmooth.continuous_fderiv (by simp)) hwloc x
  have hright := hκcompact.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hκsmooth.continuous hwgloc x
  simp only [MeasureTheory.convolution]
  rw [ContinuousLinearMap.integral_apply hleft e]
  change _ = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) i)
    (∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (κ t) (w.grad (x - t)))
  rw [← ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) i) hright]
  simp only [ContinuousLinearMap.lsmul_apply, PiLp.proj_apply,
    PiLp.smul_apply, smul_eq_mul]
  change (∫ t, fderiv ℝ κ t e * w.val (x - t)) =
    ∫ t, κ t * w.grad (x - t) i
  rw [← integral_sub_left_eq_self
    (fun y ↦ fderiv ℝ κ y e * w.val (x - y)) volume x]
  rw [← integral_sub_left_eq_self
    (fun y ↦ κ y * w.grad (x - y) i) volume x]
  simp only [sub_sub_cancel]
  dsimp [e] at hfderiv
  simp_rw [hfderiv] at hweak
  simpa [φ, e, mul_neg, integral_neg, mul_comm] using hweak

set_option maxHeartbeats 800000 in
lemma apm_m01J04_mollify_convolution_weakGradient
    {d : ℕ} (w : apm_m01J04_H1 d Set.univ)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hκcompact : HasCompactSupport κ) :
    ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      ∀ i : Fin d,
        (∫ x, MeasureTheory.convolution κ w.val
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x *
            fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
          -(∫ x, MeasureTheory.convolution κ w.grad
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x i * ψ x) := by
  intro ψ hψsmooth hψcompact i
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  let f := MeasureTheory.convolution κ w.val
    (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let g := MeasureTheory.convolution κ w.grad
    (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hwloc : LocallyIntegrable w.val volume := by
    simpa only [Measure.restrict_univ] using w.val_memLp.locallyIntegrable (by norm_num)
  have hwgloc : LocallyIntegrable w.grad volume := by
    simpa only [Measure.restrict_univ] using w.grad_memLp.locallyIntegrable (by norm_num)
  have hfsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    hκcompact.contDiff_convolution_left _ hκsmooth hwloc
  have hgsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    hκcompact.contDiff_convolution_left _ hκsmooth hwgloc
  have hfderiv (x : EuclideanSpace ℝ (Fin d)) :
      fderiv ℝ f x e = g x i := by
    have hd := hκcompact.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (hκsmooth.of_le (by simp)) hwloc x
    rw [hd.fderiv]
    exact apm_m01J04_mollify_convolution_weakGradient_aux_pointwise
      w κ hκsmooth hκcompact x i
  have hψderivcompact : HasCompactSupport (fun x ↦ fderiv ℝ ψ x e) := by
    simpa only [Function.comp_apply] using
      (hψcompact.fderiv ℝ).comp_left (g := fun L ↦ L e) (by simp)
  have hψderivcont : Continuous (fun x ↦ fderiv ℝ ψ x e) :=
    (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp
      (hψsmooth.continuous_fderiv (by simp))
  have hfderivcont : Continuous (fun x ↦ fderiv ℝ f x e) :=
    (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp
      (hfsmooth.continuous_fderiv (by simp))
  have hI1 : Integrable (fun x ↦ f x * fderiv ℝ ψ x e) volume := by
    have h :=
      (hfsmooth.continuous.locallyIntegrable (μ := volume)).integrable_smul_left_of_hasCompactSupport
        hψderivcont hψderivcompact
    exact h.congr (Filter.Eventually.of_forall (fun x ↦ by simp [mul_comm]))
  have hI2 : Integrable (fun x ↦ fderiv ℝ f x e * ψ x) volume := by
    simpa [smul_eq_mul, mul_comm] using
      (hfderivcont.locallyIntegrable (μ := volume))
        |>.integrable_smul_left_of_hasCompactSupport hψsmooth.continuous hψcompact
  have hI0 : Integrable (fun x ↦ f x * ψ x) volume := by
    simpa [smul_eq_mul, mul_comm] using
      (hfsmooth.continuous.locallyIntegrable (μ := volume)).integrable_smul_left_of_hasCompactSupport
        hψsmooth.continuous hψcompact
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI2 hI1 hI0]
  · apply congrArg Neg.neg
    apply integral_congr_ae
    filter_upwards with x
    rw [hfderiv x]
  · exact fun _ _ ↦ hfsmooth.differentiable (by simp) |>.differentiableAt
  · exact fun _ _ ↦ hψsmooth.differentiable (by simp) |>.differentiableAt

lemma apm_m01J04_mollify_package_aux_val_contDiff
    {d : ℕ} (w : apm_m01J04_H1 d Set.univ)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hκcompact : HasCompactSupport κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MeasureTheory.convolution κ w.val
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  have hwloc : LocallyIntegrable w.val volume := by
    have hw : MemLp w.val 2 volume := by
      simpa only [Measure.restrict_univ] using w.val_memLp
    exact hw.locallyIntegrable (by norm_num)
  exact hκcompact.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hκsmooth hwloc

lemma apm_m01J04_mollify_package_aux_val_compact
    {d : ℕ} (w : apm_m01J04_H1 d Set.univ)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C)
    (hwval : Function.support w.val ⊆ C)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκcompact : HasCompactSupport κ) :
    HasCompactSupport (MeasureTheory.convolution κ w.val
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  have hwcompact : HasCompactSupport w.val :=
    hC.of_isClosed_subset isClosed_closure
      (closure_minimal hwval hC.isClosed)
  exact hκcompact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hwcompact

lemma apm_m01J04_mollify_package_aux_val_memLp
    {d : ℕ} (w : apm_m01J04_H1 d Set.univ)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C)
    (hwval : Function.support w.val ⊆ C)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hκcompact : HasCompactSupport κ) :
    MemLp (MeasureTheory.convolution κ w.val
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume := by
  exact (apm_m01J04_mollify_package_aux_val_contDiff w κ hκsmooth hκcompact).continuous.memLp_of_hasCompactSupport
    (apm_m01J04_mollify_package_aux_val_compact w hC hwval κ hκcompact)

/-- Package two convolution fields into the encoded global `H¹` record.  All
analytic conclusions needed from the other leaves are explicit hypotheses, so
this assembly can be proved independently. -/
lemma apm_m01J04_mollify_package
    {d : ℕ} (w : apm_m01J04_H1 d Set.univ)
    {C : Set (EuclideanSpace ℝ (Fin d))} (hC : IsCompact C)
    (hwval : Function.support w.val ⊆ C)
    (hwgrad : Function.support w.grad ⊆ C)
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hκsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hκcompact : HasCompactSupport κ)
    {delta eta : ℝ}
    (hκsupport : Function.support κ ⊆ Metric.closedBall 0 delta)
    (herror :
      (eLpNorm (MeasureTheory.convolution κ w.val
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - w.val) 2 volume).toReal +
        (eLpNorm (MeasureTheory.convolution κ w.grad
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - w.grad) 2 volume).toReal < eta)
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      ∀ i : Fin d,
        (∫ x, MeasureTheory.convolution κ w.val
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x *
            fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
          -(∫ x, MeasureTheory.convolution κ w.grad
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x i * ψ x)) :
    ∃ a : apm_m01J04_H1 d Set.univ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.val ∧
      HasCompactSupport a.val ∧
      Function.support a.val ⊆ Metric.cthickening delta C ∧
      apm_m01J04_H1dist a w < eta := by
  let v := MeasureTheory.convolution κ w.val
    (ContinuousLinearMap.lsmul ℝ ℝ) volume
  let g := MeasureTheory.convolution κ w.grad
    (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hvLp : MemLp v 2 volume := by
    exact apm_m01J04_mollify_package_aux_val_memLp
      w hC hwval κ hκsmooth hκcompact
  have hwgradCompact : HasCompactSupport w.grad :=
    hC.of_isClosed_subset isClosed_closure
      (closure_minimal hwgrad hC.isClosed)
  have hgCompact : HasCompactSupport g := by
    exact hκcompact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hwgradCompact
  have hwgradLoc : LocallyIntegrable w.grad volume := by
    have hm : MemLp w.grad 2 volume := by
      simpa only [Measure.restrict_univ] using w.grad_memLp
    exact hm.locallyIntegrable (by norm_num)
  have hgSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    exact hκcompact.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hκsmooth hwgradLoc
  have hgLp : MemLp g 2 volume :=
    hgSmooth.continuous.memLp_of_hasCompactSupport hgCompact
  let a : apm_m01J04_H1 d Set.univ :=
    { val := v
      grad := g
      val_memLp := by simpa only [Measure.restrict_univ] using hvLp
      grad_memLp := by simpa only [Measure.restrict_univ] using hgLp
      weakGradient := by
        intro ψ hψsmooth hψcompact _ i
        simpa only [Measure.restrict_univ, v, g] using
          hweak ψ hψsmooth hψcompact i }
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · exact apm_m01J04_mollify_package_aux_val_contDiff
      w κ hκsmooth hκcompact
  · exact apm_m01J04_mollify_package_aux_val_compact
      w hC hwval κ hκcompact
  · exact apm_m01J04_support_convolution_subset_cthickening
      hκsupport hwval
  · simpa only [apm_m01J04_H1dist, a, v, g,
      Measure.restrict_univ] using herror

/-- Triangle transfer for the two-stage compact-core/mollification error. -/
lemma apm_m01J04_mollify_error_transfer_aux_triangle
    {d : ℕ} (a w u : apm_m01J04_H1 d Set.univ) :
    apm_m01J04_H1dist a u ≤
      apm_m01J04_H1dist a w + apm_m01J04_H1dist w u := by
  have hv := eLpNorm_add_le
    (a.val_memLp.sub w.val_memLp).1
    (w.val_memLp.sub u.val_memLp).1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg := eLpNorm_add_le
    (a.grad_memLp.sub w.grad_memLp).1
    (w.grad_memLp.sub u.grad_memLp).1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hvtop : eLpNorm (fun x ↦ a.val x - w.val x) 2 (volume.restrict Set.univ) +
      eLpNorm (fun x ↦ w.val x - u.val x) 2 (volume.restrict Set.univ) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(a.val_memLp.sub w.val_memLp).eLpNorm_ne_top,
      (w.val_memLp.sub u.val_memLp).eLpNorm_ne_top⟩
  have hgtop : eLpNorm (fun x ↦ a.grad x - w.grad x) 2 (volume.restrict Set.univ) +
      eLpNorm (fun x ↦ w.grad x - u.grad x) 2 (volume.restrict Set.univ) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(a.grad_memLp.sub w.grad_memLp).eLpNorm_ne_top,
      (w.grad_memLp.sub u.grad_memLp).eLpNorm_ne_top⟩
  have hv' : (eLpNorm (fun x ↦ a.val x - u.val x) 2 (volume.restrict Set.univ)).toReal ≤
      (eLpNorm (fun x ↦ a.val x - w.val x) 2 (volume.restrict Set.univ)).toReal +
      (eLpNorm (fun x ↦ w.val x - u.val x) 2 (volume.restrict Set.univ)).toReal := by
    calc
      _ ≤ (eLpNorm (fun x ↦ a.val x - w.val x) 2 (volume.restrict Set.univ) +
          eLpNorm (fun x ↦ w.val x - u.val x) 2 (volume.restrict Set.univ)).toReal := by
        apply ENNReal.toReal_mono hvtop
        simpa only [Pi.add_apply, sub_add_sub_cancel] using hv
      _ = _ := ENNReal.toReal_add
        (a.val_memLp.sub w.val_memLp).eLpNorm_ne_top
        (w.val_memLp.sub u.val_memLp).eLpNorm_ne_top
  have hg' : (eLpNorm (fun x ↦ a.grad x - u.grad x) 2 (volume.restrict Set.univ)).toReal ≤
      (eLpNorm (fun x ↦ a.grad x - w.grad x) 2 (volume.restrict Set.univ)).toReal +
      (eLpNorm (fun x ↦ w.grad x - u.grad x) 2 (volume.restrict Set.univ)).toReal := by
    calc
      _ ≤ (eLpNorm (fun x ↦ a.grad x - w.grad x) 2 (volume.restrict Set.univ) +
          eLpNorm (fun x ↦ w.grad x - u.grad x) 2 (volume.restrict Set.univ)).toReal := by
        apply ENNReal.toReal_mono hgtop
        simpa only [Pi.add_apply, sub_add_sub_cancel] using hg
      _ = _ := ENNReal.toReal_add
        (a.grad_memLp.sub w.grad_memLp).eLpNorm_ne_top
        (w.grad_memLp.sub u.grad_memLp).eLpNorm_ne_top
  dsimp [apm_m01J04_H1dist]
  linarith

lemma apm_m01J04_mollify_error_transfer
    {d : ℕ} (a w u : apm_m01J04_H1 d Set.univ)
    {eta : ℝ}
    (haw : apm_m01J04_H1dist a w < eta / 2)
    (hwu : apm_m01J04_H1dist w u < eta / 2) :
    apm_m01J04_H1dist a u < eta := by
  have htri := apm_m01J04_mollify_error_transfer_aux_triangle a w u
  linarith

lemma apm_m01J04_core_exists_smooth_global_approx_aux_mollify
    {d : ℕ} (u : apm_m01J04_H1 d Set.univ)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (huval : Function.support u.val ⊆ K)
    (hugrad : Function.support u.grad ⊆ K)
    {delta eta : ℝ} (hdelta : 0 < delta) (heta : 0 < eta) :
    ∃ a : apm_m01J04_H1 d Set.univ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.val ∧
      HasCompactSupport a.val ∧
      Function.support a.val ⊆ Metric.cthickening delta K ∧
      apm_m01J04_H1dist a u < eta := by
  obtain ⟨w, C, hCcompact, hCK, hwval, hwgrad, hwu⟩ :=
    apm_m01J04_mollify_exists_compact_core u huval hugrad (half_pos heta)
  obtain ⟨κ, hκsmooth, hκcompact, hκsupport, hκerror⟩ :=
    apm_m01J04_mollify_exists_L2_kernel w hdelta (half_pos heta)
  have hweak := apm_m01J04_mollify_convolution_weakGradient w κ hκsmooth hκcompact
  obtain ⟨a, hasmooth, hacompact, hasupport, haw⟩ :=
    apm_m01J04_mollify_package w hCcompact hwval hwgrad κ hκsmooth hκcompact hκsupport hκerror hweak
  refine ⟨a, hasmooth, hacompact, ?_,
    apm_m01J04_mollify_error_transfer a w u haw hwu⟩
  rw [← Metric.cthickening_closure]
  exact hasupport.trans (Metric.cthickening_subset_of_subset delta hCK)

lemma apm_m01J04_core_exists_smooth_global_approx
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (u : apm_m01J04_H1 d Set.univ)
    (huval : Function.support u.val ⊆ {x | epsilon ≤ |φ x|})
    (hugrad : Function.support u.grad ⊆ {x | epsilon ≤ |φ x|})
    {eta : ℝ} (heta : 0 < eta) :
    ∃ a : apm_m01J04_H1 d Set.univ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.val ∧
      HasCompactSupport a.val ∧ Function.support a.val ⊆ Ω ∧
      apm_m01J04_H1dist a u < eta := by
  obtain ⟨delta, hdelta, hsupport, hsupportOmega⟩ :=
    apm_m01J04_test_levelSet_exists_cthickening φ hφ hepsilon
  obtain ⟨a, hasmooth, hacompact, hasupport, hadist⟩ :=
    apm_m01J04_core_exists_smooth_global_approx_aux_mollify u huval hugrad
      hdelta heta
  refine ⟨a, hasmooth, hacompact, ?_, hadist⟩
  exact hasupport.trans hsupportOmega

/-- Diagonal assembly of core truncation and support-safe smoothing.  Both
analytic inputs are hypotheses so this lemma can be proved independently of
the two construction lemmas above. -/
lemma apm_m01J04_localization_isH1Zero_of_core_approximations_aux_triangle
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (a u v : apm_m01J04_H1 d Ω) :
    apm_m01J04_H1dist a v ≤
      apm_m01J04_H1dist a u + apm_m01J04_H1dist u v := by
  have hv := eLpNorm_add_le
    (a.val_memLp.sub u.val_memLp).1
    (u.val_memLp.sub v.val_memLp).1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg := eLpNorm_add_le
    (a.grad_memLp.sub u.grad_memLp).1
    (u.grad_memLp.sub v.grad_memLp).1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hvtop : eLpNorm (fun x ↦ a.val x - u.val x) 2
        (volume.restrict Ω) +
      eLpNorm (fun x ↦ u.val x - v.val x) 2
        (volume.restrict Ω) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(a.val_memLp.sub u.val_memLp).eLpNorm_ne_top,
      (u.val_memLp.sub v.val_memLp).eLpNorm_ne_top⟩
  have hgtop : eLpNorm (fun x ↦ a.grad x - u.grad x) 2
        (volume.restrict Ω) +
      eLpNorm (fun x ↦ u.grad x - v.grad x) 2
        (volume.restrict Ω) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(a.grad_memLp.sub u.grad_memLp).eLpNorm_ne_top,
      (u.grad_memLp.sub v.grad_memLp).eLpNorm_ne_top⟩
  have hv' : (eLpNorm (fun x ↦ a.val x - v.val x) 2
        (volume.restrict Ω)).toReal ≤
      (eLpNorm (fun x ↦ a.val x - u.val x) 2
        (volume.restrict Ω)).toReal +
      (eLpNorm (fun x ↦ u.val x - v.val x) 2
        (volume.restrict Ω)).toReal := by
    calc
      _ ≤ (eLpNorm (fun x ↦ a.val x - u.val x) 2
          (volume.restrict Ω) + eLpNorm (fun x ↦ u.val x - v.val x) 2
          (volume.restrict Ω)).toReal := by
        apply ENNReal.toReal_mono hvtop
        simpa only [Pi.add_apply, sub_add_sub_cancel] using hv
      _ = _ := ENNReal.toReal_add
        (a.val_memLp.sub u.val_memLp).eLpNorm_ne_top
        (u.val_memLp.sub v.val_memLp).eLpNorm_ne_top
  have hg' : (eLpNorm (fun x ↦ a.grad x - v.grad x) 2
        (volume.restrict Ω)).toReal ≤
      (eLpNorm (fun x ↦ a.grad x - u.grad x) 2
        (volume.restrict Ω)).toReal +
      (eLpNorm (fun x ↦ u.grad x - v.grad x) 2
        (volume.restrict Ω)).toReal := by
    calc
      _ ≤ (eLpNorm (fun x ↦ a.grad x - u.grad x) 2
          (volume.restrict Ω) + eLpNorm (fun x ↦ u.grad x - v.grad x) 2
          (volume.restrict Ω)).toReal := by
        apply ENNReal.toReal_mono hgtop
        simpa only [Pi.add_apply, sub_add_sub_cancel] using hg
      _ = _ := ENNReal.toReal_add
        (a.grad_memLp.sub u.grad_memLp).eLpNorm_ne_top
        (u.grad_memLp.sub v.grad_memLp).eLpNorm_ne_top
  dsimp [apm_m01J04_H1dist]
  linarith

lemma apm_m01J04_localization_isH1Zero_of_core_approximations
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω)
    (hcore : ∀ eta : ℝ, 0 < eta →
      ∃ (epsilon : ℝ) (u : apm_m01J04_H1 d Set.univ),
        0 < epsilon ∧
        Function.support u.val ⊆ {x | epsilon ≤ |φ x|} ∧
        Function.support u.grad ⊆ {x | epsilon ≤ |φ x|} ∧
        apm_m01J04_H1dist u (apm_m01J04_globalLocalizedH1 φ hφ f) < eta)
    (hsmooth : ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ (u : apm_m01J04_H1 d Set.univ),
        Function.support u.val ⊆ {x | epsilon ≤ |φ x|} →
        Function.support u.grad ⊆ {x | epsilon ≤ |φ x|} →
        ∀ eta : ℝ, 0 < eta →
          ∃ a : apm_m01J04_H1 d Set.univ,
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.val ∧
            HasCompactSupport a.val ∧ Function.support a.val ⊆ Ω ∧
            apm_m01J04_H1dist a u < eta) :
    apm_m01J04_isH1Zero (apm_m01J04_H1mul φ hφ f) := by
  let eta : ℕ → ℝ := fun n ↦ 1 / (2 * (n + 1 : ℝ))
  have heta (n : ℕ) : 0 < eta n := by
    dsimp [eta]
    positivity
  let core (n : ℕ) := Classical.choose (hcore (eta n) (heta n))
  let u (n : ℕ) := Classical.choose (Classical.choose_spec
    (hcore (eta n) (heta n)))
  have hcore_spec (n : ℕ) := Classical.choose_spec (Classical.choose_spec
    (hcore (eta n) (heta n)))
  let a (n : ℕ) := Classical.choose
    (hsmooth (core n) (hcore_spec n).1 (u n) (hcore_spec n).2.1
      (hcore_spec n).2.2.1 (eta n) (heta n))
  have ha_spec (n : ℕ) := Classical.choose_spec
    (hsmooth (core n) (hcore_spec n).1 (u n) (hcore_spec n).2.1
      (hcore_spec n).2.2.1 (eta n) (heta n))
  apply apm_m01J04_localization_isH1Zero_of_globalApprox φ hφ f a
  · intro n
    exact ⟨(ha_spec n).1, (ha_spec n).2.1, (ha_spec n).2.2.1⟩
  · apply squeeze_zero
      (fun n ↦ add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun n ↦ le_trans
        (apm_m01J04_localization_isH1Zero_of_core_approximations_aux_triangle
          (a n) (u n) (apm_m01J04_globalLocalizedH1 φ hφ f))
        (add_le_add (ha_spec n).2.2.2.le (hcore_spec n).2.2.2.le))
    have hlim : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    convert hlim using 1
    funext n
    dsimp [eta]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num

lemma apm_m01J04_localization_isH1Zero_aux_zero_fields
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (h : apm_m01J04_H1 d Ω) (hv : h.val = 0) (hg : h.grad = 0) :
    apm_m01J04_isH1Zero h := by
  refine ⟨fun _ ↦ h, ?_, ?_⟩
  · intro n
    rw [hv]
    exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  · simp [apm_m01J04_H1dist, hv, hg]

lemma apm_m01J04_localization_isH1Zero_aux_zero_multiplier
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) (hzero : φ = 0) :
    apm_m01J04_isH1Zero (apm_m01J04_H1mul φ hφ f) := by
  apply apm_m01J04_localization_isH1Zero_aux_zero_fields
  · rw [apm_m01J04_H1mul_val, hzero]
    funext x
    simp
  · rw [apm_m01J04_H1mul_grad, hzero]
    funext x
    ext i
    simp

lemma apm_m01J04_localization_isH1Zero
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ)
    (f : apm_m01J04_H1 d Ω) :
    apm_m01J04_isH1Zero (apm_m01J04_H1mul φ hφ f) := by
  by_cases hzero : φ = 0
  · exact apm_m01J04_localization_isH1Zero_aux_zero_multiplier φ hφ f hzero
  · apply apm_m01J04_localization_isH1Zero_of_core_approximations φ hφ f
    · intro eta heta
      exact apm_m01J04_localization_core_approx φ hφ f heta
    · intro epsilon hepsilon u huval hugrad eta heta
      exact apm_m01J04_core_exists_smooth_global_approx
        φ hφ hepsilon u huval hugrad heta

/-- Why this unblocks `apm_m01j04`: this is the missing bounded multiplier
and weak Leibniz theorem for the custom `H¹` record. It constructs the
endpoint-zero test record used in `divStronglyConverges`, with a norm bound
uniform in the multiplied function. -/
theorem apm_m01J04_bridge_1
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : apm_m01J04_H1 d Ω,
        ∃ h : apm_m01J04_H1 d Ω,
          h.val = (fun x ↦ f.val x * φ x) ∧
          h.grad = (fun x ↦
            φ x • f.grad x +
              f.val x • WithLp.toLp 2
                (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) ∧
          apm_m01J04_isH1Zero h ∧
          apm_m01J04_H1norm h ≤ C * apm_m01J04_H1norm f := by
  obtain ⟨C, hC0, hnorm⟩ := apm_m01J04_test_mul_H1norm_le φ hφ
  refine ⟨C, hC0, fun f ↦ ?_⟩
  refine ⟨apm_m01J04_H1mul φ hφ f, apm_m01J04_H1mul_val φ hφ f,
    apm_m01J04_H1mul_grad φ hφ f,
    apm_m01J04_localization_isH1Zero φ hφ f, ?_⟩
  simpa [apm_m01J04_H1norm, apm_m01J04_H1mul_val,
    apm_m01J04_H1mul_grad] using hnorm f

/-- Uniformly bounded localized product records associated to a weakly
convergent `H¹` sequence. -/
lemma apm_m01J04_bridge_sequence
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    (hf : apm_m01J04_H1WeaklyConverges f fLim)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ h : ℕ → apm_m01J04_H1 d Ω, ∃ B : ℝ, 0 < B ∧
      (∀ n, (h n).val = fun x ↦ (f n).val x * φ x) ∧
      (∀ n, (h n).grad = fun x ↦
        φ x • (f n).grad x + (f n).val x • WithLp.toLp 2
          (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) ∧
      (∀ n, apm_m01J04_isH1Zero (h n)) ∧
      (∀ n, apm_m01J04_H1norm (h n) ≤ B) := by
  obtain ⟨C, hC0, hbridge⟩ := apm_m01J04_bridge_1 φ hφ
  obtain ⟨Cf, hCf⟩ := apm_m01J04_H1WeaklyConverges_uniform_norm hf
  have hCf0 : 0 ≤ Cf := le_trans
    (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hCf 0)
  choose h hval hgrad hzero hnorm using fun n ↦ hbridge (f n)
  refine ⟨h, C * Cf + 1, by positivity, hval, hgrad, hzero, fun n ↦ ?_⟩
  calc
    apm_m01J04_H1norm (h n) ≤ C * apm_m01J04_H1norm (f n) := hnorm n
    _ ≤ C * Cf := mul_le_mul_of_nonneg_left (hCf n) hC0
    _ ≤ C * Cf + 1 := le_add_of_nonneg_right zero_le_one

/-- Applying strong divergence convergence to the uniformly bounded bridge
sequence produces the vanishing product-gradient pairing used in part (c). -/
lemma apm_m01J04_bridge_divergence_pairing
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : apm_m01J04_H1WeaklyConverges f fLim)
    (hdiv : apm_m01J04_divStronglyConverges (Ω := Ω) v vLim)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    ∃ h : ℕ → apm_m01J04_H1 d Ω,
      (∀ n, (h n).val = fun x ↦ (f n).val x * φ x) ∧
      (∀ n, (h n).grad = fun x ↦
        φ x • (f n).grad x + (f n).val x • WithLp.toLp 2
          (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) ∧
      Tendsto (fun n ↦ ∫ x in Ω,
        inner ℝ (v n x - vLim x) ((h n).grad x)) atTop (nhds 0) := by
  obtain ⟨h, B, hB, hval, hgrad, hzero, hnorm⟩ :=
    apm_m01J04_bridge_sequence hf φ hφ
  exact ⟨h, hval, hgrad,
    apm_m01J04_divStronglyConverges_pairing hdiv h hzero B hB hnorm⟩

lemma apm_m01J04_principal_difference_tendsto_zero
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hrel : apm_m01J04_HasRellichProperty d Ω)
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : apm_m01J04_H1WeaklyConverges f fLim)
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v vLim)
    (hdiv : apm_m01J04_divStronglyConverges (Ω := Ω) v vLim)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    Tendsto (fun n ↦ ∫ x in Ω,
      inner ℝ (v n x - vLim x) (φ x • (f n).grad x))
      atTop (nhds 0) := by
  obtain ⟨h, hval, hgrad, hbridge⟩ :=
    apm_m01J04_bridge_divergence_pairing hf hdiv φ hφ
  have hlower := apm_m01J04_lower_order_tendsto_zero hrel hf hv φ hφ
  have hdiff := hbridge.sub hlower
  convert hdiff using 1
  · funext n
    rw [hgrad n]
    have hvsub : MemLp (fun x ↦ v n x - vLim x) 2
        (volume.restrict Ω) := (hv.1 n).sub hv.2.1
    have hφtop : MemLp φ ⊤ (volume.restrict Ω) :=
      hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
    have hp : MemLp (fun x ↦ φ x • (f n).grad x) 2
        (volume.restrict Ω) := (f n).grad_memLp.smul hφtop
    have hDtop := apm_m01J04_isTestFunction_fderivField_memLp hφ ⊤
    have hl : MemLp (fun x ↦ (f n).val x • WithLp.toLp 2
        (fun i ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) 2
        (volume.restrict Ω) := hDtop.smul (f n).val_memLp
    simp only
    simp_rw [inner_add_right]
    rw [MeasureTheory.integral_add
      (apm_m01J04_integrable_inner _ _ hvsub hp)
      (apm_m01J04_integrable_inner _ _ hvsub hl)]
    ring
  · simp

lemma apm_m01J04_compensated_pairing
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hrel : apm_m01J04_HasRellichProperty d Ω)
    {f : ℕ → apm_m01J04_H1 d Ω} {fLim : apm_m01J04_H1 d Ω}
    {v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : apm_m01J04_H1WeaklyConverges f fLim)
    (hv : apm_m01J04_L2WeaklyConverges (Ω := Ω) v vLim)
    (hdiv : apm_m01J04_divStronglyConverges (Ω := Ω) v vLim)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : apm_m01J04_isTestFunction Ω φ) :
    Tendsto (fun n ↦ ∫ x in Ω,
      inner ℝ (v n x) ((f n).grad x) * φ x) atTop
      (nhds (∫ x in Ω, inner ℝ (vLim x) (fLim.grad x) * φ x)) := by
  have hprincipal :=
    apm_m01J04_principal_difference_tendsto_zero hrel hf hv hdiv φ hφ
  have hφtop : MemLp φ ⊤ (volume.restrict Ω) :=
    hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  have hq : MemLp (fun x ↦ φ x • vLim x) 2 (volume.restrict Ω) :=
    hv.2.1.smul hφtop
  have hfixed := hf.2 (fun x ↦ φ x • vLim x) hq
  have hsum := hprincipal.add hfixed
  convert hsum using 1
  · funext n
    have hvsub : MemLp (fun x ↦ v n x - vLim x) 2
        (volume.restrict Ω) := (hv.1 n).sub hv.2.1
    have hp : MemLp (fun x ↦ φ x • (f n).grad x) 2
        (volume.restrict Ω) := (f n).grad_memLp.smul hφtop
    have hgn : MemLp (f n).grad 2 (volume.restrict Ω) := (f n).grad_memLp
    rw [← MeasureTheory.integral_add
      (apm_m01J04_integrable_inner _ _ hvsub hp)
      (apm_m01J04_integrable_inner _ _ hgn hq)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    simp only [real_inner_smul_right, inner_sub_left]
    rw [real_inner_comm ((f n).grad x) (vLim x)]
    ring
  · apply congrArg nhds
    simp only [zero_add]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [real_inner_smul_right,
      real_inner_comm (fLim.grad x) (vLim x)]
    ring

theorem apm_m01j04 :
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        [CompleteSpace X] (f : ℕ → X) (x : X)
        (g : ℕ → X →L[ℝ] ℝ) (h : X →L[ℝ] ℝ),
      apm_m01J04_weaklyConverges f x →
      Tendsto g atTop (nhds h) →
        Tendsto (fun n ↦ g n (f n)) atTop (nhds (h x))) ∧
    (∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))),
      apm_m01J04_HasRellichProperty d Ω →
      (∀ u : ℕ → apm_m01J04_H1 d Ω,
        (∃ C : ℝ, ∀ n, apm_m01J04_H1norm (u n) ≤ C) →
          ∃ k : ℕ → ℕ, StrictMono k ∧
            ∃ w : apm_m01J04_H1 d Ω,
              ∀ ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
                MemLp ψ ⊤ (volume.restrict Ω) →
                  Tendsto (fun n ↦ ∫ x in Ω,
                    (u (k n)).val x * inner ℝ ((u (k n)).grad x) (ψ x))
                    atTop (nhds (∫ x in Ω,
                      w.val x * inner ℝ (w.grad x) (ψ x)))) ∧
      (∀ (f : ℕ → apm_m01J04_H1 d Ω) (fLim : apm_m01J04_H1 d Ω)
          (v : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
          (vLim : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        apm_m01J04_H1WeaklyConverges f fLim →
        apm_m01J04_L2WeaklyConverges (Ω := Ω) v vLim →
        apm_m01J04_divStronglyConverges (Ω := Ω) v vLim →
          ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
            apm_m01J04_isTestFunction Ω φ →
              Tendsto (fun n ↦ ∫ x in Ω,
                inner ℝ (v n x) ((f n).grad x) * φ x) atTop
                (nhds (∫ x in Ω,
                  inner ℝ (vLim x) (fLim.grad x) * φ x)))) := by
  constructor
  · intro X _ _ _ f x g h hf hg
    have hpoint : ∀ q : X →L[ℝ] ℝ, ∃ C : ℝ, ∀ n : ℕ,
        ‖(NormedSpace.inclusionInDoubleDual ℝ X) (f n) q‖ ≤ C := by
      intro q
      obtain ⟨C, hC⟩ :=
        (Metric.isBounded_range_of_tendsto (fun n ↦ q (f n)) (hf q)).exists_norm_le
      refine ⟨C, fun n ↦ ?_⟩
      simpa [NormedSpace.dual_def] using hC (q (f n)) ⟨n, rfl⟩
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun n ↦ (NormedSpace.inclusionInDoubleDual ℝ X) (f n)) hpoint
    have hf_bounded : ∀ n, ‖f n‖ ≤ C := by
      intro n
      rw [← (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ).norm_map]
      exact hC n
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hf_bounded 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Ng, hNg⟩ := Metric.tendsto_atTop.mp hg
      (ε / (2 * (C + 1))) (by positivity)
    obtain ⟨Nf, hNf⟩ := Metric.tendsto_atTop.mp (hf h) (ε / 2) (by positivity)
    refine ⟨max Ng Nf, fun n hn => ?_⟩
    have hng := hNg n (le_trans (le_max_left _ _) hn)
    have hnf := hNf n (le_trans (le_max_right _ _) hn)
    have hfirst : dist (g n (f n)) (h (f n)) < ε / 2 := by
      rw [dist_eq_norm, ← ContinuousLinearMap.sub_apply]
      calc
        ‖(g n - h) (f n)‖ ≤ ‖g n - h‖ * ‖f n‖ := (g n - h).le_opNorm _
        _ ≤ ‖g n - h‖ * C := mul_le_mul_of_nonneg_left (hf_bounded n) (norm_nonneg _)
        _ ≤ (ε / (2 * (C + 1))) * C := by
          rw [dist_eq_norm] at hng
          exact mul_le_mul_of_nonneg_right (le_of_lt hng) hC0
        _ < (ε / (2 * (C + 1))) * (C + 1) := by
          exact mul_lt_mul_of_pos_left (lt_add_one C) (by positivity)
        _ = ε / 2 := by field_simp
    exact lt_of_le_of_lt (dist_triangle _ (h (f n)) _) (by
      simpa only [add_halves ε] using add_lt_add hfirst hnf)
  · /-
    Boundary for the Sobolev/compensated-compactness clauses: applying the
    supplied `apm_m01J04_HasRellichProperty` yields a subsequence with weak
    `H¹` and strong `L²` convergence. Part (b) then needs measurable Hölder
    estimates showing multiplication by an `L∞` vector field preserves the
    strong `L²` limit before invoking the weak×strong lemma above. Part (c)
    additionally needs a fully formal Leibniz rule for the custom weak-gradient
    structure, preservation of `apm_m01J04_isH1Zero` under multiplication by a
    test function, and the integration-by-parts identity connecting
    `apm_m01J04_divStronglyConverges` to the target integral. Repository and
    Mathlib searches found no sibling or packaged theorem matching these custom
    predicates.

    Closer hop 1 closes the abstract weak×strong pairing conjunct above,
    including weak boundedness via `banach_steinhaus` and the explicit operator
    norm estimate. Further searches of `LEMMA-INDEX.md`, all fully closed
    artifacts, `ConstructionTargets/`, and `YoungL2.lean` returned no theorem
    connecting the bespoke `apm_m01J04_H1` weak-gradient record to multiplication
    by test functions. Thus the remaining sorry is specifically the measurable
    Hölder/Leibniz/integration-by-parts assembly for these frozen predicates,
    rather than the functional-analytic pairing step.

    Closer hop 2 inspected the nearby closed Hölder argument in sibling
    `a96A03` and Mathlib's `MeasureTheory.Function.L2Space`.  The raw analytic
    components do exist: `MemLp.mul'` proves an `L²×L²` product is in `L¹`,
    `eLpNorm_smul_le_mul_eLpNorm` gives the required multiplier estimate, and
    `L2.integrable_inner` handles vector-valued `L²` pairings.  These can close
    the integrability and strong-multiplier portions of part (b), but they do
    not connect raw functions to the custom weak-gradient record.

    For part (c), source searches for weak-gradient multiplication,
    distributional Leibniz rules, and compactly-supported multiplier closure
    returned no declaration.  The precise remaining local development is to
    construct the `apm_m01J04_H1` record for `f * φ`, prove the gradient
    formula, preserve `apm_m01J04_isH1Zero` by multiplying its approximants,
    establish a uniform `H1norm` bound, and rewrite the divergence test into
    the target integral. No closed artifact or construction library packages
    these record-level steps.
    -/
    intro d Ω hrel
    by_cases hd : d = 0
    · subst d
      have hvec_zero (x : EuclideanSpace ℝ (Fin 0)) : x = 0 :=
        Subsingleton.elim _ _
      constructor
      · intro u hu
        obtain ⟨k, hk, w, hw⟩ := hrel u hu
        refine ⟨k, hk, w, ?_⟩
        intro ψ hψ
        simpa [hvec_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
      · intro f fLim v vLim hf hv hdiv φ hφ
        simpa [hvec_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
    · /-
      Closer hop 3 closes both Sobolev/compensated-compactness clauses when
      `d = 0`: all gradient-valued fields lie in a subsingleton Euclidean
      space, hence every displayed pairing is zero. The remaining branch has
      `0 < d` and still requires the record-level multiplier/Leibniz
      construction described above. Mathlib's raw `MemLp.mul'` and
      `L2.integrable_inner` estimates do not manufacture that custom record.
      -/
      constructor
      · intro u hu
        obtain ⟨k, hk, w, hwweak, hwstrong⟩ := hrel u hu
        obtain ⟨C, hC⟩ := apm_m01J04_uniform_grad_norm
          (u := fun n ↦ u (k n)) (by
            obtain ⟨C, hC⟩ := hu
            exact ⟨C, fun n ↦ hC (k n)⟩)
        refine ⟨k, hk, w, fun ψ hψ ↦ ?_⟩
        exact apm_m01J04_rellich_pairing hwweak hwstrong C hC ψ hψ
      · /-
        The remaining positive-dimensional div-curl clause uses
        `apm_m01J04_bridge_1`; its only unresolved prerequisite is the local
        Meyers--Serrin theorem isolated as
        `apm_m01J04_localization_isH1Zero`.
        -/
        intro f fLim v vLim hf hv hdiv φ hφ
        exact apm_m01J04_compensated_pairing hrel hf hv hdiv φ hφ

#print axioms apm_m01j04
