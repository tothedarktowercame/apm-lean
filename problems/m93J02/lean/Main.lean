import Mathlib

/-!
# APM m93J02: Local and global Hölder seminorms

## Statement repairs

1. The global denominator is printed as `|x - y^α|`; it must be
   `|x-y|^α`, matching the standard Hölder seminorm and the rest of the
   problem.
2. The problem omits the range of `α` and permits a singleton `Ω`, although
   the requested counterexamples and completeness verdicts require the strict
   Hölder range `0 < α < 1` and at least two points. We add those hypotheses,
   as used by the supplied solution.

## Encoding questions

None. Potentially infinite seminorms are represented in `ℝ≥0∞`. The norm
axioms and metric completeness are stated explicitly on the common finite
Hölder space, avoiding any assumption that the desired norm instances already
exist in Mathlib.
-/

open Set Metric
open scoped ENNReal

noncomputable section

def apm_m93J02_quotient {n : ℕ} {U : Set (Fin n → ℝ)} (α : ℝ)
    (f : U → ℝ) (y z : U) : ℝ≥0∞ :=
  ENNReal.ofReal (|f z - f y| / dist (z : Fin n → ℝ) y ^ α)

/-- The infinitesimal/local Hölder seminorm from the source. -/
def apm_m93J02_localSeminorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ≥0∞ :=
  ⨆ x : U,
    Filter.limsup
      (fun ε : ℝ ↦
        ⨆ y : U, ⨆ z : U,
          if dist (y : Fin n → ℝ) x ≤ ε ∧
              dist (z : Fin n → ℝ) x ≤ ε ∧ z ≠ y then
            apm_m93J02_quotient α f y z
          else 0)
      (nhdsWithin 0 (Ioi 0))

/-- The usual global Hölder seminorm. -/
def apm_m93J02_globalSeminorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ≥0∞ :=
  ⨆ y : U, ⨆ z : U,
    if z ≠ y then apm_m93J02_quotient α f y z else 0

def apm_m93J02_supNorm {n : ℕ} {U : Set (Fin n → ℝ)}
    (f : U → ℝ) : ℝ≥0∞ :=
  ⨆ x : U, ENNReal.ofReal |f x|

def apm_m93J02_holderFunctions {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) : Set (U → ℝ) :=
  {f | apm_m93J02_globalSeminorm U α f ≠ ⊤}

def apm_m93J02_localNorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ :=
  (apm_m93J02_localSeminorm U α f + apm_m93J02_supNorm f).toReal

def apm_m93J02_globalNorm {n : ℕ} (U : Set (Fin n → ℝ))
    (α : ℝ) (f : U → ℝ) : ℝ :=
  (apm_m93J02_globalSeminorm U α f + apm_m93J02_supNorm f).toReal

private lemma apm_m93J02_eq_zero_of_supNorm_eq_zero
    {n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ}
    (hf : apm_m93J02_supNorm f = 0) : f = 0 := by
  funext x
  have hx : ENNReal.ofReal |f x| ≤ apm_m93J02_supNorm f := by
    exact le_iSup (fun y : U ↦ ENNReal.ofReal |f y|) x
  rw [hf] at hx
  have hz : ENNReal.ofReal |f x| = 0 := bot_unique hx
  rw [ENNReal.ofReal_eq_zero] at hz
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

/-- Definiteness is independent of the seminorm algebra once the encoded
ENNReal norm sum is known to be finite. -/
private lemma apm_m93J02_eq_zero_of_toReal_add_eq_zero
    {n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ} {s : ℝ≥0∞}
    (hfinite : s + apm_m93J02_supNorm f ≠ ⊤)
    (hzero : (s + apm_m93J02_supNorm f).toReal = 0) : f = 0 := by
  have hsum : s + apm_m93J02_supNorm f = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hfinite
  exact apm_m93J02_eq_zero_of_supNorm_eq_zero (add_eq_zero.mp hsum).2

private lemma apm_m93J02_quotient_le_globalSeminorm
    {n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ} {y z : U} {alpha : ℝ} :
    apm_m93J02_quotient alpha f y z ≤
      apm_m93J02_globalSeminorm U alpha f := by
  by_cases hyz : z = y
  · subst z
    simp [apm_m93J02_quotient]
  · exact le_iSup_of_le y <| le_iSup_of_le z <| by
      simp [hyz]

private lemma apm_m93J02_holderWith_of_globalSeminorm_ne_top
    {n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hf : apm_m93J02_globalSeminorm U alpha f ≠ ⊤) :
    HolderWith (apm_m93J02_globalSeminorm U alpha f).toNNReal
      ⟨alpha, halpha.le⟩ f := by
  intro y z
  by_cases hyz : z = y
  · subst z
    simp
  · have hdist : 0 < dist (z : Fin n → ℝ) y := dist_pos.mpr (by
      exact fun h ↦ hyz (Subtype.ext h))
    have hq := apm_m93J02_quotient_le_globalSeminorm
      (f := f) (y := y) (z := z) (alpha := alpha)
    calc
      edist (f y) (f z) = ENNReal.ofReal |f z - f y| := by
        simp [edist_dist, Real.dist_eq, abs_sub_comm]
      _ = apm_m93J02_quotient alpha f y z *
          ENNReal.ofReal (dist (z : Fin n → ℝ) y ^ alpha) := by
        rw [apm_m93J02_quotient, ← ENNReal.ofReal_mul (by positivity),
          div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hdist alpha))]
      _ ≤ apm_m93J02_globalSeminorm U alpha f *
          ENNReal.ofReal (dist (z : Fin n → ℝ) y ^ alpha) :=
        mul_le_mul_right' hq _
      _ = ((apm_m93J02_globalSeminorm U alpha f).toNNReal : ℝ≥0∞) *
          edist y z ^ alpha := by
        rw [ENNReal.coe_toNNReal hf, edist_dist,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg halpha.le]
        simp [Subtype.dist_eq, dist_comm]

private lemma apm_m93J02_holderOnWith_of_quotient_le
    {n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ} {alpha : ℝ}
    {s : Set U} {C : ℝ≥0∞} (halpha : 0 < alpha) (hC : C ≠ ⊤)
    (hq : ∀ y ∈ s, ∀ z ∈ s, apm_m93J02_quotient alpha f y z ≤ C) :
    HolderOnWith C.toNNReal ⟨alpha, halpha.le⟩ f s := by
  intro y hy z hz
  by_cases hyz : z = y
  · subst z
    simp
  · have hdist : 0 < dist (z : Fin n → ℝ) y := dist_pos.mpr (by
      exact fun h ↦ hyz (Subtype.ext h))
    calc
      edist (f y) (f z) = ENNReal.ofReal |f z - f y| := by
        simp [edist_dist, Real.dist_eq, abs_sub_comm]
      _ = apm_m93J02_quotient alpha f y z *
          ENNReal.ofReal (dist (z : Fin n → ℝ) y ^ alpha) := by
        rw [apm_m93J02_quotient, ← ENNReal.ofReal_mul (by positivity),
          div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hdist alpha))]
      _ ≤ C * ENNReal.ofReal (dist (z : Fin n → ℝ) y ^ alpha) :=
        mul_le_mul_right' (hq y hy z hz) _
      _ = (C.toNNReal : ℝ≥0∞) * edist y z ^ alpha := by
        rw [ENNReal.coe_toNNReal hC, edist_dist,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg halpha.le]
        simp [Subtype.dist_eq, dist_comm]

private lemma apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
    {n : ℕ} {U : Set (Fin n → ℝ)} (hUcompact : IsCompact U)
    {f : U → ℝ} {alpha : ℝ} (halpha : 0 < alpha)
    (hf : apm_m93J02_globalSeminorm U alpha f ≠ ⊤) :
    apm_m93J02_supNorm f ≠ ⊤ := by
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hUcompact
  have hcontinuous : Continuous f :=
    (apm_m93J02_holderWith_of_globalSeminorm_ne_top halpha hf).continuous
      (by simpa using halpha)
  have hcompact : IsCompact (Set.range fun x : U ↦ |f x|) :=
    isCompact_range hcontinuous.abs
  obtain ⟨C, hC⟩ := hcompact.bddAbove
  refine ne_top_of_le_ne_top
    (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top) ?_
  unfold apm_m93J02_supNorm
  refine iSup_le fun x ↦ ENNReal.ofReal_le_ofReal ?_
  exact hC (Set.mem_range_self x)

private lemma apm_m93J02_quotient_smul
    {n : ℕ} {U : Set (Fin n → ℝ)} (alpha c : ℝ) (f : U → ℝ)
    (y z : U) :
    apm_m93J02_quotient alpha (c • f) y z =
      ENNReal.ofReal |c| * apm_m93J02_quotient alpha f y z := by
  unfold apm_m93J02_quotient
  rw [show |(c • f) z - (c • f) y| = |c| * |f z - f y| by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul]]
  rw [mul_div_assoc, ENNReal.ofReal_mul (abs_nonneg c)]

private lemma apm_m93J02_quotient_add_le
    {n : ℕ} {U : Set (Fin n → ℝ)} (alpha : ℝ) (f g : U → ℝ)
    (y z : U) :
    apm_m93J02_quotient alpha (f + g) y z ≤
      apm_m93J02_quotient alpha f y z +
        apm_m93J02_quotient alpha g y z := by
  unfold apm_m93J02_quotient
  have hdenom : 0 ≤ dist (z : Fin n → ℝ) y ^ alpha :=
    Real.rpow_nonneg dist_nonneg alpha
  calc
    ENNReal.ofReal
        (|(f + g) z - (f + g) y| / dist (z : Fin n → ℝ) y ^ alpha) ≤
        ENNReal.ofReal
          ((|f z - f y| + |g z - g y|) /
            dist (z : Fin n → ℝ) y ^ alpha) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ hdenom
      simpa only [Pi.add_apply, add_sub_add_comm] using
        abs_add_le (f z - f y) (g z - g y)
    _ = ENNReal.ofReal
          (|f z - f y| / dist (z : Fin n → ℝ) y ^ alpha) +
        ENNReal.ofReal
          (|g z - g y| / dist (z : Fin n → ℝ) y ^ alpha) := by
      rw [add_div, ENNReal.ofReal_add]
      · exact div_nonneg (abs_nonneg _) hdenom
      · exact div_nonneg (abs_nonneg _) hdenom

private lemma apm_m93J02_globalSeminorm_smul
    {n : ℕ} (U : Set (Fin n → ℝ)) (alpha c : ℝ) (f : U → ℝ) :
    apm_m93J02_globalSeminorm U alpha (c • f) =
      ENNReal.ofReal |c| * apm_m93J02_globalSeminorm U alpha f := by
  unfold apm_m93J02_globalSeminorm
  rw [ENNReal.mul_iSup]
  congr with y
  rw [ENNReal.mul_iSup]
  congr with z
  by_cases hyz : z ≠ y
  · simp [hyz, apm_m93J02_quotient_smul]
  · simp [hyz]

private lemma apm_m93J02_globalSeminorm_add_le
    {n : ℕ} (U : Set (Fin n → ℝ)) (alpha : ℝ) (f g : U → ℝ) :
    apm_m93J02_globalSeminorm U alpha (f + g) ≤
      apm_m93J02_globalSeminorm U alpha f +
        apm_m93J02_globalSeminorm U alpha g := by
  unfold apm_m93J02_globalSeminorm
  refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
  by_cases hyz : z ≠ y
  · rw [if_pos hyz]
    exact (apm_m93J02_quotient_add_le alpha f g y z).trans <|
      add_le_add
        (apm_m93J02_quotient_le_globalSeminorm
          (f := f) (y := y) (z := z) (alpha := alpha))
        (apm_m93J02_quotient_le_globalSeminorm
          (f := g) (y := y) (z := z) (alpha := alpha))
  · simp [hyz]

private lemma apm_m93J02_supNorm_smul
    {n : ℕ} {U : Set (Fin n → ℝ)} (c : ℝ) (f : U → ℝ) :
    apm_m93J02_supNorm (c • f) = ENNReal.ofReal |c| * apm_m93J02_supNorm f := by
  unfold apm_m93J02_supNorm
  rw [ENNReal.mul_iSup]
  congr with x
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]

private lemma apm_m93J02_supNorm_add_le
    {n : ℕ} {U : Set (Fin n → ℝ)} (f g : U → ℝ) :
    apm_m93J02_supNorm (f + g) ≤
      apm_m93J02_supNorm f + apm_m93J02_supNorm g := by
  unfold apm_m93J02_supNorm
  refine iSup_le fun x ↦ ?_
  calc
    ENNReal.ofReal |(f + g) x| ≤
        ENNReal.ofReal |f x| + ENNReal.ofReal |g x| := by
      exact (ENNReal.ofReal_le_ofReal (abs_add_le (f x) (g x))).trans
        (ENNReal.ofReal_add_le)
    _ ≤ (⨆ x, ENNReal.ofReal |f x|) + (⨆ x, ENNReal.ofReal |g x|) :=
      add_le_add
        (le_iSup (fun x : U ↦ ENNReal.ofReal |f x|) x)
        (le_iSup (fun x : U ↦ ENNReal.ofReal |g x|) x)

private lemma apm_m93J02_globalSeminorm_sub_ne_top
    {n : ℕ} (U : Set (Fin n → ℝ)) (alpha : ℝ) {f g : U → ℝ}
    (hf : apm_m93J02_globalSeminorm U alpha f ≠ ⊤)
    (hg : apm_m93J02_globalSeminorm U alpha g ≠ ⊤) :
    apm_m93J02_globalSeminorm U alpha (f - g) ≠ ⊤ := by
  have hneg : apm_m93J02_globalSeminorm U alpha (-g) =
      apm_m93J02_globalSeminorm U alpha g := by
    simpa using apm_m93J02_globalSeminorm_smul U alpha (-1) g
  have hneg_top : apm_m93J02_globalSeminorm U alpha (-g) ≠ ⊤ := by
    rw [hneg]
    exact hg
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, hneg_top⟩) <| by
    simpa only [sub_eq_add_neg] using
      apm_m93J02_globalSeminorm_add_le U alpha f (-g)

private lemma apm_m93J02_abs_apply_le_globalNorm
    {n : ℕ} {U : Set (Fin n → ℝ)} (hUcompact : IsCompact U)
    {alpha : ℝ} (halpha : 0 < alpha) {f : U → ℝ}
    (hf : apm_m93J02_globalSeminorm U alpha f ≠ ⊤) (x : U) :
    |f x| ≤ apm_m93J02_globalNorm U alpha f := by
  have hsup : apm_m93J02_supNorm f ≠ ⊤ :=
    apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
      hUcompact halpha hf
  have hsum : apm_m93J02_globalSeminorm U alpha f +
      apm_m93J02_supNorm f ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hf, hsup⟩
  have hle : ENNReal.ofReal |f x| ≤
      apm_m93J02_globalSeminorm U alpha f + apm_m93J02_supNorm f :=
    (le_iSup (fun x : U ↦ ENNReal.ofReal |f x|) x).trans
      (le_add_of_nonneg_left bot_le)
  simpa [apm_m93J02_globalNorm, ENNReal.toReal_ofReal (abs_nonneg (f x))] using
    ENNReal.toReal_mono hsum hle

private lemma apm_m93J02_quotient_real_le_globalNorm
    {n : ℕ} {U : Set (Fin n → ℝ)} (hUcompact : IsCompact U)
    {alpha : ℝ} (halpha : 0 < alpha) {f : U → ℝ}
    (hf : apm_m93J02_globalSeminorm U alpha f ≠ ⊤) (y z : U) :
    |f z - f y| / dist (z : Fin n → ℝ) y ^ alpha ≤
      apm_m93J02_globalNorm U alpha f := by
  have hsup : apm_m93J02_supNorm f ≠ ⊤ :=
    apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
      hUcompact halpha hf
  have hsum : apm_m93J02_globalSeminorm U alpha f +
      apm_m93J02_supNorm f ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hf, hsup⟩
  have hle : apm_m93J02_quotient alpha f y z ≤
      apm_m93J02_globalSeminorm U alpha f + apm_m93J02_supNorm f :=
    apm_m93J02_quotient_le_globalSeminorm.trans
      (le_add_of_nonneg_right bot_le)
  have hreal := ENNReal.toReal_mono hsum hle
  rw [apm_m93J02_quotient,
    ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _)
      (Real.rpow_nonneg dist_nonneg alpha))] at hreal
  exact hreal

private lemma apm_m93J02_limsup_add_le {iota : Type*}
    (l : Filter iota) [l.NeBot] (u v : iota → ℝ≥0∞) :
    Filter.limsup (u + v) l ≤ Filter.limsup u l + Filter.limsup v l := by
  rw [Filter.limsup_le_iff']
  intro b hb
  obtain ⟨a, ha, c, hc, hac⟩ := ENNReal.exists_add_lt_of_add_lt hb
  filter_upwards [
    (Filter.limsup_le_iff').1 le_rfl a ha,
    (Filter.limsup_le_iff').1 le_rfl c hc] with x hux hvx
  exact (add_le_add hux hvx).trans hac.le

private lemma apm_m93J02_localSeminorm_smul
    {n : ℕ} (U : Set (Fin n → ℝ)) (alpha c : ℝ) (f : U → ℝ) :
    apm_m93J02_localSeminorm U alpha (c • f) =
      ENNReal.ofReal |c| * apm_m93J02_localSeminorm U alpha f := by
  unfold apm_m93J02_localSeminorm
  rw [ENNReal.mul_iSup]
  congr with x
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  congr with epsilon
  rw [ENNReal.mul_iSup]
  congr with y
  rw [ENNReal.mul_iSup]
  congr with z
  by_cases hnear : dist (y : Fin n → ℝ) x ≤ epsilon ∧
      dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y
  · simp [hnear, apm_m93J02_quotient_smul]
  · simp [hnear]

private lemma apm_m93J02_localSeminorm_add_le
    {n : ℕ} (U : Set (Fin n → ℝ)) (alpha : ℝ) (f g : U → ℝ) :
    apm_m93J02_localSeminorm U alpha (f + g) ≤
      apm_m93J02_localSeminorm U alpha f +
        apm_m93J02_localSeminorm U alpha g := by
  unfold apm_m93J02_localSeminorm
  refine iSup_le fun x ↦ ?_
  let F := fun (h : U → ℝ) (epsilon : ℝ) ↦
    ⨆ y : U, ⨆ z : U,
      if dist (y : Fin n → ℝ) x ≤ epsilon ∧
          dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
        apm_m93J02_quotient alpha h y z
      else 0
  have hF : ∀ epsilon, F (f + g) epsilon ≤ F f epsilon + F g epsilon := by
    intro epsilon
    dsimp only [F]
    refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
    by_cases hnear : dist (y : Fin n → ℝ) x ≤ epsilon ∧
        dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y
    · rw [if_pos hnear]
      exact (apm_m93J02_quotient_add_le alpha f g y z).trans <|
        add_le_add
          (le_iSup_of_le y <| le_iSup_of_le z <| by rw [if_pos hnear])
          (le_iSup_of_le y <| le_iSup_of_le z <| by rw [if_pos hnear])
    · simp [hnear]
  change Filter.limsup (F (f + g)) (nhdsWithin 0 (Ioi 0)) ≤ _
  calc
    Filter.limsup (F (f + g)) (nhdsWithin 0 (Ioi 0)) ≤
        Filter.limsup (fun epsilon ↦ F f epsilon + F g epsilon)
          (nhdsWithin 0 (Ioi 0)) := by
      refine Filter.limsup_le_limsup ?_
      exact Filter.Eventually.of_forall hF
    _ ≤ Filter.limsup (F f) (nhdsWithin 0 (Ioi 0)) +
        Filter.limsup (F g) (nhdsWithin 0 (Ioi 0)) :=
      apm_m93J02_limsup_add_le _ (F f) (F g)
    _ ≤ _ := add_le_add
      (le_iSup (fun x : U ↦ Filter.limsup
        (fun epsilon ↦
          ⨆ y : U, ⨆ z : U,
            if dist (y : Fin n → ℝ) x ≤ epsilon ∧
                dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
              apm_m93J02_quotient alpha f y z
            else 0)
        (nhdsWithin 0 (Ioi 0))) x)
      (le_iSup (fun x : U ↦ Filter.limsup
        (fun epsilon ↦
          ⨆ y : U, ⨆ z : U,
            if dist (y : Fin n → ℝ) x ≤ epsilon ∧
                dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
              apm_m93J02_quotient alpha g y z
            else 0)
        (nhdsWithin 0 (Ioi 0))) x)

private lemma apm_m93J02_localSeminorm_dist_eq_zero
    {n : ℕ} {U : Set (Fin n → ℝ)} (p : U) {alpha : ℝ}
    (halpha : alpha < 1) :
    apm_m93J02_localSeminorm U alpha
      (fun x : U ↦ dist (x : Fin n → ℝ) p) = 0 := by
  unfold apm_m93J02_localSeminorm
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    let B := fun epsilon : ℝ ↦
      ENNReal.ofReal (2 * epsilon) ^ (1 - alpha)
    have hreal : Filter.Tendsto (fun epsilon : ℝ ↦ 2 * epsilon)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hreal_full : Filter.Tendsto (fun epsilon : ℝ ↦ 2 * epsilon)
          (nhds 0) (nhds 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
      exact hreal_full.mono_left nhdsWithin_le_nhds
    have hbase : Filter.Tendsto (fun epsilon : ℝ ↦ ENNReal.ofReal (2 * epsilon))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hreal
    have hB : Filter.Tendsto B (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [B, sub_pos.mpr halpha] using
        hbase.ennrpow_const (1 - alpha)
    have hbound : ∀ epsilon : ℝ,
        (⨆ y : U, ⨆ z : U,
          if dist (y : Fin n → ℝ) x ≤ epsilon ∧
              dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
            apm_m93J02_quotient alpha
              (fun w : U ↦ dist (w : Fin n → ℝ) p) y z
          else 0) ≤ B epsilon := by
      intro epsilon
      refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
      by_cases hnear : dist (y : Fin n → ℝ) x ≤ epsilon ∧
          dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y
      · rw [if_pos hnear]
        have hepsilon : 0 ≤ epsilon := dist_nonneg.trans hnear.1
        have hd_le : dist (z : Fin n → ℝ) y ≤ 2 * epsilon := by
          calc
            dist (z : Fin n → ℝ) y ≤
                dist (z : Fin n → ℝ) x + dist (y : Fin n → ℝ) x :=
              dist_triangle_right _ _ _
            _ ≤ epsilon + epsilon := add_le_add hnear.2.1 hnear.1
            _ = 2 * epsilon := by ring
        unfold apm_m93J02_quotient
        dsimp only [B]
        rw [ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (by norm_num) hepsilon) (sub_nonneg.mpr halpha.le)]
        apply ENNReal.ofReal_le_ofReal
        change
          |dist (z : Fin n → ℝ) p - dist (y : Fin n → ℝ) p| /
              dist (z : Fin n → ℝ) y ^ alpha ≤
            (2 * epsilon) ^ (1 - alpha)
        calc
          |dist (z : Fin n → ℝ) p - dist (y : Fin n → ℝ) p| /
                dist (z : Fin n → ℝ) y ^ alpha ≤
              dist (z : Fin n → ℝ) y /
                dist (z : Fin n → ℝ) y ^ alpha := by
            exact div_le_div_of_nonneg_right
              (abs_dist_sub_le (z : Fin n → ℝ) y p)
              (Real.rpow_nonneg dist_nonneg alpha)
          _ = dist (z : Fin n → ℝ) y ^ (1 - alpha) := by
            exact (Real.rpow_one_sub' dist_nonneg
              (sub_ne_zero.mpr (ne_of_gt halpha))).symm
          _ ≤ (2 * epsilon) ^ (1 - alpha) :=
            Real.rpow_le_rpow dist_nonneg hd_le (sub_nonneg.mpr halpha.le)
      · simp [hnear, B]
    calc
      Filter.limsup
          (fun epsilon : ℝ ↦
            ⨆ y : U, ⨆ z : U,
              if dist (y : Fin n → ℝ) x ≤ epsilon ∧
                  dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
                apm_m93J02_quotient alpha
                  (fun w : U ↦ dist (w : Fin n → ℝ) p) y z
              else 0)
          (nhdsWithin 0 (Ioi 0)) ≤
          Filter.limsup B (nhdsWithin 0 (Ioi 0)) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall hbound)
      _ = 0 := hB.limsup_eq
  · exact bot_le

private lemma apm_m93J02_localSeminorm_eq_zero_of_lipschitzWith
    {n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ} {C : NNReal}
    {alpha : ℝ} (hf : LipschitzWith C f) (halpha : alpha < 1) :
    apm_m93J02_localSeminorm U alpha f = 0 := by
  unfold apm_m93J02_localSeminorm
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    let B := fun epsilon : ℝ ↦
      ENNReal.ofReal (C : ℝ) *
        ENNReal.ofReal (2 * epsilon) ^ (1 - alpha)
    have hreal : Filter.Tendsto (fun epsilon : ℝ ↦ 2 * epsilon)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hreal_full : Filter.Tendsto (fun epsilon : ℝ ↦ 2 * epsilon)
          (nhds 0) (nhds 0) := by
        simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
      exact hreal_full.mono_left nhdsWithin_le_nhds
    have hbase : Filter.Tendsto (fun epsilon : ℝ ↦ ENNReal.ofReal (2 * epsilon))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hreal
    have hpow : Filter.Tendsto
        (fun epsilon : ℝ ↦ ENNReal.ofReal (2 * epsilon) ^ (1 - alpha))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [sub_pos.mpr halpha] using
        hbase.ennrpow_const (1 - alpha)
    have hB : Filter.Tendsto B (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa only [B, mul_zero] using
        ENNReal.Tendsto.const_mul
          (a := ENNReal.ofReal (C : ℝ)) hpow
          (Or.inr ENNReal.ofReal_ne_top)
    have hbound : ∀ epsilon : ℝ,
        (⨆ y : U, ⨆ z : U,
          if dist (y : Fin n → ℝ) x ≤ epsilon ∧
              dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
            apm_m93J02_quotient alpha f y z
          else 0) ≤ B epsilon := by
      intro epsilon
      refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
      by_cases hnear : dist (y : Fin n → ℝ) x ≤ epsilon ∧
          dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y
      · rw [if_pos hnear]
        have hepsilon : 0 ≤ epsilon := dist_nonneg.trans hnear.1
        have hd_le : dist (z : Fin n → ℝ) y ≤ 2 * epsilon := by
          calc
            dist (z : Fin n → ℝ) y ≤
                dist (z : Fin n → ℝ) x + dist (y : Fin n → ℝ) x :=
              dist_triangle_right _ _ _
            _ ≤ epsilon + epsilon := add_le_add hnear.2.1 hnear.1
            _ = 2 * epsilon := by ring
        have hlip : |f z - f y| ≤
            (C : ℝ) * dist (z : Fin n → ℝ) y := by
          simpa [Real.dist_eq, abs_sub_comm, Subtype.dist_eq] using
            hf.dist_le_mul z y
        unfold apm_m93J02_quotient
        dsimp only [B]
        rw [ENNReal.ofReal_rpow_of_nonneg
            (mul_nonneg (by norm_num) hepsilon) (sub_nonneg.mpr halpha.le),
          ← ENNReal.ofReal_mul C.coe_nonneg]
        apply ENNReal.ofReal_le_ofReal
        calc
          |f z - f y| / dist (z : Fin n → ℝ) y ^ alpha ≤
              ((C : ℝ) * dist (z : Fin n → ℝ) y) /
                dist (z : Fin n → ℝ) y ^ alpha := by
            exact div_le_div_of_nonneg_right hlip
              (Real.rpow_nonneg dist_nonneg alpha)
          _ = (C : ℝ) * dist (z : Fin n → ℝ) y ^ (1 - alpha) := by
            rw [mul_div_assoc,
              Real.rpow_one_sub' dist_nonneg
                (sub_ne_zero.mpr (ne_of_gt halpha))]
          _ ≤ (C : ℝ) * (2 * epsilon) ^ (1 - alpha) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow dist_nonneg hd_le
                (sub_nonneg.mpr halpha.le)) C.coe_nonneg
      · simp [hnear, B]
    calc
      Filter.limsup
          (fun epsilon : ℝ ↦
            ⨆ y : U, ⨆ z : U,
              if dist (y : Fin n → ℝ) x ≤ epsilon ∧
                  dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
                apm_m93J02_quotient alpha f y z
              else 0)
          (nhdsWithin 0 (Ioi 0)) ≤
          Filter.limsup B (nhdsWithin 0 (Ioi 0)) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall hbound)
      _ = 0 := hB.limsup_eq
  · exact bot_le

private lemma apm_m93J02_lipschitzWith_shifted_rpow_dist
    {n : ℕ} {U : Set (Fin n → ℝ)} (p : U) {alpha a : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (ha : 0 < a) :
    ∃ C : NNReal, LipschitzWith C (fun x : U ↦
      (dist (x : Fin n → ℝ) p + a) ^ alpha - a ^ alpha) := by
  let C : NNReal :=
    ⟨alpha * a ^ (alpha - 1),
      mul_nonneg halpha0.le (Real.rpow_nonneg ha.le _)⟩
  have hscalar : LipschitzOnWith C (fun t : ℝ ↦ t ^ alpha) (Ici a) := by
    apply (convex_Ici a).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (Real.hasDerivAt_rpow_const
        (Or.inl (ne_of_gt (ha.trans_le ht)))).differentiableAt
    · intro t ht
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs,
        Real.deriv_rpow_const]
      rw [abs_of_nonneg
        (mul_nonneg halpha0.le (Real.rpow_nonneg (ha.trans_le ht).le _))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha (show a ≤ t from ht)
          (sub_nonpos.mpr halpha1.le)) halpha0.le
  let r : U → ℝ := fun x ↦ dist (x : Fin n → ℝ) p + a
  have hr : LipschitzWith 1 r := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [r, Real.dist_eq, add_sub_add_right_eq_sub,
      NNReal.coe_one, one_mul, Subtype.dist_eq, abs_sub_comm] using
      (LipschitzWith.dist_left p).dist_le_mul x y
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have hx : r x ∈ Ici a := by
    dsimp only [r]
    exact le_add_of_nonneg_left dist_nonneg
  have hy : r y ∈ Ici a := by
    dsimp only [r]
    exact le_add_of_nonneg_left dist_nonneg
  have hscalar_xy := hscalar.dist_le_mul (r x) hx (r y) hy
  calc
    dist ((dist (x : Fin n → ℝ) p + a) ^ alpha - a ^ alpha)
        ((dist (y : Fin n → ℝ) p + a) ^ alpha - a ^ alpha) =
        dist ((r x) ^ alpha) ((r y) ^ alpha) := by
          simp only [r, Real.dist_eq, sub_sub_sub_cancel_right]
    _ ≤ (C : ℝ) * dist (r x) (r y) := hscalar_xy
    _ ≤ (C : ℝ) * (1 * dist x y) :=
      mul_le_mul_of_nonneg_left (hr.dist_le_mul x y) C.coe_nonneg
    _ = (C : ℝ) * dist x y := by ring

private lemma apm_m93J02_shifted_rpow_approx
    {r a alpha : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    |((r + a) ^ alpha - a ^ alpha) - r ^ alpha| ≤ a ^ alpha := by
  have hsum : (r + a) ^ alpha ≤ r ^ alpha + a ^ alpha :=
    Real.rpow_add_le_add_rpow hr ha halpha0 halpha1
  have hmono : r ^ alpha ≤ (r + a) ^ alpha :=
    Real.rpow_le_rpow hr (le_add_of_nonneg_right ha) halpha0
  rw [abs_le]
  constructor <;> linarith [Real.rpow_nonneg ha alpha]

private lemma apm_m93J02_one_le_localSeminorm_rpow_dist
    {n : ℕ} {U : Set (Fin n → ℝ)} (p : U) {alpha : ℝ}
    (halpha0 : 0 < alpha)
    (hp : ∀ epsilon : ℝ, 0 < epsilon → ∃ z : U,
      dist (z : Fin n → ℝ) p ≤ epsilon ∧ z ≠ p) :
    1 ≤ apm_m93J02_localSeminorm U alpha
      (fun x : U ↦ dist (x : Fin n → ℝ) p ^ alpha) := by
  let A := fun epsilon : ℝ ↦
    ⨆ y : U, ⨆ z : U,
      if dist (y : Fin n → ℝ) p ≤ epsilon ∧
          dist (z : Fin n → ℝ) p ≤ epsilon ∧ z ≠ y then
        apm_m93J02_quotient alpha
          (fun x : U ↦ dist (x : Fin n → ℝ) p ^ alpha) y z
      else 0
  have hA : ∀ epsilon : ℝ, 0 < epsilon → 1 ≤ A epsilon := by
    intro epsilon hepsilon
    obtain ⟨z, hzdist, hzp⟩ := hp epsilon hepsilon
    have hdist : 0 < dist (z : Fin n → ℝ) p :=
      dist_pos.mpr fun h ↦ hzp (Subtype.ext h)
    have hquot : apm_m93J02_quotient alpha
        (fun x : U ↦ dist (x : Fin n → ℝ) p ^ alpha) p z = 1 := by
      unfold apm_m93J02_quotient
      dsimp only
      rw [show dist (p : Fin n → ℝ) p ^ alpha = 0 by
        simp [halpha0.ne'], sub_zero, abs_of_nonneg
          (Real.rpow_nonneg dist_nonneg alpha),
        div_self (ne_of_gt (Real.rpow_pos_of_pos hdist alpha)),
        ENNReal.ofReal_one]
    exact le_iSup_of_le p <| le_iSup_of_le z <| by
      rw [if_pos]
      · exact hquot.ge
      · exact ⟨by simpa using hepsilon.le, hzdist, hzp⟩
  have heventually : ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Ioi 0),
      1 ≤ A epsilon := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact hA epsilon hepsilon
  have hlim : 1 ≤ Filter.limsup A (nhdsWithin 0 (Ioi 0)) :=
    Filter.le_limsup_of_frequently_le' heventually.frequently
  exact hlim.trans <| by
    unfold apm_m93J02_localSeminorm
    exact le_iSup (fun x : U ↦
      Filter.limsup
        (fun epsilon : ℝ ↦
          ⨆ y : U, ⨆ z : U,
            if dist (y : Fin n → ℝ) x ≤ epsilon ∧
                dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
              apm_m93J02_quotient alpha
                (fun w : U ↦ dist (w : Fin n → ℝ) p ^ alpha) y z
            else 0)
        (nhdsWithin 0 (Ioi 0))) p

/-- The norm axioms restricted to a specified vector subspace carrier. -/
def apm_m93J02_isNormOn {V : Type} [AddCommGroup V] [Module ℝ V]
    (S : Set V) (q : V → ℝ) : Prop :=
  q 0 = 0 ∧
  (∀ f ∈ S, q f = 0 → f = 0) ∧
  (∀ (c : ℝ) f, f ∈ S → q (c • f) = |c| * q f) ∧
  ∀ f ∈ S, ∀ g ∈ S, q (f + g) ≤ q f + q g

/-- Sequential completeness for the metric induced by `q` on `S`. -/
def apm_m93J02_isCompleteOn {V : Type} [AddCommGroup V]
    (S : Set V) (q : V → ℝ) : Prop :=
  ∀ u : ℕ → V, (∀ n, u n ∈ S) →
    (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, q (u m - u n) < ε) →
    ∃ f ∈ S, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, q (u n - f) < ε

theorem apm_m93j02
    (n : ℕ) (U : Set (Fin n → ℝ)) (hUcompact : IsCompact U)
    (hUconnected : IsConnected U)
    (hUnontrivial : ∃ x ∈ U, ∃ y ∈ U, x ≠ y)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ f : U → ℝ,
      apm_m93J02_localSeminorm U α f ≠ ⊤ →
        apm_m93J02_globalSeminorm U α f ≠ ⊤) ∧
    (∀ f : U → ℝ,
      apm_m93J02_globalSeminorm U α f ≠ ⊤ →
        apm_m93J02_localSeminorm U α f ≠ ⊤) ∧
    (∀ f : U → ℝ,
      apm_m93J02_localSeminorm U α f ≤
        apm_m93J02_globalSeminorm U α f) ∧
    ¬(∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ f : U → ℝ,
      apm_m93J02_globalSeminorm U α f ≤
        K * apm_m93J02_localSeminorm U α f) ∧
    apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_localNorm U α) ∧
    ¬apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_localNorm U α) ∧
    apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_globalNorm U α) ∧
    apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
      (apm_m93J02_globalNorm U α) := by
  have hle : ∀ f : U → ℝ,
      apm_m93J02_localSeminorm U α f ≤
        apm_m93J02_globalSeminorm U α f := by
    intro f
    unfold apm_m93J02_localSeminorm apm_m93J02_globalSeminorm
    refine iSup_le fun x ↦ Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [] with ε
    refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
    split_ifs with hyz
    · exact le_iSup_of_le y (le_iSup_of_le z (by simp [hyz.2.2]))
    · exact bot_le
  have hglobal_local : ∀ f : U → ℝ,
      apm_m93J02_globalSeminorm U α f ≠ ⊤ →
        apm_m93J02_localSeminorm U α f ≠ ⊤ := by
    intro f hf htop
    exact hf (top_unique (htop ▸ hle f))
  have hquotient_zero (y z : U) :
      apm_m93J02_quotient α (0 : U → ℝ) y z = 0 := by
    simp [apm_m93J02_quotient]
  have hglobal_zero :
      apm_m93J02_globalSeminorm U α (0 : U → ℝ) = 0 := by
    simp [apm_m93J02_globalSeminorm, hquotient_zero]
  have hsup_zero : apm_m93J02_supNorm (0 : U → ℝ) = 0 := by
    simp [apm_m93J02_supNorm]
  have hlocal_zero :
      apm_m93J02_localSeminorm U α (0 : U → ℝ) = 0 := by
    simp [apm_m93J02_localSeminorm, hquotient_zero]
  have hlocalNorm_zero :
      apm_m93J02_localNorm U α (0 : U → ℝ) = 0 := by
    simp [apm_m93J02_localNorm, hlocal_zero, hsup_zero]
  have hglobalNorm_zero :
      apm_m93J02_globalNorm U α (0 : U → ℝ) = 0 := by
    simp [apm_m93J02_globalNorm, hglobal_zero, hsup_zero]
  /-
  Boundary (closer hop 2): the zero-function quotient, global seminorm,
  supremum norm, and both norms are now compiled (`hquotient_zero`,
  `hglobal_zero`, `hlocal_zero`, `hsup_zero`, `hglobalNorm_zero`,
  `hlocalNorm_zero`), discharging the first axiom needed by both norm
  predicates.  The new helper `apm_m93J02_eq_zero_of_supNorm_eq_zero` also
  proves the definiteness core shared by both norms. The remaining clauses
  require a compactness/cluster-point proof
  that finite local limsup forces a finite global seminorm, an explicit
  nonconstant Lipschitz function on an arbitrary compact connected nontrivial
  subtype (and proof that its local ENNReal limsup is zero), the ENNReal
  algebra needed for both norm predicates, and complete/incomplete sequence
  constructions for the two induced metrics.

  This hop searched Mathlib's `HolderOnWith`, `ContDiffPointwiseHolderAt`,
  compact-image/connected-image, ENNReal `iSup`/`toReal`, and filter `limsup`
  APIs.  The packaged Hölder predicates use a fixed global constant and do not
  convert to or from this nested infinitesimal ENNReal `limsup`.  For arbitrary
  compact connected `U`, the informal interval constructions can be routed
  through `x ↦ dist x x₀`, whose compact connected image contains an interval;
  however, transporting the Lipschitz-zero local seminorm and the incomplete
  sequence through that map still needs a substantial new limsup development.
  No closed sibling, construction module, or indexed helper supplies it.

  Closer hop 3 compiles the remaining generic definiteness step as
  `apm_m93J02_eq_zero_of_toReal_add_eq_zero`: whenever the ENNReal sum of an
  arbitrary seminorm and `apm_m93J02_supNorm f` is finite, vanishing of its
  `toReal` forces the sum, then the supremum norm, and finally `f` itself to
  vanish.  This uses `ENNReal.toReal_eq_zero_iff` and the previous supremum
  helper.  Hence definiteness for both proposed norms is now reduced solely
  to finiteness of their encoded sums on the Hölder carrier.  Searches of
  compact-domain boundedness and `HolderOnWith` still found no theorem proving
  boundedness of this completely unbundled function from the frozen nested
  `iSup` definition; the compact-chain/local-to-global and completeness
  developments remain open.
  -/
  have hlocal_global : ∀ f : U → ℝ,
      apm_m93J02_localSeminorm U α f ≠ ⊤ →
        apm_m93J02_globalSeminorm U α f ≠ ⊤ := by
    intro f hf
    let S := apm_m93J02_localSeminorm U α f
    let C := S + 1
    let F := fun (x : U) (epsilon : ℝ) ↦
      ⨆ y : U, ⨆ z : U,
        if dist (y : Fin n → ℝ) x ≤ epsilon ∧
            dist (z : Fin n → ℝ) x ≤ epsilon ∧ z ≠ y then
          apm_m93J02_quotient α f y z
        else 0
    have hS_eq : S = ⨆ x : U,
        Filter.limsup (F x) (nhdsWithin 0 (Ioi 0)) := rfl
    have hS_top : S ≠ ⊤ := by simpa only [S] using hf
    have hC_top : C ≠ ⊤ := by
      exact ENNReal.add_ne_top.2 ⟨hS_top, ENNReal.one_ne_top⟩
    have hSC : S < C := by
      exact ENNReal.lt_add_right hS_top one_ne_zero
    have hradius : ∀ x : U, ∃ r : ℝ, 0 < r ∧ F x r ≤ C := by
      intro x
      have hlim : Filter.limsup (F x) (nhdsWithin 0 (Ioi 0)) ≤ S := by
        rw [hS_eq]
        exact le_iSup (fun x : U ↦
          Filter.limsup (F x) (nhdsWithin 0 (Ioi 0))) x
      have heventually : ∀ᶠ epsilon in nhdsWithin 0 (Ioi 0), F x epsilon < C :=
        Filter.eventually_lt_of_limsup_lt (hlim.trans_lt hSC)
      obtain ⟨r, hrC, hrpos⟩ :=
        (heventually.and (show ∀ᶠ epsilon : ℝ in nhdsWithin 0 (Ioi 0),
          epsilon ∈ Ioi 0 from self_mem_nhdsWithin)).exists
      exact ⟨r, hrpos, hrC.le⟩
    choose r hrpos hrbound using hradius
    have hquot_ball (x : U) : ∀ y ∈ Metric.ball x (r x),
        ∀ z ∈ Metric.ball x (r x),
          apm_m93J02_quotient α f y z ≤ C := by
      intro y hy z hz
      by_cases hyz : z = y
      · subst z
        simp [apm_m93J02_quotient]
      · have hterm : apm_m93J02_quotient α f y z ≤ F x (r x) := by
          dsimp only [F]
          refine le_iSup_of_le y <| le_iSup_of_le z ?_
          rw [if_pos]
          exact ⟨by simpa [Subtype.dist_eq] using hy.le,
            by simpa [Subtype.dist_eq] using hz.le, hyz⟩
        exact hterm.trans (hrbound x)
    letI : CompactSpace U := isCompact_iff_compactSpace.mp hUcompact
    have hcontinuous : Continuous f := continuous_iff_continuousAt.2 fun x ↦
      ((apm_m93J02_holderOnWith_of_quotient_le hα0 hC_top
        (hquot_ball x)).continuousOn (by simpa using hα0)).continuousAt
          (Metric.ball_mem_nhds x (hrpos x))
    have hcompact_abs : IsCompact (Set.range fun x : U ↦ |f x|) :=
      isCompact_range hcontinuous.abs
    obtain ⟨M, hM⟩ := hcompact_abs.bddAbove
    obtain ⟨x0, hx0, _, _, _⟩ := hUnontrivial
    let p0 : U := ⟨x0, hx0⟩
    have hM_nonneg : 0 ≤ M :=
      (abs_nonneg (f p0)).trans (hM (Set.mem_range_self p0))
    obtain ⟨delta, hdelta, hcover⟩ := lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set U)) (c := fun x : U ↦ Metric.ball x (r x))
      isCompact_univ (fun _ ↦ Metric.isOpen_ball) (by
        intro x _
        exact Set.mem_iUnion.2 ⟨x, Metric.mem_ball_self (hrpos x)⟩)
    let D := ENNReal.ofReal (2 * M / delta ^ α)
    have hD_top : D ≠ ⊤ := by
      exact ENNReal.ofReal_ne_top
    have hCD_top : C + D ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hC_top, hD_top⟩
    have hglobal_le : apm_m93J02_globalSeminorm U α f ≤ C + D := by
      unfold apm_m93J02_globalSeminorm
      refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
      by_cases hyz : z ≠ y
      · rw [if_pos hyz]
        by_cases hclose : dist z y < delta
        · obtain ⟨i, hi⟩ := hcover y (Set.mem_univ y)
          have hyi : y ∈ Metric.ball i (r i) :=
            hi (Metric.mem_ball_self hdelta)
          have hzi : z ∈ Metric.ball i (r i) := by
            apply hi
            simpa [dist_comm] using hclose
          exact (hquot_ball i y hyi z hzi).trans
            (le_add_of_nonneg_right bot_le)
        · have hfar : delta ≤ dist (z : Fin n → ℝ) y := by
            simpa [Subtype.dist_eq] using le_of_not_gt hclose
          have hnum : |f z - f y| ≤ 2 * M := by
            calc
              |f z - f y| ≤ |f z| + |f y| := by
                simpa only [sub_eq_add_neg, abs_neg] using
                  abs_add_le (f z) (-f y)
              _ ≤ M + M := add_le_add
                (hM (Set.mem_range_self z)) (hM (Set.mem_range_self y))
              _ = 2 * M := by ring
          have hdenom : delta ^ α ≤
              dist (z : Fin n → ℝ) y ^ α :=
            Real.rpow_le_rpow hdelta.le hfar hα0.le
          have hratio : |f z - f y| /
              dist (z : Fin n → ℝ) y ^ α ≤
                2 * M / delta ^ α := by
            calc
              |f z - f y| / dist (z : Fin n → ℝ) y ^ α ≤
                  (2 * M) / dist (z : Fin n → ℝ) y ^ α :=
                div_le_div_of_nonneg_right hnum
                  (Real.rpow_nonneg dist_nonneg α)
              _ ≤ (2 * M) / delta ^ α :=
                div_le_div_of_nonneg_left
                  (mul_nonneg (by norm_num) hM_nonneg)
                  (Real.rpow_pos_of_pos hdelta α) hdenom
          unfold apm_m93J02_quotient
          exact (ENNReal.ofReal_le_ofReal hratio).trans
            (le_add_of_nonneg_left bot_le)
      · simp [hyz]
    exact ne_top_of_le_ne_top hCD_top hglobal_le
  have hno_uniform_bound : ¬(∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ f : U → ℝ,
      apm_m93J02_globalSeminorm U α f ≤
        K * apm_m93J02_localSeminorm U α f) := by
    rintro ⟨K, _, hK⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hUnontrivial
    let x0 : U := ⟨x, hx⟩
    let y0 : U := ⟨y, hy⟩
    have hxy0 : x0 ≠ y0 := by
      intro h
      exact hxy (congrArg Subtype.val h)
    let f : U → ℝ := fun z ↦ dist (z : Fin n → ℝ) x0
    have hlocal : apm_m93J02_localSeminorm U α f = 0 := by
      simpa [f] using apm_m93J02_localSeminorm_dist_eq_zero x0 hα1
    have hdist : 0 < dist (y0 : Fin n → ℝ) x0 := by
      exact dist_pos.mpr fun h ↦ hxy0 (Subtype.ext h.symm)
    have hquotient : 0 < apm_m93J02_quotient α f x0 y0 := by
      unfold apm_m93J02_quotient
      rw [ENNReal.ofReal_pos]
      dsimp only [f]
      simpa using div_pos hdist (Real.rpow_pos_of_pos hdist α)
    have hglobal : 0 < apm_m93J02_globalSeminorm U α f :=
      hquotient.trans_le <|
        apm_m93J02_quotient_le_globalSeminorm
          (f := f) (y := x0) (z := y0) (alpha := α)
    have hineq := hK f
    rw [hlocal, mul_zero] at hineq
    exact (not_le_of_gt hglobal) hineq
  have hlocal_isNorm :
      apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_localNorm U α) := by
    refine ⟨hlocalNorm_zero, ?_, ?_, ?_⟩
    · intro f hf hzero
      change apm_m93J02_globalSeminorm U α f ≠ ⊤ at hf
      have hlocal : apm_m93J02_localSeminorm U α f ≠ ⊤ :=
        hglobal_local f hf
      have hsup : apm_m93J02_supNorm f ≠ ⊤ :=
        apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
          hUcompact hα0 hf
      exact apm_m93J02_eq_zero_of_toReal_add_eq_zero
        (ENNReal.add_ne_top.2 ⟨hlocal, hsup⟩) hzero
    · intro c f _
      unfold apm_m93J02_localNorm
      rw [apm_m93J02_localSeminorm_smul,
        apm_m93J02_supNorm_smul, ← mul_add, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg c)]
    · intro f hf g hg
      change apm_m93J02_globalSeminorm U α f ≠ ⊤ at hf
      change apm_m93J02_globalSeminorm U α g ≠ ⊤ at hg
      have hlocal_f : apm_m93J02_localSeminorm U α f ≠ ⊤ :=
        hglobal_local f hf
      have hlocal_g : apm_m93J02_localSeminorm U α g ≠ ⊤ :=
        hglobal_local g hg
      have hsup_f : apm_m93J02_supNorm f ≠ ⊤ :=
        apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
          hUcompact hα0 hf
      have hsup_g : apm_m93J02_supNorm g ≠ ⊤ :=
        apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
          hUcompact hα0 hg
      have hsum_f : apm_m93J02_localSeminorm U α f +
          apm_m93J02_supNorm f ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hlocal_f, hsup_f⟩
      have hsum_g : apm_m93J02_localSeminorm U α g +
          apm_m93J02_supNorm g ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hlocal_g, hsup_g⟩
      unfold apm_m93J02_localNorm
      rw [← ENNReal.toReal_add hsum_f hsum_g]
      apply ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsum_f, hsum_g⟩)
      calc
        apm_m93J02_localSeminorm U α (f + g) +
            apm_m93J02_supNorm (f + g) ≤
            (apm_m93J02_localSeminorm U α f +
              apm_m93J02_localSeminorm U α g) +
            (apm_m93J02_supNorm f + apm_m93J02_supNorm g) :=
          add_le_add
            (apm_m93J02_localSeminorm_add_le U α f g)
            (apm_m93J02_supNorm_add_le f g)
        _ = (apm_m93J02_localSeminorm U α f +
              apm_m93J02_supNorm f) +
            (apm_m93J02_localSeminorm U α g +
              apm_m93J02_supNorm g) := by
          calc
            (apm_m93J02_localSeminorm U α f +
                apm_m93J02_localSeminorm U α g) +
                (apm_m93J02_supNorm f + apm_m93J02_supNorm g) =
                apm_m93J02_localSeminorm U α f +
                  (apm_m93J02_localSeminorm U α g +
                    (apm_m93J02_supNorm f + apm_m93J02_supNorm g)) :=
              add_assoc _ _ _
            _ = apm_m93J02_localSeminorm U α f +
                (apm_m93J02_supNorm f +
                  (apm_m93J02_localSeminorm U α g +
                    apm_m93J02_supNorm g)) := by
              congr 1
              exact add_left_comm _ _ _
            _ = (apm_m93J02_localSeminorm U α f +
                  apm_m93J02_supNorm f) +
                (apm_m93J02_localSeminorm U α g +
                  apm_m93J02_supNorm g) := (add_assoc _ _ _).symm
  have hlocal_not_complete :
      ¬apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_localNorm U α) := by
    intro hcomplete
    obtain ⟨x, hx, y, hy, hxy⟩ := hUnontrivial
    let p : U := ⟨x, hx⟩
    let q : U := ⟨y, hy⟩
    have hpq : p ≠ q := by
      intro hpq
      exact hxy (congrArg Subtype.val hpq)
    letI : ConnectedSpace U :=
      isConnected_iff_connectedSpace.mp hUconnected
    have hp_near : ∀ epsilon : ℝ, 0 < epsilon → ∃ z : U,
        dist (z : Fin n → ℝ) p ≤ epsilon ∧ z ≠ p := by
      intro epsilon hepsilon
      by_contra hnone
      have hball_subset : Metric.ball p epsilon ⊆ ({p} : Set U) := by
        intro z hz
        have hzdist : dist (z : Fin n → ℝ) p ≤ epsilon := by
          simpa [Subtype.dist_eq] using hz.le
        by_contra hzp
        exact hnone ⟨z, hzdist, hzp⟩
      have hball_eq : Metric.ball p epsilon = ({p} : Set U) := by
        apply Set.Subset.antisymm hball_subset
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact Metric.mem_ball_self hepsilon
      have hopen : IsOpen ({p} : Set U) := by
        rw [← hball_eq]
        exact Metric.isOpen_ball
      have huniv : ({p} : Set U) = Set.univ :=
        (show IsClopen ({p} : Set U) from
          ⟨isClosed_singleton, hopen⟩).eq_univ (Set.singleton_nonempty p)
      have hqp : q = p := Set.mem_singleton_iff.mp <| by
        rw [huniv]
        exact Set.mem_univ q
      exact hpq hqp.symm
    let a : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
    have ha_pos (k : ℕ) : 0 < a k := by
      dsimp only [a]
      positivity
    have ha_pow_nonneg (k : ℕ) : 0 ≤ a k ^ α :=
      Real.rpow_nonneg (ha_pos k).le α
    have ha_tendsto : Filter.Tendsto a Filter.atTop (nhds 0) := by
      simpa only [a] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have ha_pow_tendsto : Filter.Tendsto (fun k ↦ a k ^ α)
        Filter.atTop (nhds 0) := by
      simpa [Real.zero_rpow hα0.ne'] using
        ha_tendsto.rpow_const (Or.inr hα0.le)
    let target : U → ℝ := fun z ↦ dist (z : Fin n → ℝ) p ^ α
    let u : ℕ → U → ℝ := fun k z ↦
      (dist (z : Fin n → ℝ) p + a k) ^ α - a k ^ α
    have hu_approx (k : ℕ) (z : U) :
        |u k z - target z| ≤ a k ^ α := by
      simpa only [u, target] using apm_m93J02_shifted_rpow_approx
        (r := dist (z : Fin n → ℝ) p) (a := a k)
        dist_nonneg (ha_pos k).le hα0.le hα1.le
    have hu_lipschitz (k : ℕ) : ∃ C : NNReal, LipschitzWith C (u k) := by
      simpa only [u] using
        apm_m93J02_lipschitzWith_shifted_rpow_dist p
          hα0 hα1 (ha_pos k)
    choose C hC using hu_lipschitz
    have hlocal_u (k : ℕ) :
        apm_m93J02_localSeminorm U α (u k) = 0 :=
      apm_m93J02_localSeminorm_eq_zero_of_lipschitzWith
        (hC k) hα1
    have hu_holder (k : ℕ) :
        u k ∈ apm_m93J02_holderFunctions U α := by
      change apm_m93J02_globalSeminorm U α (u k) ≠ ⊤
      exact hlocal_global (u k) (by simp [hlocal_u k])
    have hu_global (k : ℕ) :
        apm_m93J02_globalSeminorm U α (u k) ≠ ⊤ := by
      simpa [apm_m93J02_holderFunctions] using hu_holder k
    have hlocal_neg (g : U → ℝ) :
        apm_m93J02_localSeminorm U α (-g) =
          apm_m93J02_localSeminorm U α g := by
      simpa using apm_m93J02_localSeminorm_smul U α (-1) g
    have hlocal_diff (m k : ℕ) :
        apm_m93J02_localSeminorm U α (u m - u k) = 0 := by
      apply le_antisymm
      · calc
          apm_m93J02_localSeminorm U α (u m - u k) =
              apm_m93J02_localSeminorm U α (u m + (-u k)) := by
                rw [sub_eq_add_neg]
          _ ≤ apm_m93J02_localSeminorm U α (u m) +
                apm_m93J02_localSeminorm U α (-u k) :=
              apm_m93J02_localSeminorm_add_le U α _ _
          _ = 0 := by rw [hlocal_u m, hlocal_neg, hlocal_u k, zero_add]
      · exact bot_le
    have hsup_diff (m k : ℕ) :
        apm_m93J02_supNorm (u m - u k) ≤
          ENNReal.ofReal (a m ^ α + a k ^ α) := by
      unfold apm_m93J02_supNorm
      refine iSup_le fun z ↦ ENNReal.ofReal_le_ofReal ?_
      calc
        |(u m - u k) z| = |u m z - u k z| := by rfl
        _ ≤ |u m z - target z| + |target z - u k z| := by
          simpa [Real.dist_eq] using
            dist_triangle (u m z) (target z) (u k z)
        _ = |u m z - target z| + |u k z - target z| := by
          rw [abs_sub_comm (target z) (u k z)]
        _ ≤ a m ^ α + a k ^ α :=
          add_le_add (hu_approx m z) (hu_approx k z)
    have hu_cauchy : ∀ epsilon : ℝ, 0 < epsilon → ∃ N,
        ∀ m ≥ N, ∀ k ≥ N,
          apm_m93J02_localNorm U α (u m - u k) < epsilon := by
      intro epsilon hepsilon
      have heventually : ∀ᶠ k in Filter.atTop, a k ^ α < epsilon / 3 :=
        ha_pow_tendsto.eventually (Iio_mem_nhds (by linarith))
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
      refine ⟨N, fun m hm k hk ↦ ?_⟩
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (hsup_diff m k)
      rw [ENNReal.toReal_ofReal
        (add_nonneg (ha_pow_nonneg m) (ha_pow_nonneg k))] at hreal
      unfold apm_m93J02_localNorm
      rw [hlocal_diff, zero_add]
      exact hreal.trans_lt (by linarith [hN m hm, hN k hk])
    obtain ⟨f, hf, huf⟩ := hcomplete u hu_holder hu_cauchy
    have hf_global : apm_m93J02_globalSeminorm U α f ≠ ⊤ := by
      simpa [apm_m93J02_holderFunctions] using hf
    have hlocalNorm_apply {g : U → ℝ}
        (hg : apm_m93J02_globalSeminorm U α g ≠ ⊤) (z : U) :
        |g z| ≤ apm_m93J02_localNorm U α g := by
      have hlocal : apm_m93J02_localSeminorm U α g ≠ ⊤ :=
        hglobal_local g hg
      have hsup : apm_m93J02_supNorm g ≠ ⊤ :=
        apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
          hUcompact hα0 hg
      have hsum : apm_m93J02_localSeminorm U α g +
          apm_m93J02_supNorm g ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hlocal, hsup⟩
      have hz : ENNReal.ofReal |g z| ≤
          apm_m93J02_localSeminorm U α g + apm_m93J02_supNorm g :=
        (le_iSup (fun z : U ↦ ENNReal.ofReal |g z|) z).trans
          (le_add_of_nonneg_left bot_le)
      simpa [apm_m93J02_localNorm,
        ENNReal.toReal_ofReal (abs_nonneg (g z))] using
          ENNReal.toReal_mono hsum hz
    have hu_tendsto_f (z : U) : Filter.Tendsto (fun k ↦ u k z)
        Filter.atTop (nhds (f z)) := by
      rw [Metric.tendsto_atTop]
      intro epsilon hepsilon
      obtain ⟨N, hN⟩ := huf epsilon hepsilon
      refine ⟨N, fun k hk ↦ ?_⟩
      have hdiff : apm_m93J02_globalSeminorm U α (u k - f) ≠ ⊤ :=
        apm_m93J02_globalSeminorm_sub_ne_top U α
          (hu_global k) hf_global
      have happ := hlocalNorm_apply hdiff z
      rw [Real.dist_eq]
      have happ' : |u k z - f z| ≤
          apm_m93J02_localNorm U α (u k - f) := by
        simpa [Pi.sub_apply] using happ
      exact happ'.trans_lt (hN k hk)
    have hu_tendsto_target (z : U) : Filter.Tendsto (fun k ↦ u k z)
        Filter.atTop (nhds (target z)) := by
      rw [Metric.tendsto_atTop]
      intro epsilon hepsilon
      have heventually : ∀ᶠ k in Filter.atTop, a k ^ α < epsilon :=
        ha_pow_tendsto.eventually (Iio_mem_nhds hepsilon)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
      refine ⟨N, fun k hk ↦ ?_⟩
      rw [Real.dist_eq]
      exact (hu_approx k z).trans_lt (hN k hk)
    have hf_eq : f = target := by
      funext z
      exact tendsto_nhds_unique (hu_tendsto_f z) (hu_tendsto_target z)
    have htarget : 1 ≤ apm_m93J02_localSeminorm U α target := by
      simpa only [target] using
        apm_m93J02_one_le_localSeminorm_rpow_dist p hα0 hp_near
    have hf_one : 1 ≤ apm_m93J02_localSeminorm U α f := by
      rw [hf_eq]
      exact htarget
    obtain ⟨N, hN⟩ := huf (1 / 2) (by norm_num)
    have hdiff_global :
        apm_m93J02_globalSeminorm U α (u N - f) ≠ ⊤ :=
      apm_m93J02_globalSeminorm_sub_ne_top U α
        (hu_global N) hf_global
    have hdiff_local :
        apm_m93J02_localSeminorm U α (u N - f) ≠ ⊤ :=
      hglobal_local (u N - f) hdiff_global
    have hdiff_sup : apm_m93J02_supNorm (u N - f) ≠ ⊤ :=
      apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
        hUcompact hα0 hdiff_global
    have hfrepr : f = u N + (-(u N - f)) := by
      funext z
      simp
    have hlocal_le : apm_m93J02_localSeminorm U α f ≤
        apm_m93J02_localSeminorm U α (u N - f) := by
      calc
        apm_m93J02_localSeminorm U α f =
            apm_m93J02_localSeminorm U α (u N + (-(u N - f))) := by
              exact congrArg (apm_m93J02_localSeminorm U α) hfrepr
        _ ≤ apm_m93J02_localSeminorm U α (u N) +
              apm_m93J02_localSeminorm U α (-(u N - f)) :=
            apm_m93J02_localSeminorm_add_le U α _ _
        _ = apm_m93J02_localSeminorm U α (u N - f) := by
          rw [hlocal_u N, hlocal_neg, zero_add]
    have hone_real : 1 ≤
        (apm_m93J02_localSeminorm U α (u N - f)).toReal := by
      simpa using ENNReal.toReal_mono hdiff_local (hf_one.trans hlocal_le)
    have hsem_norm :
        (apm_m93J02_localSeminorm U α (u N - f)).toReal ≤
          apm_m93J02_localNorm U α (u N - f) := by
      unfold apm_m93J02_localNorm
      exact ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨hdiff_local, hdiff_sup⟩)
        (le_add_of_nonneg_right bot_le)
    linarith [hN N le_rfl, hone_real.trans hsem_norm]
  have hglobal_isNorm :
      apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_globalNorm U α) := by
    refine ⟨hglobalNorm_zero, ?_, ?_, ?_⟩
    · intro f hf hzero
      change apm_m93J02_globalSeminorm U α f ≠ ⊤ at hf
      have hsup : apm_m93J02_supNorm f ≠ ⊤ :=
        apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
          hUcompact hα0 hf
      exact apm_m93J02_eq_zero_of_toReal_add_eq_zero
        (ENNReal.add_ne_top.2 ⟨hf, hsup⟩) hzero
    · intro c f _
      unfold apm_m93J02_globalNorm
      rw [apm_m93J02_globalSeminorm_smul,
        apm_m93J02_supNorm_smul, ← mul_add, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg c)]
    · intro f hf g hg
      change apm_m93J02_globalSeminorm U α f ≠ ⊤ at hf
      change apm_m93J02_globalSeminorm U α g ≠ ⊤ at hg
      have hsup_f : apm_m93J02_supNorm f ≠ ⊤ :=
        apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
          hUcompact hα0 hf
      have hsup_g : apm_m93J02_supNorm g ≠ ⊤ :=
        apm_m93J02_supNorm_ne_top_of_globalSeminorm_ne_top
          hUcompact hα0 hg
      have hsum_f : apm_m93J02_globalSeminorm U α f +
          apm_m93J02_supNorm f ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hf, hsup_f⟩
      have hsum_g : apm_m93J02_globalSeminorm U α g +
          apm_m93J02_supNorm g ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hg, hsup_g⟩
      unfold apm_m93J02_globalNorm
      rw [← ENNReal.toReal_add hsum_f hsum_g]
      apply ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsum_f, hsum_g⟩)
      calc
        apm_m93J02_globalSeminorm U α (f + g) +
            apm_m93J02_supNorm (f + g) ≤
            (apm_m93J02_globalSeminorm U α f +
              apm_m93J02_globalSeminorm U α g) +
            (apm_m93J02_supNorm f + apm_m93J02_supNorm g) :=
          add_le_add
            (apm_m93J02_globalSeminorm_add_le U α f g)
            (apm_m93J02_supNorm_add_le f g)
        _ = (apm_m93J02_globalSeminorm U α f +
              apm_m93J02_supNorm f) +
            (apm_m93J02_globalSeminorm U α g +
              apm_m93J02_supNorm g) := by
          calc
            (apm_m93J02_globalSeminorm U α f +
                apm_m93J02_globalSeminorm U α g) +
                (apm_m93J02_supNorm f + apm_m93J02_supNorm g) =
                apm_m93J02_globalSeminorm U α f +
                  (apm_m93J02_globalSeminorm U α g +
                    (apm_m93J02_supNorm f + apm_m93J02_supNorm g)) :=
              add_assoc _ _ _
            _ = apm_m93J02_globalSeminorm U α f +
                (apm_m93J02_supNorm f +
                  (apm_m93J02_globalSeminorm U α g +
                    apm_m93J02_supNorm g)) := by
              congr 1
              exact add_left_comm _ _ _
            _ = (apm_m93J02_globalSeminorm U α f +
                  apm_m93J02_supNorm f) +
                (apm_m93J02_globalSeminorm U α g +
                  apm_m93J02_supNorm g) := (add_assoc _ _ _).symm
  have hglobal_complete :
      apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_globalNorm U α) := by
    intro u hu hCauchy
    have hu_global (k : ℕ) :
        apm_m93J02_globalSeminorm U α (u k) ≠ ⊤ := by
      simpa [apm_m93J02_holderFunctions] using hu k
    have hpoint_cauchy (x : U) : CauchySeq (fun k ↦ u k x) := by
      rw [Metric.cauchySeq_iff]
      intro epsilon hepsilon
      obtain ⟨N, hN⟩ := hCauchy epsilon hepsilon
      refine ⟨N, fun m hm k hk ↦ ?_⟩
      have hsub : apm_m93J02_globalSeminorm U α (u m - u k) ≠ ⊤ :=
        apm_m93J02_globalSeminorm_sub_ne_top U α
          (hu_global m) (hu_global k)
      have happ := apm_m93J02_abs_apply_le_globalNorm
        hUcompact hα0 hsub x
      rw [Real.dist_eq]
      have happ' : |u m x - u k x| ≤
          apm_m93J02_globalNorm U α (u m - u k) := by
        simpa [Pi.sub_apply] using happ
      exact happ'.trans_lt (hN m hm k hk)
    choose f hf_tendsto using fun x ↦
      cauchySeq_tendsto_of_complete (hpoint_cauchy x)
    have hlimit_bounds : ∀ eta : ℝ, 0 < eta → ∃ N, ∀ k ≥ N,
        apm_m93J02_globalSeminorm U α (u k - f) ≤ ENNReal.ofReal eta ∧
          apm_m93J02_supNorm (u k - f) ≤ ENNReal.ofReal eta := by
      intro eta heta
      obtain ⟨N, hN⟩ := hCauchy eta heta
      refine ⟨N, fun k hk ↦ ?_⟩
      have hpoint (x : U) : |(u k - f) x| ≤ eta := by
        have htend : Filter.Tendsto (fun m ↦ |u k x - u m x|)
            Filter.atTop (nhds |u k x - f x|) := by
          simpa using (tendsto_const_nhds.sub (hf_tendsto x)).abs
        apply le_of_tendsto htend
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have hsub : apm_m93J02_globalSeminorm U α (u k - u m) ≠ ⊤ :=
          apm_m93J02_globalSeminorm_sub_ne_top U α
            (hu_global k) (hu_global m)
        have happ := apm_m93J02_abs_apply_le_globalNorm
          hUcompact hα0 hsub x
        have happ' : |u k x - u m x| ≤
            apm_m93J02_globalNorm U α (u k - u m) := by
          simpa [Pi.sub_apply] using happ
        exact happ'.trans (hN k hk m hm).le
      have hquotient (y z : U) :
          |(u k - f) z - (u k - f) y| /
              dist (z : Fin n → ℝ) y ^ α ≤ eta := by
        have hz : Filter.Tendsto (fun m ↦ u k z - u m z)
            Filter.atTop (nhds (u k z - f z)) :=
          tendsto_const_nhds.sub (hf_tendsto z)
        have hy : Filter.Tendsto (fun m ↦ u k y - u m y)
            Filter.atTop (nhds (u k y - f y)) :=
          tendsto_const_nhds.sub (hf_tendsto y)
        have htend : Filter.Tendsto
            (fun m ↦ |(u k z - u m z) - (u k y - u m y)| /
              dist (z : Fin n → ℝ) y ^ α)
            Filter.atTop
            (nhds (|(u k z - f z) - (u k y - f y)| /
              dist (z : Fin n → ℝ) y ^ α)) := by
          simpa using (hz.sub hy).abs.div_const
            (dist (z : Fin n → ℝ) y ^ α)
        have hle : |(u k z - f z) - (u k y - f y)| /
            dist (z : Fin n → ℝ) y ^ α ≤ eta := by
          apply le_of_tendsto htend
          filter_upwards [Filter.eventually_ge_atTop N] with m hm
          have hsub : apm_m93J02_globalSeminorm U α (u k - u m) ≠ ⊤ :=
            apm_m93J02_globalSeminorm_sub_ne_top U α
              (hu_global k) (hu_global m)
          have hq := apm_m93J02_quotient_real_le_globalNorm
            hUcompact hα0 hsub y z
          have hq' : |(u k z - u m z) - (u k y - u m y)| /
              dist (z : Fin n → ℝ) y ^ α ≤
                apm_m93J02_globalNorm U α (u k - u m) := by
            simpa [Pi.sub_apply] using hq
          exact hq'.trans (hN k hk m hm).le
        simpa [Pi.sub_apply] using hle
      constructor
      · unfold apm_m93J02_globalSeminorm
        refine iSup_le fun y ↦ iSup_le fun z ↦ ?_
        by_cases hyz : z ≠ y
        · rw [if_pos hyz]
          unfold apm_m93J02_quotient
          exact ENNReal.ofReal_le_ofReal (hquotient y z)
        · simp [hyz]
      · unfold apm_m93J02_supNorm
        refine iSup_le fun x ↦ ENNReal.ofReal_le_ofReal (hpoint x)
    have hf_global : apm_m93J02_globalSeminorm U α f ≠ ⊤ := by
      obtain ⟨N, hN⟩ := hlimit_bounds 1 zero_lt_one
      have hdiff : apm_m93J02_globalSeminorm U α (u N - f) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN N le_rfl).1
      have hrepr : f = u N - (u N - f) := by
        funext x
        simp
      rw [hrepr]
      exact apm_m93J02_globalSeminorm_sub_ne_top U α
        (hu_global N) hdiff
    refine ⟨f, ?_, ?_⟩
    · simpa [apm_m93J02_holderFunctions] using hf_global
    · intro epsilon hepsilon
      obtain ⟨N, hN⟩ := hlimit_bounds (epsilon / 3) (div_pos hepsilon (by norm_num))
      refine ⟨N, fun k hk ↦ ?_⟩
      have hbounds := hN k hk
      have hupper : ENNReal.ofReal (epsilon / 3) +
          ENNReal.ofReal (epsilon / 3) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
      have hsum : apm_m93J02_globalSeminorm U α (u k - f) +
          apm_m93J02_supNorm (u k - f) ≤
            ENNReal.ofReal (epsilon / 3) + ENNReal.ofReal (epsilon / 3) :=
        add_le_add hbounds.1 hbounds.2
      have hreal := ENNReal.toReal_mono hupper hsum
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (le_of_lt (div_pos hepsilon (by norm_num)))] at hreal
      unfold apm_m93J02_globalNorm
      exact hreal.trans_lt (by linarith)
  have hremaining :
      (∀ f : U → ℝ,
        apm_m93J02_localSeminorm U α f ≠ ⊤ →
          apm_m93J02_globalSeminorm U α f ≠ ⊤) ∧
      ¬(∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ f : U → ℝ,
        apm_m93J02_globalSeminorm U α f ≤
          K * apm_m93J02_localSeminorm U α f) ∧
      apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_localNorm U α) ∧
      ¬apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_localNorm U α) ∧
      apm_m93J02_isNormOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_globalNorm U α) ∧
      apm_m93J02_isCompleteOn (apm_m93J02_holderFunctions U α)
        (apm_m93J02_globalNorm U α) :=
    ⟨hlocal_global, hno_uniform_bound, hlocal_isNorm,
      hlocal_not_complete, hglobal_isNorm, hglobal_complete⟩
  exact ⟨hremaining.1, hglobal_local, hle,
    hremaining.2.1, hremaining.2.2.1, hremaining.2.2.2.1,
    hremaining.2.2.2.2.1, hremaining.2.2.2.2.2⟩
