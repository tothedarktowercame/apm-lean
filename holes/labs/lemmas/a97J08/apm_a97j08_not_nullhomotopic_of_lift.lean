import Mathlib
import ConstructionTargets.Rouche
import ConstructionTargets.CircleHomology
import ConstructionTargets.SingularHomologyHomotopy

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

open CategoryTheory Filter Metric Set
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

lemma apm_a97j08_curveInterior_subset_compl (γ : ℝ → ℂ) :
    apm_a97j08_curveInterior γ ⊆ (apm_a97j08_curveImage γ)ᶜ := by
  intro z hz
  exact hz.1

/-- The encoded union of bounded complement components is open.  This uses
only compactness of the curve image and local connectedness of `ℂ`, not the
Jordan separation theorem. -/
lemma apm_a97j08_curveInterior_isOpen {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    IsOpen (apm_a97j08_curveInterior γ) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  let V := (apm_a97j08_curveImage γ)ᶜ
  have hV : IsOpen V := (apm_a97j08_curveImage_compact hγ_cont).isClosed.isOpen_compl
  have hzV : z ∈ V := hz.1
  have hopen : IsOpen (connectedComponentIn V z) := hV.connectedComponentIn
  have hzmem : z ∈ connectedComponentIn V z := mem_connectedComponentIn hzV
  apply _root_.mem_nhds_iff.mpr
  refine ⟨connectedComponentIn V z, ?_, hopen, hzmem⟩
  intro w hw
  have hwV : w ∈ V := connectedComponentIn_subset V z hw
  refine ⟨hwV, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

/-- Every frontier point of the selected bounded components lies on the
curve.  Off the curve, the open complement component is either wholly
selected or wholly rejected, so no such point can be a frontier point. -/
lemma apm_a97j08_frontier_curveInterior_subset_curveImage {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    frontier (apm_a97j08_curveInterior γ) ⊆ apm_a97j08_curveImage γ := by
  intro z hz
  have hznotint : z ∉ interior (apm_a97j08_curveInterior γ) := hz.2
  by_contra hzcurve
  let V := (apm_a97j08_curveImage γ)ᶜ
  let S := connectedComponentIn V z
  have hzV : z ∈ V := hzcurve
  have hzS : z ∈ S := mem_connectedComponentIn hzV
  have hSopen : IsOpen S :=
    (apm_a97j08_curveImage_compact hγ_cont).isClosed.isOpen_compl.connectedComponentIn
  by_cases hSb : Bornology.IsBounded S
  · have hzU : z ∈ apm_a97j08_curveInterior γ := ⟨hzV, hSb⟩
    have hzint : z ∈ interior (apm_a97j08_curveInterior γ) := by
      rw [(apm_a97j08_curveInterior_isOpen hγ_cont).interior_eq]
      exact hzU
    exact hznotint hzint
  · obtain ⟨w, hwS, hwU⟩ :=
      (_root_.mem_closure_iff.mp (frontier_subset_closure hz)) S hSopen hzS
    have heq : S = connectedComponentIn V w := connectedComponentIn_eq hwS
    apply hSb
    rw [heq]
    exact hwU.2

/-- Consequently the closure adds no points except curve points. -/
lemma apm_a97j08_closure_curveInterior_subset_union_curveImage {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    closure (apm_a97j08_curveInterior γ) ⊆
      apm_a97j08_curveInterior γ ∪ apm_a97j08_curveImage γ := by
  rw [closure_eq_self_union_frontier]
  exact union_subset_union_right _
    (apm_a97j08_frontier_curveInterior_subset_curveImage hγ_cont)

/-- In the proper metric space `ℂ`, global boundedness of the encoded
interior is exactly the remaining input needed for compactness of its closure. -/
lemma apm_a97j08_curveInterior_isCompact_closure_of_isBounded {γ : ℝ → ℂ}
    (hU : Bornology.IsBounded (apm_a97j08_curveInterior γ)) :
    IsCompact (closure (apm_a97j08_curveInterior γ)) :=
  hU.isCompact_closure

/-- For any bounded obstacle in the complex plane, the union of its bounded
complement components is bounded.  This is the elementary ``ray to infinity''
part of Jordan separation and does not require simplicity of the curve. -/
lemma apm_a97j08_curveInterior_isBounded {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    Bornology.IsBounded (apm_a97j08_curveInterior γ) := by
  have hK : Bornology.IsBounded (apm_a97j08_curveImage γ) :=
    (apm_a97j08_curveImage_compact hγ_cont).isBounded
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : ℂ)
  have hR0 : 0 ≤ R := by
    have hγ0 : γ 0 ∈ apm_a97j08_curveImage γ := ⟨0, by simp, rfl⟩
    have hγ0R : ‖γ 0‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hγ0
    exact (norm_nonneg (γ 0)).trans hγ0R
  apply Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.2
  refine ⟨R, fun z hz ↦ ?_⟩
  by_contra hzR
  have hRz : R < ‖z‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hzR
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    have : R < 0 := by simpa using hRz
    exact (not_lt_of_ge hR0 this).elim
  let ray : Set ℂ := (fun t : ℝ ↦ (t : ℂ) * z) '' Ici 1
  have hzray : z ∈ ray := by
    refine ⟨1, self_mem_Ici, ?_⟩
    simp
  have hray_pre : IsPreconnected ray := by
    exact isPreconnected_Ici.image _
      (Complex.continuous_ofReal.comp continuous_id |>.mul continuous_const).continuousOn
  have hray_compl : ray ⊆ (apm_a97j08_curveImage γ)ᶜ := by
    rintro w ⟨t, ht, rfl⟩ hwK
    have ht' : 1 ≤ t := ht
    have hwR := hR hwK
    have htz : ‖z‖ ≤ ‖(t : ℂ) * z‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (zero_le_one.trans ht')]
      exact le_mul_of_one_le_left (norm_nonneg z) ht'
    have : ‖t • z‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hwR
    exact (not_le_of_gt hRz) (htz.trans this)
  have hray_component : ray ⊆
      connectedComponentIn (apm_a97j08_curveImage γ)ᶜ z :=
    hray_pre.subset_connectedComponentIn hzray hray_compl
  obtain ⟨C, hC⟩ := hz.2.exists_norm_le
  let t : ℝ := (C + 1) / ‖z‖
  have hzC : ‖z‖ ≤ C := hC z (hray_component hzray)
  have hC0 : 0 ≤ C := (norm_nonneg z).trans hzC
  have ht1 : 1 ≤ t := by
    dsimp [t]
    rw [le_div_iff₀ (norm_pos_iff.mpr hz0)]
    linarith
  have htzmem : (t : ℂ) * z ∈ connectedComponentIn
      (apm_a97j08_curveImage γ)ᶜ z :=
    hray_component ⟨t, ht1, rfl⟩
  have hfinal := hC ((t : ℂ) * z) htzmem
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans ht1)] at hfinal
  rw [show t * ‖z‖ = C + 1 by
    dsimp [t]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz0)] at hfinal
  linarith

/-- A general containment bridge: if the complement of the ambient domain is
one unbounded connected set, then no bounded component of the curve
complement can meet it.  The unavailable planar-topology step is precisely
deriving these two complement properties from `IsSimplyConnected D`. -/
lemma apm_a97j08_curveInterior_subset_of_compl_preconnected_unbounded
    {D : Set ℂ} {γ : ℝ → ℂ}
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hDc_conn : IsPreconnected Dᶜ)
    (hDc_unbounded : ¬ Bornology.IsBounded Dᶜ) :
    apm_a97j08_curveInterior γ ⊆ D := by
  intro z hz
  by_contra hzD
  have hzDc : z ∈ Dᶜ := hzD
  have hDcKc : Dᶜ ⊆ (apm_a97j08_curveImage γ)ᶜ := by
    exact compl_subset_compl.mpr hγD
  have hDc_component : Dᶜ ⊆
      connectedComponentIn (apm_a97j08_curveImage γ)ᶜ z :=
    hDc_conn.subset_connectedComponentIn hzDc hDcKc
  exact hDc_unbounded (hz.2.subset hDc_component)

lemma apm_a97j08_curveInterior_isCompact_closure {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    IsCompact (closure (apm_a97j08_curveInterior γ)) :=
  (apm_a97j08_curveInterior_isBounded hγ_cont).isCompact_closure

/-- Interior containment and the registered curve containment together imply
the closure-level containment consumed by the analytic part. -/
lemma apm_a97j08_closure_curveInterior_subset
    {D : Set ℂ} {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : apm_a97j08_curveInterior γ ⊆ D)
    (hγD : apm_a97j08_curveImage γ ⊆ D) :
    closure (apm_a97j08_curveInterior γ) ⊆ D :=
  (apm_a97j08_closure_curveInterior_subset_union_curveImage hγ_cont).trans
    (union_subset hUD hγD)

/-- Closure-level version of the complement criterion, matching the sole
topological input consumed by the completed analytic theorem. -/
lemma apm_a97j08_closure_curveInterior_subset_of_compl_preconnected_unbounded
    {D : Set ℂ} {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hDc_conn : IsPreconnected Dᶜ)
    (hDc_unbounded : ¬ Bornology.IsBounded Dᶜ) :
    closure (apm_a97j08_curveInterior γ) ⊆ D :=
  apm_a97j08_closure_curveInterior_subset hγ_cont
    (apm_a97j08_curveInterior_subset_of_compl_preconnected_unbounded
      hγD hDc_conn hDc_unbounded) hγD

/-- Exact componentwise planar criterion: every curve-complement component
which meets the ambient complement escapes to infinity.  Unlike requiring
`Dᶜ` itself to be preconnected, this criterion also covers simply connected
domains such as strips, whose planar complement is disconnected. -/
lemma apm_a97j08_closure_curveInterior_subset_of_exterior_components_unbounded
    {D : Set ℂ} {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hescape : ∀ z ∈ Dᶜ,
      ¬ Bornology.IsBounded
        (connectedComponentIn (apm_a97j08_curveImage γ)ᶜ z)) :
    closure (apm_a97j08_curveInterior γ) ⊆ D := by
  apply apm_a97j08_closure_curveInterior_subset hγ_cont ?_ hγD
  intro z hz
  by_contra hzD
  exact hescape z hzD hz.2

/-- The exact ambient-domain seam: if every component of `Dᶜ` is unbounded,
then no such component can lie in a bounded component of the curve
complement.  The missing classical plane theorem is precisely that simple
connectivity of an open domain implies this hypothesis. -/
lemma apm_a97j08_closure_curveInterior_subset_of_compl_components_unbounded
    {D : Set ℂ} {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hDescape : ∀ z ∈ Dᶜ,
      ¬ Bornology.IsBounded (connectedComponentIn Dᶜ z)) :
    closure (apm_a97j08_curveInterior γ) ⊆ D := by
  apply apm_a97j08_closure_curveInterior_subset_of_exterior_components_unbounded
    hγ_cont hγD
  intro z hzD hbounded
  apply hDescape z hzD
  apply hbounded.subset
  exact connectedComponentIn_mono z (compl_subset_compl.mpr hγD)

/-- Simple connectivity supplies the concrete nullhomotopy of the frozen
parametrized loop inside `D`.  Closing the planar gap now amounts to the
missing Jordan fact that such a filling prevents bounded components of
`Dᶜ`. -/
lemma apm_a97j08_exists_nullhomotopy_in_simplyConnected
    {D : Set ℂ} {γ : ℝ → ℂ}
    (hD_simplyConnected : IsSimplyConnected D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_closed : γ 0 = γ 1)
    (hγD : apm_a97j08_curveImage γ ⊆ D) :
    ∃ H : (Path.ofLine hγ_cont rfl hγ_closed.symm).Homotopy
        (Path.refl (γ 0)),
      ∀ t, H t ∈ D := by
  apply (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
    hD_simplyConnected).2 (γ 0)
    (Path.ofLine hγ_cont rfl hγ_closed.symm)
  intro t
  apply hγD
  exact Path.ofLine_mem hγ_cont rfl hγ_closed.symm t

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

/-- Once the encoded closed interior is placed in `D`, local uniform
convergence becomes uniform convergence on that compact closure. -/
lemma apm_a97j08_tendstoUniformlyOn_curveInterior_closure
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D) :
    TendstoUniformlyOn F g atTop
      (closure (apm_a97j08_curveInterior γ)) := by
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).mp hF_tendsto
    _ hUD (apm_a97j08_curveInterior_isCompact_closure hγ_cont)

/-- Quantitative sup-norm form used simultaneously by every zero disk and
the zero-free compact remainder. -/
lemma apm_a97j08_eventually_norm_sub_lt_on_curveInterior_closure
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z ∈ closure (apm_a97j08_curveInterior γ),
      ‖F n z - g z‖ < ε := by
  have h := tendstoUniformlyOn_iff.mp
    (apm_a97j08_tendstoUniformlyOn_curveInterior_closure
      hD_open hγ_cont hUD hF_tendsto) ε hε
  filter_upwards [h] with n hn
  intro z hz
  simpa [dist_eq_norm, norm_sub_rev] using hn z hz

/-- A reusable positive norm margin on any nonempty compact zero-free set. -/
lemma apm_a97j08_exists_compact_norm_margin
    {K : Set ℂ} {g : ℂ → ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hg_cont : ContinuousOn g K) (hg_ne : ∀ z ∈ K, g z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ε ≤ ‖g z‖ := by
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hKne hg_cont.norm
  exact ⟨‖g z‖, norm_pos_iff.mpr (hg_ne z hz), hmin⟩

lemma apm_a97j08_ne_zero_of_norm_sub_lt_norm {a b : ℂ}
    (h : ‖a - b‖ < ‖b‖) : a ≠ 0 := by
  intro ha
  subst a
  simp only [zero_sub, norm_neg] at h
  exact (lt_irrefl _ h)

/-- Uniform convergence on the closed interior eventually preserves
nonvanishing on any compact zero-free subset. -/
lemma apm_a97j08_eventually_ne_zero_on_compact_subset
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {K : Set ℂ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hKsub : K ⊆ closure (apm_a97j08_curveInterior γ))
    (hg_cont : ContinuousOn g K) (hg_ne : ∀ z ∈ K, g z ≠ 0) :
    ∀ᶠ n in atTop, ∀ z ∈ K, F n z ≠ 0 := by
  obtain ⟨ε, hε, hεg⟩ :=
    apm_a97j08_exists_compact_norm_margin hK hKne hg_cont hg_ne
  filter_upwards [apm_a97j08_eventually_norm_sub_lt_on_curveInterior_closure
    hD_open hγ_cont hUD hF_tendsto hε] with n hn
  intro z hz
  apply apm_a97j08_ne_zero_of_norm_sub_lt_norm
  exact lt_of_lt_of_le (hn z (hKsub hz)) (hεg z hz)

/-- Consumer-side reduction of the frozen Hurwitz statement to an
arbitrary-Jordan Rouché transfer theorem.  This records the exact interface
needed from the missing argument-principle/Jordan-curve infrastructure: once
that transfer is available, the existing compact-boundary estimate and
Weierstrass theorem close the eventual zero-count equality directly. -/
lemma apm_a97j08_of_jordan_rouche_transfer
    (D : Set ℂ) (γ : ℝ → ℂ) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_closed : γ 0 = γ 1)
    (hγ_simple : Set.InjOn γ (Ico (0 : ℝ) 1))
    (hγ_rectifiable : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0)
    (hrouche : ∀ (f g : ℂ → ℂ),
      IsOpen D → IsSimplyConnected D →
      ContinuousOn γ (Icc (0 : ℝ) 1) → γ 0 = γ 1 →
      Set.InjOn γ (Ico (0 : ℝ) 1) →
      BoundedVariationOn γ (Icc (0 : ℝ) 1) →
      apm_a97j08_curveImage γ ⊆ D →
      DifferentiableOn ℂ f D → DifferentiableOn ℂ g D →
      (∀ z ∈ apm_a97j08_curveImage γ, ‖f z - g z‖ < ‖g z‖) →
      apm_a97j08_zeroCount f (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ)) :
    ∃ N : ℕ, ∀ n ≥ N,
      apm_a97j08_zeroCount (F n) (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  have hg_analytic : DifferentiableOn ℂ g D :=
    apm_a97j08_limit_differentiableOn hD_open hF_analytic hF_tendsto
  obtain ⟨N, hN⟩ := apm_a97j08_eventually_boundary_rouche
    hD_open hγ_cont hγD hF_analytic hF_tendsto hg_ne
  refine ⟨N, fun n hn ↦ ?_⟩
  exact hrouche (F n) g hD_open hD_simplyConnected hγ_cont hγ_closed
    hγ_simple hγ_rectifiable hγD (hF_analytic n) hg_analytic (hN n hn)

/-- The frozen zero-count encoding vanishes definitionally when the function
is not meromorphic on the whole counting domain.  This is the fallback branch
that follows from Mathlib's totalized `MeromorphicOn.divisor`. -/
lemma apm_a97j08_zeroCount_eq_zero_of_not_meromorphicOn
    {f : ℂ → ℂ} {U : Set ℂ} (hf : ¬ MeromorphicOn f U) :
    apm_a97j08_zeroCount f U = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  simp [MeromorphicOn.divisor_def, hf]

/-- Analyticity on the ambient open set transports to the encoded interior
once the independent Jordan-containment obligation has been discharged. -/
lemma apm_a97j08_analyticOnNhd_curveInterior
    {D : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ}
    (hD_open : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hUD : apm_a97j08_curveInterior γ ⊆ D) :
    AnalyticOnNhd ℂ f (apm_a97j08_curveInterior γ) := by
  exact (hf.analyticOnNhd hD_open).mono hUD

/-- The closure-level form needed by an argument principle: ambient
holomorphy restricts to a neighborhood of the closed counting domain. -/
lemma apm_a97j08_analyticOnNhd_curveInterior_closure
    {D : Set ℂ} {γ : ℝ → ℂ} {f : ℂ → ℂ}
    (hD_open : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D) :
    AnalyticOnNhd ℂ f (closure (apm_a97j08_curveInterior γ)) := by
  exact (hf.analyticOnNhd hD_open).mono hUD

lemma apm_a97j08_add_smul_ne_zero_of_norm_le_one
    {a b t : ℂ} (ht : ‖t‖ ≤ 1) (hab : ‖b‖ < ‖a‖) :
    a + t * b ≠ 0 := by
  intro hzero
  have ha : a = -(t * b) := eq_neg_of_add_eq_zero_left hzero
  have hle : ‖a‖ ≤ ‖b‖ := by
    rw [ha, norm_neg, norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ht (norm_nonneg b)
  exact (not_lt_of_ge hle) hab

/-- The circle-independent elementary half of Rouché: along the straight
homotopy from `g` to `f`, every member is analytic near the closed interior
and nonzero on the parametrized boundary. -/
lemma apm_a97j08_rouche_homotopy_analytic_and_boundary_ne
    {γ : ℝ → ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closure (apm_a97j08_curveInterior γ)))
    (hg : AnalyticOnNhd ℂ g (closure (apm_a97j08_curveInterior γ)))
    (hfg : ∀ z ∈ apm_a97j08_curveImage γ, ‖f z - g z‖ < ‖g z‖)
    (t : Set.Icc (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (fun z ↦ g z + (t.1 : ℂ) * (f z - g z))
        (closure (apm_a97j08_curveInterior γ)) ∧
      ∀ z ∈ apm_a97j08_curveImage γ,
        g z + (t.1 : ℂ) * (f z - g z) ≠ 0 := by
  constructor
  · exact hg.add (analyticOnNhd_const.mul (hf.sub hg))
  · intro z hz
    apply apm_a97j08_add_smul_ne_zero_of_norm_le_one
    · simpa [abs_of_nonneg t.2.1] using t.2.2
    · exact hfg z hz

/-- Endpoint bookkeeping for the remaining homotopy-invariance theorem. -/
lemma apm_a97j08_zeroCount_eq_of_rouche_homotopy_invariant
    {γ : ℝ → ℂ} {f g : ℂ → ℂ}
    (hinv : ∀ t : Set.Icc (0 : ℝ) 1,
      apm_a97j08_zeroCount
          (fun z ↦ g z + (t.1 : ℂ) * (f z - g z))
          (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ)) :
    apm_a97j08_zeroCount f (apm_a97j08_curveInterior γ) =
      apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  have h := hinv (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1)
  have heq : (fun z ↦ g z +
      (((⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1).1 : ℂ) * (f z - g z))) = f := by
    funext z
    norm_num
  rw [heq] at h
  exact h

/-- An integer-valued zero count that varies continuously along the Rouché
homotopy is constant, because the parameter interval is preconnected and
`ℤ` is discrete.  Thus the only missing analytic input is continuity of this
count (normally supplied by the argument principle). -/
lemma apm_a97j08_zeroCount_eq_of_continuous_rouche_count
    {γ : ℝ → ℂ} {f g : ℂ → ℂ}
    (hcont : Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
      apm_a97j08_zeroCount
        (fun z ↦ g z + (t.1 : ℂ) * (f z - g z))
        (apm_a97j08_curveInterior γ))) :
    apm_a97j08_zeroCount f (apm_a97j08_curveInterior γ) =
      apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  let N : Set.Icc (0 : ℝ) 1 → ℤ := fun t ↦
    apm_a97j08_zeroCount
      (fun z ↦ g z + (t.1 : ℂ) * (f z - g z))
      (apm_a97j08_curveInterior γ)
  have hN : Continuous N := hcont
  have hconst : ∀ t, N t = N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
    intro t
    exact PreconnectedSpace.constant (by infer_instance) hN
  apply apm_a97j08_zeroCount_eq_of_rouche_homotopy_invariant
  intro t
  change N t = _
  rw [hconst t]
  change apm_a97j08_zeroCount
      (fun z ↦ g z + (((⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1).1 : ℂ) *
        (f z - g z))) (apm_a97j08_curveInterior γ) = _
  norm_num

/-- A continuous complex certificate for an integer-valued quantity makes
that quantity constant when every certificate value is a fixed nonzero
complex period times the integer.  This is the abstract lattice argument
behind the disk argument principle and does not depend on a circle. -/
lemma apm_a97j08_int_eq_of_continuous_period_certificate
    (N : Set.Icc (0 : ℝ) 1 → ℤ) (H : Set.Icc (0 : ℝ) 1 → ℂ) (C : ℂ)
    (hC : C ≠ 0) (hH : Continuous H)
    (hHN : ∀ t, H t = (N t : ℂ) * C) :
    N (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) =
      N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
  let K : Set.Icc (0 : ℝ) 1 → AddSubgroup.zmultiples C := fun t ↦
    ⟨H t, by
      rw [hHN t]
      exact ⟨N t, by dsimp; rw [zsmul_eq_mul]⟩⟩
  have hK : Continuous K := Continuous.subtype_mk hH _
  have hconst : K (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) =
      K (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) :=
    PreconnectedSpace.constant (by infer_instance) hK
  have hmul :
      (N (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) * C =
        (N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) * C := by
    rw [← hHN, ← hHN]
    exact congrArg Subtype.val hconst
  have hcast :
      (N (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) =
        (N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) :=
    mul_right_cancel₀ hC hmul
  exact_mod_cast hcast

/-- Rouché transfer from an arbitrary-curve argument-principle certificate.
The certificate construction and identity are now the sole analytic seam. -/
lemma apm_a97j08_zeroCount_eq_of_rouche_period_certificate
    {γ : ℝ → ℂ} {f g : ℂ → ℂ}
    (H : Set.Icc (0 : ℝ) 1 → ℂ) (C : ℂ)
    (hC : C ≠ 0) (hH : Continuous H)
    (hHN : ∀ t, H t =
      (apm_a97j08_zeroCount
        (fun z ↦ g z + (t.1 : ℂ) * (f z - g z))
        (apm_a97j08_curveInterior γ) : ℂ) * C) :
    apm_a97j08_zeroCount f (apm_a97j08_curveInterior γ) =
      apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  let N : Set.Icc (0 : ℝ) 1 → ℤ := fun t ↦
    apm_a97j08_zeroCount
      (fun z ↦ g z + (t.1 : ℂ) * (f z - g z))
      (apm_a97j08_curveInterior γ)
  have hend := apm_a97j08_int_eq_of_continuous_period_certificate
    N H C hC hH hHN
  have hf_end : N (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) =
      apm_a97j08_zeroCount f (apm_a97j08_curveInterior γ) := by
    change apm_a97j08_zeroCount
      (fun z ↦ g z + (((⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1).1 : ℂ) *
        (f z - g z))) (apm_a97j08_curveInterior γ) = _
    congr 1
    funext z
    norm_num
  have hg_end : N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) =
      apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
    change apm_a97j08_zeroCount
      (fun z ↦ g z + (((⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1).1 : ℂ) *
        (f z - g z))) (apm_a97j08_curveInterior γ) = _
    congr 1
    funext z
    norm_num
  rwa [hf_end, hg_end] at hend

/-- Analyticity on a compact closure makes the divisor support in the open
counting set finite: it is the restriction of the finite divisor on the
closure. -/
lemma apm_a97j08_divisor_support_finite_of_compact_closure
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsCompact (closure U))
    (hf : AnalyticOnNhd ℂ f (closure U)) :
    (MeromorphicOn.divisor f U).support.Finite := by
  have hm : MeromorphicOn f (closure U) := hf.meromorphicOn
  have hfin : (MeromorphicOn.divisor f (closure U)).support.Finite :=
    (MeromorphicOn.divisor f (closure U)).finiteSupport hU
  apply hfin.subset
  intro z hz
  have hzU : z ∈ U :=
    (MeromorphicOn.divisor f U).supportWithinDomain hz
  have hrestrict :
      (MeromorphicOn.divisor f (closure U)).restrict subset_closure =
        MeromorphicOn.divisor f U :=
    MeromorphicOn.divisor_restrict hm subset_closure
  have heq : MeromorphicOn.divisor f (closure U) z =
      MeromorphicOn.divisor f U z := by
    have hpoint := congrArg
      (fun D : Function.locallyFinsuppWithin U ℤ ↦ D z) hrestrict
    simpa [Function.locallyFinsuppWithin.restrict_apply, hzU] using hpoint
  exact Function.mem_support.mpr (heq.trans_ne (Function.mem_support.mp hz))

/-- The positive part used by the frozen zero count also has finite support
on a compact analytic closure. -/
lemma apm_a97j08_positive_divisor_support_finite
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsCompact (closure U))
    (hf : AnalyticOnNhd ℂ f (closure U)) :
    (Function.support fun z ↦ max (MeromorphicOn.divisor f U z) 0).Finite := by
  apply (apm_a97j08_divisor_support_finite_of_compact_closure hU hf).subset
  intro z hz
  apply Function.mem_support.mpr
  intro hzero
  apply Function.mem_support.mp hz
  simp [hzero]

/-- Casting the frozen integer zero count commutes with its now-certified
finite sum.  This is the algebraic side of the desired argument-principle
certificate identity. -/
lemma apm_a97j08_intCast_zeroCount_of_compact_closure
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsCompact (closure U))
    (hf : AnalyticOnNhd ℂ f (closure U)) :
    (apm_a97j08_zeroCount f U : ℂ) =
      ∑ᶠ z, ((max (MeromorphicOn.divisor f U z) 0 : ℤ) : ℂ) := by
  unfold apm_a97j08_zeroCount
  exact (Int.castAddHom ℂ).map_finsum
    (apm_a97j08_positive_divisor_support_finite hU hf)

/-- For an analytic function the frozen positive-part count is just the
ordinary divisor sum, since analytic divisors have no negative values. -/
lemma apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f (closure U)) :
    apm_a97j08_zeroCount f U =
      ∑ᶠ z, MeromorphicOn.divisor f U z := by
  unfold apm_a97j08_zeroCount
  apply finsum_congr
  intro z
  exact max_eq_left
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.mono subset_closure) z)

/-- Closure compactness and analyticity identify the complex cast of the
frozen count with the cast of the ordinary finite divisor sum, matching the
standard argument-principle right-hand side. -/
lemma apm_a97j08_intCast_zeroCount_eq_divisor_sum
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsCompact (closure U))
    (hf : AnalyticOnNhd ℂ f (closure U)) :
    (apm_a97j08_zeroCount f U : ℂ) =
      ∑ᶠ z, (MeromorphicOn.divisor f U z : ℂ) := by
  rw [apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic hf]
  exact (Int.castAddHom ℂ).map_finsum
    (apm_a97j08_divisor_support_finite_of_compact_closure hU hf)

/-- A finite subset of an open metric set admits one positive closed-ball
radius valid at every point. -/
lemma apm_a97j08_exists_uniform_closedBall_subset_of_finite
    {S U : Set ℂ} (hS : S.Finite) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ S, closedBall z r ⊆ U := by
  obtain ⟨r, hr, hrsub⟩ := hS.isCompact.exists_cthickening_subset_open hU hSU
  refine ⟨r, hr, fun z hz ↦ ?_⟩
  exact (closedBall_subset_cthickening hz r).trans hrsub

/-- Applied to an analytic function, all divisor-support points in the
encoded interior have a common positive disk radius staying inside it. -/
lemma apm_a97j08_exists_zeroSupport_closedBall_radius
    {γ : ℝ → ℂ} {g : ℂ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hg : AnalyticOnNhd ℂ g (closure (apm_a97j08_curveInterior γ))) :
    ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ (MeromorphicOn.divisor g (apm_a97j08_curveInterior γ)).support,
        closedBall z r ⊆ apm_a97j08_curveInterior γ := by
  apply apm_a97j08_exists_uniform_closedBall_subset_of_finite
    (apm_a97j08_divisor_support_finite_of_compact_closure
      (apm_a97j08_curveInterior_isCompact_closure hγ_cont) hg)
    (apm_a97j08_curveInterior_isOpen hγ_cont)
  exact (MeromorphicOn.divisor g (apm_a97j08_curveInterior γ)).supportWithinDomain

/-- A uniform strict separation estimate makes the corresponding closed
balls pairwise disjoint. -/
lemma apm_a97j08_pairwiseDisjoint_closedBall_of_separated
    {S : Set ℂ} {r : ℝ}
    (hsep : S.Pairwise fun x y ↦ 2 * r < dist x y) :
    S.PairwiseDisjoint fun z ↦ closedBall z r := by
  intro x hx y hy hxy
  apply closedBall_disjoint_closedBall
  simpa [two_mul] using hsep hx hy hxy

/-- Distinct points of a finite metric set have a uniform positive
separation.  The empty and singleton cases are handled by the vacuous
pairwise condition. -/
lemma apm_a97j08_exists_uniform_separation_of_finite
    {S : Set ℂ} (hS : S.Finite) :
    ∃ r : ℝ, 0 < r ∧ S.Pairwise fun x y ↦ 2 * r < dist x y := by
  classical
  let P : Set (ℂ × ℂ) :=
    {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2}
  have hP_finite : P.Finite := by
    apply (hS.prod hS).subset
    rintro p ⟨hp₁, hp₂, -⟩
    exact ⟨hp₁, hp₂⟩
  by_cases hP : P.Nonempty
  · obtain ⟨p, hp⟩ := hP_finite.exists_minimalFor
      (fun q : ℂ × ℂ ↦ dist q.1 q.2) P hP
    have hpP : p ∈ P := hp.1
    have hpdist : 0 < dist p.1 p.2 := dist_pos.mpr hpP.2.2
    refine ⟨dist p.1 p.2 / 3, by positivity, ?_⟩
    intro x hx y hy hxy
    have hxyP : (x, y) ∈ P := ⟨hx, hy, hxy⟩
    have hle : dist p.1 p.2 ≤ dist x y :=
      le_of_not_gt (hp.not_lt hxyP)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx y hy hxy
    exact False.elim (hP ⟨(x, y), hx, hy, hxy⟩)

/-- A finite subset of an open metric set admits a common positive radius
whose centered closed balls stay in the open set and are pairwise disjoint. -/
lemma apm_a97j08_exists_pairwiseDisjoint_closedBall_subset_of_finite
    {S U : Set ℂ} (hS : S.Finite) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ S, closedBall z r ⊆ U) ∧
      S.PairwiseDisjoint fun z ↦ closedBall z r := by
  obtain ⟨r₀, hr₀, hr₀U⟩ :=
    apm_a97j08_exists_uniform_closedBall_subset_of_finite hS hU hSU
  obtain ⟨r₁, hr₁, hr₁sep⟩ :=
    apm_a97j08_exists_uniform_separation_of_finite hS
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_, ?_⟩
  · intro z hz
    exact (closedBall_subset_closedBall (min_le_left r₀ r₁)).trans (hr₀U z hz)
  · apply apm_a97j08_pairwiseDisjoint_closedBall_of_separated
    intro x hx y hy hxy
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (min_le_right r₀ r₁) (by positivity))
      (hr₁sep hx hy hxy)

/-- The finite divisor support of an analytic function therefore has one
family of interior-contained pairwise-disjoint closed zero disks. -/
lemma apm_a97j08_exists_pairwiseDisjoint_zeroSupport_closedBalls
    {γ : ℝ → ℂ} {g : ℂ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hg : AnalyticOnNhd ℂ g (closure (apm_a97j08_curveInterior γ))) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ (MeromorphicOn.divisor g
          (apm_a97j08_curveInterior γ)).support,
        closedBall z r ⊆ apm_a97j08_curveInterior γ) ∧
      (MeromorphicOn.divisor g
        (apm_a97j08_curveInterior γ)).support.PairwiseDisjoint
          fun z ↦ closedBall z r := by
  apply apm_a97j08_exists_pairwiseDisjoint_closedBall_subset_of_finite
    (apm_a97j08_divisor_support_finite_of_compact_closure
      (apm_a97j08_curveInterior_isCompact_closure hγ_cont) hg)
    (apm_a97j08_curveInterior_isOpen hγ_cont)
  exact (MeromorphicOn.divisor g
    (apm_a97j08_curveInterior γ)).supportWithinDomain

/-- Restricting a meromorphic divisor does not change its value at a point
of the smaller domain. -/
lemma apm_a97j08_divisor_eq_of_mem_of_subset
    {f : ℂ → ℂ} {U V : Set ℂ} (hf : MeromorphicOn f U)
    (hVU : V ⊆ U) {z : ℂ} (hz : z ∈ V) :
    MeromorphicOn.divisor f V z = MeromorphicOn.divisor f U z := by
  have hrestrict :
      (MeromorphicOn.divisor f U).restrict hVU =
        MeromorphicOn.divisor f V :=
    MeromorphicOn.divisor_restrict hf hVU
  have hpoint := congrArg
    (fun D : Function.locallyFinsuppWithin V ℤ ↦ D z) hrestrict
  simpa [Function.locallyFinsuppWithin.restrict_apply, hz] using hpoint.symm

/-- If a smaller domain contains the entire global divisor support, then
restriction loses no zeros and hence preserves the frozen zero count. -/
lemma apm_a97j08_zeroCount_eq_of_support_subset
    {f : ℂ → ℂ} {U V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hVU : V ⊆ U) (hcl : closure V ⊆ closure U)
    (hsupp : (MeromorphicOn.divisor f U).support ⊆ V) :
    apm_a97j08_zeroCount f V = apm_a97j08_zeroCount f U := by
  rw [apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic (hf.mono hcl),
    apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic hf]
  apply finsum_congr
  intro z
  by_cases hz : z ∈ V
  · exact apm_a97j08_divisor_eq_of_mem_of_subset
      (fun w hw ↦ hf.meromorphicOn w (subset_closure hw)) hVU hz
  · have hglobal : MeromorphicOn.divisor f U z = 0 := by
      by_contra hne
      exact hz (hsupp (Function.mem_support.mpr hne))
    have hlocal : MeromorphicOn.divisor f V z = 0 := by
      by_contra hne
      exact hz ((MeromorphicOn.divisor f V).supportWithinDomain
        (Function.mem_support.mpr hne))
    rw [hlocal, hglobal]

/-- An analytic function which is nonzero throughout the counting domain has
zero frozen zero count.  This discharges the compact-remainder contribution
after uniform convergence supplies nonvanishing there. -/
lemma apm_a97j08_zeroCount_eq_zero_of_ne_zero
    {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hne : ∀ z ∈ U, f z ≠ 0) :
    apm_a97j08_zeroCount f U = 0 := by
  rw [apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic hf]
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  by_cases hz : z ∈ U
  · have hfz : AnalyticAt ℂ f z := hf z (subset_closure hz)
    rw [MeromorphicOn.divisor_apply
      (fun w hw ↦ (hf w (subset_closure hw)).meromorphicAt) hz,
      hfz.meromorphicOrderAt_eq,
      hfz.analyticOrderAt_eq_zero.mpr (hne z hz)]
    rfl
  · simp [hz]

/-- A restricted analytic zero count can be computed as an ordinary finite
sum by filtering the finite support of the ambient divisor. -/
lemma apm_a97j08_zeroCount_eq_sum_filter_divisor
    {f : ℂ → ℂ} {U V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hVU : V ⊆ U) (hcl : closure V ⊆ closure U)
    (hfin : (MeromorphicOn.divisor f U).support.Finite) :
    apm_a97j08_zeroCount f V =
      ∑ z ∈ (hfin.inter_of_left V).toFinset,
        MeromorphicOn.divisor f U z := by
  classical
  rw [apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic (hf.mono hcl)]
  rw [finsum_eq_sum_of_support_subset
    (s := (hfin.inter_of_left V).toFinset)]
  · apply Finset.sum_congr rfl
    intro z hz
    exact apm_a97j08_divisor_eq_of_mem_of_subset
      (fun w hw ↦ hf.meromorphicOn w (subset_closure hw)) hVU
      (Set.Finite.mem_toFinset (hfin.inter_of_left V) |>.mp hz).2
  · intro z hz
    have hzV : z ∈ V :=
      (MeromorphicOn.divisor f V).supportWithinDomain hz
    have heq := apm_a97j08_divisor_eq_of_mem_of_subset
      (fun w hw ↦ hf.meromorphicOn w (subset_closure hw)) hVU hzV
    apply Set.Finite.mem_toFinset (hfin.inter_of_left V) |>.mpr
    refine ⟨?_, hzV⟩
    exact Function.mem_support.mpr
      (heq ▸ Function.mem_support.mp hz)

/-- In particular, the count in one selected closed disk is the ambient
divisor sum over precisely the ambient support points lying in that disk. -/
lemma apm_a97j08_zeroCount_closedBall_eq_sum_filter_divisor
    {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hball : closedBall c r ⊆ U)
    (hfin : (MeromorphicOn.divisor f U).support.Finite) :
    apm_a97j08_zeroCount f (closedBall c r) =
      ∑ z ∈ (hfin.inter_of_left (closedBall c r)).toFinset,
        MeromorphicOn.divisor f U z := by
  apply apm_a97j08_zeroCount_eq_sum_filter_divisor hf hball
  · rw [isClosed_closedBall.closure_eq]
    exact hball.trans subset_closure
  · exact hfin

/-- Finite additivity of the frozen analytic zero count over a pairwise
disjoint family which covers the ambient divisor support. -/
lemma apm_a97j08_zeroCount_eq_sum_pairwiseDisjoint
    {ι : Type*} {f : ℂ → ℂ} {U : Set ℂ} {C : Finset ι}
    {B : ι → Set ℂ}
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hBU : ∀ i ∈ C, B i ⊆ U)
    (hBcl : ∀ i ∈ C, closure (B i) ⊆ closure U)
    (hdis : (C : Set ι).PairwiseDisjoint B)
    (hcover : (MeromorphicOn.divisor f U).support ⊆ ⋃ i ∈ C, B i)
    (hfin : (MeromorphicOn.divisor f U).support.Finite) :
    apm_a97j08_zeroCount f U =
      ∑ i ∈ C, apm_a97j08_zeroCount f (B i) := by
  classical
  let T : ι → Finset ℂ := fun i ↦
    (hfin.inter_of_left (B i)).toFinset
  have hTdis : (C : Set ι).PairwiseDisjoint T := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    have hziB : z ∈ B i :=
      (Set.Finite.mem_toFinset (hfin.inter_of_left (B i)) |>.mp hzi).2
    have hzjB : z ∈ B j :=
      (Set.Finite.mem_toFinset (hfin.inter_of_left (B j)) |>.mp hzj).2
    exact (Set.disjoint_left.mp (hdis hi hj hij)) hziB hzjB
  have hUnion : C.biUnion T = hfin.toFinset := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hiC, hzi⟩ := Finset.mem_biUnion.mp hz
      exact Set.Finite.mem_toFinset hfin |>.mpr
        (Set.Finite.mem_toFinset (hfin.inter_of_left (B i)) |>.mp hzi).1
    · intro hz
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support :=
        Set.Finite.mem_toFinset hfin |>.mp hz
      have hzunion := hcover hzsup
      simp only [mem_iUnion] at hzunion
      obtain ⟨i, hi⟩ := hzunion
      obtain ⟨hiC, hziB⟩ := hi
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hiC, Set.Finite.mem_toFinset
        (hfin.inter_of_left (B i)) |>.mpr ?_⟩
      exact ⟨hzsup, hziB⟩
  have hsuppfin : (MeromorphicOn.divisor f U).support ⊆
      (hfin.toFinset : Set ℂ) := fun z hz ↦
    Set.Finite.mem_toFinset hfin |>.mpr hz
  rw [apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic hf,
    finsum_eq_sum_of_support_subset _ hsuppfin, ← hUnion,
    Finset.sum_biUnion hTdis]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  exact apm_a97j08_zeroCount_eq_sum_filter_divisor hf
    (hBU i hi) (hBcl i hi) hfin

/-- Specialization of finite additivity to the common-radius zero disks
selected above. -/
lemma apm_a97j08_zeroCount_eq_sum_support_closedBalls
    {f : ℂ → ℂ} {U : Set ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closure U))
    (hr : 0 ≤ r)
    (hball : ∀ z ∈ (MeromorphicOn.divisor f U).support,
      closedBall z r ⊆ U)
    (hdis : (MeromorphicOn.divisor f U).support.PairwiseDisjoint
      fun z ↦ closedBall z r)
    (hfin : (MeromorphicOn.divisor f U).support.Finite) :
    apm_a97j08_zeroCount f U =
      ∑ z ∈ hfin.toFinset,
        apm_a97j08_zeroCount f (closedBall z r) := by
  apply apm_a97j08_zeroCount_eq_sum_pairwiseDisjoint hf
  · intro z hz
    exact hball z (Set.Finite.mem_toFinset hfin |>.mp hz)
  · intro z hz
    rw [isClosed_closedBall.closure_eq]
    exact (hball z (Set.Finite.mem_toFinset hfin |>.mp hz)).trans subset_closure
  · simpa using hdis
  · intro z hz
    simp only [mem_iUnion]
    refine ⟨z, Set.Finite.mem_toFinset hfin |>.mpr hz, ?_⟩
    exact mem_closedBall_self hr
  · exact hfin

/-- The reusable closed-ball Rouché theorem, translated to the frozen
`apm_a97j08_zeroCount` encoding and a direct pair of functions. -/
lemma apm_a97j08_zeroCount_closedBall_eq_of_rouche
    {f g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hfg : ∀ z ∈ sphere c r, ‖f z - g z‖ < ‖g z‖) :
    apm_a97j08_zeroCount f (closedBall c r) =
      apm_a97j08_zeroCount g (closedBall c r) := by
  rw [apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic
      (by simpa using hf),
    apm_a97j08_zeroCount_eq_divisor_finsum_of_analytic
      (by simpa using hg)]
  change ConstructionTargets.Rouche.zeroCountInClosedBall f c r =
    ConstructionTargets.Rouche.zeroCountInClosedBall g c r
  have h := ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq
    hr hg (hf.sub hg) (by simpa [norm_sub_rev] using hfg)
  simpa only [Pi.add_apply, add_sub_cancel] using h

/-- Uniform convergence on the compact encoded closure eventually gives the
strict Rouché inequality on any selected zero-free disk boundary. -/
lemma apm_a97j08_eventually_rouche_on_sphere
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {c : ℂ} {r : ℝ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hr : 0 < r)
    (hsphere : sphere c r ⊆ closure (apm_a97j08_curveInterior γ))
    (hg_cont : ContinuousOn g (sphere c r))
    (hg_ne : ∀ z ∈ sphere c r, g z ≠ 0) :
    ∀ᶠ n in atTop, ∀ z ∈ sphere c r,
      ‖F n z - g z‖ < ‖g z‖ := by
  obtain ⟨ε, hε, hεg⟩ := apm_a97j08_exists_compact_norm_margin
    (isCompact_sphere c r) (by
      refine ⟨c + (r : ℂ), ?_⟩
      simp [Real.norm_eq_abs, abs_of_pos hr]) hg_cont hg_ne
  filter_upwards [apm_a97j08_eventually_norm_sub_lt_on_curveInterior_closure
    hD_open hγ_cont hUD hF_tendsto hε] with n hn
  intro z hz
  exact lt_of_lt_of_le (hn z (hsphere hz)) (hεg z hz)

/-- For an analytic function, membership in the divisor support is exactly
vanishing at points of the domain. -/
lemma apm_a97j08_mem_divisor_support_iff_eq_zero
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {z : ℂ} (hz : z ∈ U) (hfin : meromorphicOrderAt f z ≠ ⊤) :
    z ∈ (MeromorphicOn.divisor f U).support ↔ f z = 0 := by
  have hfz : AnalyticAt ℂ f z := hf z hz
  have ha : analyticOrderAt f z ≠ ⊤ := by
    intro ha
    apply hfin
    rw [hfz.meromorphicOrderAt_eq, ha]
    rfl
  rw [Function.mem_support,
    MeromorphicOn.divisor_apply hf.meromorphicOn hz]
  simp [WithTop.untop₀_eq_zero, ha,
    hfz.meromorphicOrderAt_eq, hfz.analyticOrderAt_ne_zero]

/-- Pairwise-disjoint support-centered closed disks have zero-free boundary,
provided all zeros in the ambient domain are represented in the divisor
support (equivalently, infinite analytic order has been excluded). -/
lemma apm_a97j08_zero_free_sphere_of_pairwiseDisjoint_support
    {g : ℂ → ℂ} {U S : Set ℂ} {r : ℝ}
    (hr : 0 < r)
    (hball : ∀ c ∈ S, closedBall c r ⊆ U)
    (hdis : S.PairwiseDisjoint fun c ↦ closedBall c r)
    (hzero : ∀ z ∈ U, g z = 0 → z ∈ S) :
    ∀ c ∈ S, ∀ z ∈ sphere c r, g z ≠ 0 := by
  intro c hc z hz hgz
  have hzU : z ∈ U := hball c hc (sphere_subset_closedBall hz)
  have hzS : z ∈ S := hzero z hzU hgz
  by_cases hzc : z = c
  · subst z
    have : (0 : ℝ) = r := by simpa using (mem_sphere.mp hz)
    linarith
  · exact (Set.disjoint_left.mp (hdis hc hzS (fun h ↦ hzc h.symm)))
      (sphere_subset_closedBall hz) (mem_closedBall_self hr.le)

/-- The finitely many selected zero disks admit one eventual index at which
all of their boundary Rouché inequalities hold simultaneously. -/
lemma apm_a97j08_eventually_rouche_on_support_spheres
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {U S : Set ℂ} {r : ℝ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg : AnalyticOnNhd ℂ g (closure U))
    (hU : U = apm_a97j08_curveInterior γ)
    (hS : S.Finite) (hr : 0 < r)
    (hball : ∀ c ∈ S, closedBall c r ⊆ U)
    (hdis : S.PairwiseDisjoint fun c ↦ closedBall c r)
    (hzero : ∀ z ∈ U, g z = 0 → z ∈ S) :
    ∀ᶠ n in atTop, ∀ c ∈ S, ∀ z ∈ sphere c r,
      ‖F n z - g z‖ < ‖g z‖ := by
  rw [hS.eventually_all]
  intro c hc
  apply apm_a97j08_eventually_rouche_on_sphere
    hD_open hγ_cont hUD hF_tendsto hr
  · rw [← hU]
    exact (sphere_subset_closedBall.trans (hball c hc)).trans subset_closure
  · exact hg.continuousOn.mono
      ((sphere_subset_closedBall.trans (hball c hc)).trans subset_closure)
  · exact apm_a97j08_zero_free_sphere_of_pairwiseDisjoint_support
      hr hball hdis hzero c hc

/-- Simultaneous boundary inequalities immediately transfer the frozen zero
count on every selected support disk. -/
lemma apm_a97j08_eventually_zeroCount_eq_on_support_closedBalls
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {U S : Set ℂ} {r : ℝ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) (closure U))
    (hg : AnalyticOnNhd ℂ g (closure U))
    (hU : U = apm_a97j08_curveInterior γ)
    (hS : S.Finite) (hr : 0 < r)
    (hball : ∀ c ∈ S, closedBall c r ⊆ U)
    (hdis : S.PairwiseDisjoint fun c ↦ closedBall c r)
    (hzero : ∀ z ∈ U, g z = 0 → z ∈ S) :
    ∀ᶠ n in atTop, ∀ c ∈ S,
      apm_a97j08_zeroCount (F n) (closedBall c r) =
        apm_a97j08_zeroCount g (closedBall c r) := by
  filter_upwards [apm_a97j08_eventually_rouche_on_support_spheres
    hD_open hγ_cont hUD hF_tendsto hg hU hS hr hball hdis hzero] with n hn
  intro c hc
  apply apm_a97j08_zeroCount_closedBall_eq_of_rouche hr
  · exact (hF n).mono
      ((hball c hc).trans subset_closure)
  · exact hg.mono ((hball c hc).trans subset_closure)
  · exact hn c hc

/-- Removing a finite union of open zero disks from a compact closure leaves
a compact remainder. -/
lemma apm_a97j08_isCompact_disk_remainder
    {U S : Set ℂ} {r : ℝ} (hU : IsCompact (closure U)) (hS : S.Finite) :
    IsCompact (closure U \ ⋃ c ∈ hS.toFinset, ball c r) := by
  apply hU.diff
  exact isOpen_biUnion fun _ _ ↦ isOpen_ball

/-- If the selected centers contain every zero of the limit, uniform
convergence eventually makes every approximant nonzero on the compact
remainder outside their open disks. -/
lemma apm_a97j08_eventually_ne_zero_on_disk_remainder
    {D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {S : Set ℂ} {r : ℝ}
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg : AnalyticOnNhd ℂ g
      (closure (apm_a97j08_curveInterior γ)))
    (hg_curve : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0)
    (hS : S.Finite) (hr : 0 < r)
    (hzero : ∀ z ∈ apm_a97j08_curveInterior γ, g z = 0 → z ∈ S)
    :
    ∀ᶠ n in atTop, ∀ z ∈
      closure (apm_a97j08_curveInterior γ) \
        ⋃ c ∈ hS.toFinset, ball c r,
      F n z ≠ 0 := by
  let K := closure (apm_a97j08_curveInterior γ) \
    ⋃ c ∈ hS.toFinset, ball c r
  have hKcompact : IsCompact K :=
    apm_a97j08_isCompact_disk_remainder
      (apm_a97j08_curveInterior_isCompact_closure hγ_cont) hS
  have hKsub : K ⊆ closure (apm_a97j08_curveInterior γ) := diff_subset
  have hgK : ContinuousOn g K := hg.continuousOn.mono hKsub
  have hg_ne : ∀ z ∈ K, g z ≠ 0 := by
    intro z hz hgz
    rcases apm_a97j08_closure_curveInterior_subset_union_curveImage
      hγ_cont hz.1 with hzU | hzcurve
    · have hzS := hzero z hzU hgz
      apply hz.2
      simp only [mem_iUnion]
      exact ⟨z, Set.Finite.mem_toFinset hS |>.mpr hzS,
        mem_ball_self hr⟩
    · exact hg_curve z hzcurve hgz
  by_cases hKne : K.Nonempty
  · exact apm_a97j08_eventually_ne_zero_on_compact_subset
      hD_open hγ_cont hUD hF_tendsto hKcompact hKne hKsub hgK hg_ne
  · filter_upwards [] with n
    intro z hz
    exact False.elim (hKne ⟨z, hz⟩)

/-- Every point in the support of an analytic divisor is a zero.  This
direction is unconditional: nonzero support itself rules out infinite order. -/
lemma apm_a97j08_eq_zero_of_mem_divisor_support
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {z : ℂ} (hz : z ∈ (MeromorphicOn.divisor f U).support) :
    f z = 0 := by
  have hzU := (MeromorphicOn.divisor f U).supportWithinDomain hz
  have horder : meromorphicOrderAt f z ≠ ⊤ := by
    intro htop
    apply Function.mem_support.mp hz
    rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzU, htop]
    rfl
  exact (apm_a97j08_mem_divisor_support_iff_eq_zero hf hzU horder).mp hz

/-- Nonvanishing on the compact complement forces the approximant's entire
ambient divisor support into the selected open disks. -/
lemma apm_a97j08_divisor_support_subset_disk_union_of_remainder_ne_zero
    {f : ℂ → ℂ} {U S : Set ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closure U)) (hS : S.Finite)
    (hne : ∀ z ∈ closure U \ ⋃ c ∈ hS.toFinset, ball c r, f z ≠ 0) :
    (MeromorphicOn.divisor f U).support ⊆
      ⋃ c ∈ hS.toFinset, closedBall c r := by
  intro z hz
  have hzU := (MeromorphicOn.divisor f U).supportWithinDomain hz
  have hfz : f z = 0 := apm_a97j08_eq_zero_of_mem_divisor_support
    (hf.mono subset_closure) hz
  by_contra hzclosed
  have hzopen : z ∉ ⋃ c ∈ hS.toFinset, ball c r := by
    intro hzopen
    apply hzclosed
    simp only [mem_iUnion] at hzopen ⊢
    obtain ⟨c, hc, hzc⟩ := hzopen
    exact ⟨c, hc, ball_subset_closedBall hzc⟩
  exact hne z ⟨subset_closure hzU, hzopen⟩ hfz

/-- Complete finite-disk Rouché assembly.  Its sole nonstandard analytic
input is that every zero of `g` in the encoded interior appears in the
divisor support, i.e. infinite analytic order has already been excluded. -/
lemma apm_a97j08_eventually_zeroCount_eq_of_zero_mem_support
    (D : Set ℂ) (γ : ℝ → ℂ) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hF : ∀ n, AnalyticOnNhd ℂ (F n)
      (closure (apm_a97j08_curveInterior γ)))
    (hg : AnalyticOnNhd ℂ g
      (closure (apm_a97j08_curveInterior γ)))
    (hg_curve : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0)
    (hzero : ∀ z ∈ apm_a97j08_curveInterior γ, g z = 0 →
      z ∈ (MeromorphicOn.divisor g
        (apm_a97j08_curveInterior γ)).support) :
    ∀ᶠ n in atTop,
      apm_a97j08_zeroCount (F n) (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  let U := apm_a97j08_curveInterior γ
  let S := (MeromorphicOn.divisor g U).support
  have hfin : S.Finite :=
    apm_a97j08_divisor_support_finite_of_compact_closure
      (apm_a97j08_curveInterior_isCompact_closure hγ_cont) hg
  obtain ⟨r, hr, hball, hdis⟩ :=
    apm_a97j08_exists_pairwiseDisjoint_zeroSupport_closedBalls hγ_cont hg
  have hlocal := apm_a97j08_eventually_zeroCount_eq_on_support_closedBalls
    hD_open hγ_cont hUD hF_tendsto hF hg rfl hfin hr hball hdis hzero
  have hremainder := apm_a97j08_eventually_ne_zero_on_disk_remainder
    hD_open hγ_cont hUD hF_tendsto hg hg_curve hfin hr hzero
  filter_upwards [hlocal, hremainder] with n hnlocal hnremainder
  have hfinF : (MeromorphicOn.divisor (F n) U).support.Finite :=
    apm_a97j08_divisor_support_finite_of_compact_closure
      (apm_a97j08_curveInterior_isCompact_closure hγ_cont) (hF n)
  have hcoverF : (MeromorphicOn.divisor (F n) U).support ⊆
      ⋃ c ∈ hfin.toFinset, closedBall c r :=
    apm_a97j08_divisor_support_subset_disk_union_of_remainder_ne_zero
      (hF n) hfin hnremainder
  calc
    apm_a97j08_zeroCount (F n) U =
        ∑ c ∈ hfin.toFinset,
          apm_a97j08_zeroCount (F n) (closedBall c r) := by
      apply apm_a97j08_zeroCount_eq_sum_pairwiseDisjoint (hF n)
      · intro c hc
        exact hball c (Set.Finite.mem_toFinset hfin |>.mp hc)
      · intro c hc
        rw [isClosed_closedBall.closure_eq]
        exact (hball c (Set.Finite.mem_toFinset hfin |>.mp hc)).trans
          subset_closure
      · simpa using hdis
      · exact hcoverF
      · exact hfinF
    _ = ∑ c ∈ hfin.toFinset,
          apm_a97j08_zeroCount g (closedBall c r) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hnlocal c (Set.Finite.mem_toFinset hfin |>.mp hc)
    _ = apm_a97j08_zeroCount g U := by
      symm
      exact apm_a97j08_zeroCount_eq_sum_support_closedBalls
        hg hr.le hball hdis hfin

/-- Connected-domain nontriviality excludes infinite analytic order, so every
interior zero is represented in the divisor support. -/
lemma apm_a97j08_zero_mem_divisor_support_of_connected_domain
    {D : Set ℂ} {γ : ℝ → ℂ} {g : ℂ → ℂ}
    (hD_conn : IsPreconnected D)
    (hUD : apm_a97j08_curveInterior γ ⊆ D)
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hg : AnalyticOnNhd ℂ g D)
    (hg_curve : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) :
    ∀ z ∈ apm_a97j08_curveInterior γ, g z = 0 →
      z ∈ (MeromorphicOn.divisor g
        (apm_a97j08_curveInterior γ)).support := by
  intro z hzU hgz
  have hzD := hUD hzU
  have hfz : AnalyticAt ℂ g z := hg z hzD
  have horder : meromorphicOrderAt g z ≠ ⊤ := by
    intro htop
    have hatop : analyticOrderAt g z = ⊤ := by
      rw [hfz.meromorphicOrderAt_eq] at htop
      simpa using htop
    have hevent : g =ᶠ[𝓝 z] 0 := by
      simpa only [Pi.zero_apply] using analyticOrderAt_eq_top.mp hatop
    have hall := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hD_conn hzD hevent
    have hzeroCurve : g (γ 0) = 0 := hall (hγD ⟨0, ⟨by simp, by simp⟩, rfl⟩)
    exact hg_curve (γ 0) ⟨0, ⟨by simp, by simp⟩, rfl⟩ hzeroCurve
  exact (apm_a97j08_mem_divisor_support_iff_eq_zero
    (hg.mono hUD) hzU horder).mpr hgz

/-- End-to-end analytic theorem once the encoded closed interior has been
placed in the connected ambient domain. -/
lemma apm_a97j08_eventual_zeroCount_of_closure_subset
    (D : Set ℂ) (γ : ℝ → ℂ) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hD_open : IsOpen D) (hD_conn : IsPreconnected D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg_curve : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0)
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D) :
    ∃ N : ℕ, ∀ n ≥ N,
      apm_a97j08_zeroCount (F n) (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  have hgD : DifferentiableOn ℂ g D :=
    apm_a97j08_limit_differentiableOn hD_open hF_analytic hF_tendsto
  have hg : AnalyticOnNhd ℂ g
      (closure (apm_a97j08_curveInterior γ)) :=
    apm_a97j08_analyticOnNhd_curveInterior_closure hD_open hgD hUD
  have hF : ∀ n, AnalyticOnNhd ℂ (F n)
      (closure (apm_a97j08_curveInterior γ)) := fun n ↦
    apm_a97j08_analyticOnNhd_curveInterior_closure
      hD_open (hF_analytic n) hUD
  have hzero := apm_a97j08_zero_mem_divisor_support_of_connected_domain
    hD_conn (subset_closure.trans hUD) hγD
    (hgD.analyticOnNhd hD_open) hg_curve
  have hevent := apm_a97j08_eventually_zeroCount_eq_of_zero_mem_support
    D γ F g hD_open hγ_cont hUD hF_tendsto hF hg hg_curve hzero
  rw [eventually_atTop] at hevent
  exact hevent

/-- Sharpened end-to-end reduction.  Topology is used only to place the
encoded bounded components inside `D`; the analytic provider only has to
transfer zero counts for functions analytic on that concrete interior. -/
lemma apm_a97j08_of_interior_subset_and_rouche
    (D : Set ℂ) (γ : ℝ → ℂ) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hD_open : IsOpen D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0)
    (hUD : closure (apm_a97j08_curveInterior γ) ⊆ D)
    (hrouche : ∀ (f g : ℂ → ℂ),
      AnalyticOnNhd ℂ f (closure (apm_a97j08_curveInterior γ)) →
      AnalyticOnNhd ℂ g (closure (apm_a97j08_curveInterior γ)) →
      (∀ z ∈ apm_a97j08_curveImage γ, ‖f z - g z‖ < ‖g z‖) →
      apm_a97j08_zeroCount f (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ)) :
    ∃ N : ℕ, ∀ n ≥ N,
      apm_a97j08_zeroCount (F n) (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ) := by
  have hg_analytic : DifferentiableOn ℂ g D :=
    apm_a97j08_limit_differentiableOn hD_open hF_analytic hF_tendsto
  have hgU := apm_a97j08_analyticOnNhd_curveInterior_closure
    hD_open hg_analytic hUD
  obtain ⟨N, hN⟩ := apm_a97j08_eventually_boundary_rouche
    hD_open hγ_cont hγD hF_analytic hF_tendsto hg_ne
  refine ⟨N, fun n hn ↦ ?_⟩
  exact hrouche (F n) g
    (apm_a97j08_analyticOnNhd_curveInterior_closure
      hD_open (hF_analytic n) hUD)
    hgU (hN n hn)

/-! ## Blocker analysis

This is the Hurwitz/Rouché theorem: zeros are stable under locally uniform
convergence.  The development below has now discharged the analytic items:

1. **Weierstrass convergence theorem**: discharged using the current
   `TendstoLocallyUniformlyOn.differentiableOn` API.

2. **Jordan curve theorem**: the interior of a Jordan curve is well-defined.
   - Mathlib has NO Jordan curve theorem. `apm_a97j08_curveInterior` is defined
     via `connectedComponentIn` and `Bornology.IsBounded`, but there is no
     theorem that a simple closed curve bounds a unique bounded region.

3. **Rouché transfer**: discharged without arbitrary-contour integration by
   selecting finitely many disjoint zero disks, applying
   `ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq`, and excluding
   zeros on the compact remainder.

4. **Global zero-count assembly**: discharged by finite divisor-support
   restriction and additivity across the selected disjoint disks.

Consequently the sole remaining gap is item 2, now factored below as the
construction of an essential loop around a compact connected complementary
component. -/

/-- A loop is nullhomotopic within `D` when both the loop and a contraction to
its base point remain in `D`.  Packaging this condition keeps the missing
plane-topology interface independent of Mathlib's simply-connected wrapper. -/
def apm_a97j08_LoopNullhomotopicIn (D : Set ℂ) {x : ℂ} (p : Path x x) : Prop :=
  (∀ t, p t ∈ D) ∧
    ∃ H : p.Homotopy (Path.refl x), ∀ t, H t ∈ D

/-- The identity loop on the topological circle is not nullhomotopic.  This
is the concrete detector for the planned planar construction: nullhomotopy
would kill its map on integral first singular homology, whereas
`ConstructionTargets.CircleHomology.circleH1IsoInt` identifies that homology
with `ℤ`. -/
lemma apm_a97j08_circle_id_not_nullhomotopic :
    ¬ ContinuousMap.Nullhomotopic (ContinuousMap.id Circle) := by
  intro hnull
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hzero : F.map (TopCat.ofHom (ContinuousMap.id Circle)) = 0 :=
    ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_zero_of_nullhomotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero
        (ContinuousMap.id Circle) hnull
  have hid : F.map (TopCat.ofHom (ContinuousMap.id Circle)) =
      𝟙 (F.obj (TopCat.of Circle)) := by
    change F.map (𝟙 (TopCat.of Circle)) = 𝟙 (F.obj (TopCat.of Circle))
    exact F.map_id (TopCat.of Circle)
  have hIdZero : 𝟙 (F.obj (TopCat.of Circle)) = 0 := hid.symm.trans hzero
  let e := ConstructionTargets.CircleHomology.circleH1IsoInt
  have hezero : e.hom = 0 := by
    rw [← CategoryTheory.Category.id_comp e.hom, hIdZero]
    simp
  have hidZ : 𝟙 (ModuleCat.of ℤ ℤ) = 0 := by
    calc
      𝟙 (ModuleCat.of ℤ ℤ) = e.inv ≫ e.hom := e.inv_hom_id.symm
      _ = e.inv ≫ 0 := by rw [hezero]
      _ = 0 := by simp
  have hone := congrArg
    (fun f : (ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) => f (1 : ℤ)) hidZ
  norm_num at hone

/-- A circle map with a continuous left inverse is not nullhomotopic.  This
turns the homology calculation above into a geometric interface: a future
surrounding-circle construction only has to provide its retraction
certificate. -/
lemma apm_a97j08_not_nullhomotopic_of_circle_leftInverse
    {X : Type*} [TopologicalSpace X]
    (c : C(Circle, X)) (r : C(X, Circle))
    (hr : r.comp c = ContinuousMap.id Circle) :
    ¬ ContinuousMap.Nullhomotopic c := by
  intro hc
  apply apm_a97j08_circle_id_not_nullhomotopic
  rw [← hr]
  exact hc.comp_right r

/-- A homotopy left inverse is already enough to detect noncontractibility.
This is the form produced by radial deformation-retract arguments. -/
lemma apm_a97j08_not_nullhomotopic_of_circle_homotopyLeftInverse
    {X : Type*} [TopologicalSpace X]
    (c : C(Circle, X)) (r : C(X, Circle))
    (hr : (r.comp c).Homotopic (ContinuousMap.id Circle)) :
    ¬ ContinuousMap.Nullhomotopic c := by
  intro hc
  apply apm_a97j08_circle_id_not_nullhomotopic
  obtain ⟨y, hy⟩ := hc.comp_right r
  exact ⟨y, hr.symm.trans hy⟩

/-- Traverse a continuous map out of `Circle` once along the standard
exponential parametrization.  This is the endpoint-compatible half of the
bridge between the circle-valued homology detector above and Mathlib's
`Path.Homotopy` formulation of simple connectivity. -/
noncomputable def apm_a97j08_circlePath
    {X : Type*} [TopologicalSpace X]
    (c : C(Circle, X)) : Path (c 1) (c 1) where
  toFun t := c (Circle.exp ((2 * Real.pi) * (t : ℝ)))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- The standard compact interval parametrization of the circle. -/
noncomputable def apm_a97j08_circleParam : unitInterval → Circle :=
  fun t => Circle.exp ((2 * Real.pi) * (t : ℝ))

lemma apm_a97j08_circleParam_continuous :
    Continuous apm_a97j08_circleParam := by
  unfold apm_a97j08_circleParam
  fun_prop

lemma apm_a97j08_circleParam_surjective :
    Function.Surjective apm_a97j08_circleParam := by
  intro u
  by_cases harg : 0 ≤ Complex.arg u
  · refine ⟨⟨Complex.arg u / (2 * Real.pi), ?_⟩, ?_⟩
    · constructor
      · positivity
      · rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
        linarith [Complex.arg_le_pi u, Real.pi_pos]
    · change Circle.exp
        ((2 * Real.pi) * (Complex.arg u / (2 * Real.pi))) = u
      rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), Circle.exp_arg]
  · have harg' : Complex.arg u < 0 := lt_of_not_ge harg
    refine ⟨⟨(Complex.arg u + 2 * Real.pi) / (2 * Real.pi), ?_⟩, ?_⟩
    · constructor
      · exact div_nonneg
          (by linarith [Complex.neg_pi_lt_arg u, Real.pi_pos]) (by positivity)
      · rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
        linarith
    · change Circle.exp ((2 * Real.pi) *
        ((Complex.arg u + 2 * Real.pi) / (2 * Real.pi))) = u
      rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0),
        Circle.exp_add_two_pi, Circle.exp_arg]

/-- The interval parametrization is a quotient map.  This is the precise
product-lifting input needed to descend a two-parameter path homotopy to a
circle homotopy. -/
lemma apm_a97j08_circleParam_isQuotientMap :
    Topology.IsQuotientMap apm_a97j08_circleParam :=
  IsQuotientMap.of_surjective_continuous
    apm_a97j08_circleParam_surjective apm_a97j08_circleParam_continuous

/-- A two-parameter function on the circle is continuous as soon as its pullback
along the standard interval parametrization is continuous.  This packages the
parameterized quotient gluing required to turn a `Path.Homotopy` into an
ordinary homotopy of circle maps. -/
lemma apm_a97j08_continuous_circleHomotopy_of_param
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace unitInterval]
    {G : unitInterval × Circle → X}
    (hG : Continuous fun p : unitInterval × unitInterval =>
      G (p.1, apm_a97j08_circleParam p.2)) :
    Continuous G :=
  apm_a97j08_circleParam_isQuotientMap.continuous_lift_prod_right hG

lemma apm_a97j08_circlePath_mem
    {X : Type*} [TopologicalSpace X] {D : Set X} (c : C(Circle, X))
    (hcD : ∀ u, c u ∈ D) :
    ∀ t, apm_a97j08_circlePath c t ∈ D := by
  intro t
  exact hcD _

/-- The canonical traversal loses no points: it has exactly the same range as
the original circle map. -/
lemma apm_a97j08_circlePath_surjective_on_range
    {X : Type*} [TopologicalSpace X] (c : C(Circle, X)) (u : Circle) :
    ∃ t, apm_a97j08_circlePath c t = c u := by
  by_cases harg : 0 ≤ Complex.arg u
  · let t : unitInterval :=
      ⟨Complex.arg u / (2 * Real.pi), by
        constructor
        · positivity
        · have hu := Complex.arg_le_pi u
          rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
          linarith [Real.pi_pos]⟩
    refine ⟨t, ?_⟩
    change c (Circle.exp ((2 * Real.pi) * (Complex.arg u / (2 * Real.pi)))) = c u
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), Circle.exp_arg]
  · have harg' : Complex.arg u < 0 := lt_of_not_ge harg
    let t : unitInterval :=
      ⟨(Complex.arg u + 2 * Real.pi) / (2 * Real.pi), by
        constructor
        · have hu := Complex.neg_pi_lt_arg u
          exact div_nonneg (by linarith [Real.pi_pos]) (by positivity)
        · rw [div_le_one (by positivity : 0 < 2 * Real.pi)]
          linarith⟩
    refine ⟨t, ?_⟩
    change c (Circle.exp
      ((2 * Real.pi) * ((Complex.arg u + 2 * Real.pi) / (2 * Real.pi)))) = c u
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0),
      Circle.exp_add_two_pi, Circle.exp_arg]

/-- Descend an endpoint-closed path through the endpoint quotient and identify
that quotient with `Circle`.  Together with `apm_a97j08_circlePath`, this
provides both directions of the Path/Circle encoding used by the planar
obstruction. -/
noncomputable def apm_a97j08_pathCircleMap
    {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) : C(Circle, X) :=
  let q : C(AddCircle (1 : ℝ), X) :=
    ⟨AddCircle.liftIco 1 0 (fun r : ℝ => p (projIcc 0 1 zero_le_one r)), by
      apply AddCircle.liftIco_zero_continuous
      · simp
      · fun_prop⟩
  q.comp ⟨(AddCircle.homeomorphCircle one_ne_zero).symm,
    (AddCircle.homeomorphCircle one_ne_zero).symm.continuous⟩

lemma apm_a97j08_pathCircleMap_range_subset
    {X : Type*} [TopologicalSpace X] {D : Set X} {x : X} (p : Path x x)
    (hpD : ∀ t, p t ∈ D) :
    Set.range (apm_a97j08_pathCircleMap p) ⊆ D := by
  rintro _ ⟨u, rfl⟩
  exact hpD _

lemma apm_a97j08_pathCircleMap_apply_circleParam
    {X : Type*} [TopologicalSpace X] {x : X}
    (p : Path x x) (t : unitInterval) :
    apm_a97j08_pathCircleMap p (apm_a97j08_circleParam t) = p t := by
  have hinv :
      (AddCircle.homeomorphCircle one_ne_zero).symm
          (apm_a97j08_circleParam t) =
        ((t : ℝ) : AddCircle (1 : ℝ)) := by
    apply (AddCircle.homeomorphCircle one_ne_zero).injective
    simp [apm_a97j08_circleParam, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk]
  rw [apm_a97j08_pathCircleMap]
  change AddCircle.liftIco 1 0
      (fun r : ℝ => p (projIcc 0 1 zero_le_one r))
      ((AddCircle.homeomorphCircle one_ne_zero).symm
        (apm_a97j08_circleParam t)) = p t
  rw [hinv]
  by_cases ht : (t : ℝ) < 1
  · rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, ht⟩]
    simp
  · have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (not_lt.mp ht))
    subst t
    have heq : ((1 : ℝ) : AddCircle (1 : ℝ)) =
        ((0 : ℝ) : AddCircle (1 : ℝ)) := by
      convert (AddCircle.coe_add_period (p := (1 : ℝ)) (0 : ℝ)) using 1
      norm_num
    change AddCircle.liftIco 1 0
      (fun r : ℝ => p (projIcc 0 1 zero_le_one r))
      ((1 : ℝ) : AddCircle (1 : ℝ)) = p 1
    rw [heq]
    rw [AddCircle.liftIco_zero_coe_apply (by norm_num)]
    simp

/-- Descending every intermediate path in a path homotopy gives a jointly
continuous family of circle maps. -/
lemma apm_a97j08_pathCircleMap_homotopy_continuous
    {X : Type*} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : p.Homotopy q) :
    Continuous fun w : unitInterval × Circle =>
      apm_a97j08_pathCircleMap (H.eval w.1) w.2 := by
  apply apm_a97j08_continuous_circleHomotopy_of_param
  change Continuous fun w : unitInterval × unitInterval =>
    apm_a97j08_pathCircleMap (H.eval w.1)
      (apm_a97j08_circleParam w.2)
  simp_rw [apm_a97j08_pathCircleMap_apply_circleParam]
  exact H.toHomotopy.continuous

/-- The jointly continuous descended family, packaged as Mathlib's ordinary
homotopy between the endpoint circle maps. -/
noncomputable def apm_a97j08_pathCircleMapHomotopy
    {X : Type*} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : p.Homotopy q) :
    ContinuousMap.Homotopy
      (apm_a97j08_pathCircleMap p) (apm_a97j08_pathCircleMap q) where
  toFun w := apm_a97j08_pathCircleMap (H.eval w.1) w.2
  continuous_toFun := apm_a97j08_pathCircleMap_homotopy_continuous H
  map_zero_left u := by simp
  map_one_left u := by simp

lemma apm_a97j08_pathCircleMap_refl
    {X : Type*} [TopologicalSpace X] (x : X) :
    apm_a97j08_pathCircleMap (Path.refl x) = ContinuousMap.const Circle x := by
  ext u
  obtain ⟨t, rfl⟩ := apm_a97j08_circleParam_surjective u
  rw [apm_a97j08_pathCircleMap_apply_circleParam]
  rfl

lemma apm_a97j08_pathCircleMap_circlePath
    {X : Type*} [TopologicalSpace X] (c : C(Circle, X)) :
    apm_a97j08_pathCircleMap (apm_a97j08_circlePath c) = c := by
  ext u
  obtain ⟨t, rfl⟩ := apm_a97j08_circleParam_surjective u
  rw [apm_a97j08_pathCircleMap_apply_circleParam]
  rfl

/-- A contraction of a closed path descends to a nullhomotopy of its circle
encoding. -/
lemma apm_a97j08_pathCircleMap_nullhomotopic_of_pathHomotopy
    {X : Type*} [TopologicalSpace X] {x : X}
    {p : Path x x} (H : p.Homotopy (Path.refl x)) :
    ContinuousMap.Nullhomotopic (apm_a97j08_pathCircleMap p) := by
  refine ⟨x, ?_⟩
  rw [← apm_a97j08_pathCircleMap_refl x]
  exact ⟨apm_a97j08_pathCircleMapHomotopy H⟩

lemma apm_a97j08_circle_nullhomotopic_of_circlePath_homotopy
    {X : Type*} [TopologicalSpace X] (c : C(Circle, X))
    (H : (apm_a97j08_circlePath c).Homotopy (Path.refl (c 1))) :
    ContinuousMap.Nullhomotopic c := by
  rw [← apm_a97j08_pathCircleMap_circlePath c]
  exact apm_a97j08_pathCircleMap_nullhomotopic_of_pathHomotopy H

/-- A noncontractible circle in the subtype `D` gives the ambient essential
loop used by the simply-connectedness argument. -/
lemma apm_a97j08_exists_essential_loop_of_subtype_circle
    (D : Set ℂ) (c : C(Circle, D))
    (hc : ¬ ContinuousMap.Nullhomotopic c) :
    ∃ x : ℂ, ∃ p : Path x x,
      (∀ t, p t ∈ D) ∧ ¬ apm_a97j08_LoopNullhomotopicIn D p := by
  let pD := apm_a97j08_circlePath c
  let p : Path ((c 1 : D) : ℂ) ((c 1 : D) : ℂ) :=
    pD.map continuous_subtype_val
  refine ⟨c 1, p, ?_, ?_⟩
  · intro t
    exact (pD t).property
  · rintro ⟨_, ⟨H, hHD⟩⟩
    have HD : pD.Homotopy (Path.refl (c 1)) :=
      { toFun := fun w => ⟨H w, hHD w⟩
        continuous_toFun := H.continuous.subtype_mk hHD
        map_zero_left := fun t => Subtype.ext (by simp [p, pD])
        map_one_left := fun t => Subtype.ext (by simp [p, pD])
        prop' := fun t y hy => by
          apply Subtype.ext
          rcases hy with rfl | rfl <;> simp }
    exact hc (apm_a97j08_circle_nullhomotopic_of_circlePath_homotopy c HD)

lemma apm_a97j08_exists_essential_loop_of_subtype_circle_homotopyLeftInverse
    (D : Set ℂ) (c : C(Circle, D)) (r : C(D, Circle))
    (hr : (r.comp c).Homotopic (ContinuousMap.id Circle)) :
    ∃ x : ℂ, ∃ p : Path x x,
      (∀ t, p t ∈ D) ∧ ¬ apm_a97j08_LoopNullhomotopicIn D p :=
  apm_a97j08_exists_essential_loop_of_subtype_circle D c
    (apm_a97j08_not_nullhomotopic_of_circle_homotopyLeftInverse c r hr)

/-- In a simply connected set, every loop which lies in the set is
nullhomotopic there. -/
lemma apm_a97j08_loopNullhomotopicIn_of_isSimplyConnected
    {D : Set ℂ} (hD : IsSimplyConnected D) {x : ℂ} (p : Path x x)
    (hpD : ∀ t, p t ∈ D) :
    apm_a97j08_LoopNullhomotopicIn D p := by
  refine ⟨hpD, ?_⟩
  exact (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hD).2 x p hpD

/-- The existence of a bounded complementary component rules out the
degenerate empty domain. -/
lemma apm_a97j08_nonempty_of_bounded_compl_component
    {D : Set ℂ} {z : ℂ} (hz : z ∈ Dᶜ)
    (hzbounded : Bornology.IsBounded (connectedComponentIn Dᶜ z)) :
    D.Nonempty := by
  by_contra hDne
  have hD : D = ∅ := not_nonempty_iff_eq_empty.mp hDne
  subst D
  simp only [compl_empty] at hzbounded
  have hall : (Set.univ : Set ℂ) ⊆ connectedComponentIn Set.univ z :=
    isPreconnected_univ.subset_connectedComponentIn trivial (subset_refl _)
  have huniv : Bornology.IsBounded (Set.univ : Set ℂ) := hzbounded.subset hall
  obtain ⟨C, hC⟩ := huniv.exists_norm_le
  have hC0 : 0 ≤ C := by simpa using hC 0 trivial
  have hlarge := hC ((C + 1 : ℝ) : ℂ) trivial
  simp only [Complex.norm_real, Real.norm_eq_abs] at hlarge
  rw [abs_of_nonneg (by linarith)] at hlarge
  linarith

/-- A bounded complementary component of an open plane domain is compact.
This is the compact-hole input needed by any future polygonal-neighborhood or
Alexander-duality construction of its essential surrounding loop. -/
lemma apm_a97j08_isCompact_compl_component
    {D : Set ℂ} (hD_open : IsOpen D) {z : ℂ} (hz : z ∈ Dᶜ)
    (hzbounded : Bornology.IsBounded (connectedComponentIn Dᶜ z)) :
    IsCompact (connectedComponentIn Dᶜ z) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, hzbounded⟩
  rw [connectedComponentIn_eq_image hz]
  exact hD_open.isClosed_compl.isClosedMap_subtype_val _
    isClosed_connectedComponent

/-- The bounded complementary component, packaged as the nonempty connected
compactum used by planar separation arguments. -/
lemma apm_a97j08_compl_component_compact_connected
    {D : Set ℂ} (hD_open : IsOpen D) {z : ℂ} (hz : z ∈ Dᶜ)
    (hzbounded : Bornology.IsBounded (connectedComponentIn Dᶜ z)) :
    IsCompact (connectedComponentIn Dᶜ z) ∧
      IsConnected (connectedComponentIn Dᶜ z) ∧
      z ∈ connectedComponentIn Dᶜ z ∧
      connectedComponentIn Dᶜ z ⊆ Dᶜ := by
  exact ⟨apm_a97j08_isCompact_compl_component hD_open hz hzbounded,
    isConnected_connectedComponentIn_iff.mpr hz,
    mem_connectedComponentIn hz,
    connectedComponentIn_subset Dᶜ z⟩

/-- Radial normalization about a point outside `D`.  This is the explicit
`D → Circle` half of the surrounding-circle certificate. -/
noncomputable def apm_a97j08_radialMap
    (D : Set ℂ) (z : ℂ) (hz : z ∈ Dᶜ) : C(D, Circle) where
  toFun w := ⟨(w.1 - z) / ‖w.1 - z‖, by
    have hwz : w.1 ≠ z := fun h => hz (h ▸ w.property)
    have hw : w.1 - z ≠ 0 := sub_ne_zero.mpr hwz
    simp [Submonoid.unitSphere, hw]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro w
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact_mod_cast norm_ne_zero_iff.mpr
        (sub_ne_zero.mpr fun h : w.1 = z => hz (h ▸ w.property))

/-- A degree-one certificate for the explicit radial map produces the weakest
noncontractibility witness required by the remaining planar theorem. -/
lemma apm_a97j08_not_nullhomotopic_of_radial_homotopy
    (D : Set ℂ) {z : ℂ} (hz : z ∈ Dᶜ)
    (c : C(Circle, D))
    (hdegree : ((apm_a97j08_radialMap D z hz).comp c).Homotopic
      (ContinuousMap.id Circle)) :
    ¬ ContinuousMap.Nullhomotopic c :=
  apm_a97j08_not_nullhomotopic_of_circle_homotopyLeftInverse c
    (apm_a97j08_radialMap D z hz) hdegree

def apm_a97j08_GridInput
    (D : Set ℂ) (z : ℂ) (R δ : ℝ) (A B : Set ℂ) : Prop :=
    0 < R ∧ 0 < δ ∧ z ∈ A ∧
    IsCompact A ∧ IsCompact B ∧
    connectedComponentIn Dᶜ z ⊆ A ∧
    Dᶜ ∩ Metric.closedBall 0 R = A ∪ B ∧
    Disjoint A B ∧
    (∀ a ∈ A, ∀ b ∈ B, δ ≤ dist a b) ∧
    A ⊆ Metric.ball 0 (R - δ)

def apm_a97j08_ClopenSeparationFact
    (D : Set ℂ) (z : ℂ) : Prop :=
  ∃ R δ : ℝ, ∃ A B : Set ℂ, apm_a97j08_GridInput D z R δ A B

def apm_a97j08_gridSquare (shift : ℂ) (δ : ℝ) (q : ℤ × ℤ) : Set ℂ :=
  {w | shift.re + q.1 * δ ≤ w.re ∧ w.re ≤ shift.re + (q.1 + 1) * δ ∧
    shift.im + q.2 * δ ≤ w.im ∧ w.im ≤ shift.im + (q.2 + 1) * δ}

def apm_a97j08_IsGridRegion
    (A B : Set ℂ) (R δ : ℝ) (z : ℂ) (U : Set ℂ) : Prop :=
  ∃ shift : ℂ, ∃ Q : Finset (ℤ × ℤ),
    U = ⋃ q ∈ Q, apm_a97j08_gridSquare shift δ q ∧
    z ∈ interior U ∧ A ⊆ interior U ∧ Disjoint U B ∧
    U ⊆ Metric.closedBall 0 R ∧
    z.re ∉ {x | ∃ k : ℤ, x = shift.re + k * δ} ∧
    z.im ∉ {y | ∃ k : ℤ, y = shift.im + k * δ}

/-! ### Grid winding: lattice edges, angle steps, cycles

A lattice edge is an ordered pair of lattice vertices.  Each grid square
contributes its four counterclockwise edges; the boundary edges of a finite
family of squares are those whose reverse is not also a square edge.  Seen from
`z`, an oriented segment `[p, q]` turns through `arg ((q - z) / (p - z))`; when
the segment misses `z` this is the exact angle swept, so sums of these steps
around closed polygons are winding numbers times `2π`. -/

def apm_a97j08_gridVertex (shift : ℂ) (δ : ℝ) (v : ℤ × ℤ) : ℂ :=
  shift + (((v.1 : ℝ) * δ : ℝ) : ℂ) + (((v.2 : ℝ) * δ : ℝ) : ℂ) * Complex.I

def apm_a97j08_squareEdges (q : ℤ × ℤ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {((q.1, q.2), (q.1 + 1, q.2)), ((q.1 + 1, q.2), (q.1 + 1, q.2 + 1)),
    ((q.1 + 1, q.2 + 1), (q.1, q.2 + 1)), ((q.1, q.2 + 1), (q.1, q.2))}

def apm_a97j08_allEdges (Q : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  Q.biUnion apm_a97j08_squareEdges

def apm_a97j08_boundaryEdges (Q : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (apm_a97j08_allEdges Q).filter fun e => e.swap ∉ apm_a97j08_allEdges Q

noncomputable def apm_a97j08_angleStep (z p q : ℂ) : ℝ :=
  Complex.arg ((q - z) / (p - z))

noncomputable def apm_a97j08_edgeAngle (z shift : ℂ) (δ : ℝ)
    (e : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  apm_a97j08_angleStep z (apm_a97j08_gridVertex shift δ e.1)
    (apm_a97j08_gridVertex shift δ e.2)

/-- The closing edge list `(c₀,c₁), …, (cₙ₋₁,c₀)` of a cyclic vertex list. -/
def apm_a97j08_cycleEdges {V : Type*} (c : List V) : List (V × V) :=
  c.zip (c.rotate 1)

noncomputable def apm_a97j08_cycleSum {V : Type*} (f : V × V → ℝ) (c : List V) : ℝ :=
  ((apm_a97j08_cycleEdges c).map f).sum

def apm_a97j08_Balanced {V : Type*} [DecidableEq V] (E : Finset (V × V)) : Prop :=
  ∀ v : V, (E.filter fun e => e.1 = v).card = (E.filter fun e => e.2 = v).card

theorem apm_a97j08_clopen_separation_of_bounded_component
    (D : Set ℂ) (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ Dᶜ)
    (hzbounded : Bornology.IsBounded (connectedComponentIn Dᶜ z)) :
    apm_a97j08_ClopenSeparationFact D z := by
  sorry

theorem apm_a97j08_grid_region_construction
    (D : Set ℂ) {z : ℂ}
    (hsep : apm_a97j08_ClopenSeparationFact D z) :
    ∃ R δ : ℝ, ∃ A B : Set ℂ, ∃ U : Set ℂ,
      apm_a97j08_GridInput D z R δ A B ∧
      apm_a97j08_IsGridRegion A B R δ z U := by
  sorry


-- (A1) A segment missing `z` turns through opposite angles in the two directions.
theorem apm_a97j08_angleStep_swap {z p q : ℂ} (h : z ∉ segment ℝ p q) :
    apm_a97j08_angleStep z q p = -apm_a97j08_angleStep z p q := by
  sorry

-- (A2) A grid square missing `z` has total angle step zero.
theorem apm_a97j08_squareSum_outside {z shift : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (q : ℤ × ℤ) (hz : z ∉ apm_a97j08_gridSquare shift δ q) :
    ∑ e ∈ apm_a97j08_squareEdges q, apm_a97j08_edgeAngle z shift δ e = 0 := by
  sorry

-- (A3) A grid square with `z` in its interior has total angle step `2π`.
theorem apm_a97j08_squareSum_inside {z shift : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (q : ℤ × ℤ) (hz : z ∈ interior (apm_a97j08_gridSquare shift δ q)) :
    ∑ e ∈ apm_a97j08_squareEdges q, apm_a97j08_edgeAngle z shift δ e =
      2 * Real.pi := by
  sorry

-- (A4) Off the grid lines, every lattice edge angle is antisymmetric (from A1).
theorem apm_a97j08_edgeAngle_swap {z shift : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hre : z.re ∉ {x | ∃ k : ℤ, x = shift.re + k * δ})
    (him : z.im ∉ {y | ∃ k : ℤ, y = shift.im + k * δ})
    (hA1 : ∀ {p q : ℂ}, z ∉ segment ℝ p q →
      apm_a97j08_angleStep z q p = -apm_a97j08_angleStep z p q)
    (q : ℤ × ℤ) (e : (ℤ × ℤ) × (ℤ × ℤ)) (he : e ∈ apm_a97j08_squareEdges q) :
    apm_a97j08_edgeAngle z shift δ e.swap = -apm_a97j08_edgeAngle z shift δ e := by
  sorry

-- (C1) Interior edges cancel: summing an antisymmetric edge function over the
-- boundary edges equals summing it over all square boundaries.
theorem apm_a97j08_boundary_sum (Q : Finset (ℤ × ℤ))
    (f : (ℤ × ℤ) × (ℤ × ℤ) → ℝ)
    (hf : ∀ e ∈ apm_a97j08_allEdges Q, f e.swap = -f e) :
    ∑ e ∈ apm_a97j08_boundaryEdges Q, f e =
      ∑ q ∈ Q, ∑ e ∈ apm_a97j08_squareEdges q, f e := by
  sorry

-- (C2) The boundary edges are balanced (apply C1 to `[e.1 = v] - [e.2 = v]`).
theorem apm_a97j08_boundary_balanced (Q : Finset (ℤ × ℤ))
    (hC1 : ∀ f : (ℤ × ℤ) × (ℤ × ℤ) → ℝ,
      (∀ e ∈ apm_a97j08_allEdges Q, f e.swap = -f e) →
      ∑ e ∈ apm_a97j08_boundaryEdges Q, f e =
        ∑ q ∈ Q, ∑ e ∈ apm_a97j08_squareEdges q, f e) :
    apm_a97j08_Balanced (apm_a97j08_boundaryEdges Q) := by
  sorry

-- (C3a) A nonempty balanced finite edge set contains a simple directed cycle.
theorem apm_a97j08_exists_simple_cycle {V : Type*} [DecidableEq V]
    (E : Finset (V × V)) (hbal : apm_a97j08_Balanced E) (hne : E.Nonempty) :
    ∃ c : List V, c ≠ [] ∧ c.Nodup ∧ ∀ e ∈ apm_a97j08_cycleEdges c, e ∈ E := by
  sorry

-- (C3b) Peeling off simple cycles decomposes a balanced edge set (given C3a).
theorem apm_a97j08_cycle_decomposition {V : Type*} [DecidableEq V]
    (hC3a : ∀ E : Finset (V × V), apm_a97j08_Balanced E → E.Nonempty →
      ∃ c : List V, c ≠ [] ∧ c.Nodup ∧ ∀ e ∈ apm_a97j08_cycleEdges c, e ∈ E)
    (E : Finset (V × V)) (hbal : apm_a97j08_Balanced E) :
    ∃ cs : List (List V), (∀ c ∈ cs, c ≠ [] ∧ ∀ e ∈ apm_a97j08_cycleEdges c, e ∈ E) ∧
      ∀ f : V × V → ℝ, ∑ e ∈ E, f e = (cs.map (apm_a97j08_cycleSum f)).sum := by
  sorry

-- (E1) Boundary edges of the grid region lie in `D`.
theorem apm_a97j08_boundaryEdge_segment_subset
    (D : Set ℂ) {z : ℂ} {R δ : ℝ} {A B : Set ℂ}
    (hinput : apm_a97j08_GridInput D z R δ A B)
    (shift : ℂ) (Q : Finset (ℤ × ℤ))
    (hU_A : A ⊆ interior (⋃ q ∈ Q, apm_a97j08_gridSquare shift δ q))
    (hU_B : Disjoint (⋃ q ∈ Q, apm_a97j08_gridSquare shift δ q) B)
    (hU_R : (⋃ q ∈ Q, apm_a97j08_gridSquare shift δ q) ⊆ Metric.closedBall 0 R)
    (e : (ℤ × ℤ) × (ℤ × ℤ)) (he : e ∈ apm_a97j08_boundaryEdges Q) :
    segment ℝ (apm_a97j08_gridVertex shift δ e.1)
      (apm_a97j08_gridVertex shift δ e.2) ⊆ D := by
  sorry

-- (Z1) Exactly one selected square contains `z`, so the square sums total `2π`.
theorem apm_a97j08_square_total {z shift : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (Q : Finset (ℤ × ℤ)) (hzU : z ∈ ⋃ q ∈ Q, apm_a97j08_gridSquare shift δ q)
    (hre : z.re ∉ {x | ∃ k : ℤ, x = shift.re + k * δ})
    (him : z.im ∉ {y | ∃ k : ℤ, y = shift.im + k * δ})
    (hA2 : ∀ q, z ∉ apm_a97j08_gridSquare shift δ q →
      ∑ e ∈ apm_a97j08_squareEdges q, apm_a97j08_edgeAngle z shift δ e = 0)
    (hA3 : ∀ q, z ∈ interior (apm_a97j08_gridSquare shift δ q) →
      ∑ e ∈ apm_a97j08_squareEdges q, apm_a97j08_edgeAngle z shift δ e =
        2 * Real.pi) :
    ∑ q ∈ Q, ∑ e ∈ apm_a97j08_squareEdges q, apm_a97j08_edgeAngle z shift δ e =
      2 * Real.pi := by
  sorry

-- (L1) The straight segment from `p` to `q` has a continuous angle lift about
-- `z` whose total change is the angle step.
theorem apm_a97j08_segment_lift {z p q : ℂ} (h : z ∉ segment ℝ p q) :
    ∃ θ : C(unitInterval, ℝ),
      (∀ t : unitInterval, Complex.exp ((θ t : ℂ) * Complex.I) =
        (AffineMap.lineMap p q (t : ℝ) - z) /
          ((‖AffineMap.lineMap p q (t : ℝ) - z‖ : ℝ) : ℂ)) ∧
      θ 1 - θ 0 = apm_a97j08_angleStep z p q := by
  sorry

-- (L2) A closed polygon in `D` has a closed path in `D` with an angle lift
-- whose total change is the sum of the angle steps (given L1).
theorem apm_a97j08_polygon_path_lift (D : Set ℂ) {z : ℂ} (hz : z ∈ Dᶜ)
    (hL1 : ∀ {p q : ℂ}, z ∉ segment ℝ p q → ∃ θ : C(unitInterval, ℝ),
      (∀ t : unitInterval, Complex.exp ((θ t : ℂ) * Complex.I) =
        (AffineMap.lineMap p q (t : ℝ) - z) /
          ((‖AffineMap.lineMap p q (t : ℝ) - z‖ : ℝ) : ℂ)) ∧
      θ 1 - θ 0 = apm_a97j08_angleStep z p q)
    (c : List ℂ) (hc : c ≠ [])
    (hseg : ∀ e ∈ apm_a97j08_cycleEdges c, segment ℝ e.1 e.2 ⊆ D) :
    ∃ x : ℂ, ∃ p : Path x x, (∀ t, p t ∈ D) ∧ ∃ θ : C(unitInterval, ℝ),
      (∀ t : unitInterval, Complex.exp ((θ t : ℂ) * Complex.I) =
        (p t - z) / ((‖p t - z‖ : ℝ) : ℂ)) ∧
      θ 1 - θ 0 = apm_a97j08_cycleSum (fun e => apm_a97j08_angleStep z e.1 e.2) c := by
  sorry

-- (L3) A closed path in `D` whose angle lift about `z ∉ D` has nonzero total
-- change gives a noncontractible circle in `D`.
-- BEGIN SEAT AREA
theorem apm_a97j08_not_nullhomotopic_of_lift (D : Set ℂ) {z : ℂ} (hz : z ∈ Dᶜ)
    {x : ℂ} (p : Path x x) (hpD : ∀ t, p t ∈ D) (θ : C(unitInterval, ℝ))
    (hθ : ∀ t : unitInterval, Complex.exp ((θ t : ℂ) * Complex.I) =
        (p t - z) / ((‖p t - z‖ : ℝ) : ℂ))
    (hs : θ 1 ≠ θ 0) :
    ∃ cD : C(Circle, D), ¬ ContinuousMap.Nullhomotopic cD := by
  sorry
-- END SEAT AREA

lemma apm_a97j08_cycleEdges_map {V W : Type*} (g : V → W) (c : List V) :
    apm_a97j08_cycleEdges (c.map g) = (apm_a97j08_cycleEdges c).map (Prod.map g g) := by
  simp only [apm_a97j08_cycleEdges, ← List.map_rotate, List.map_prod_left_eq_zip]
  rw [List.zip_map]

/-- A bounded complementary component produces a noncontractible circle in
the domain subtype: separate, pixelate, sum the angle steps over the boundary
edges (total `2π`), split them into cycles, and take a cycle with nonzero sum. -/
lemma apm_a97j08_exists_noncontractible_circle_of_bounded_compl_component
    (D : Set ℂ) (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ Dᶜ)
    (hzbounded : Bornology.IsBounded (connectedComponentIn Dᶜ z)) :
    ∃ c : C(Circle, D),
      ¬ ContinuousMap.Nullhomotopic c := by
  have hsep := apm_a97j08_clopen_separation_of_bounded_component
    D hD_open hz hzbounded
  obtain ⟨R, δ, A, B, U, hinput, shift, Q, hU, hzU, hAU, hUB, hUR, hre, him⟩ :=
    apm_a97j08_grid_region_construction D hsep
  have hδ : 0 < δ := hinput.2.1
  subst hU
  set f := apm_a97j08_edgeAngle z shift δ
  have hanti : ∀ e ∈ apm_a97j08_allEdges Q, f e.swap = -f e := by
    intro e he
    obtain ⟨q, -, heq⟩ := Finset.mem_biUnion.mp he
    exact apm_a97j08_edgeAngle_swap hδ hre him
      (fun h => apm_a97j08_angleStep_swap h) q e heq
  have hC1 := apm_a97j08_boundary_sum Q
  have hbal := apm_a97j08_boundary_balanced Q (fun g hg => hC1 g hg)
  obtain ⟨cs, hcs, hsum⟩ := apm_a97j08_cycle_decomposition
    (fun E hE hne => apm_a97j08_exists_simple_cycle E hE hne) _ hbal
  have htotal : (cs.map (apm_a97j08_cycleSum f)).sum = 2 * Real.pi := by
    rw [← hsum f, hC1 f hanti]
    exact apm_a97j08_square_total hδ Q (interior_subset hzU) hre him
      (fun q hq => apm_a97j08_squareSum_outside hδ q hq)
      (fun q hq => apm_a97j08_squareSum_inside hδ q hq)
  obtain ⟨c, hc, hcne⟩ : ∃ c ∈ cs, apm_a97j08_cycleSum f c ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : (cs.map (apm_a97j08_cycleSum f)).sum = 0 :=
      List.sum_eq_zero fun x hx => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact hall c hc
    rw [this] at htotal
    linarith [Real.pi_pos]
  obtain ⟨hcne', hcE⟩ := hcs c hc
  set g := apm_a97j08_gridVertex shift δ
  have hseg : ∀ e ∈ apm_a97j08_cycleEdges (c.map g), segment ℝ e.1 e.2 ⊆ D := by
    intro e he
    rw [apm_a97j08_cycleEdges_map] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact apm_a97j08_boundaryEdge_segment_subset D hinput shift Q hAU hUB hUR e'
      (hcE e' he')
  obtain ⟨x, p, hpD, θ, hθ, hdisp⟩ := apm_a97j08_polygon_path_lift D hz
    (fun h => apm_a97j08_segment_lift h) (c.map g) (by simpa using hcne') hseg
  refine apm_a97j08_not_nullhomotopic_of_lift D hz p hpD θ hθ ?_
  intro h01
  apply hcne
  have : apm_a97j08_cycleSum (fun e => apm_a97j08_angleStep z e.1 e.2) (c.map g) =
      apm_a97j08_cycleSum f c := by
    simp only [apm_a97j08_cycleSum, apm_a97j08_cycleEdges_map, List.map_map]
    rfl
  rw [← this, ← hdisp, h01, sub_self]

/-- The genuinely planar obstruction missing from Mathlib: a bounded
component of the complement of an open plane domain produces a loop in the
domain which cannot be contracted while remaining in the domain.  This is the
Jordan/winding-number input; the deduction from it and simple connectivity is
purely the fundamental-groupoid API and is proved below. -/
lemma apm_a97j08_exists_essential_loop_of_bounded_compl_component
    (D : Set ℂ)
    (hD_open : IsOpen D)
    {z : ℂ} (hz : z ∈ Dᶜ)
    (hzbounded : Bornology.IsBounded (connectedComponentIn Dᶜ z)) :
    ∃ x : ℂ, ∃ p : Path x x,
      (∀ t, p t ∈ D) ∧ ¬ apm_a97j08_LoopNullhomotopicIn D p := by
  obtain ⟨c, hc⟩ :=
    apm_a97j08_exists_noncontractible_circle_of_bounded_compl_component
      D hD_open hz hzbounded
  exact apm_a97j08_exists_essential_loop_of_subtype_circle D c hc

/-- Every complementary component of an open simply connected plane domain
is unbounded.  Once the planar essential-loop obstruction is exposed, this is
an immediate application of Mathlib's characterization of simple
connectivity by nullhomotopies of all loops. -/
lemma apm_a97j08_compl_component_unbounded_of_isSimplyConnected
    (D : Set ℂ)
    (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D) :
    ∀ z ∈ Dᶜ,
      ¬ Bornology.IsBounded (connectedComponentIn Dᶜ z) := by
  intro z hz hzbounded
  obtain ⟨x, p, hpD, hpessential⟩ :=
    apm_a97j08_exists_essential_loop_of_bounded_compl_component
      D hD_open hz hzbounded
  apply hpessential
  exact apm_a97j08_loopNullhomotopicIn_of_isSimplyConnected
    hD_simplyConnected p hpD

/-- The remaining planar-topology interface: a simple closed curve contained
in an open simply connected planar domain has its encoded bounded side, and
hence its closure, in that domain.  Mathlib currently has no Jordan separation
or planar complement-connectivity theorem from which to derive this. -/
lemma apm_a97j08_closure_curveInterior_subset_of_simplyConnected
    (D : Set ℂ) (γ : ℝ → ℂ)
    (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_closed : γ 0 = γ 1)
    (hγ_simple : Set.InjOn γ (Ico (0 : ℝ) 1))
    (hγ_rectifiable : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D) :
    closure (apm_a97j08_curveInterior γ) ⊆ D := by
  have _hclosed : γ 0 = γ 1 := hγ_closed
  have _hsimple : Set.InjOn γ (Ico (0 : ℝ) 1) := hγ_simple
  have _hrectifiable : BoundedVariationOn γ (Icc (0 : ℝ) 1) := hγ_rectifiable
  exact apm_a97j08_closure_curveInterior_subset_of_compl_components_unbounded
    hγ_cont hγD
      (apm_a97j08_compl_component_unbounded_of_isSimplyConnected
        D hD_open hD_simplyConnected)

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
  have hUD := apm_a97j08_closure_curveInterior_subset_of_simplyConnected
    D γ hD_open hD_simplyConnected hγ_cont hγ_closed hγ_simple
      hγ_rectifiable hγD
  exact apm_a97j08_eventual_zeroCount_of_closure_subset
    D γ F g hD_open hD_simplyConnected.isPathConnected.isConnected.isPreconnected
    hγ_cont hγD hF_analytic hF_tendsto hg_ne hUD

#print axioms apm_a97j08
