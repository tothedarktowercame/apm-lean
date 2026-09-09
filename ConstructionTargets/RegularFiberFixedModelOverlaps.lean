import ConstructionTargets.RegularFiberFixedModel
open Set
open scoped ContDiff Topology
noncomputable section
namespace ConstructionTargets.RegularFiberFixedModelOverlaps
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
abbrev Model := RegularFiberFixedModel.Model (E := E) (F := F)
structure FiberChart (f : E → F) (c : F) where
  chart : OpenPartialHomeomorph {x : E // f x = c} (Model (E := E) (F := F))
  ambient : Set E
  forward : E → Model (E := E) (F := F)
  backward : Model (E := E) (F := F) → E
  source_eq : chart.source = Subtype.val ⁻¹' ambient
  forward_eq : ∀ x, chart x = forward x.val
  backward_eq : ∀ z ∈ chart.target, (chart.symm z).val = backward z
  forward_smooth : ContDiffOn ℝ ∞ forward ambient
  backward_smooth : ContDiffOn ℝ ∞ backward chart.target

 theorem exists_chart (f : E → F) (c : F) (hsm : ContDiff ℝ ∞ f)
    (x : {x : E // f x = c}) (hs : Function.Surjective (fderiv ℝ f x.val)) :
    ∃ d : FiberChart f c, x ∈ d.chart.source := by
  classical
  let L := fderiv ℝ f x.val
  obtain ⟨e, hx, he0, hfst, hfor, hback, hopen, hz, himage, hsmg, hder⟩ :=
    SmoothRegularFiberCoordinates.exists_smooth_fiber_slice f L x.val
      (RegularFiberChart.smooth_derivative hsm) hs hsm
  let A := RegularFiberFixedModel.kernelEquiv L hs
  let V : Set (Model (E := E) (F := F)) := {z | (0, A.symm z) ∈ e.target}
  let g : Model (E := E) (F := F) → E := fun z => e.symm (0, A.symm z)
  have hg (z) (hz : z ∈ V) : f (g z) = c := by
    have h := congrArg Prod.fst (e.right_inv hz)
    rw [hfst] at h
    change f (g z) - f x.val = 0 at h
    exact (sub_eq_zero.mp h).trans x.property
  have pair (y : {y : E // f y = c}) : e y.val = (0,(e y.val).2) := by
    apply Prod.ext
    · simp [hfst, y.property, x.property]
    · rfl
  let inv : Model (E := E) (F := F) → {y : E // f y = c} :=
    fun z => if hz : z ∈ V then ⟨g z, hg z hz⟩ else x
  have hinv (z) (hz : z ∈ V) : (inv z).val = g z := by simp [inv, hz]
  let p : OpenPartialHomeomorph {y : E // f y = c} (Model (E := E) (F := F)) :=
    { toFun := fun y => A (e y.val).2
      invFun := inv
      source := {y | y.val ∈ e.source}
      target := V
      map_source' := by
        intro y hy
        change (0, A.symm (A (e y.val).2)) ∈ e.target
        simpa only [A.symm_apply_apply, ← pair y] using e.map_source hy
      map_target' := by
        intro z hz
        change (inv z).val ∈ e.source
        rw [hinv z hz]
        exact e.map_target hz
      left_inv' := by
        intro y hy
        apply Subtype.ext
        have hv : A (e y.val).2 ∈ V := by
          change (0,A.symm (A (e y.val).2)) ∈ e.target
          simpa only [A.symm_apply_apply, ← pair y] using e.map_source hy
        rw [hinv _ hv]
        change e.symm (0,A.symm (A (e y.val).2)) = y.val
        rw [A.symm_apply_apply, ← pair y]
        exact e.left_inv hy
      right_inv' := by
        intro z hz
        change A (e (inv z).val).2 = z
        rw [hinv z hz]
        change A (e (e.symm (0,A.symm z))).2 = z
        rw [e.right_inv hz]
        exact A.apply_symm_apply z
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := hopen.preimage A.symm.continuous
      continuousOn_toFun := A.continuous.comp_continuousOn
        ((e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h)).snd)
      continuousOn_invFun := by
        apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        apply (e.symm.continuousOn.comp
          (continuous_const.prodMk A.symm.continuous).continuousOn (fun _ h => h)).congr
        intro z hz
        exact hinv z hz }
  refine ⟨⟨p,e.source,(fun y => A (e y).2),g,rfl,(fun _ => rfl),hinv,?_,?_⟩,hx⟩
  · exact A.contDiff.comp_contDiffOn hfor.snd
  · exact hsmg.comp A.symm.contDiff.contDiffOn (fun _ h => h)

 omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] in
 theorem overlap_smooth (f : E → F) (c : F) (d d' : FiberChart f c) :
    ContDiffOn ℝ ∞ (d.chart.symm.trans d'.chart)
      (d.chart.symm.trans d'.chart).source := by
  let S := (d.chart.symm.trans d'.chart).source
  have hb : ContDiffOn ℝ ∞ d.backward S :=
    d.backward_smooth.mono (fun z hz => hz.1)
  have h : ContDiffOn ℝ ∞ (d'.forward ∘ d.backward) S := d'.forward_smooth.comp hb (by
      intro z hz
      rw [← d.backward_eq z hz.1]
      exact (congrArg (fun s => d.chart.symm z ∈ s) d'.source_eq).mp hz.2)
  apply h.congr
  intro z hz
  change d'.chart (d.chart.symm z) = d'.forward (d.backward z)
  rw [d'.forward_eq, d.backward_eq z hz.1]

 omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] in
 theorem backward_image (f : E → F) (c : F) (d : FiberChart f c) :
    d.backward '' d.chart.target = d.ambient ∩ {y | f y = c} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← d.backward_eq z hz]
    refine ⟨?_, (d.chart.symm z).property⟩
    have h := d.chart.map_target hz
    rwa [d.source_eq] at h
  · rintro ⟨hy, hc⟩
    let x : {x : E // f x = c} := ⟨y,hc⟩
    have hx : x ∈ d.chart.source := by rw [d.source_eq]; exact hy
    refine ⟨d.chart x, d.chart.map_source hx, ?_⟩
    rw [← d.backward_eq _ (d.chart.map_source hx), d.chart.left_inv hx]

 omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] in
 theorem overlap_formula (f : E → F) (c : F) (d d' : FiberChart f c)
    (z : Model (E := E) (F := F))
    (hz : z ∈ (d.chart.symm.trans d'.chart).source) :
    (d.chart.symm.trans d'.chart) z = d'.forward (d.backward z) := by
  change d'.chart (d.chart.symm z) = _
  rw [d'.forward_eq, d.backward_eq z hz.1]

 theorem exists_cover (f : E → F) (c : F) (hsm : ContDiff ℝ ∞ f)
    (hreg : ∀ x, f x = c → Function.Surjective (fderiv ℝ f x)) :
    ∃ d : {x : E // f x = c} → FiberChart f c,
      (∀ x, x ∈ (d x).chart.source) ∧
      (∀ x y, ContDiffOn ℝ ∞ ((d x).chart.symm.trans (d y).chart)
        ((d x).chart.symm.trans (d y).chart).source) := by
  classical
  choose d hd using fun x : {x : E // f x = c} => exists_chart f c hsm x (hreg x x.property)
  exact ⟨d,hd,fun x y => overlap_smooth f c (d x) (d y)⟩
#print axioms backward_image
#print axioms overlap_formula
#print axioms exists_chart
#print axioms overlap_smooth
#print axioms exists_cover
end ConstructionTargets.RegularFiberFixedModelOverlaps
