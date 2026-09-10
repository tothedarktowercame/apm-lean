import ConstructionTargets.ManifoldTargetFiberChartExtension
import ConstructionTargets.FiberPredicateTransfer
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.ManifoldTargetRegularFiberCharts
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
abbrev Model := RegularFiberFixedModelOverlaps.Model (E := E) (F := F)
structure FiberChart (f : M → N) (c : N) where
  chart : OpenPartialHomeomorph {x // f x = c} (Model (E := E) (F := F))
  ambient : Set M
  forward : M → Model (E := E) (F := F)
  backward : Model (E := E) (F := F) → M
  source_eq : chart.source = Subtype.val ⁻¹' ambient
  forward_eq : ∀ x ∈ chart.source, chart x = forward x.val
  backward_eq : ∀ z ∈ chart.target, (chart.symm z).val = backward z
  forward_smooth : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,Model (E := E) (F := F)) ∞ forward ambient
  backward_smooth : ContMDiffOn 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) ∞ backward chart.target

theorem exists_chart (f : M → N) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (x : M)
    (hs : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) :
    ∃ d : FiberChart (E := E) (F := F) f (f x), (⟨x,rfl⟩ : {y // f y = f x}) ∈ d.chart.source := by
  obtain ⟨g,hg,V,hV,hxV,hVt,_,_,hiff,hxg,d,hd⟩ :=
    ManifoldTargetFiberChartExtension.exists_extension_chart f hf x hs
  let e := chartAt E x
  have hVe : V ⊆ e.target := fun z hz => (hVt hz).1
  let P := fun y => f y = f x
  let Q := fun z => g z = (chartAt F (f x)) (f x)
  let p := FiberPredicateTransfer.transfer e P Q V hV hVe hiff
    ⟨x,rfl⟩ (mem_chart_source E x) hxV
  have hp (u) (hu : u ∈ p.source) : (p u).val = e u.val :=
    FiberPredicateTransfer.forward_eq e P Q V hV hVe hiff
      ⟨x,rfl⟩ (mem_chart_source E x) hxV u hu
  have hpb (v : {y // g y = (chartAt F (f x)) (f x)}) (hv : v.val ∈ V) : (p.symm v).val = e.symm v.val :=
    FiberPredicateTransfer.backward_eq e P Q V hV hVe hiff
      ⟨x,rfl⟩ (mem_chart_source E x) hxV v hv
  have hps : p.source = {u | u.val ∈ e.source ∧ e u.val ∈ V} :=
    FiberPredicateTransfer.source_eq e P Q V hV hVe hiff _ _ _
  have hpt : p.target = Subtype.val ⁻¹' V :=
    FiberPredicateTransfer.target_eq e P Q V hV hVe hiff _ _ _
  let q := p.trans d.chart
  let A : Set M := {y | y ∈ e.source ∧ e y ∈ V ∧ e y ∈ d.ambient}
  have hsource : q.source = Subtype.val ⁻¹' A := by
    ext u
    change (u ∈ p.source ∧ p u ∈ d.chart.source) ↔ _
    rw [d.source_eq]
    constructor
    · rintro ⟨hu,hd⟩
      change (p u).val ∈ d.ambient at hd
      rw [hp u hu] at hd
      rw [hps] at hu
      exact ⟨hu.1,hu.2,hd⟩
    · rintro ⟨hu,hv,hd⟩
      have huV : u ∈ p.source := by rw [hps]; exact ⟨hu,hv⟩
      refine ⟨huV,?_⟩
      change (p u).val ∈ d.ambient
      rw [hp u huV]
      exact hd
  have htarget (z) (hz : z ∈ q.target) : d.backward z ∈ V := by
    have hv : (d.chart.symm z).val ∈ V := by
      have hh := hz.2
      change d.chart.symm z ∈ p.target at hh
      rwa [hpt] at hh
    rw [d.backward_eq z hz.1] at hv
    exact hv
  refine ⟨⟨q,A,(d.forward ∘ e),(e.symm ∘ d.backward),hsource,?_,?_,?_,?_⟩,?_⟩
  · intro u hu
    change d.chart (p u) = d.forward (e u.val)
    rw [d.forward_eq, hp u hu.1]
  · intro z hz
    change (p.symm (d.chart.symm z)).val = e.symm (d.backward z)
    have hv : (d.chart.symm z).val ∈ V := by
      have hh := hz.2
      change d.chart.symm z ∈ p.target at hh
      rwa [hpt] at hh
    rw [hpb _ hv, d.backward_eq z hz.1]
  · have hE : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e A :=
      contMDiffOn_chart.mono (fun y hy => hy.1)
    exact d.forward_smooth.contMDiffOn.comp hE (fun y hy => hy.2.2)
  · have hB : ContMDiffOn 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) ∞ d.backward q.target :=
      (d.backward_smooth.mono (fun z hz => hz.1)).contMDiffOn
    exact contMDiffOn_chart_symm.comp hB (fun z hz => hVe (htarget z hz))
  · change (⟨x,rfl⟩ : {y // f y = f x}) ∈ p.source ∧ p ⟨x,rfl⟩ ∈ d.chart.source
    have hc : (⟨x,rfl⟩ : {y // f y = f x}) ∈ p.source := by
      rw [hps]
      exact ⟨mem_chart_source E x,hxV⟩
    refine ⟨hc,?_⟩
    have hpcenter : p ⟨x,rfl⟩ = ⟨e x,hxg⟩ := Subtype.ext (hp _ hc)
    rw [hpcenter]
    exact hd

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] [TopologicalSpace N] [ChartedSpace F N] in
theorem overlap_smooth (f : M → N) (c : N) (d d' : FiberChart (E := E) (F := F) f c) :
    ContDiffOn ℝ ∞ (d.chart.symm.trans d'.chart) (d.chart.symm.trans d'.chart).source := by
  let S := (d.chart.symm.trans d'.chart).source
  have hb := d.backward_smooth.mono (show S ⊆ d.chart.target from fun z hz => hz.1)
  have h := d'.forward_smooth.comp hb (by
    intro z hz
    change d.backward z ∈ d'.ambient
    rw [← d.backward_eq z hz.1]
    exact (congrArg (fun s => d.chart.symm z ∈ s) d'.source_eq).mp hz.2)
  apply h.contDiffOn.congr
  intro z hz
  change d'.chart (d.chart.symm z) = d'.forward (d.backward z)
  have hz' : d.chart.symm z ∈ d'.chart.source := hz.2
  rw [d'.forward_eq (d.chart.symm z) hz', d.backward_eq z hz.1]

theorem exists_cover (f : M → N) (c : N)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hr : ∀ x, f x = c → Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) :
    ∃ d : {x // f x = c} → FiberChart (E := E) (F := F) f c,
      (∀ x, x ∈ (d x).chart.source) ∧
      ∀ x y, ContDiffOn ℝ ∞ ((d x).chart.symm.trans (d y).chart)
        ((d x).chart.symm.trans (d y).chart).source := by
  have h (x : {x // f x = c}) : ∃ d : FiberChart (E := E) (F := F) f c, x ∈ d.chart.source := by
    rcases x with ⟨x,hx⟩
    subst c
    exact exists_chart f hf x (hr x rfl)
  choose d hd using h
  exact ⟨d,hd,fun x y => overlap_smooth f c (d x) (d y)⟩
#print axioms exists_chart
#print axioms overlap_smooth
#print axioms exists_cover
end ConstructionTargets.ManifoldTargetRegularFiberCharts
