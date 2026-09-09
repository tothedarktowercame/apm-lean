import ConstructionTargets.SardGenuineSmoothManifoldVector
open Set MeasureTheory
open scoped ContDiff Manifold



/-! # APM t93A04: a line with smooth inverse image

## Statement repairs

None.

## Encoding notes

The domain is a genuine finite-dimensional Mathlib smooth manifold. A smooth
inverse image is certified by transversality to an actual affine line: at each
point mapping to the line, the image of the manifold derivative together with
the line direction spans `ℝ³`. This is the concrete regular-preimage
criterion, with the subset pinned to the actual set-theoretic inverse image.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t93a04_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t93a04_Model (n : ℕ) := 𝓘(ℝ, apm_t93a04_E n)
abbrev apm_t93a04_Point := EuclideanSpace ℝ (Fin 3)

def apm_t93a04_line (p v : apm_t93a04_Point) : Set apm_t93a04_Point :=
  {x | ∃ t : ℝ, x = p + t • v}

def apm_t93a04_IsSmoothLinePreimage
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (apm_t93a04_E n) M]
    (f : M → apm_t93a04_Point) (ℓ : Set apm_t93a04_Point) (S : Set M) : Prop :=
  S = f ⁻¹' ℓ ∧
    ∃ (p v : apm_t93a04_Point),
      v ≠ 0 ∧ ℓ = apm_t93a04_line p v ∧
      ∀ x : M, f x ∈ ℓ →
        LinearMap.range
            (mfderiv (apm_t93a04_Model n) (𝓘(ℝ, apm_t93a04_Point)) f x).toLinearMap ⊔
          Submodule.span ℝ ({v} : Set apm_t93a04_Point) = ⊤

@[simp] lemma apm_t93a04_isSmoothLinePreimage_preimage_iff
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (apm_t93a04_E n) M]
    (f : M → apm_t93a04_Point) (ℓ : Set apm_t93a04_Point) :
    apm_t93a04_IsSmoothLinePreimage (n := n) f ℓ (f ⁻¹' ℓ) ↔
      ∃ (p v : apm_t93a04_Point),
        v ≠ 0 ∧ ℓ = apm_t93a04_line p v ∧
        ∀ x : M, f x ∈ ℓ →
          LinearMap.range
              (mfderiv (apm_t93a04_Model n)
                (modelWithCornersSelf ℝ apm_t93a04_Point) f x).toLinearMap ⊔
            Submodule.span ℝ ({v} : Set apm_t93a04_Point) = ⊤ := by
  simp [apm_t93a04_IsSmoothLinePreimage]

/-- The linear-algebra bridge in the projection proof: if projection along
`v` is surjective on the derivative range, that range together with `v`
spans the target. -/
lemma apm_t93a04_range_sup_span_eq_top_of_projection_surjective
    {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module ℝ E] [Module ℝ F] [Module ℝ G]
    (L : E →ₗ[ℝ] F) (q : F →ₗ[ℝ] G) (v : F)
    (hker : LinearMap.ker q = Submodule.span ℝ ({v} : Set F))
    (hsurj : Function.Surjective (q.comp L)) :
    LinearMap.range L ⊔ Submodule.span ℝ ({v} : Set F) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨y, hy⟩ := hsurj (q x)
  have hd : x - L y ∈ Submodule.span ℝ ({v} : Set F) := by
    rw [← hker, LinearMap.mem_ker]
    simpa [LinearMap.comp_apply] using congrArg (fun z => q x - z) hy
  rw [← add_sub_cancel (L y) x]
  exact Submodule.add_mem_sup ⟨y, rfl⟩ hd

def apm_t93a04_lineDirection : apm_t93a04_Point :=
  EuclideanSpace.single 0 1

lemma apm_t93a04_lineDirection_ne_zero : apm_t93a04_lineDirection ≠ 0 := by
  intro h
  have h0 := congrFun (congrArg WithLp.ofLp h) 0
  simpa [apm_t93a04_lineDirection] using h0


namespace T93A04Closure
abbrev P2 := EuclideanSpace ℝ (Fin 2)
def proj : apm_t93a04_Point →L[ℝ] P2 :=
 (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
   (ContinuousLinearMap.pi (fun i : Fin 2 => EuclideanSpace.proj i.succ))
@[simp] theorem proj_apply (x : apm_t93a04_Point) (i : Fin 2) : proj x i = x i.succ := rfl
 theorem proj_surjective : Function.Surjective proj := by
 intro b
 refine ⟨WithLp.toLp 2 ![0,b 0,b 1],?_⟩
 ext i
 fin_cases i <;> rfl
 theorem proj_ker : LinearMap.ker proj.toLinearMap =
    Submodule.span ℝ ({apm_t93a04_lineDirection} : Set apm_t93a04_Point) := by
 ext x
 rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
 constructor
 · intro hx
   have h1 := congrArg (fun b : P2 => b 0) hx
   have h2 := congrArg (fun b : P2 => b 1) hx
   change x 1 = 0 at h1
   change x 2 = 0 at h2
   refine ⟨x 0,?_⟩
   ext i
   fin_cases i <;> simp_all [apm_t93a04_lineDirection]
 · rintro ⟨c,rfl⟩
   ext i
   fin_cases i <;> simp [apm_t93a04_lineDirection]
end T93A04Closure
theorem apm_t93a04 :
    ∀ (n : ℕ) (M : Type)
      [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [ChartedSpace (apm_t93a04_E n) M]
      [IsManifold (apm_t93a04_Model n) ∞ M]
      (f : M → apm_t93a04_Point),
      ContMDiff (apm_t93a04_Model n) (𝓘(ℝ, apm_t93a04_Point)) ∞ f →
      ∃ ℓ : Set apm_t93a04_Point,
        apm_t93a04_IsSmoothLinePreimage (n := n) f ℓ (f ⁻¹' ℓ) := by
  intro n M hT hT2 hSC hCh hMan f hf
  let q := T93A04Closure.proj
  have hq : ContMDiff (𝓘(ℝ,apm_t93a04_Point)) (𝓘(ℝ,T93A04Closure.P2)) ∞ q :=
    q.contDiff.contMDiff
  have hg := hq.comp hf
  have hn := T93A04ManifoldWork.null_critical (volume : Measure T93A04Closure.P2) (q ∘ f) hg
  obtain ⟨b,hb⟩ : ∃ b : T93A04Closure.P2, b ∉
      (q ∘ f) '' {y | ¬ Function.Surjective
        (mfderiv (apm_t93a04_Model n) (𝓘(ℝ,T93A04Closure.P2)) (q ∘ f) y)} := by
    by_contra h
    have he : (q ∘ f) '' {y | ¬ Function.Surjective
        (mfderiv (apm_t93a04_Model n) (𝓘(ℝ,T93A04Closure.P2)) (q ∘ f) y)} = univ := by
      apply Set.eq_univ_of_forall
      simpa using h
    rw [he] at hn
    exact (NeZero.ne ((volume : Measure T93A04Closure.P2) univ)) hn
  obtain ⟨p,hp⟩ := T93A04Closure.proj_surjective b
  refine ⟨apm_t93a04_line p apm_t93a04_lineDirection, rfl,
    p,apm_t93a04_lineDirection,apm_t93a04_lineDirection_ne_zero,rfl,?_⟩
  intro x hx
  obtain ⟨t,ht⟩ := hx
  have hv : q apm_t93a04_lineDirection = 0 := by
    change apm_t93a04_lineDirection ∈ LinearMap.ker T93A04Closure.proj.toLinearMap
    rw [T93A04Closure.proj_ker]
    exact Submodule.subset_span (by simp)
  have hxb : q (f x) = b := by rw [ht,map_add,map_smul,hv,smul_zero,add_zero]; exact hp
  have hs : Function.Surjective
      (mfderiv (apm_t93a04_Model n) (𝓘(ℝ,T93A04Closure.P2)) (q ∘ f) x) := by
    by_contra hh
    exact hb ⟨x,hh,hxb⟩
  have hd := mfderiv_comp x (hq.mdifferentiable (by simp) (f x)) (hf.mdifferentiable (by simp) x)
  rw [mfderiv_eq_fderiv, q.fderiv] at hd
  rw [hd] at hs
  exact apm_t93a04_range_sup_span_eq_top_of_projection_surjective
    (mfderiv (apm_t93a04_Model n) (𝓘(ℝ,apm_t93a04_Point)) f x).toLinearMap
    q.toLinearMap apm_t93a04_lineDirection T93A04Closure.proj_ker hs
#print axioms apm_t93a04
