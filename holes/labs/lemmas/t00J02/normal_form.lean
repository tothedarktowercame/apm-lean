import Mathlib
import ConstructionTargets.t00J02Closure

open Set
open scoped Manifold Topology ContDiff

noncomputable section
set_option autoImplicit false

namespace ConstructionTargets.T00J02Closure

/-- Linear core of the transverse normal-form argument.  If the source
derivative together with the curve derivative spans the target, the
straightening derivative sends the curve into the kernel of the normal
coordinate, and that normal coordinate is nonzero somewhere after
straightening, then its composite with the source derivative is nonzero. -/
theorem transverse_normal_component_ne_zero
    {R E F G H K : Type}
    [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    [AddCommGroup H] [Module R H]
    [AddCommGroup K] [Module R K]
    (A : E →ₗ[R] G) (C : F →ₗ[R] G)
    (B : G →ₗ[R] H) (q : H →ₗ[R] K)
    (hspan : LinearMap.range A ⊔ LinearMap.range C = ⊤)
    (hcurve : ∀ v, q (B (C v)) = 0)
    (hnormal : ∃ y, q (B y) ≠ 0) :
    q.comp (B.comp A) ≠ 0 := by
  rintro hzero
  obtain ⟨y, hy⟩ := hnormal
  have hyspan : y ∈ LinearMap.range A ⊔ LinearMap.range C := by
    rw [hspan]
    trivial
  rw [Submodule.mem_sup] at hyspan
  obtain ⟨a, ha, c, hc, rfl⟩ := hyspan
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hc
  apply hy
  rw [map_add, map_add, hcurve, add_zero]
  have hz := LinearMap.congr_fun hzero u
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hz

/-- An injective endomorphism of a finite-dimensional space cannot send the
whole space into the kernel of a nonzero linear functional. -/
theorem exists_normal_value_of_ker_eq_bot
    {K V W : Type}
    [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (B : V →ₗ[K] V) (q : V →ₗ[K] W)
    (hB : LinearMap.ker B = ⊥) (hq : q ≠ 0) :
    ∃ y, q (B y) ≠ 0 := by
  have hBinj : Function.Injective B := LinearMap.ker_eq_bot.mp hB
  have hBsurj : Function.Surjective B :=
    LinearMap.injective_iff_surjective.mp hBinj
  have hqvalue : ∃ w, q w ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hq
    ext w
    exact hall w
  obtain ⟨w, hw⟩ := hqvalue
  obtain ⟨y, rfl⟩ := hBsurj w
  exact ⟨y, hw⟩

#print axioms transverse_normal_component_ne_zero
#print axioms exists_normal_value_of_ker_eq_bot

end ConstructionTargets.T00J02Closure
