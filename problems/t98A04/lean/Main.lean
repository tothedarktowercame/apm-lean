import Mathlib

/-!
# APM t98A04

## Statement repairs

Part (c) prints `ι : S² → S²`, but the composite `π ∘ ι` is defined only
when `ι : S² → S³`. The codomain of `ι` is repaired to `S³`.

## Encoding questions

Mathlib has no smooth-manifold structure for complex projectivization and
hence no packaged submersion predicate for the Hopf map. Submersivity is the
single opaque typed predicate below. The unit sphere in `ℂ²`, `ℂP¹` with its
quotient topology, the projectivization map, its exact circle-orbit fibers,
the fiber over `[1,0]`, and the continuous-section assertion are explicit.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev apm_t98a04_C2 := EuclideanSpace ℂ (Fin 2)
abbrev apm_t98a04_S3 :=
  {z : apm_t98a04_C2 // z ≠ 0 ∧ ‖z‖ = 1}
abbrev apm_t98a04_CP1 := Projectivization ℂ apm_t98a04_C2

noncomputable instance : TopologicalSpace apm_t98a04_CP1 :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance

def apm_t98a04_hopf (z : apm_t98a04_S3) : apm_t98a04_CP1 :=
  Projectivization.mk ℂ z.1 z.2.1

def apm_t98a04_e0 : {z : apm_t98a04_C2 // z ≠ 0} :=
  ⟨WithLp.toLp 2 ![(1 : ℂ), 0], by
    intro h
    have h0 := congrArg (fun z : apm_t98a04_C2 ↦ z 0) h
    simpa using h0⟩

def apm_t98a04_p10 : apm_t98a04_CP1 :=
  Projectivization.mk' ℂ apm_t98a04_e0

def apm_t98a04_fiber (p : apm_t98a04_CP1) : Set apm_t98a04_S3 :=
  {z | apm_t98a04_hopf z = p}

def apm_t98a04_circleOrbit (z : apm_t98a04_S3) : Set apm_t98a04_S3 :=
  {w | ∃ u : Circle, w.1 = (u : ℂ) • z.1}

opaque apm_t98a04_IsSubmersion
    (f : apm_t98a04_S3 → apm_t98a04_CP1) : Prop

theorem apm_t98a04 :
    Continuous apm_t98a04_hopf ∧
    apm_t98a04_IsSubmersion apm_t98a04_hopf ∧
    apm_t98a04_fiber apm_t98a04_p10 = {z | z.1 1 = 0} ∧
    (∀ p : apm_t98a04_CP1,
      Nonempty (apm_t98a04_fiber p ≃ₜ Circle) ∧
      ∀ z ∈ apm_t98a04_fiber p,
        apm_t98a04_fiber p = apm_t98a04_circleOrbit z) ∧
    ¬∃ i : apm_t98a04_CP1 → apm_t98a04_S3,
      Continuous i ∧ ∀ p, apm_t98a04_hopf (i p) = p := by
  sorry
