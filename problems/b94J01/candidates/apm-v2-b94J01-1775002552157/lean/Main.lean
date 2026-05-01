import Mathlib

noncomputable section

namespace ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1775002552157.Main

/-! # APM b94J01: FTFAG, cyclic criterion, finite subgroups of fields -/

-- Part (c): CLOSED — finite subgroup of K* is cyclic
-- Mathlib: instance [IsDomain R] [Finite Rˣ] : IsCyclic Rˣ
-- (in Mathlib.RingTheory.IntegralDomain)
-- For a field K (which is an integral domain), any finite subgroup of Kˣ is cyclic.

-- The full unit group of a finite field is cyclic:
instance units_cyclic_of_field {K : Type*} [Field K] [Finite Kˣ] : IsCyclic Kˣ :=
  inferInstance

-- A finite subgroup of units of a field is cyclic:
instance subgroup_cyclic_of_field {K : Type*} [Field K] (G : Subgroup Kˣ) [Finite G] :
    IsCyclic G :=
  inferInstance

-- Part (b): ℤ/mℤ × ℤ/nℤ cyclic iff coprime
-- Mathlib has the general characterization via AddGroup.isAddCyclic_prod_iff.
-- The specific ZMod instance: for coprime m n, ZMod (m*n) ≃+ ZMod m × ZMod n (CRT).
-- Since ZMod (m*n) is cyclic, the product is cyclic when m,n coprime.
-- Conversely: if not coprime, gcd > 1, and every element has order dividing lcm(m,n) < m*n,
-- so the product has fewer than m*n distinct orders → not cyclic.

-- The Mathlib iff:
#check @AddGroup.isAddCyclic_prod_iff

end ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1775002552157.Main
