/-
! # APM a96A07: Injective on the boundary implies injective on the disk

g is analytic in a neighborhood of the closed unit disk Δ̄, one-to-one on the
unit circle Γ = ∂Δ. Show g maps Δ one-to-one onto the bounded domain D
whose boundary is C = g(Γ).

## Proof strategy (informal)

1. g(Γ) = C is a Jordan curve (injective continuous image of a circle).
2. By the argument principle: for w ∉ C, the number of preimages of w under g
   in Δ equals (1/2πi)∮ g'(z)/(g(z)-w) dz, which is the winding number of C around w.
3. Since C is a simple closed curve, the winding number is 1 for w inside C (in D),
   and 0 for w outside. So each w ∈ D has exactly one preimage.
4. Since the count is exactly 1 (with multiplicity), g'(z₀) ≠ 0 at each preimage,
   and g is locally injective, hence globally injective on Δ.

## Theory boundary

This proof requires three deep results not available in Mathlib:
- **Argument principle**: counting preimages via the contour integral of g'/(g-w).
- **Jordan curve theorem**: the image of a circle under an injective continuous
  map bounds a simply connected domain.
- **Winding number = 1 for simple closed curves**: a topological fact about
  simple closed curves in the plane.

These are at the frontier of Mathlib's complex analysis development.
The file records the theorem statement and proven infrastructure where possible.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.Basic

open Complex Metric Set Topology

noncomputable section

/-- **Main theorem**: g injective on ∂Δ ⟹ g injective on Δ.

    g is analytic in a neighborhood of the closed unit disk and injective on
    the unit circle. Then g is injective on the open unit disk.

    **Proof:** By the argument principle, for any w, the number of preimages
    of w in Δ equals the winding number of g(Γ) around w. Since g is injective
    on Γ, g(Γ) is a simple closed curve, so the winding number is 1 for w inside
    and 0 for w outside. Each interior point has exactly one preimage (counted
    with multiplicity), so g is injective.

    **Theory boundary:** The argument principle (connecting contour integrals
    of g'/(g-w) to preimage counting) and the Jordan curve theorem (connecting
    injective images of circles to bounded domains) are not available in
    Mathlib at the required level of generality. -/
theorem injOn_disk_of_injOn_circle
    {g : ℂ → ℂ}
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_bdy : InjOn g (sphere (0 : ℂ) 1)) :
    InjOn g (ball (0 : ℂ) 1) := by
  -- The proof requires the argument principle: for w not in g(sphere 0 1),
  -- (1/2πi) ∮ g'(z)/(g(z)-w) dz = number of preimages of w in ball 0 1.
  -- For injective g on the boundary, g(sphere 0 1) is a Jordan curve, and
  -- the winding number is 1 for interior points.
  --
  -- This is a genuine Mathlib theory boundary: the argument principle and
  -- Jordan curve theorem are not formalized at the required generality.
  /-
  CLOSER HOP 1 boundary: `ConstructionTargets.Rouche` was checked first. It
  now contains a sorry-free argument-principle formula and Rouché zero-count
  transfer on closed disks, so raw zero-counting is no longer the principal
  gap. The missing implication is topological: injectivity of the boundary
  parametrization must identify its image as a Jordan curve and show that the
  relevant interior winding number is one. Mathlib has no Jordan separation
  or winding-number theorem at this generality.

  `ConstructionTargets.UnivalentDeriv` was also checked. Its sorry-free
  `deriv_ne_zero_of_injOn` proves the derivative conclusion once interior
  injectivity is known, but cannot establish that injectivity from boundary
  data. Searches of `LEMMA-INDEX.md`, all closed siblings, Mathlib's contour,
  divisor, open-mapping, connectedness and plane-topology APIs, the remaining
  `ConstructionTargets/`, staging directories, and git history found no
  replacement for the Jordan/winding bridge. The frozen statement is
  unchanged and no unproved intermediate assertion was introduced.
  -/
  sorry

/-- **Surjectivity**: g maps Δ onto the bounded domain D enclosed by g(∂Δ). -/
theorem surjOn_domain_of_injOn_circle
    {g : ℂ → ℂ}
    (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε)))
    (hg_inj_bdy : InjOn g (sphere (0 : ℂ) 1)) :
    ∃ D : Set ℂ, IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      frontier D = g '' sphere (0 : ℂ) 1 ∧
      g '' ball (0 : ℂ) 1 = D := by
  /-
  CLOSER HOP 1 boundary: choosing `D = g '' ball 0 1` makes the last equality
  immediate; holomorphic open mapping (after excluding the constant case via
  boundary injectivity) and connected-image lemmas can provide openness and
  connectedness. The remaining exact frontier identity and boundedness in the
  required combined form again need the Jordan-curve theorem plus control of
  which complementary component is the image. Neither Mathlib nor a closed
  sibling packages that bridge. This second `sorry` is therefore downstream
  of the same Jordan/winding obstruction documented above.
  -/
  sorry

end
