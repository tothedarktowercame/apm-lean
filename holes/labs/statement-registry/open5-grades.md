# Open statement repairs, 2026-11-04 (claude-14)

Rows whose Lean statement was unregistered (graded unfaithful) and whose proof is open.
Each repair writes a faithful statement with the proof left as `sorry`, then registers it as open.

## t99J03

Repair by codex-5 (packet ~/notes/packets/lemmas/repairs/open5/t99J03.md), reviewed by claude-14:
the seat's `[IsManifold 𝓘(ℝ,E2) ⊤ X]` (⊤ = analytic) was removed, so X, Y range over compact
connected Hausdorff topological surfaces (the triangulated class, by Radó).

Outside grade (read-only Claude subagent, 2026-11-04): faithful, with one gap: the statement did not
say which normal forms are orientable, so Σ_g and N_{2g} (equal χ) could not be separated. Fixed by
claude-14: two conjuncts `∀ g, IsOrientable (Surface true g)` and `∀ k > 0, ¬ IsOrientable (Surface false k)`.
Grader's checks: polygon words correct at g = 0, g = 1, k = 1, k = 2; H₂(X;ℤ) ≅ ℤ is the right
orientability test for closed connected surfaces; HasEulerCharacteristic is single-valued, junk-free
and a homeomorphism invariant; χ arguments are in ℚ (no ℕ subtraction); statement true. Part (b)
(proof outline) is prose and is not formalised.

## t02A08

Repair by codex-6 (packet ~/notes/packets/lemmas/repairs/open5/t02A08.md). Z = S¹×{q} as the
dimensions force (triage-1101). The intersection number is now a signed count of transverse
preimage points (no longer the degree of pr₂ ∘ f): smooth = ambient C^∞ (`(⊤ : ℕ∞)` is ∞, not ω),
tangent spaces are kernels of ⟨x,·⟩, transversality is surjectivity of pr₂ ∘ df onto T_qS², and
the sign is the determinant of [ν_S¹, ν_S², df u, df v, ccw p] in ℝ⁵ for a positive frame (u, v).

Outside grade (read-only Claude subagent, 2026-11-04): faithful. Checks: ∀ q is at least the
problem's claim and true by rotation; the ambient encoding is equivalent for an existence statement;
the sign is frame-independent and nonzero at transverse points; finiteness is asserted, so the
finite-sum branch is the one used; true via F = (p₀, G) with G of degree −n; not gameable.
Defect found outside the theorem: the sanity lemma claimed +1 for x ↦ (p, x); with normals-first
orientation of Y (opposite to the product orientation, one global sign) it is −1. Corrected by
claude-14 (checked by hand: three column swaps to block form, det[p, ccw p] = 1, det[q,u,v] > 0).
The request to explain the computation is prose and is not formalised.

## t99A04

Repair by codex-14 (packet open5/t99A04.md) on the shared integral (ConstructionTargets/ManifoldTopFormIntegral,
graded standard 11-04). Readings: F = X (F undefined in the print); compact 2-manifold = boundaryless (on a
compact annulus the core separates yet dθ has nonzero period). claude-14 fix: the seat defined the circle's
orientation by `Classical.choose` of a sorry'd sanity theorem, which put sorryAx into the definition; the
circle orientation is now a universally quantified parameter (both answers are invariant under reversal).

Outside grade (read-only Claude subagent, 2026-11-04): faithful. (a) every smooth closed η has period 0 on a
separating embedded circle; (b) on a nonseparating one every real is a period (stronger than the bare "no",
and the complete answer). Integrability is part of the conclusion, so the integral's zero branch cannot fake an
answer. The orientation of X is used (on RP² the Möbius core does not separate but H¹ = 0). True; not vacuous.

## t94J07

Repair by codex-10 in two rounds (packets open5/t94J07.md, t94J07-r2.md). Restored per the triage: X oriented,
ω of degree dim X. Round 1 stated Y boundaryless (narrower: the print restricts only ∂X); claude-14 sent it back,
and round 2 models Y by an arbitrary ModelWithCorners J, with smoothness, closedness (extDerivWithin on extended
chart targets) and pullback defined in Mathlib's extended charts; `pullback_self_eq` ties them to the shared
vocabulary for boundaryless Y. Homotopy: smooth H : X × ℝ → Y with slices f, g.

Outside grade (read-only Claude subagent, 2026-11-04): faithful, no defects. Closedness on chart targets (open in
the convex range of J) is dω = 0 including boundary and corner points, chart-independent; X × ℝ homotopies are
equivalent to X × [0,1]; integrability is proved in the conclusion, so the zero branch cannot make the equality
trivial; true (homotopy operator plus Stokes on closed X); degenerate n = 0, m = 0, n > m, empty X checked.

## t01A05

Repair by codex-15 in two rounds (packets open5/t01A05.md, t01A05-r2.md) on the shared integral. Both orientations
are inputs tied by orientation-preserving π (fixes the earlier FALSE encoding, X ⊔ X → X). Round 1's part (c)
left the lifted orientations free and added a transversality hypothesis; claude-14 sent it back. Round 2: lifts
come with smooth orientation-preserving lift maps ρ commuting with π; the intersection number is the
Guillemin–Pollack one (smooth homotopy of Z₁'s inclusion to a map transverse to Z₂, finite signed count), and (c)
is stated as I(Z₁,Z₂) = m → I(Z̃₁,Z̃₂) = k·m with no transversality hypothesis.

Outside grade (read-only Claude subagent, 2026-11-04): (b) and (c) faithful and true, lifts cannot be gamed
(range = preimage plus injective inclusions determine ρ; orientation preservation forces dρ invertible); (a)
vacuous: X = X̃ = ∅ satisfies it. Fixed by claude-14: (a) now also requires `Nonempty X ∧ ConnectedSpace Xtilde`
(the intended witness is the torus map (z, w) ↦ (z^k, w); a disconnected k-copy cover is also excluded).
Grade with the fix: faithful (the extra conditions only strengthen the existential example).
