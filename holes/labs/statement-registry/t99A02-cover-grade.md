# t99A02 statement repair: universal covers stated (2026-10-15)

Joe 2026-10-15: fix t99A02 so it is not artificially narrowed. Earlier attempts (holes/labs/blueprints/t99A02/old-2026-10-15/, repair-grades-4.md) stated only presentations / π₁ and were held as narrower.

New statement: concrete models of both pictures and the claim that each is the universal cover.
- SphereChain = (ℤ × S²)/((n, north) ~ (n+1, south)): bi-infinite chain of 2-spheres.
- LineSphereTree = ((G × I) ⊕ (G × S²))/~ with G = ℤ * ℤ/2 discrete: edge g → g·a, vertex g = north of sphere copy g, copies g and g·b identified antipodally (one line per coset g⟨a⟩, one sphere per coset {g, g·b}; Bass–Serre tree).
- Theorem: each is SimplyConnectedSpace and has a surjective IsCoveringMap onto RP²∨RP² (ProjectivePlaneWedge) resp. S¹∨RP² (Wedge (1 : Circle) (surfacePoint false 1)).

Grader (read-only Claude subagent, claude-14 2026-10-15): **faithful**, **TRUE**.
- Models: Surface false 1 is word aa (RP²), wedge at the disk centre (homogeneous, harmless); S² negation is Mathlib's antipodal InvolutiveNeg.
- Chain: junctions are two disks at a point; sphere n → RP² copy (n mod 2) by the antipodal quotient is a surjective covering; simply connected.
- Tree: pair∘pair consistent (b² = 1); vertex classes finite {(g,0),(ga⁻¹,1),(g,north),(gb,south)}, so locally finite, local picture arc + disk = wedge point of S¹∨RP²; simply connected (tree of simply connected pieces).
- Encoding: IsCoveringMap implies continuity; Surjective excludes empty fibres; simply connected cover of a connected locally path-connected base = universal cover. No vacuity.
