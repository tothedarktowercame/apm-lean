# Repair grades 4: proposed revisions (holes/labs/blueprints/<id>/RevisedMain.lean)

Read-only grading. The proposed revisions are compared with problem.md, the current
problems/<id>/lean/Main.lean, and triage-3.md. Nothing was built.

| id | grade (revision) | TRUE? | one-line reason | change classification (current -> revision) | remaining defect |
|---|---|---|---|---|---|
| t99A02 | narrower (still a stand-in: algebra only, no space) | TRUE | Both conjuncts are correct presentation isomorphisms: ⟨a,b∣a²,b²⟩ ≅ `DihedralGroup 0` (= D∞) and ⟨a,b∣b²⟩ ≅ ℤ * ℤ/2. But no space, no π₁ and no covering map appears. | improvement (it replaces three near-vacuous conjuncts with real content, but it is still not the problem's claim) | It never mentions RP²∨RP², S¹∨RP², π₁ or a cover. The docstring's "records the two fundamental-group identifications" overclaims: the link from presentation to π₁ (van Kampen) is not stated. |
| t99A03 | faithful | TRUE (both parts) | The models check out. `Surface false 1` is the disk with antipodal boundary identification, i.e. RP². The 4-fold wedge is the wedge of two 2-wedges at their wedge points. `Surface false 4` is the word a₁a₁a₂a₂a₃a₃a₄a₄, i.e. N₄. (a) "yes" and (b) "no" are both correct. | correction (the current statement is a true but generic deck-transformation lemma that never mentions the spaces, so it did not say what problem.md says) | None substantive. Minor: the wedge point is the disk centre rather than a polygon vertex, which is harmless because a surface is homogeneous. The `RationalLefschetz` import is unused by the statement. |

## Evidence notes

### t99A02
- Revised statement:
  ```lean
  Nonempty (PresentedGroup APMT99A02.rp2WedgeRp2Relations ≃* DihedralGroup 0) ∧
  Nonempty (PresentedGroup APMT99A02.circleWedgeRp2Relations ≃*
    Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2)))
  ```
  The relators are `{of 0 ^ 2, of 1 ^ 2}` and `{of 1 ^ 2}`.
- Both conjuncts are true:
  - Mathlib's `DihedralGroup 0` is the infinite dihedral group (`ZMod 0 = ℤ`), and Z/2 * Z/2 ≅ D∞ via a ↦ sr, b ↦ s.
  - ⟨a,b ∣ b²⟩ is by definition the free product ℤ * ℤ/2. `Monoid.Coprod` of two groups is a group, and it is the free product.
- This fixes triage-3's complaint that the current conjuncts `of i ^ 2 = 1` hold because the relator is in the set. It is exactly the "minimum fix" triage-3 proposed. The infinitude of π₁(RP²∨RP²) is now implied, since D∞ is infinite.
- It is still a stand-in. The problem asks for the universal covers of two spaces, and the statement is pure combinatorial group theory. Nothing ties these presentations to RP²∨RP² or S¹∨RP², so a reader cannot recover the problem from the theorem. Grade: narrower, with the specific restriction that it states only the group-theoretic input (π₁ up to presentation) of the pictures, not the spaces or their covers.
- The smallest faithful step uses models that already exist in `ConstructionTargets.StatementSurfaceModels`:
  - The spaces:
    - `ProjectivePlaneWedge` (= RP²∨RP²) already exists.
    - S¹∨RP² is `Wedge (1 : Circle) (surfacePoint false 1)`.
  - (i) π₁ form, a narrower but honest statement:
    - `Nonempty (FundamentalGroup ProjectivePlaneWedge x₀ ≃* DihedralGroup 0)`
    - `Nonempty (FundamentalGroup (Wedge (1 : Circle) (surfacePoint false 1)) y₀ ≃* Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2)))`
    - Here x₀ and y₀ are the wedge points.
  - (ii) Faithful form: an explicit simply connected cover in each case, `SimplyConnectedSpace E ∧ ∃ p : E → X, IsCoveringMap p`.
    - For RP²∨RP², E is the ℤ-chain of spheres: `ℤ × S²` modulo (n, north) ~ (n+1, south). The two RP² summands lift alternately as the spheres, and the antipodal maps generate the D∞ action.
    - For S¹∨RP², E is the Bass–Serre tree of lines and spheres. Each lift of the basepoint lies on exactly one line (a lift of S¹, carrying ℤ basepoint lifts) and one sphere (a lift of RP², carrying 2 antipodal basepoint lifts).
    - (ii) is expressible as quotients but heavy. (i) is the realistic next step and needs van Kampen for wedges, which is the proof gap.

### t99A03
- Revised statement:
  ```lean
  (∀ f : C(T99A03.FourProjectivePlanesWedge, T99A03.FourProjectivePlanesWedge), ∃ x, f x = x) ∧
  (∃ f : C(T99A03.FourProjectivePlanesConnectedSum, T99A03.FourProjectivePlanesConnectedSum), ∀ x, f x ≠ x)
  ```
- Checking the models:
  - `RealProjectivePlane := Surface false 1`. In `Surfaces.SurfaceRel false 1`, edge 0 at parameter t is exp(iπt) and edge 1 at t is exp(iπ(1+t)) = −exp(iπt). The relation is therefore z ~ −z on the boundary circle, which gives RP². The topology is coinduced from the closed disk in ℂ.
  - `surfacePoint false 1` is the image of the disk centre, an interior point.
  - `ProjectivePlaneWedge := Wedge (surfacePoint false 1) (surfacePoint false 1)`. It is the quotient of `Sum`, identifying the two points, with the coinduced topology.
  - `twoWedgePoint = quotientMap … (Sum.inl (surfacePoint false 1))` is that wedge's common point. So `FourProjectivePlanesWedge = Wedge twoWedgePoint twoWedgePoint` is the two-fold wedge of RP²∨RP² at its wedge points, which is the 4-fold wedge (RP²)^∨4.
  - All the quotients are finite and of compact spaces, so the iterated quotient topology is the standard wedge topology.
  - Wedging at an interior point instead of a polygon vertex gives a homeomorphic space, because closed surfaces are homogeneous.
  - `FourProjectivePlanesConnectedSum := Surface false 4`. It is a 2·4-gon with edge 2j glued to edge 2j+1 in the same direction, i.e. the word a₁a₁a₂a₂a₃a₃a₄a₄, which is N₄ = #⁴RP². All vertices are identified through `EqvGen` at the endpoints t = 0 and t = 1, as in the standard polygon model.
- Truth:
  - (a) is TRUE. H̃_*(RP²;ℚ) = 0, so the 4-fold wedge (a finite CW complex) is ℚ-acyclic. Every self-map therefore has L(f) = 1 ≠ 0, and Lefschetz gives a fixed point.
  - (b) is TRUE. χ(N₄) = −2 = 2·χ(N₃), and N₄ is the nonorientable double cover of N₃, so its deck involution is a fixed-point-free self-map. Equivalently, N₄ = K#K has a free involution.
- Classification: correction.
  - The current `apm_t99a03` (a connected-cover deck transformation ≠ id has no fixed point) is true, but it mentions neither space and omits (a) entirely. It does not say what problem.md says.
  - The revision states both answers on concrete models, as triage-3 recommended, using the repo `Surface false 4` and a quotient wedge.
- Proof gaps, which are not statement defects:
  - (a) needs the Lefschetz fixed-point theorem or a substitute. `ConstructionTargets.RationalLefschetz` is imported but not used in the statement.
  - (b) needs an explicit free involution on the polygon model, or the deck lemma (the current theorem) plus an explicit double cover N₄ → N₃.
