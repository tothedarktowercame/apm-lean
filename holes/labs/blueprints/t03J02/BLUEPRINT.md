# Blueprint for t03J02

## Triage and interface repair

The registered statement is true and faithful. Embeddings are essential for
the collar geometry: constant maps happen to give the same `π₁` answer, but a
general degree-zero immersed loop can change `H₂`. Null-homotopy is used both
on `π₁` and `H₁`. Mayer--Vietoris gives `H₂ ≅ ℤ² ⊕ ker(ℤ → ℤ⁴) = ℤ³`.

Definitions through `apm_t03J02_gluedDescEquiv` now match current `Main.lean`.
`apm_t03J02_CompatibleOpenCover` contains the open cover, its three homotopy
equivalences, and homotopies identifying the transported overlap inclusions
with `j₁` and `j₂`. Consumers therefore see the actual attaching maps. They
take the certificate as a parameter, so all consumer leaves are independent
of the geometric construction leaf.

## Leaves

| leaf | claim, intended tools | size | dependency |
|---|---|---:|---|
| `apm_t03J02_isPushout` | Concrete quotient is a `CategoryTheory.IsPushout`; use `gluedDescEquiv`, `gluedDesc_inl/inr`, `gluedDesc_unique`, and `PushoutCocone.IsColimit`. | 50–90 | definitions only |
| `apm_t03J02_compatibleOpenCover` | Construct the compatible cover from global annular collars. `SurfaceSchoenflies.embeddedCircle_isClosed_range`, `embeddedCircle_finite_flat_subcover`, and local product charts are available, but no global collar theorem is. | **LIBRARY 500–1000** | definitions only |
| `apm_t03J02_fundamentalGroup_of_compatibleOpenCover` | Van Kampen, transport via compatibility, kill both legs by null-homotopy, identify presentation. Use `PointWedgeVanKampen` and `TwoOpenFreeProductMapping`. | 150–250, possibly LIBRARY | certificate parameter |
| `apm_t03J02_H0_of_compatibleOpenCover` | Degree-zero integral MV and connectedness. Use `IntegralOpenCoverMayerVietoris.integralMayerVietoris`, `ProductionOpenCoverMayerVietoris`, and `T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv`. | 60–100 | certificate parameter |
| `apm_t03J02_H1_of_compatibleOpenCover` | Compatibility plus null-homotopy makes `H₁(S¹) → H₁(T²)²` zero; MV gives `ℤ⁴`. | 100–150 | certificate and null-homotopies |
| `apm_t03J02_H2_of_compatibleOpenCover` | MV gives `0 → ℤ² → H₂ → ℤ → 0`; split using freeness/projectivity of `ℤ`, yielding `ℤ³`. | 120–180 | certificate and null-homotopies |
| `apm_t03J02_Hhigh_of_compatibleOpenCover` | MV plus circle/torus homology vanishing above their dimensions. | 60–100 | certificate parameter |

### Split of `..._fundamentalGroup_of_compatibleOpenCover` (2026-10-24)

Assembly, `_aux_pathConnected`, `_aux_vanKampen` (from `_aux_trivialLegs` and
`_aux_vanKampen_aux_torus`, both banked by lemma-3) and `_aux_trivialLegs`
itself are proved. Open, all prefixed `apm_t03J02_fundamentalGroup_of_compatibleOpenCover_`:

| leaf | claim | size |
|---|---|---:|
| `_aux_presentation` | `ℤ² * ℤ² ≃* freeProductZ2Z2` | 60–120 |
| `_aux_vanKampen_aux_trivialLegs_aux_general` | two-open van Kampen with **nullhomotopic** overlap legs (overlap not simply connected): `π₁ X ≃* π₁ U * π₁ V`. Follow `TwoOpenFreeProductMapping`, replacing the simple-connectivity collapse of the overlap by the natural iso of each leg functor with a constant one. | proved from `_aux_mapping` (claude-14, 2026-10-24, after lemma-3 PARTIAL banked `_aux_groupoid`, `_aux_map_eq_one`; `_aux_isConnected` proved) |
| `_aux_general_aux_collapse` | generic: over a connected `W`, pseudo-cocones on a span whose legs factor through `W ⥤ pt` ≌ pseudo-cocones on the point span, natural in the target (`Functor.const` full for `IsConnected W`). The only place the old simply-connected argument is replaced. | 80–200 |
| `_aux_general_aux_mapping` | target-natural `(Π X ⥤ C) ≌ (SingleObj (End u * End v) ⥤ C)`: chain as in `TwoOpenFreeProductMapping.mapping`; legs → const via `_aux_groupoid` + `pseudoCoconeEquivalenceOfSpanEquivalences` with identity equivalences; `_aux_collapse`; then the point-span comparison with `pathConnector` connector systems (not `leftConnectors`, which need a simply connected overlap). | 120–250 |
| `_aux_vanKampen_aux_trivialLegs_aux_nullLegs` | both legs of a compatible cover are nullhomotopic (`leftEquiv.invFun ∘ leftEquiv ∘ leg`). | 20–40 |
| `_aux_vanKampen_aux_trivialLegs_aux_hequiv` | homotopy equivalence, path-connected target ⇒ `π₁ X x ≃* π₁ Y y`; use `FundamentalGroupoidFunctor.equivOfHomotopyEquiv`. | 20–50 |
| `_aux_vanKampen_aux_trivialLegs_aux_pathConnectedSpace` | `U ∪ V = univ`, both path-connected, meeting ⇒ `PathConnectedSpace X`. | 15–30 |

All seven leaves are layer 1 and mutually independent as statements. Layer 2
is the sorry-free `apm_t03j02` assembly. The pushout leaf is reusable library
infrastructure and is not artificially forced into the conjunction proof.

## C1–C10 checks

- `isPushout`: C1 quotient topology gives maps-out universality; C2 nonvacuous;
  C3 small adapter; C4 uniqueness closes the cocone; C5 both canonical maps
  exposed; C6 valid for arbitrary continuous maps; C7 exact `TopCat.ofHom`
  types compile; C8 constant maps harmless; C9 new; C10 prose matches.
- `compatibleOpenCover`: C1 needs embeddings and a genuine global collar; C2
  does not assume the result; C3 honestly LIBRARY; C4 includes every cover
  field; C5 includes both map homotopies; C6 exactly the embedding hypotheses;
  C7 literal subtype intersections; C8 Circle is nonempty and cannot collapse;
  C9 strictly strengthens the old interface; C10 matches.
- `fundamentalGroup`: C1 compatible null legs give the free product; C2 result
  not assumed; C3 limited to van Kampen/presentation algebra; C4 both legs
  supplied; C5 compatibility fields used; C6 both null hypotheses retained;
  C7 registered basepoint; C8 overlap nonempty; C9 new; C10 matches.
- `H0`: C1 connected cover data gives `ℤ`; C2 nonvacuous; C3 one degree; C4 MV
  inputs complete; C5 actual cover supplied; C6 null hypotheses correctly
  omitted; C7 integral coefficients; C8 nonempty overlap; C9 new; C10 matches.
- `H1`: C1 zero legs give rank four; C2 nonvacuous; C3 one degree; C4 exactness
  supplies kernel/cokernel; C5 transported maps explicit; C6 both null inputs;
  C7 signs irrelevant for zero; C8 no zero-dimensional edge; C9 new; C10 matches.
- `H2`: C1 kernel contributes one `ℤ`; C2 nonvacuous; C3 one exact-sequence
  calculation; C4 adjacent terms included; C5 compatibility explicit; C6 both
  null inputs; C7 iso existence avoids coordinate-sign ambiguity; C8 degrees
  1/2 included; C9 new; C10 matches.
- `Hhigh`: C1 all adjacent terms vanish; C2 nonvacuous; C3 uniform MV; C4
  adjacent degrees covered; C5 homotopy types suffice; C6 null hypotheses
  correctly omitted; C7 natural-number inequality; C8 checks `k = 3`; C9 new;
  C10 matches.

## Missing foundation

`SurfaceSchoenflies` stops at closed image, finite local-flat charts, and
transport of local flatness. Cohering those charts into a global annular
neighborhood is a genuine surface collar/Schoenflies library project, so the
cover leaf is marked LIBRARY. The van Kampen leaf may additionally require a
circle-overlap groupoid-pushout adapter beyond the existing simply-connected
overlap convenience theorem.

## Verification (2026-10-24)

`lake env lean holes/labs/blueprints/t03J02/Blueprint.lean`: 0 errors; 7
`sorry` warnings, one per leaf above (lines 180, 214, 224, 237, 244, 253, 262).
`#print axioms apm_t03j02`: `[propext, sorryAx, Classical.choice, Quot.sound]`.
`scripts/statement-registry.py check t03J02`: 1 registered statement matches.

`apm_t03J02_isPushout` is not used by the main theorem. It is kept as a
statement, not queued for a seat.

## Earlier record (blueprint time)

Kept from the first blueprint. Its three leaves (`pushout_openCover`,
`fundamentalGroup_of_openCover`, `homology_of_openCover`) are superseded by the
table above; the cover now carries the inclusion homotopies its caveat asked for.

### Triage

`Main.lean` encodes each simple closed curve by an embedding of `Circle` into
the standard torus, records null-homotopy, forms the generated-relation
quotient, and asks for exactly the classical answers
`π₁ = ℤ² * ℤ²`, `H₀ = ℤ`, `H₁ = ℤ⁴`, `H₂ = ℤ³`, and `H_k = 0` for `k ≥ 3`.

Edge cases tried: `Circle` and the torus are nonempty, so the basepoint and
gluing locus cannot disappear. An embedding rules out a constant attaching map.
Null-homotopy makes both induced fundamental-group and first-homology maps
trivial. Abelianizing `ℤ² * ℤ²` gives `ℤ⁴`, agreeing with `H₁`; the ranks give
Euler characteristic `1 - 4 + 3 = 0`, agreeing with `χ(T²) + χ(T²) - χ(S¹) = 0`.
No counterexample appears in the solve-loop records or topology audit.

The topology ledger's reviewed STOP is genuine: maps-out universality of the
quotient does not itself produce collars. For arbitrary topological embedded
circles, one first needs annular-neighborhood/Jordan--Schoenflies input before
the open-cover van Kampen and Mayer--Vietoris infrastructure applies.

### Infrastructure search

`TwoOpenFreeProductMapping` gives a two-open free-product theorem only when the
overlap is simply connected, so it does not directly handle this circle overlap.
Searches for `annulusNeighborhood`, `pushout_openCover`, `TwoOpenFreeProduct`,
and `MayerVietoris` found no sorry-free construction of the embedded-circle
collar or quotient cover.
