# Torus-circle wedge Mayer–Vietoris calculation

`genericWedge_complete_module_homology` computes the integral singular
homology of `TorusCircleWedgeOpenCover.GenericWedge`, the generic point wedge
of a torus and a circle:

- `H₀ ≅ ℤ`;
- `H₁ ≅ ℤ³`;
- `H₂ ≅ ℤ`;
- `Hₙ` is zero for `n ≥ 3`.

The calculation applies the production two-open-cover Mayer–Vietoris sequence
to the established `U`, `V`, and `U ∩ V` homotopy equivalences. In degree
zero, `openCoverH0IsoOfCoordinates` normalizes the actual intersection arrow
to the signed diagonal and uses its existing cokernel/augmentation
reassembly. In degree one, exactness and the vanishing of overlap `H₁` make
the reassembly map monic; monicity of the degree-zero intersection arrow makes
the connecting map zero and hence reassembly epic. The resulting isomorphism
orders the torus `Fin 2` coordinates first and the circle coordinate last via
the local `torusFirstFinThreeModuleIso`. Its three compiled evaluation lemmas
state that output coordinates zero and one are the original torus coordinates
in order, and output coordinate two is the circle coordinate.

For degrees at least two, vanishing of overlap homology in consecutive degrees
makes reassembly an isomorphism. Degree two then reduces to the torus `H₂`
because the circle term vanishes, while both summands vanish above degree two.
The final results are converted from `AddCommGrpCat` to the exact
`ModuleCat ℤ` objects in the statement.

## Frozen consumers

The reviewed fixture also compiled a local copy of the frozen quotient and an
identity-on-representatives homeomorphism to `GenericWedge`. Those
fixture-local definitions were intentionally not promoted here. A later
consumer adapter should substitute its own frozen names for:

- `FrozenWedgeGlue` → `apm_t02a03_WedgeGlue` or the corresponding `t97J04`
  relation;
- `FrozenY` → `apm_t02a03_Y` or the corresponding `t97J04` quotient;
- `genericToFrozenHomeomorph` → a consumer-owned homeomorphism proved by the
  same relation-comparison and quotient-lift construction;
- `FMH` → that consumer's exact singular-homology expression.

The fixture at `/tmp/TorusCircleWedgeH0.lean`, SHA-256
`bfd4e682efc5672f8b5ba05cdcc79e64b8e07375facdf19e06555cfae4161452`,
compiled both substitutions for its local frozen model. This target imports
neither frozen problem and contains no frozen uptake theorem.
