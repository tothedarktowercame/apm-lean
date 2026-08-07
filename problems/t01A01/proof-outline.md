# Proof Outline: t01A01

The Lean attempt proves that every nonsurjective continuous self-map of the
real projective plane factors continuously through the complement of a missed
point (`apm_t01A01_factor_through_complement`).

Closer hop 2 proves `apm_t01A01_nullhomotopic_of_factor`: any null-homotopy of
that complement-valued factor descends through the subtype inclusion to the
required null-homotopy of the original self-map.

Closer hop 3 found
`FundamentalGroupoidFunctor.homotopicMapsNatIso`, which can transport the
eventual null-homotopy to triviality of the induced fundamental-group map
(up to the basepoint conjugation encoded by its natural-isomorphism
component). This reduces both frozen conclusions to constructing the
complement-valued null-homotopy, but does not supply that construction.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A01.md`

## Remaining bridge

To finish, formalize the topology used by the paper proof:

1. identify `Projectivization ℝ (Fin 3 → ℝ)` with real projective 2-space;
2. show the complement of a point deformation retracts to `RP¹ ≃ S¹`;
3. compute `π₁(RP²) ≃ ZMod 2` and use the inclusion of the punctured space to
   prove the induced map is trivial;
4. apply the universal-cover lifting/null-homotopy criterion to contract the
   complement-valued factor; the compiled descent lemma then finishes the
   original map.

Mathlib currently has `OnePoint.equivProjectivization` for the projective
line, but no packaged RP² fundamental-group computation or punctured-RP²
deformation retraction. The theorem therefore remains partial with one
documented `sorry`.
