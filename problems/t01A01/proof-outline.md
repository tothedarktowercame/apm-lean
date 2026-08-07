# Proof Outline: t01A01

The Lean attempt proves that every nonsurjective continuous self-map of the
real projective plane factors continuously through the complement of a missed
point (`apm_t01A01_factor_through_complement`).

Closer hop 2 proves `apm_t01A01_nullhomotopic_of_factor`: any null-homotopy of
that complement-valued factor descends through the subtype inclusion to the
required null-homotopy of the original self-map.

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
