# Proof Outline: t94A06

The zero-parameter identity is compiled as `apm_t94a06_family_zero`.

For almost-every parameter, form the incidence space where the translated map
lands on the z-axis. The parameter derivative spans the normal plane, so the
total family is transverse. Sard applied to the projection of the incidence
space then says almost every parameter is regular, equivalently its slice is
transverse to the axis.

## Remaining boundary

Mathlib has fixed-vector-space Sard lemmas but no manifold Sard or parametric
transversality theorem in the required generality. The incidence-submanifold
construction, its projection derivative, and chartwise null-set transport
remain to be formalized.
