# Mayer--Vietoris exactness-to-zero lemma

`MayerVietorisExactnessIsZero.lean` proves the generic categorical final step
for the proposed second-stage calculation of `H₁(S² × S³)`.

Given consecutive exact triples

```text
A → B → C
B → C → D,
```

if `A` is zero and `C → D` is monic, then `B` is zero.  The proof uses
Mathlib's `ShortComplex.Exact.mono_g_iff` on the second triple to show
`B → C = 0`, then `ShortComplex.Exact.isZero_X₂` on the first triple.

For Mayer--Vietoris, the intended substitution is:

- `A = H₁(U) ⊞ H₁(V)`;
- `B = H₁(U ∪ V)`;
- `C = H₀(U ∩ V)`;
- `D = H₀(U) ⊞ H₀(V)`.

The file deliberately does not assert any of those identifications.  The
remaining producer must construct the concrete open/subcomplex cover and
prove that its signed overlap map is monic.  `T02A06SphereH0` already supplies
the needed connected-space generator and naturality facts, including
`singularVertexH0Class_epi`, `singularVertexH0Class_mono`, and
`pathConnectedSubspace_homologyMap_mono_zero`; what is not yet packaged is the
signed biproduct map for the chosen overlap and its comparison with the
`SingularExcision.subcomplexMayerVietorisShortComplex` degree-zero map.

The companion lemma `mono_signedBiprodLift_of_mono_left` proves the purely
algebraic signed-diagonal fact: `biprod.lift i (-j)` is monic whenever `i` is.
Consequently, after the comparison equation is available, the existing
`pathConnectedSubspace_homologyMap_mono_zero` theorem supplies injectivity.

No topology, homology vanishing, or final product result is assumed here.
