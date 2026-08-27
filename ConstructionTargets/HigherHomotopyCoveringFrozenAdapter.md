# Frozen-facing higher-homotopy covering adapter

This target mirrors frozen `t01J02`'s induced-map definition exactly: it uses
the compiled quotient postcomposition map and transports its codomain along
the supplied equality `p e = x`.

`inducedMap_rfl` records the definitional equality before basepoint transport.
`inducedMap_bijective` substitutes the target basepoint equality and applies
the already proved `fin_homotopyMap_bijective`; no surjectivity or bijectivity
premise is introduced.  `inducedMap_surjective` exposes the new half
separately so the frozen file can retain its existing injectivity proof.

Because standalone problem files are not importable library modules, this
target cannot name `apm_t01j02_inducedMap` directly.  Its definition has the
same binders, domain, codomain, equality transport, and body, so the final
problem-side replacement is a direct import plus `exact inducedMap_bijective
...`, with only namespace qualification required.
