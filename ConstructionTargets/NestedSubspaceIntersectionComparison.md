# Nested-subspace intersection comparison

For arbitrary subsets `U,V` of a topological space, this target constructs the
literal homeomorphism

`(U ∩ V : Set X) ≃ₜ {x : V | x.1 ∈ U}`.

It proves both underlying-value equations and the commuting inclusion square
into `V` for continuous maps, `TopCat` morphisms, integral singular chains,
and integral singular homology. It also descends the square through cokernels,
identifying the direct relative cokernel of `(U ∩ V) → V` with the production
relative singular-chain complex of the nested pair inside `V`.

No subtype equality is assumed. The remaining open-cover comparison is to
compose this nested-pair isomorphism with the ambient range-chain isomorphisms
and prove that the resulting cokernel map is the same map as
`unionToRightRelative`; after that equality, the projection/excision
identification from the preceding targets can be assembled. No antipodal sign
recurrence or frozen theorem is asserted.
