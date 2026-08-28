# Connecting-map negation naturality

This target proves a reusable sign rule for the connecting morphism in the
homology sequence of a short exact sequence of chain complexes.  It is derived
directly from `HomologicalComplex.HomologySequence.δ_naturality`.

`eq_neg_of_comp_neg_id_eq_id_comp` is the normalized same-source/target
calculation.  `delta_eq_neg_of_first_neg_iso_third_iso` derives the actual
connecting-map statement from `δ_naturality`, retaining explicit isomorphism
transports on the first and third terms as required when the two pieces of a
Mayer--Vietoris cover are exchanged.  Keeping those transports explicit also
avoids silently identifying the `HasHomology` witnesses selected by two
different `ShortExact` proofs.

The target does not construct the cover-swap morphism or compare the
Mayer--Vietoris connecting map with the pair/excision composite used by the
sphere suspension shift.  In particular, it does not assert the antipodal
recurrence or repair the false `n = 0` frozen `t94J08` statement.
