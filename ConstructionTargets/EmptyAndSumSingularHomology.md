# Empty and sum singular homology

This target proves directly that the integral singular chain group of the
empty topological space is zero in every degree: a singular simplex would
evaluate at a point of the nonempty topological standard simplex to produce
an element of `Empty`.  The generic
homological-complex zero-object theorem then gives zero integral singular
homology in every degree.
The result is also transported to Mathlib's canonical `ModuleCat ℤ` singular
homology through `IntegralSingularHomologyComparison`; no second chain model
or coefficient identification is assumed.

The next step is to instantiate the production open-cover Mayer--Vietoris
sequence for the two clopen summands of `X ⊕ Y`.  Its intersection must first
be identified, including its inclusion maps, with `Empty`; after that the
zero intersection term should turn the production reassembly arrow into the
desired biproduct isomorphism.  The exact remaining interface is a
homeomorphism (and induced-map normalization) between the intersection
subtype of the two sum-side opens and `Empty`, followed by the categorical
lemma that the production exact reassembly arrow is an isomorphism when its
kernel and cokernel terms are zero.  This module does not assume or claim that
sum splitting.
