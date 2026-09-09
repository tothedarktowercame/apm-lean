# Actual fixed-model regular-fiber charts and smooth overlaps

For real finite-dimensional normed spaces E and F, with E complete, a globally
ContDiff real genuine-infinity map f and a regular value c, `exists_cover`
constructs a chart at every point of the literal subtype {x : E // f x = c}.
The common model is EuclideanSpace real (Fin (finrank E - finrank F)).
No fiber charts, smooth transitions, constant-rank neighborhood or dimension
identity are supplied as premises. Empty fibers and zero-dimensional kernels
are included; no nonempty or nontrivial instances are required.

At x, set L = fderiv real f x. The existing smooth-derivative theorem supplies
the strict derivative. SmoothRegularFiberCoordinates supplies its actual
centered partial homeomorphism e into F times ker L, smooth on both domains.
RegularFiberFixedModel.kernelEquiv supplies A : ker L equivL Model from the
proved rank-nullity identity. The new chart is explicitly

    y -> A ((e y).snd)
    z -> e.symm (0, A.symm z)

on source {y in the literal fiber | y.val in e.source} and target
{z | (0, A.symm z) in e.target}. The inverse outside the target is the center
point; it is never used in a smoothness claim. Its actual target restriction
is the ambient smooth parameterization. Both inverse identities and open
domains are proved, giving an actual OpenPartialHomeomorph.

FiberChart retains ambient forward/backward maps, their smoothness, source
equality and exact forward/inverse formulas. `backward_image` proves the
parameterization image equals ambient intersect the literal level set.
`overlap_formula` identifies each actual chart transition on its source with
the ambient forward map of the second chart composed with the first inverse
parameterization. `overlap_smooth` proves ContDiffOn infinity on that actual
open overlap by composition, deriving the required image containment from
the chart-source conditions. `exists_cover` chooses these constructed charts
at all fiber points, proves each center lies in its source, and supplies all
smooth transitions. This does not infer neighborhood infinity from pointwise
regularity.

Next: construct common-model ChartedSpace and IsManifold instances, smooth
embedded inclusion and tangent-image comparison, then transport to manifold
sources and frozen regular-preimage consumers. No global atlas instance,
orientation, manifold-source preimage result or consumer closure is claimed.
Consumer t96J05 and proposed consumers t00J02, t02A07, t94A06, t97J05 retain
those subsequent obligations.

The fixture imports existing coordinate producers rather than rebuilding the
implicit function theorem. Preserve their APIs. Validation: direct Lean compile,
five standard-only axiom prints, no placeholders or added axioms. The probe
changes no canonical files. Implementation scope is only the new Lean module
and this documentation.
