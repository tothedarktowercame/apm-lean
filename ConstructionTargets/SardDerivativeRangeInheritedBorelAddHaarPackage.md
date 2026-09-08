# Derivative-range inherited-Borel additive-Haar package

`exists_inherited_range_orthogonal_addHaarMeasure` supplies additive Haar
measures on a derivative range and its orthogonal complement using the
measurable structures those subtypes inherit from an already Borel target.
For a nonsurjective derivative it also installs the required nontriviality of
the orthogonal complement.

This avoids replacing the concrete chart-coordinate measurable structures
with fresh `borel` instances, whose associated `Measure` types are not
definitionally interchangeable with the inherited ones.
