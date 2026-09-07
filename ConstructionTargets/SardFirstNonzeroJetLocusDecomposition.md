# First-nonzero-jet locus decomposition

This module refines the higher-jet decomposition by assigning each non-flat point to the least positive derivative order at which its iterated Fréchet derivative is nonzero.

The resulting `firstNonzeroJetLocus` records both nonvanishing at order `i` and vanishing at every positive lower order. This is the representation needed by the implicit-function induction: a lower scalarized jet is constant on the localized stratum, so the stratum can lie in its level hypersurface.

The module also aggregates nullity of the flat image and all finitely indexed first-nonzero-jet images into nullity of the full localized image. Local hypersurface containment, source-dimension induction, and Taylor-flat nullity remain downstream.
