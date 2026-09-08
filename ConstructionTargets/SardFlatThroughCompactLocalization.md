# Flat-through compact localization

This module derives the topological inputs needed to apply Taylor nullity to the exact `flatThrough` locus.

Under global `ContDiff` regularity through order `k`, each relevant iterated-derivative zero set is closed. Their intersection with a compact localized source set is therefore compact. Because `flatThrough f K k` is a subset of `K`, it also inherits any closed-ball bound already available for `K`.

These conclusions feed directly into the compiled flat-through Taylor-nullity adapter.
