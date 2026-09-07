# Scalar implicit-function defining fields

This module strengthens the scalar implicit-function construction by exposing
all of its defining fields.

Given a scalar strict derivative `L` that is nonzero on one direction, the
constructed `ImplicitFunctionData` retains the original scalar function and
derivative as its left fields, the orthogonal projection onto `ker L` as both
its right function and right derivative, and the original point as `pt`.
The kernel's complete-space witness is explicit and agrees with the existing
scalarized-jet construction.

These equalities permit direct verification of the left and right `ContDiffAt`
hypotheses needed for smooth kernel parameterization. Their scalarized-jet
specialization and source-dimension induction remain downstream.
