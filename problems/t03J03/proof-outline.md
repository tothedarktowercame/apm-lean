# Proof Outline: t03J03

The elementary classification invariants are now formalized and compile.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J03.md`

## Compiled steps

- The Euler characteristics of `N₃`, `Σ₂`, and `N₄` are `-1`, `-2`, and
  `-2`, respectively.
- The subtype of nonzero characters `Fin 3 → ZMod 2` has cardinality seven.
- The all-ones orientation character is proved nonzero and bundled as an
  element of the character subtype.
- `apm_t03J03_exists_cylinderLift_of_range_le` applies Mathlib's precise
  fundamental-group lifting criterion and produces the continuous cylinder
  lift, including its commuting equation, once a fiber point and range
  inclusion are supplied.

## Remaining boundary

One must build the seven connected double covers, classify every connected
cover uniquely by its character, identify the orientable cover with `Σ₂` and
the other six with `N₄`, classify disconnected double covers as trivial, and
prove the cylinder's standard connectivity instances, choose a point in the
relevant fiber, and use the orientation character to verify the
fundamental-group range condition. The remaining polygon-surface fundamental
groups and cover classification needed for that inclusion are absent.

## Hop 4 bridge statements

- `apm_t03J03_bridge_1` states the complete connected-double-cover character
  classification and the `Sigma₂`/`N₄` orientation-character dichotomy.
- `apm_t03J03_bridge_2` states that every disconnected double cover is the
  trivial cover.
- `apm_t03J03_bridge_3` states the exact cylinder-lifting consequence for an
  orientable double cover, isolating the missing orientation-character range
  inclusion from the already-compiled general lifting criterion.

Together these are exactly the three nonnumerical conjuncts still required by
the frozen theorem.
