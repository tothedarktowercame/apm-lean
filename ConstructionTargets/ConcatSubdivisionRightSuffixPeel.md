# ConcatSubdivisionRightSuffixPeel

This target proves the terminal step required by the shrinking-prefix
induction. The final right segment and vertex are identified with the actual
final indices of the full concatenated chain. The final full-chain mapped
piece is then related to the final right-block piece with both dependent
endpoint transports explicit.

The remaining induction must repeat this calculation after restricting the
full chain by two structural `Fin.castSucc` maps from
`composeFin_dropLast_two`. Its exact unresolved equality is the predecessor
boundary: the restricted full-chain last index must be identified with
`rightBlockVertex` at the predecessor right vertex before applying the
induction hypothesis. No suffix split or evaluation equality is claimed.
