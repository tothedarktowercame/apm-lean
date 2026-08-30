# T97J08 beta winding integral

This target connects the frozen beta integral to the unique winding integer.
The radial/tangential algebra and interval FTC are local calculations; the
remaining library seam is regularity of the lift constructed by Mathlib's
covering-space API.  That API currently returns only a `ContinuousMap`.

`LiftIsCOne f hf` records the exact missing fact: the canonical global lift of
the smooth normalized loop is `C¹`.  Once supplied, the intended theorem is
`winding_eq_betaIntegral_of_liftIsCOne`.
