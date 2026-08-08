# Proof Outline: t97J03

Assume an extension `F` exists. Fix the second circle coordinate at `1` and
define `g z` to be the first coordinate of `F (z, 1)`. Continuity of `F` and
the product projections proves `g` continuous. Applying the boundary identity
and projecting its first coordinate proves that `g` restricts to the identity
on the unit circle. These steps are compiled in `Main.lean`.

The full abstract obstruction is now also compiled locally: a retraction
induces an injective fundamental-group map, and no injection exists from a
nontrivial group into a subsingleton group.

`apm_t97J03_no_disk_retraction` specializes this to the precise frozen
subtypes. It identifies `{z : ℂ // ‖z‖ ≤ 1}` with the metric closed ball,
transports Mathlib's contractibility instance, derives simple connectivity,
and installs the exact subsingleton disk fundamental-group instance. Its only
remaining premise is nontriviality of the exact circle fundamental group.

Thus the desired contradiction is exactly the theorem that the complex unit
disk does not retract continuously onto its boundary. All functorial and group
bookkeeping for that route is compiled. Mathlib currently lacks only the
nontriviality computation for the circle fundamental group and also has no
packaged Brouwer no-retraction theorem.

Checked Lean state: exit 0; one `sorry` remains.
