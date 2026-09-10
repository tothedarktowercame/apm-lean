# t96J07 statement repair

This is a specification repair followed by a proof of the corrected theorem, not closure of the old frozen theorem. The checkpoint20 election authorizes this repair under the standing SPEC-DEFECT policy.

Before, Lean parses the first conjunct as:

```text
forall x, (x != 0 -> projectivelyEq x (A x)) iff
  exists i, projectivelyEq x (axis i)
```

After, two explicit parentheses give:

```text
forall x, x != 0 -> (projectivelyEq x (A x) iff
  exists i, projectivelyEq x (axis i))
```

The old clause is false at zero. Its existing compiled refutation, `apm_t96j07_not_fixed_axis_clause`, is preserved verbatim, as are every definition and all five index/sum conjuncts. The corrected proof chooses a nonzero coordinate, identifies the eigenvalue, forces the other coordinates to vanish, and constructs the required scalar. The reverse implication uses the supplied axis relation. Finite products give the defined indices -1, 1, -1, 1 and their sum zero. This proves the encoded algebraic result; it adds no theorem comparing these definitions with an intrinsic projective derivative.

Original Main SHA256: e6e6a2247da5fef25f52343ba20b00c0b4b9efd9d29e4803808df7da7a645b74

Old statement SHA256: 73ea287c4fcc2f57d66253d4f3d13e1933715c77418a1d2c902a16bc2bd5c7fc

Corrected statement SHA256: 4ac8e3368212f29658a06d810fc3043f0a7b3dd16c7fbb603a46fd3cf09ee195

Statement hashes cover text beginning with `theorem apm_t96j07 :` and ending immediately before ` := by`.

Temporary complete Main SHA256: 6eac671c9e7ac401f30c08e2c10643e00c1ee968599462285b9273adf8f345e6

Probe compilation is warning-free. Both the old refutation and corrected theorem use only propext, Classical.choice and Quot.sound. Executable placeholders decrease from one in canonical Main to zero in the fixture. Canonical Main remains unchanged during probe; implementation and independent review must precede a corrected-closure record.
