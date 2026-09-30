# m98A02 statement repair (2026-09-30)

Part (b) assumes `[Nontrivial X]`.

problem.md is false as printed: on the zero Banach space X = {0}, every
operator is 0, I − A = 0 is invertible with inverse 0, and the lower bound
1/(1+‖A‖) ≤ ‖(I−A)⁻¹‖ reads 1 ≤ 0. Compiled counterexample:
holes/labs/solve-loop/refutations/m98A02/Refute.lean (gitignored lab copy).
The intended argument uses ‖I‖ = 1, which holds exactly when X ≠ {0}.

Outside grade: holes/labs/statement-registry/m98A02-revision-grade.md
(narrower only by X ≠ {0}; correction; prelim defect yes).
