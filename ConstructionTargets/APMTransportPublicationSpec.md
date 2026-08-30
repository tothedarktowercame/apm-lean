# APM transport/publication specification

`APMTransportPublicationSpec.lean` formalizes the transition vocabulary
recovered in `TN-apm-transport-conformance-program.md` Park 1.  It is a model
of the existing Clojure apparatus and its f63/f64 traces, not a replacement
scheduler design.

## Wire vocabulary

The proposed Park 3 EDN names mirror the Lean constructors:

- `:operation`: `:read`, `:write`, `:publication`,
  `:post-publication-verification`;
- `:acquired-outcome` and `:classified-outcome`: `:success`, `:timeout`,
  `:unavailable`, `:malformed`, `:authoritative-absence`, or
  `:visibility-lag`;
- `:evidence`: `:obtained`, `:not-obtained`, or `:invalid`;
- retry fields: `:attempt`, `:max-attempts`, `:wake-at-ms`, `:history`,
  `:last-valid-state`, and `:last-valid-evidence`;
- `:decision`: `[:retry wake-at-ms]`, `[:park reason]`, or `[:advance]`;
- identity fields: `:spec-id`, `:source-id`, and `:loaded-runtime-id`.

Keeping acquired and classified outcomes separate makes the f63 defect
checkable: its visibility lag/evidence-not-obtained acquisition was recorded
as authoritative absence and is therefore nonconformant.  The f64 fixture
records a timeout, a concrete delayed retry, retained evidence, one history
entry, and later successful visibility; the complete sequence is conformant.

## Proved properties

- transport failures and evidence-not-obtained cannot be authoritative
  absence;
- scheduling a retry preserves the last valid state and evidence;
- the decision function is deterministic;
- every decision either contains a concrete retry wake or is terminal;
- `f63_historical_nonconformant` rejects the historical collapse;
- `f64_retry_then_visibility_conformant` accepts the recovered two-step trace.

The target does not operate or restart a campaign and does not prescribe the
later Clojure implementation.  Park 3 should serialize this vocabulary and
compare generated values against it rather than translating failures through
a Boolean transport flag.
