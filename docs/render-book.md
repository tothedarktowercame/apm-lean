# Rendering APM Lean proofs with mfuton `render-book`

APM supplies the two project-specific seams; it does not depend on mfuton's
proof graph.

## Ordering and declaration source

`scripts/apm_render_book_provider.py` implements the shared
`BookDeclarationProvider` protocol by lifting APM's existing top-level Lean
segmenter into mfuton's typed declaration carriers. `arrange()` uses an APM id list as the editorial order. Each problem is
one section/page and contributes `problems/<id>/lean/Main.lean`; declarations
stay in source order.

Inspect or persist that arrangement with:

```sh
python3 scripts/apm_render_book_provider.py path/to/all-ids.txt
python3 scripts/apm_render_book_provider.py path/to/all-ids.txt \
  --out data/tmp/apm-render-arrangement.json
```

In a render process whose `PYTHONPATH` includes `mfuton-share/src`, call
`install()` before the ledger/ordering step. This registers the provider using
`set_book_declaration_provider`. The provider reads declaration positions and
kinds only; it neither constructs nor queries proof-graph edges.

## TeX to HTML

`config/render-book.json` owns the HTML backend choice. The default is
`latexml-oxide`; `latexml` remains an available fallback. The publication
script calls `scripts/tex-to-html.py`, so selecting a converter is data rather
than a branch embedded in the pipeline.

To override the default for one invocation:

```sh
python3 scripts/tex-to-html.py --backend latexml source.tex index.html
```

To use a different config for the existing publication command, set
`APM_RENDER_CONFIG=/path/to/render-book.json`.

The adapter needs mfuton's shared Python carrier types but does not need its
proof graph or private tree-sitter grammar.
