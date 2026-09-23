#!/usr/bin/env python3
"""Add the shared wip/ stylesheets to a LaTeXML render.

The other LaTeXML pages under zone.hyperreal.enterprises/wip/ load, in order:

    LaTeXML.css  ltx-*.css  paper-site.css  tufte.css

LaTeXML emits the first two itself. The last two are shared across the whole
wip/ area, and they are *linked* rather than copied: tufte.css resolves its
ET Book @font-face URLs relative to its own location, so a copy sitting one
directory down would look for the fonts in the wrong place. A render published
to a subdirectory therefore refers to them as ../paper-site.css and ../tufte.css.

They go in with the other <link>s, *before* any inline <style>. tuftify.py
appends its layout block after every link, and that ordering is deliberate: its
measure and margin must win. paper-site.css is still wanted for the body face
and the LaTeXML bridge rules, which tuftify does not set, so it has to lose the
layout argument and win nothing else. Inserting it before </head> instead would
put it after tuftify's block and let its own max-width fight the Tufte measure.

tufte.css is only linked when tuftify has not already shipped a copy of its own
alongside the page.

    apply-wip-styling.py DIR [--prefix ../]
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

# Injected after tuftify's block, which is itself after every <link>. Two
# things only a split render needs; a single-file paper has neither problem.
SPLIT_FIXES = """<style>
/* LaTeXML emits .ltx_document once per *document*. With --splitat each page is
   a fragment and has .ltx_page_content instead, so tuftify's page padding has
   nothing to apply to and the text sits flush against the window edge. The
   :not(:has(..)) keeps this off the index, which does carry .ltx_document and
   would otherwise be indented twice. */
.ltx_page_content:not(:has(.ltx_document)) {
  padding: 3rem var(--pad) 6rem var(--pad); }

/* Splitting also gives every page a previous/up/next header. LaTeXML floats
   those three at each other, which at a Tufte measure makes them overstrike in
   the middle of the line. Lay them out as one wrapping row. */
.ltx_page_header { padding: .9rem var(--pad) 0; font-size: .8rem;
  line-height: 1.45; border-bottom: 1px solid #e4e2d8; margin-bottom: 1.2rem; }
.ltx_page_header .ltx_align_center { display: flex; flex-wrap: wrap;
  gap: .3rem 1.4rem; align-items: baseline; text-align: left; }
.ltx_page_header a, .ltx_page_header .ltx_ref { float: none !important;
  display: inline-block; max-width: 100%; }
.ltx_page_footer .ltx_align_center { display: flex; flex-wrap: wrap;
  gap: .3rem 1.4rem; }
.ltx_page_footer a { float: none !important; }

/* tuftify numbers a sidenote itself, from a CSS counter on .sidenote-number.
   LaTeXML also emits its own footnote number inside the note body as
   .ltx_tag_note, so each note opened with two numbers that did not even agree
   (the CSS counter is per page, LaTeXML's is per document). */
.sidenote .ltx_tag_note, .marginnote .ltx_tag_note { display: none; }

/* Upstream tufte.css sets `h1 span { display: table }` so that a .subtitle in
   a hand-written heading sits on its own line. LaTeXML puts a <span> inside
   every <sup>, <sub> and styled run, so a section title like "Weak-L² implies
   local L¹ with the right bound" came apart into five stacked lines. Keep the
   block treatment for the section number, which does want its own line. */
.ltx_title span:not(.ltx_tag) { display: inline; }

/* LaTeXML wraps a heading's hypertarget in <a name=..> with no href. It is a
   target, not a link, and colouring it made section titles two-tone: the part
   after the last <sup> turned blue. */
.ltx_title a.ltx_anchor { color: inherit; text-decoration: none; }

/* Lean listings. Code does not wrap (Joe, 2026-09-23): a wrapped continuation
   is indistinguishable from the next line of Lean, and indentation is how a
   tactic block is read. So white-space:pre, and the type is sized to make the
   scrollbar a rarity rather than the normal case -- over the 135,605 lines in
   the corpus the 99th percentile is 84 characters and the longest is 137,
   against roughly 100 that fit the measure here. LaTeXML writes font-size
   inline on the <pre>, hence the !important; tuftify sets overflow only under
   its 600px phone query. */
.ltx_verbatim, .ltx_listing, .ltx_para > pre {
  max-width: var(--measure);
  font-size: .7rem !important; line-height: 1.45;
  white-space: pre; overflow-x: auto; }
</style>
"""

HEAD_END = re.compile(r"</head>", re.I)
LAST_LINK = re.compile(r'(<link[^>]*\.css"[^>]*>)(?![\s\S]*<link[^>]*\.css")', re.I)


def style(text: str, prefix: str, local_tufte: bool) -> tuple[str, int]:
    sheets = ["paper-site.css"] + ([] if local_tufte else ["tufte.css"])
    if all(f"{prefix}{s}" in text for s in sheets):
        return text, 0
    links = "".join(
        f'\n<link rel="stylesheet" href="{prefix}{s}" type="text/css">' for s in sheets
    )
    fixed, n = LAST_LINK.subn(lambda m: m.group(1) + links, text, count=1)
    if not n:
        fixed, n = HEAD_END.subn(links + "\n</head>", text, count=1)
    if n and "ltx_page_content { padding" not in fixed:
        fixed = HEAD_END.sub(SPLIT_FIXES + "</head>", fixed, count=1)
    return fixed, n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("directory")
    ap.add_argument("--prefix", default="../",
                    help="path from the rendered pages to the shared stylesheets")
    args = ap.parse_args()

    directory = Path(args.directory)
    local_tufte = (directory / "tufte.css").is_file()
    done = skipped = 0
    for p in sorted(directory.glob("*.html")):
        src = p.read_text(encoding="utf-8", errors="replace")
        fixed, n = style(src, args.prefix, local_tufte)
        if n:
            p.write_text(fixed, encoding="utf-8")
            done += 1
        else:
            skipped += 1
    print(f"Styled {done} page(s)" + (f", {skipped} already styled or headless" if skipped else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
