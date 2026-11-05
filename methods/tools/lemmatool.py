#!/usr/bin/env python3
"""Per-lemma files for parallel seats (claude-14, 2026-10-13).

make P NAME   -> holes/labs/lemmas/P/NAME.lean: Blueprint.lean with the lemma NAME
                 wrapped in SEAT AREA markers (seat edits only inside them).
check P NAME  -> outside-area text identical to the template, NAME's statement
                 unchanged, file compiles, NAME's axioms exclude sorryAx.
splice P NAME -> copy the seat area into holes/labs/blueprints/P/Blueprint.lean.
path P        -> print the source file of P, relative to the worktree.

P = CT.Module names a shared file, ConstructionTargets/Module.lean (family
blueprints, 2026-10-18); its lemma files go in holes/labs/lemmas/CT.Module/.
"""
import re, subprocess, sys
from pathlib import Path
W = Path.home() / "worktrees/apm-lean/lemmas"
B, E = "-- BEGIN SEAT AREA", "-- END SEAT AREA"

def rel(p):
    return f"ConstructionTargets/{p[3:]}.lean" if p.startswith("CT.") else f"holes/labs/blueprints/{p}/Blueprint.lean"
def blueprint(p): return W / rel(p)
def lemfile(p, n): return W / f"holes/labs/lemmas/{p}/{n}.lean"

def block(src, n):
    m = re.search(rf"^(theorem|lemma) {re.escape(n)}\b", src, re.M)
    s = m.start()
    # The sorry must be this lemma's own: stop at the next top-level declaration.
    # Without the bound, re-landing an already-spliced lemma replaced everything
    # up to a later lemma's sorry (a02945480, 2026-10-18).
    nxt = re.compile(r"^(/--|@\[|(private |protected |noncomputable )*(theorem|lemma|def|instance|abbrev|structure|class|example) |end |namespace |section )", re.M).search(src, src.index("\n", s) + 1)
    lim = nxt.start() if nxt else len(src)
    so = re.compile(r"^[ \t]*sorry[ \t]*$", re.M).search(src, s, lim)
    if not so: sys.exit(f"{n}: no sorry of its own in the blueprint (already spliced?)")
    e = src.index("\n", so.start()) + 1
    return s, e

def header(text, n):
    s = re.search(rf"^(theorem|lemma) {re.escape(n)}\b", text, re.M).start()
    return " ".join(text[s:text.index(":= by", s)].split())

def qualified(src, n):
    # Namespace in force at the lemma, for #print axioms (a00J04 sits in
    # ApmCanaries.A00J04).
    stack = []
    for m in re.finditer(r"^(namespace|end) ([\w.]+)", src[:re.search(rf"^(theorem|lemma) {re.escape(n)}\b", src, re.M).start()], re.M):
        if m.group(1) == "namespace": stack.append(m.group(2))
        elif stack and stack[-1] == m.group(2): stack.pop()
    return ".".join(stack + [n])

def split(text):
    i, j = text.index(B), text.index(E)
    return text[:i], text[i + len(B):j], text[j + len(E):]

def make(p, n):
    src = blueprint(p).read_text(); s, e = block(src, n)
    f = lemfile(p, n); f.parent.mkdir(parents=True, exist_ok=True)
    f.write_text(src[:s] + B + "\n" + src[s:e] + E + "\n" + src[e:]); print(f)

def template(p, n):
    # The blueprint as it was when the lemma file was made: later splices of
    # other lemmas must not count as edits outside this seat's area.
    # A re-queued lemma is re-issued from a newer blueprint by next.sh ("lemmas: file
    # for P/N"); the latest such commit is the template, else the file's creation.
    rev = subprocess.run(["git", "log", "--format=%H", "-1", "--fixed-strings",
                          f"--grep=lemmas: file for {p}/{n} ", "--",
                          str(lemfile(p, n).relative_to(W))], cwd=W, capture_output=True, text=True).stdout.strip()
    if not rev:
        rev = subprocess.run(["git", "log", "--format=%H", "--diff-filter=A", "-1", "--",
                              str(lemfile(p, n).relative_to(W))], cwd=W, capture_output=True, text=True).stdout.strip()
    return subprocess.run(["git", "show", f"{rev}:{rel(p)}"],
                          cwd=W, capture_output=True, text=True, check=True).stdout

def check(p, n):
    f = lemfile(p, n); t = f.read_text(); src = template(p, n); s, e = block(src, n)
    a, mid, z = split(t)
    if a != src[:s] or z.lstrip("\n") != src[e:].lstrip("\n"): return print("FAIL text outside the seat area changed")
    if header(mid, n) != header(src[s:e], n): return print("FAIL statement of", n, "changed")
    if re.search(r"\bsorry\b|\badmit\b|^\s*axiom\b", mid, re.M): return print("FAIL sorry/admit/axiom in seat area")
    tmp = f.with_suffix(".check.lean"); tmp.write_text(t + f"\n#print axioms {qualified(src, n)}\n")
    r = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G",
                        "lake", "env", "lean", str(tmp)], cwd=W, capture_output=True, text=True, timeout=3600)
    tmp.unlink(); out = r.stdout + r.stderr
    errs = [l for l in out.splitlines() if ": error" in l]
    # #print axioms wraps long lists over several lines: read up to the closing ']'.
    ax = re.findall(rf"'{re.escape(qualified(src, n))}' depends on axioms: \[[^\]]*\]", out)
    ax = [" ".join(a.split()) for a in ax]
    if errs: return print("FAIL compile:", *errs[:5], sep="\n  ")
    if not ax or "sorryAx" in ax[-1]: return print("FAIL axioms:", ax[-1:] or "none printed")
    print("PASS", ax[-1])

def splice(p, n):
    _, mid, _ = split(lemfile(p, n).read_text())
    src = blueprint(p).read_text(); s, e = block(src, n)
    # A seat may restate a helper the blueprint already has (banked from an
    # earlier attempt); drop such duplicates (m98J02, 2026-10-13).
    outside = src[:s] + src[e:]
    # Ignore declarations inside /- ... -/ block comments (t99A01, 2026-10-15).
    outside = re.sub(r"/-(?!-).*?-/", "", outside, flags=re.S)
    decl = re.compile(r"^(lemma|theorem) (\S+)", re.M)
    starts = [m for m in decl.finditer(mid)]
    keep, cut = [], 0
    for k, m in enumerate(starts):
        end = starts[k + 1].start() if k + 1 < len(starts) else len(mid)
        if m.group(2) != n and re.search(rf"^(lemma|theorem) {re.escape(m.group(2))}\b", outside, re.M):
            keep.append(mid[cut:m.start()]); cut = end; print("dropped duplicate", m.group(2))
    mid = "".join(keep) + mid[cut:]
    blueprint(p).write_text(src[:s] + mid.lstrip("\n") + src[e:]); print("spliced", n)

{"make": make, "check": check, "splice": splice, "path": lambda p: print(rel(p))}[sys.argv[1]](*sys.argv[2:])
