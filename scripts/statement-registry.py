#!/usr/bin/env python3
"""The approved statement registry: problems/STATEMENTS.json.

A problem counts as closed only when its statement is one an outside grader
approved (Joe, 2026-09-28: "The statements should be from a registry that is
approved, not allowed to be vacuous"). Before this, the frozen statement was
whatever Main.lean said on master, and 18 of 62 closed topology problems
turned out to be narrower than, vacuous against, or to assume the core of the
problem they claim to answer (/home/joe/topo-watch/grades-summary.md).

Fingerprint: the declared theorem(s) from `theorem NAME` to the first `:=` at
bracket depth 0, plus every same-file definition the statement reaches
(transitively), comments stripped, whitespace normalised, sha256. Following
definitions is what catches a statement changed through a definition it uses:
on 2026-09-10 t96J05's header stayed byte-identical while
apm_t96j05_IsSmoothRadialLevel changed. Library (non-file) definitions are not
fingerprinted.

Admission accepts grade faithful or stronger. narrower is accepted only with a
documented defect in problem.md itself (--prelim-defect). A statement that
reaches an `axiom`, an `opaque`, or a `sorry` inside a definition is refused.

  statement-registry.py fingerprint ID [--decl NAME]... [--rev REV]
  statement-registry.py admit ID --grade G --grader WHO --evidence PATH
                              [--decl NAME]... [--prelim-defect PATH]
  statement-registry.py check [--rev REV] [ID...]     exit 1 on any mismatch
  statement-registry.py status ID [--rev REV]         registered|mismatch|unregistered
  statement-registry.py revoke ID --reason TEXT --evidence PATH
      remove an entry found to be inadmissible; the removal is kept in "revoked"
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "problems" / "STATEMENTS.json"
ADMISSIBLE = {"faithful", "stronger"}
DECL_START = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|instance|example)\b\s*"
    r"([^\s:({\[]*)")
BLOCK_END = re.compile(r"(?m)^(?:namespace|end|section|open|variable|set_option|#)\b")
OMEGA = re.compile(r"\b(?:IsManifold|ContMDiff\w*|ContDiff\w*|IsLocalDiffeomorph\w*|MDifferentiable\w*|Diffeomorph)\b[^\n]*?\s⊤(?=[\s)\]])")
IDENT = re.compile(r"[A-Za-z_Ͱ-Ͽἀ-῿][A-Za-z0-9_'.Ͱ-Ͽἀ-῿]*")


def git(*args: str) -> str:
    r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def strip_comments(src: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
            continue
        out.append(src[i]); i += 1
    return "".join(out)


def blocks(src: str) -> list[dict]:
    starts = list(DECL_START.finditer(src))
    res = []
    for k, m in enumerate(starts):
        end = starts[k + 1].start() if k + 1 < len(starts) else len(src)
        stop = BLOCK_END.search(src, m.end(), end)
        body = src[m.start(): stop.start() if stop else end]
        res.append({"kind": m.group(1), "name": m.group(2), "body": body})
    return res


def header(body: str) -> str:
    depth = 0
    for i, ch in enumerate(body):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and body.startswith(":=", i):
            # A `let x := ...` or `have h := ...` line inside the statement is
            # not the proof. m93J05's fingerprint stopped at `let μ` and covered
            # one line of its theorem (2026-10-13).
            line = body[body.rfind("\n", 0, i) + 1:i]
            if re.match(r"\s*(let|have)\b", line):
                continue
            return body[:i]
    return body


def short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def fingerprint(src: str, decls: list[str]) -> dict:
    src = strip_comments(src)
    bs = blocks(src)
    theorems = {b["name"]: b for b in bs if b["kind"] in ("theorem", "lemma")}
    defs = {}
    for b in bs:
        if b["kind"] not in ("theorem", "lemma", "example", "instance") and b["name"]:
            defs.setdefault(short(b["name"]), b)
    parts, flags, seen, todo = [], [], set(), []
    for d in decls:
        t = theorems.get(d) or next((v for k, v in theorems.items() if short(k) == d), None)
        if t is None:
            return {"missing": d}
        h = header(t["body"])
        parts.append(" ".join(h.split()))
        todo += IDENT.findall(h[len("theorem"):])
    while todo:
        tok = short(todo.pop())
        if tok in seen or tok not in defs:
            continue
        seen.add(tok)
        b = defs[tok]
        parts.append(" ".join(b["body"].split()))
        if b["kind"] in ("axiom", "opaque"):
            flags.append(f"{b['kind']} {tok}")
        if re.search(r"\bsorry\b", b["body"]):
            flags.append(f"sorry in {tok}")
        todo += IDENT.findall(b["body"])
    text = "\n".join(parts)
    # A bare ⊤ : WithTop ℕ∞ as a smoothness order is ω (analytic) in the pinned
    # Mathlib; C^∞ is (⊤ : ℕ∞) or ∞. Seven registered statements carried it
    # unnoticed by three graders (2026-09-28, omega-check.md).
    if OMEGA.search(text):
        flags.append("smoothness order bare ⊤ (analytic, not C^∞)")
    return {"sha256": hashlib.sha256(text.encode()).hexdigest(), "defs": sorted(seen),
            "flags": flags, "text": text}


def main_src(pid: str, rev: str | None) -> str:
    path = f"problems/{pid}/lean/Main.lean"
    return git("show", f"{rev}:{path}") if rev else (ROOT / path).read_text()


def load() -> dict:
    return json.loads(REGISTRY.read_text()) if REGISTRY.exists() else {"schema": "apm-statement-registry.v1", "entries": {}}


def default_decls(pid: str) -> list[str]:
    return [f"apm_{pid.lower()}"]


def status_of(pid: str, rev: str | None, reg: dict | None = None) -> str:
    e = (reg or load())["entries"].get(pid)
    if not e:
        return "unregistered"
    fp = fingerprint(main_src(pid, rev), e["decls"])
    return "registered" if fp.get("sha256") == e["sha256"] else "mismatch"


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("fingerprint"); f.add_argument("id"); f.add_argument("--decl", action="append"); f.add_argument("--rev")
    a = sub.add_parser("admit"); a.add_argument("id"); a.add_argument("--decl", action="append")
    a.add_argument("--grade", required=True); a.add_argument("--grader", required=True)
    a.add_argument("--evidence", required=True); a.add_argument("--prelim-defect")
    c = sub.add_parser("check"); c.add_argument("ids", nargs="*"); c.add_argument("--rev", default="HEAD")
    s = sub.add_parser("status"); s.add_argument("id"); s.add_argument("--rev", default="HEAD")
    v = sub.add_parser("revoke"); v.add_argument("id"); v.add_argument("--reason", required=True)
    v.add_argument("--evidence", required=True)
    o = ap.parse_args()

    if o.cmd == "fingerprint":
        fp = fingerprint(main_src(o.id, o.rev), o.decl or default_decls(o.id))
        print(json.dumps({k: v for k, v in fp.items() if k != "text"}, indent=1)); print(fp.get("text", ""))
        return 0
    if o.cmd == "status":
        print(status_of(o.id, o.rev)); return 0
    if o.cmd == "check":
        reg = load(); bad = []
        for pid in o.ids or sorted(reg["entries"]):
            st = status_of(pid, o.rev, reg)
            if st != "registered":
                bad.append(pid); print(f"{pid}: {st}", file=sys.stderr)
        print(f"{len(o.ids or reg['entries']) - len(bad)} registered statements match, {len(bad)} do not", file=sys.stderr)
        return 1 if bad else 0

    if o.cmd == "revoke":
        reg = load()
        if o.id not in reg["entries"]:
            raise SystemExit(f"{o.id} is not registered")
        if not Path(o.evidence).exists():
            raise SystemExit(f"evidence {o.evidence} does not exist")
        entry = reg["entries"].pop(o.id)
        reg.setdefault("revoked", []).append({
            "id": o.id, "entry": entry, "reason": o.reason, "evidence": o.evidence,
            "revoked_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")})
        REGISTRY.write_text(json.dumps(reg, indent=1, ensure_ascii=False) + "\n")
        print(f"revoked {o.id}: {o.reason}")
        return 0

    # admit
    if o.grade not in ADMISSIBLE and not (o.grade == "narrower" and o.prelim_defect):
        raise SystemExit(f"refused {o.id}: grade {o.grade!r} is not admissible"
                         " (faithful/stronger; narrower only with --prelim-defect)")
    for p in [o.evidence] + ([o.prelim_defect] if o.prelim_defect else []):
        if not Path(p).exists():
            raise SystemExit(f"refused {o.id}: evidence {p} does not exist")
    decls = o.decl or default_decls(o.id)
    fp = fingerprint(main_src(o.id, "HEAD"), decls)
    if "missing" in fp:
        raise SystemExit(f"refused {o.id}: no theorem {fp['missing']} in committed Main.lean")
    if fp["flags"]:
        raise SystemExit(f"refused {o.id}: statement reaches {', '.join(fp['flags'])}")
    reg = load()
    reg["entries"][o.id] = {
        "decls": decls, "sha256": fp["sha256"], "defs": fp["defs"], "grade": o.grade,
        "grader": o.grader, "evidence": o.evidence, "prelim_defect": o.prelim_defect,
        "rev": git("rev-parse", "--short", "HEAD").strip(),
        "approved_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}
    reg["entries"] = dict(sorted(reg["entries"].items()))
    REGISTRY.write_text(json.dumps(reg, indent=1, ensure_ascii=False) + "\n")
    print(f"admitted {o.id} {o.grade} {fp['sha256'][:12]} defs={len(fp['defs'])}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
