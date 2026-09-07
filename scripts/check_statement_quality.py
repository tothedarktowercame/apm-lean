#!/usr/bin/env python3
"""Screen APM Lean statement encodings for the failure modes that got the
2026-09-07 sweep reverted (51a8a06e).

That sweep landed 42 encodings which "parameterize over named Props or free
variables instead of stating mathematics", ranging from vacuous
(apm_t99j02: three abstract Props conjoined) through trivially provable
(apm_m98j01: hypothesis identical to conclusion) to refutable
(apm_t93j05: forall dOmega : R, dOmega = 2).  All 42 typecheck -- `sorry`
makes any well-formed statement compile -- so `lake env lean` alone cannot
tell an encoding from a stub.  These checks can.

This is a SCREEN, not a proof of quality.  It catches the mechanical
failures cheaply so that human/agent review is spent on the mathematics
rather than on re-finding stubs.  A file passing every check may still
encode the wrong theorem.

Usage:  scripts/check_statement_quality.py t99A01 t99A02 ...
        scripts/check_statement_quality.py --all-missing
Exit 0 only if every id passes.
"""
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAKE_TIMEOUT = 300

# Tactics that close a goal carrying no mathematical content.  If any of these
# proves the statement, the statement was not worth stating.
TRIVIAL_TACTICS = ["trivial", "simp", "decide", "rfl", "exact trivial",
                   "constructor <;> rfl", "assumption"]


def lean_path(pid):
    return os.path.join(ROOT, "problems", pid, "lean", "Main.lean")


def compile_text(text):
    """Compile TEXT as a standalone Lean file. Returns (ok, output)."""
    fd, path = tempfile.mkstemp(suffix=".lean", dir="/tmp")
    try:
        with os.fdopen(fd, "w") as fh:
            fh.write(text)
        p = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=LAKE_TIMEOUT)
        return p.returncode == 0, (p.stdout + p.stderr)
    except subprocess.TimeoutExpired:
        return False, "timeout after %ds" % LAKE_TIMEOUT
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def split_theorem(text):
    """Return (signature, proof_body) for the last `theorem apm_...` in TEXT."""
    m = None
    for m in re.finditer(r"^theorem\s+(apm_[A-Za-z0-9_]+)", text, re.M):
        pass
    if not m:
        return None, None
    start = m.start()
    rest = text[start:]
    cut = rest.find(":= by")
    if cut < 0:
        cut = rest.find(":=")
        if cut < 0:
            return rest, ""
    return rest[:cut], rest[cut:]


def check(pid):
    """Return list of (level, message). level in {'FAIL','warn'}."""
    out = []
    path = lean_path(pid)
    if not os.path.exists(path):
        return [("FAIL", "no problems/%s/lean/Main.lean" % pid)]
    text = open(path, errors="replace").read()

    if not re.search(r"^import\s+Mathlib", text, re.M):
        out.append(("FAIL", "does not import Mathlib"))

    sig, body = split_theorem(text)
    if sig is None:
        return out + [("FAIL", "no `theorem apm_<id>` declaration")]

    # (1) OPAQUE PROPS -- the apm_t99j02 failure.  A statement that binds its
    # own propositions says nothing about the problem's mathematics.
    props = re.findall(r"\(\s*([A-Za-z][A-Za-z0-9_' ]*?)\s*:\s*Prop\s*\)", sig)
    if props:
        out.append(("FAIL", "binds opaque Prop variables (%s): a statement that "
                            "quantifies over its own propositions states nothing"
                    % ", ".join(w.strip() for w in props)))

    # (2) NO MATHEMATICAL STRUCTURE -- the apm_t93j05 failure.  Real encodings
    # carry typeclass instances ([TopologicalSpace X]) or named Mathlib
    # constructions; stubs bind bare reals and constrain them.
    instances = re.findall(r"\[[^\]]+\]", sig)
    caps = set(re.findall(r"\b([A-Z][A-Za-z0-9]{2,})\b", sig)) - {"Type", "Sort", "Prop"}
    if not instances and len(caps) < 2:
        out.append(("FAIL", "no typeclass instances and %d named structures %s: "
                            "nothing ties this to the problem's mathematics"
                    % (len(caps), sorted(caps))))

    # (3) CONSTANT CLAIM -- `dOmega = 2 and surfaceIntegral = 0`.  A conclusion
    # that only pins free variables to literals is refutable, not a theorem.
    concl = sig.split(":")[-1]
    eqs = re.findall(r"([A-Za-z][A-Za-z0-9_']*)\s*=\s*([0-9]+|[A-Za-z][A-Za-z0-9_']*)", concl)
    bare = [v for v, _ in eqs if v in sig.split(":")[0] or True]
    if eqs and not instances and len(eqs) >= 1 and len(caps) < 2:
        out.append(("FAIL", "conclusion only equates free variables to literals "
                            "(%s): refutable, not a theorem"
                    % ", ".join("%s = %s" % e for e in eqs[:3])))

    # (4) TYPECHECKS.  Necessary, not sufficient -- `sorry` compiles anything
    # well-formed -- but a statement that does not compile is not a statement.
    ok, log = compile_text(text)
    if not ok:
        first = next((l for l in log.splitlines() if "error" in l.lower()), log[:160])
        out.append(("FAIL", "does not compile: %s" % first.strip()[:160]))
        return out

    # (5) TRIVIALLY PROVABLE -- the apm_m98j01 failure (hypothesis identical to
    # conclusion).  Swap `sorry` for a content-free tactic; if the file still
    # compiles, the goal carried no content.
    if "sorry" in body:
        for tac in TRIVIAL_TACTICS:
            probe = text[:text.rfind("sorry")] + tac + text[text.rfind("sorry") + 5:]
            ok2, _ = compile_text(probe)
            if ok2:
                out.append(("FAIL", "closes by `%s`: the goal has no content" % tac))
                break
    else:
        out.append(("warn", "no `sorry`: statement is already proved, "
                            "check it is the STATEMENT that was wanted"))

    # (6) UNCONDITIONAL CLAIM -- the apm_t99a02 shape ("every type is
    # Nonempty").  Not decidable here; surfaced for the reviewer.
    if not instances and not re.search(r"\(\s*h[A-Za-z0-9_']*\s*:", sig):
        out.append(("warn", "no instances and no named hypotheses: verify the "
                            "claim is not refutable by a degenerate instance"))
    return out


def main(argv):
    ids = argv[1:]
    if ids == ["--all-missing"]:
        pdir = os.path.join(ROOT, "problems")
        ids = sorted(d for d in os.listdir(pdir)
                     if not os.path.exists(os.path.join(pdir, d, "lean", "Main.lean")))
        print("%d bundles still lack lean/Main.lean:\n  %s\n" % (len(ids), " ".join(ids)))
        return 1 if ids else 0
    if not ids:
        print(__doc__)
        return 2
    bad = 0
    for pid in ids:
        res = check(pid)
        fails = [m for lvl, m in res if lvl == "FAIL"]
        warns = [m for lvl, m in res if lvl == "warn"]
        print("%-28s %s" % (pid, "FAIL" if fails else "pass"))
        for m in fails:
            print("      FAIL  %s" % m)
        for m in warns:
            print("      warn  %s" % m)
        if fails:
            bad += 1
    print("\n%d/%d passed the screen." % (len(ids) - bad, len(ids)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
