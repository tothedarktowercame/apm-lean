#!/usr/bin/env python3
"""Bonus stage: a model judges which Lean lemma, if any, proves each informal step.

futon6's align_informal_lean.py matches S3 proof steps to Lean lemmas by word
overlap; about two thirds of its matches are right (futon6
holes/M-informal-lean-alignment.md). This asks a model to choose among the
top three candidates it recorded for each step, or to say none of them
proves it. It is an extra stage for the APM corpus, deliberately outside the
futon6 pipeline others run: it needs a served model, and its answers are a
model's judgement, not a measurement.

For every step it shows the model the step's premises, conclusion and stated
reason, and each candidate's name, docstring and statement, and requires a
JSON answer {"choice": 0..k, "reason": "..."} (0 = none). It then recomputes
the hole test from the judged choices: do the steps S3 flagged as missing a
reason have their own lemma more often than other steps?

  judge-alignment.py --alignment-dir DIR --lean-root REPO --futon6 FUTON6 \\
      --endpoint http://localhost:8000/v1 --model mark4-70b --out DIR \\
      [--ids IDS] [--concurrency 16]
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import glob
import json
import sys
import urllib.request
from pathlib import Path

PROMPT = """You are checking a match between a step of an informal proof and a Lean lemma.

Informal step
  premises: {premises}
  conclusion: {conclusion}
  stated reason: {warrant}

Candidate Lean lemmas
{candidates}

Which candidate proves this step: its hypotheses correspond to the premises (or a
subset of them) and its conclusion to the step's conclusion? Answer 0 if none of
them does. A lemma that only mentions the same objects is not a match.
Give the number and a one-sentence reason in plain words."""


def decl_text(decls: dict, name: str) -> str:
    d = decls.get(name)
    if not d:
        return f"`{name}` (statement not found)"
    doc = f"\n      doc: {d['doc'][:300]}" if d["doc"] else ""
    return f"`{name}`{doc}\n      statement: {d['signature'][:500]}"


def ask(endpoint: str, model: str, prompt: str, k: int) -> dict:
    schema = {"type": "object", "additionalProperties": False, "required": ["choice", "reason"],
              "properties": {"choice": {"type": "integer", "enum": list(range(k + 1))},
                             "reason": {"type": "string", "maxLength": 300,
                                        "pattern": '^[^\\u0000-\\u001f"\\\\]*$'}}}
    body = {"model": model, "temperature": 0, "max_tokens": 200,
            "messages": [{"role": "user", "content": prompt}],
            "response_format": {"type": "json_schema",
                                "json_schema": {"name": "judge", "strict": True, "schema": schema}}}
    req = urllib.request.Request(f"{endpoint.rstrip('/')}/chat/completions", json.dumps(body).encode(),
                                 {"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=600) as r:
        content = json.loads(r.read())["choices"][0]["message"]["content"]
    return json.loads(content)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--alignment-dir", required=True, type=Path)
    ap.add_argument("--lean-root", required=True, type=Path)
    ap.add_argument("--lean-pattern", default="problems/{paper}/lean/*.lean")
    ap.add_argument("--futon6", required=True, type=Path, help="futon6 checkout (for its Lean parser)")
    ap.add_argument("--endpoint", default="http://localhost:8000/v1")
    ap.add_argument("--model", default="mark4-70b")
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--ids")
    ap.add_argument("--concurrency", type=int, default=16)
    args = ap.parse_args()
    sys.path.insert(0, str(args.futon6 / "scripts"))
    import align_informal_lean as align  # noqa: E402

    files = sorted(args.alignment_dir.glob("*.alignment.json"))
    if args.ids:
        want = {l.strip() for l in open(args.ids) if l.strip()}
        files = [f for f in files if f.name.split(".")[0] in want]
    jobs = []
    papers = {}
    for f in files:
        res = json.loads(f.read_text())
        pid = res["paper"]
        decls = {d["name"]: d for g in sorted(glob.glob(str(args.lean_root / args.lean_pattern.format(paper=pid))))
                 for d in align.lean_decls(Path(g), pid)}
        papers[pid] = res
        for kind in ("holes", "non_hole_steps"):
            for step in res[kind]:
                cands = step.get("candidates") or []
                if not cands:
                    step["judged"] = None
                    continue
                listing = "\n".join(f"  {i}. {decl_text(decls, c['decl'])}" for i, c in enumerate(cands, 1))
                prompt = PROMPT.format(premises="; ".join(step.get("premise_text") or []) or "(none)",
                                       conclusion=step.get("conclusion_text") or step["step"],
                                       warrant=step.get("warrant") or "(none)", candidates=listing)
                jobs.append((pid, step, prompt, len(cands)))

    def run(job):
        pid, step, prompt, k = job
        try:
            ans = ask(args.endpoint, args.model, prompt, k)
            step["judged"] = (step["candidates"][ans["choice"] - 1]["decl"] if ans["choice"] else None)
            step["judge_reason"] = ans["reason"]
        except Exception as e:                       # an unanswered step is recorded, not guessed
            step["judged"] = None
            step["judge_error"] = str(e)[:200]

    with cf.ThreadPoolExecutor(args.concurrency) as pool:
        list(pool.map(run, jobs))

    args.out.mkdir(parents=True, exist_ok=True)
    tot = {"holes": 0, "holes_lemma": 0, "steps": 0, "steps_lemma": 0, "agree": 0, "judged": 0, "errors": 0}
    for pid, res in papers.items():
        (args.out / f"{pid}.judged.json").write_text(json.dumps(res, indent=1, ensure_ascii=False) + "\n")
        for kind, n_key, l_key in (("holes", "holes", "holes_lemma"), ("non_hole_steps", "steps", "steps_lemma")):
            for s in res[kind]:
                if not s.get("candidates"):
                    continue
                tot[n_key] += 1
                tot["judged"] += 1
                tot["errors"] += "judge_error" in s
                tot[l_key] += bool(s.get("judged"))
                tot["agree"] += (s.get("judged") or None) == (s.get("lemma") or None)
    (args.out / "summary.json").write_text(json.dumps(tot, indent=1) + "\n")
    print(f"judged {tot['judged']} steps ({tot['errors']} errors); agrees with the classical choice on "
          f"{tot['agree']}; holes with a lemma {tot['holes_lemma']}/{tot['holes']}, "
          f"other steps {tot['steps_lemma']}/{tot['steps']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
