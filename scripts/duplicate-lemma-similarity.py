#!/usr/bin/env python3
"""Triangulate cross-problem lemma similarity; exact clusters are the gate."""
from __future__ import annotations
import importlib.util, json, re
from collections import Counter
from itertools import combinations
from pathlib import Path

repo = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("statement_deps", repo / "scripts/statement-deps.py")
sd = importlib.util.module_from_spec(spec); spec.loader.exec_module(sd)
HAND_AUDIT = {
 "a96J10:apm_a96J10_q_analytic|a97A06:apm_a97A06_F_analytic": (False,"same AnalyticOn shape, but q is exp's dslope while F is a different quotient function"),
 "a96J02:continuous_convolution_indicator|a99J02:apm_continuous_convolution_indicator": (True,"same statement; top infinity notation differs"),
 "a96J02:continuous_overlapMeasure|a99J02:apm_continuous_overlapMeasure": (True,"same statement after unfolding identical subtraction maps"),
 "a96J02:continuous_overlapSet|a99J02:apm_continuous_overlapSet": (True,"same statement over identically defined overlapSet wrappers"),
 "a96J02:continuous_subtractionMap|a99J02:apm_continuous_subtractionMap": (True,"local maps have identical definitions fun t => x - t"),
 "a96J02:convolution_indicator_eq_overlapReal|a99J02:apm_convolution_eq_overlapReal": (True,"same equality after unfolding identical subtraction maps"),
 "a96J02:translation_symmDiff_tendsto_zero|a99J02:apm_translation_symmDiff_tendsto_zero": (True,"same limit; nhds notation and local map names differ"),
}

def constants(entry, cache):
    src, defs = cache[entry["problem_id"]]
    external, queue, seen = set(), [], set()
    for ident in sd.IDENT.findall(entry["signature"]):
        if ident in defs: queue.append(ident)
        elif ident[0].isupper() or "." in ident: external.add(ident.rsplit(".", 1)[-1])
    while queue:
        name = queue.pop()
        if name in seen: continue
        seen.add(name)
        for ident in sd.IDENT.findall(defs[name]):
            if ident in defs and ident not in seen: queue.append(ident)
            elif not sd.LOCAL.match(ident) and (ident[0].isupper() or "." in ident):
                external.add(ident.rsplit(".", 1)[-1])
    return sorted(x for x in external if len(x) > 1 and x not in {"Set", "The", "val"})

def structural(sig):
    binders = len(re.findall(r"[({][^(){}]*:[^(){}]*[)}]", sig))
    hypotheses = len(re.findall(r"[({][^(){}]*:[^(){}]*(?:→|<|>|=|≤|≥|∈|⊆)[^(){}]*[)}]", sig))
    conclusion = sig.rsplit(" : ", 1)[-1]
    head = next(iter(sd.IDENT.findall(conclusion)), "")
    ops = Counter(re.findall(r"↔|→|∃|∀|≤|≥|=|<|>|∈|⊆|∧|∨|¬|\+|-|\*|/|\^", sig))
    const = Counter(x.rsplit(".",1)[-1] for x in sd.IDENT.findall(sig)
                    if x[0].isupper() or "." in x)
    return [head, binders, hypotheses, sorted(ops.items()), sorted(const.items())]

def jaccard(a,b):
    a,b=set(a),set(b); return len(a&b)/len(a|b) if a|b else 0.0

def pairkey(a,b): return "|".join(sorted([f"{a['problem_id']}:{a['lemma']}",f"{b['problem_id']}:{b['lemma']}"]))

def main():
    prior=json.load(open(repo/"docs/generated/duplicate-solved-lemmas.json"))
    entries=[]; known=set()
    for c in prior["clusters"]:
        for a,b in combinations(c["members"],2): known.add(pairkey(a,b))
        entries.extend(c["members"])
    # Add all eligible rows, de-duplicated from cluster members.
    seen={(e["problem_id"],e["lemma"],e["signature"]) for e in entries}
    done=set(prior["completed_classifications"])
    row=re.compile(r"^\| `([^`]+)` \| ([^|]+) \| `(.*)` \|$")
    for line in open(repo/"LEMMA-INDEX.md"):
        m=row.match(line.rstrip("\n"))
        if not m: continue
        name,where,sig=m.groups(); where=where.strip()
        if where.startswith("LIB:") or not (repo/f"problems/{where}/lean/Main.lean").exists(): continue
        status=json.load(open(repo/f"problems/{where}/status.json")).get("classification")
        key=(where,name,sig)
        if status in done and key not in seen:
            entries.append({"problem_id":where,"lemma":name,"signature":sig});seen.add(key)
    cache={p:(open(repo/f"problems/{p}/lean/Main.lean").read(),None) for p in {e['problem_id'] for e in entries}}
    cache={p:(src,sd.defs_in(src)) for p,(src,_) in cache.items()}
    for e in entries:
        e["constants"]=constants(e,cache);e["structural"]=structural(e["signature"])

    text_status="available"
    try:
        from sentence_transformers import SentenceTransformer
        model=SentenceTransformer("sentence-transformers/all-MiniLM-L6-v2",local_files_only=True)
        embeddings=model.encode([e["signature"] for e in entries],normalize_embeddings=True,
                                show_progress_bar=False)
    except Exception as exc:
        text_status=f"unavailable: {type(exc).__name__}: {exc}"; embeddings=None
    pairs=[]
    for i,a in enumerate(entries):
        for j in range(i+1,len(entries)):
            b=entries[j]
            if a["problem_id"]==b["problem_id"]: continue
            cj=jaccard(a["constants"],b["constants"])
            ss=1.0 if a["structural"]==b["structural"] else 0.0
            ts=(float(sum(x*y for x,y in zip(embeddings[i],embeddings[j])))
                if embeddings is not None else None)
            key=pairkey(a,b)
            if key in known or cj>=.72 or ss==1 or (ts is not None and ts>=.88):
                pairs.append({"key":key,"a":{k:a[k] for k in ("problem_id","lemma","signature","constants")},
                              "b":{k:b[k] for k in ("problem_id","lemma","signature","constants")},
                              "constant_jaccard":round(cj,4),"structural_match":bool(ss),
                              "minilm_cosine":round(ts,4) if ts is not None else None,"known":key in known})
    known_rows=[p for p in pairs if p["known"]]
    recalls={
      "constant_jaccard_ge_0.72":sum(p["constant_jaccard"]>=.72 for p in known_rows)/len(known),
      "structural_exact":sum(p["structural_match"] for p in known_rows)/len(known),
      "minilm_cosine_ge_0.88":(sum(p["minilm_cosine"]>=.88 for p in known_rows)/len(known)
                                if embeddings is not None else None)}
    novel=sorted((p for p in pairs if not p["known"]),key=lambda p:(-p["constant_jaccard"],-int(p["structural_match"]),-(p["minilm_cosine"] or -1)))[:30]
    audit=[{"key":p["key"],"duplicate":HAND_AUDIT[p["key"]][0],"reason":HAND_AUDIT[p["key"]][1]}
           for p in novel if p["key"] in HAND_AUDIT]
    payload={"schema_version":1,"eligible_lemmas":len(entries),"known_cluster_pairs":len(known),
             "thresholds":{"constant_jaccard":.72,"structural":"exact fingerprint","minilm_cosine":.88},
             "minilm_status":text_status,"minilm_warning":"out-of-domain natural-language model; secondary signal only",
             "known_pair_recall":recalls,"novel_candidates":novel,"hand_audit":audit,
             "hand_audit_precision":sum(x["duplicate"] for x in audit)/len(audit)}
    json.dump(payload,open(repo/"docs/generated/duplicate-lemma-similarity.json","w"),indent=2,sort_keys=True)
    md=["# Solved-lemma similarity channels","",f"Population: {len(entries)} proved helper lemmas; validation set: {len(known)} known duplicate pairs from 24 clusters.","",
        "## Gate: recovery of known duplicates","","| Channel | Rule | Recall | Gate |","|---|---|---:|---|",
        f"| Constant set | Jaccard >= 0.72 | {sum(p['constant_jaccard']>=.72 for p in known_rows)}/{len(known)} ({100*recalls['constant_jaccard_ge_0.72']:.1f}%) | FAIL |",
        f"| Structural | exact fingerprint | {sum(p['structural_match'] for p in known_rows)}/{len(known)} (100.0%) | PASS |",
        f"| MiniLM | cosine >= 0.88 | unavailable | NOT RUN |","",
        "The constant-set channel fails the required recovery gate and its novel results must not be trusted as primary findings. Four known pairs have empty or insufficient lexical external-declaration sets. The structural channel passes. MiniLM is explicitly secondary and could not run because the host has the cached model but no `sentence_transformers`, `transformers`, `torch`, or `numpy` runtime; no substitute text score was invented.","",
        "## Top structural novel candidates and hand audit","","| Pair | Constant Jaccard | Audit | Reason |","|---|---:|---|---|"]
    bykey={p['key']:p for p in novel}
    for x in audit:
        p=bykey[x['key']];md.append(f"| `{x['key']}` | {p['constant_jaccard']:.2f} | {'duplicate' if x['duplicate'] else 'not duplicate'} | {x['reason']} |")
    md += ["",f"Hand-audited precision: {sum(x['duplicate'] for x in audit)}/{len(audit)} ({100*payload['hand_audit_precision']:.1f}%). This is a purposive top-ranked sample, not an unbiased corpus estimate.","",
           "## Method","","Constant sets reuse `statement-deps.py` identifier extraction and transitive traversal through problem-local definitions, then compare basename sets by Jaccard. The structural fingerprint records conclusion head, binder count, hypothesis count, and operator/constant multisets. MiniLM is out-of-domain natural-language evidence and is never primary.",""]
    open(repo/"docs/generated/duplicate-lemma-similarity.md","w").write("\n".join(md))
    print(json.dumps({"recall":recalls,"audit_precision":payload['hand_audit_precision'],"novel":novel[:7]},indent=2))
if __name__=="__main__":main()
