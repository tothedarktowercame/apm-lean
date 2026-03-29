#!/usr/bin/env bash
# Generate the task manifest from the APM LaTeX files.
# Output: manifest/tasks.tsv (id, subject, year, session, number, path)

set -euo pipefail

SRC="${1:-$HOME/code/storage/apm}"
OUT="$(dirname "$0")/manifest/tasks.tsv"

echo -e "id\tsubject\tyear\tsession\tnumber\tpath" > "$OUT"

for f in "$SRC"/*.tex; do
  base=$(basename "$f" .tex)
  # Naming: a96A03 → subject=a (analysis), year=96, session=A, number=03
  #         b03J02 → subject=b (algebra), year=03, session=J, number=02
  #         t01A01 → subject=t (topology), year=01, session=A, number=01
  #         m96A04 → subject=m (functional), year=96, session=A, number=04
  subject="${base:0:1}"
  year="${base:1:2}"
  session="${base:3:1}"
  number="${base:4:2}"
  echo -e "${base}\t${subject}\t${year}\t${session}\t${number}\t${f}" >> "$OUT"
done

total=$(tail -n+2 "$OUT" | wc -l)
echo "Manifest: $total problems written to $OUT"
echo "Subjects: $(tail -n+2 "$OUT" | cut -f2 | sort | uniq -c | sort -rn)"
