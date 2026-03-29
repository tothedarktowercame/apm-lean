#!/usr/bin/env python3
"""Extract streamed text from claude --output-format stream-json.

Reads stream-json lines from stdin, writes extracted text to the file
given as argv[1], and prints progress lines to stderr every N bytes.

Usage:
  cat prompt | claude -p - --output-format stream-json --verbose 2>/dev/null \
    | python3 stream-extract.py output.md
"""
import sys, json

if len(sys.argv) < 2:
    print("Usage: stream-extract.py <output-file>", file=sys.stderr)
    sys.exit(1)

outpath = sys.argv[0 + 1]
total_bytes = 0
last_report = 0
REPORT_INTERVAL = 500  # bytes between progress reports

with open(outpath, 'w') as out:
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue

        if obj.get('type') == 'assistant':
            msg = obj.get('message', {})
            content = msg.get('content', [])
            for part in content:
                if isinstance(part, dict) and part.get('type') == 'text':
                    text = part['text']
                    out.write(text)
                    out.flush()
                    total_bytes += len(text)
                    if total_bytes - last_report >= REPORT_INTERVAL:
                        lines = open(outpath).read().count('\n')
                        print(f"  ... {lines} lines, {total_bytes} bytes written",
                              file=sys.stderr, flush=True)
                        last_report = total_bytes

if total_bytes > 0:
    lines = open(outpath).read().count('\n')
    print(f"  => done: {lines} lines, {total_bytes} bytes",
          file=sys.stderr, flush=True)
else:
    print("  => warning: no content extracted", file=sys.stderr, flush=True)
