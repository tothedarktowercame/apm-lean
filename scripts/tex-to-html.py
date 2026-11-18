#!/usr/bin/env python3
"""Run the configured TeX-to-HTML backend for APM publication."""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CONFIG = REPO_ROOT / "config" / "render-book.json"


def command(config_path: Path, source: Path, destination: Path, backend: str | None = None) -> list[str]:
    source = source.resolve()
    destination = destination.resolve()
    config = json.loads(config_path.read_text(encoding="utf-8"))["tex_to_html"]
    selected = backend or config["backend"]
    try:
        spec = config["backends"][selected]
    except KeyError as error:
        raise ValueError(f"unknown TeX-to-HTML backend: {selected}") from error
    executable = spec["executable"]
    if shutil.which(executable) is None:
        raise FileNotFoundError(f"TeX-to-HTML backend executable not found: {executable}")
    args = [str(item) for item in spec.get("args", ())]
    if selected == "latexml":
        return [executable, *args, f"--dest={destination}", str(source)]
    return [executable, *args, "--dest", str(destination), str(source)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--backend")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    try:
        cmd = command(args.config, args.source, args.destination, args.backend)
    except (FileNotFoundError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(error, file=sys.stderr)
        return 2
    if args.dry_run:
        print(json.dumps(cmd))
        return 0
    args.destination.parent.mkdir(parents=True, exist_ok=True)
    return subprocess.run(cmd, cwd=args.source.parent).returncode


if __name__ == "__main__":
    raise SystemExit(main())
