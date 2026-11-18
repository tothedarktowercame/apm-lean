from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def load_script(name: str):
    path = ROOT / "scripts" / name
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_apm_arrangement_uses_id_order_and_skips_missing(tmp_path: Path) -> None:
    provider = load_script("apm_render_book_provider.py")
    for problem_id in ("b", "a"):
        lean = tmp_path / "problems" / problem_id / "lean" / "Main.lean"
        lean.parent.mkdir(parents=True)
        lean.write_text("theorem t : True := trivial\n", encoding="utf-8")

    payload = provider.arrangement_json(tmp_path, ["a", "missing", "b"])

    assert [section["id"] for section in payload["sections"]] == ["a", "b"]
    assert payload["sections"][0]["lean_files"] == ["problems/a/lean/Main.lean"]


def test_tex_to_html_defaults_to_oxide() -> None:
    renderer = load_script("tex-to-html.py")
    cmd = renderer.command(
        ROOT / "config" / "render-book.json", Path("book.tex"), Path("index.html")
    )
    assert cmd[0] == "latexml_oxide"
    assert "--splitat=section" in cmd
    assert cmd[-3:] == ["--dest", str(Path("index.html").resolve()), str(Path("book.tex").resolve())]


def test_tex_to_html_backend_is_overridable(tmp_path: Path) -> None:
    renderer = load_script("tex-to-html.py")
    config = {
        "tex_to_html": {
            "backend": "unused",
            "backends": {"fake": {"executable": "python3", "args": ["-V"]}},
        }
    }
    path = tmp_path / "render.json"
    path.write_text(json.dumps(config), encoding="utf-8")
    assert renderer.command(path, Path("x.tex"), Path("x.html"), "fake") == [
        "python3", "-V", "--dest", str(Path("x.html").resolve()), str(Path("x.tex").resolve())
    ]
