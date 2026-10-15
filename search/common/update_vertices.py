#!/usr/bin/env python3
# THIS FILE ONLY: Uses APACHE 2.0 license. See search/APACHE20.txt.
# (Derived from the Noperthedron formalization project, which is Apache-2.0.)
"""Install new exact rational vertices into a solid's Lean model.

Reads the rational vertex list exported by the C++ tool codebdd
(model_vertices.lean, by default in $MODEL_DIR: N = 5 S rows, rotation-major,
index = S * orbit + seed) and rewrites TARGET, whose layout it detects:
- `def rationalVertices` (the snub dodecahedron's RationalVertices.lean,
  Nopert231's Vertices.lean): the bodies of `rationalVertices` (all N rows)
  and `seedVertex` (the first S rows), and the index sizes
  (VertexIndex = Fin N, SeedIndex = Fin S). With --solid_model, also the
  seed count S where that file spells it (`Fin S`, `Fin (5 * S)`,
  `icoOrbitsCheck S`, `seedCount := S`);
- `def slotVertices` (the pentagonal and deltoidal hexecontahedra's
  SolidModel.lean): the bodies of `slotVertices` (all N rows) and
  `seedVertices` (the first S rows), and N and S wherever the file spells
  them as `Fin N`, `Fin S`, `icoOrbitsCheck S` and `seedCount := S`.
The N and S in descriptive prose are not touched.

Usage: update_vertices.py [--exported FILE] [--solid_model FILE] TARGET
"""

from __future__ import annotations

import argparse
import os
import re
from pathlib import Path


def read_rows(exported: Path) -> list[str]:
    text = exported.read_text(encoding="utf-8")
    m = re.search(r"def rationalVertices : VertexIndex → Fin 3 → ℚ := !\[\n(.*?)\n\]", text, re.S)
    if not m:
        raise SystemExit(f"{exported}: no rationalVertices definition found")
    rows = [line.strip().rstrip(",") for line in m.group(1).splitlines() if line.strip()]
    if len(rows) % 5 != 0 or not all(r.startswith("![") and r.endswith("]") for r in rows):
        raise SystemExit(f"{exported}: expected 5 * seeds rows, got {len(rows)}")
    return rows


def replace_def(path: Path, text: str, header: str, rows: list[str]) -> str:
    pattern = re.compile(re.escape(header) + r"\n.*?\n\]", re.S)
    body = header + "\n" + ",\n".join("  " + r for r in rows) + "\n]"
    new, n = pattern.subn(lambda _: body, text, count=1)
    if n != 1:
        raise SystemExit(f"could not find `{header}` in {path}")
    return new


def substitute(path: Path, text: str, rules) -> str:
    """Each rule: (pattern, replacement string or function of the match, expected count)."""
    for pattern, repl, count in rules:
        text, k = re.subn(pattern, repl if callable(repl) else (lambda _, r=repl: r), text)
        if k != count:
            raise SystemExit(f"{path}: expected {count} match(es) for {pattern}, got {k}")
    return text


def seed_count_rules(seeds: int) -> list:
    return [(r"icoOrbitsCheck \d+ iOrbitCount", f"icoOrbitsCheck {seeds} iOrbitCount", 1),
            (r"seedCount := \d+\n", f"seedCount := {seeds}\n", 1)]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exported", type=Path, default=None,
                        help="codebdd's model_vertices.lean (default: $MODEL_DIR/model_vertices.lean)")
    parser.add_argument("--solid_model", type=Path, default=None,
                        help="with a rationalVertices TARGET: the SolidModel.lean whose seed count to update")
    parser.add_argument("target", type=Path)
    args = parser.parse_args()
    if args.exported is None:
        if not os.environ.get("MODEL_DIR"):
            raise SystemExit("pass --exported or set MODEL_DIR to the C++ pipeline directory")
        args.exported = Path(os.environ["MODEL_DIR"]) / "model_vertices.lean"
    rows = read_rows(args.exported)
    n, seeds = len(rows), len(rows) // 5
    text = args.target.read_text(encoding="utf-8")
    updated = [args.target]
    if "def rationalVertices : VertexIndex" in text:
        text = replace_def(args.target, text, "def rationalVertices : VertexIndex → Fin 3 → ℚ := ![", rows)
        text = replace_def(args.target, text, "def seedVertex : SeedIndex → Fin 3 → ℚ := ![", rows[:seeds])
        text = substitute(args.target, text, [
            (r"abbrev VertexIndex := Fin \d+", f"abbrev VertexIndex := Fin {n}", 1),
            (r"abbrev SeedIndex := Fin \d+", f"abbrev SeedIndex := Fin {seeds}", 1)])
        args.target.write_text(text, encoding="utf-8")
        if args.solid_model is not None:
            model = args.solid_model.read_text(encoding="utf-8")
            model = substitute(args.solid_model, model, [
                (r"(∀ t : Fin )\d+(, \((?:\w+\.)?seedVertex)",
                 lambda m: f"{m.group(1)}{seeds}{m.group(2)}", 1),
                (r"∀ i : Fin \(5 \* \d+\),", f"∀ i : Fin (5 * {seeds}),", 2)] + seed_count_rules(seeds))
            args.solid_model.write_text(model, encoding="utf-8")
            updated.append(args.solid_model)
    elif "def slotVertices : Fin" in text:
        text = substitute(args.target, text, [
            (r"def slotVertices : Fin \d+ →", f"def slotVertices : Fin {n} →", 1),
            (r"fun i : Fin \d+ => Array\.ofFn", f"fun i : Fin {n} => Array.ofFn", 1),
            (r"def slotVerticesImpl \(i : Fin \d+\)", f"def slotVerticesImpl (i : Fin {n})", 1),
            (r"def seedVertices : Fin \d+ →", f"def seedVertices : Fin {seeds} →", 1),
            (r"∀ t : Fin \d+, \(seedVertices", f"∀ t : Fin {seeds}, (seedVertices", 1),
            (r"∀ i : Fin \d+,\n", f"∀ i : Fin {n},\n", 2)] + seed_count_rules(seeds))
        text = replace_def(args.target, text, f"def slotVertices : Fin {n} → Fin 3 → ℚ := ![", rows)
        text = replace_def(args.target, text, f"def seedVertices : Fin {seeds} → Fin 3 → ℚ := ![", rows[:seeds])
        args.target.write_text(text, encoding="utf-8")
    else:
        raise SystemExit(f"{args.target}: neither a rationalVertices nor a slotVertices layout")
    print(f"updated {' and '.join(map(str, updated))} from {args.exported}")


if __name__ == "__main__":
    main()
