#!/usr/bin/env python3
"""Build a snapshot of explicitly allowlisted theorem blockers."""

from __future__ import annotations

import argparse
import importlib.util
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Blocker:
    key: str
    module: str
    theorem: str
    line: int
    present: bool
    proved: bool


def _load_coverage_module(root: Path):
    path = root / "scripts" / "check_theorem_coverage.py"
    spec = importlib.util.spec_from_file_location("check_theorem_coverage", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load coverage module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _find_theorem_line(module_path: Path, theorem_name: str) -> int:
    if not module_path.exists():
        return 0
    needle = f"THEOREM {theorem_name}"
    for i, line in enumerate(module_path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
        if needle in line:
            return i
    return 0


def collect_blockers(root: Path) -> list[Blocker]:
    coverage = _load_coverage_module(root)
    spec_dir = root / "specifications"

    proved_all: set[str] = set()
    unproved_all: set[str] = set()
    for module_path in coverage.iter_toplevel_modules(spec_dir):
        proved, unproved = coverage.theorem_coverage(module_path)
        proved_all |= proved
        unproved_all |= unproved

    blockers: list[Blocker] = []
    for key in sorted(coverage.ALLOWED_UNPROVED):
        module_name, theorem_name = key.split(":", 1)
        path = spec_dir / module_name
        line = _find_theorem_line(path, theorem_name)
        blockers.append(
            Blocker(
                key=key,
                module=module_name,
                theorem=theorem_name,
                line=line,
                present=(key in unproved_all) or (key in proved_all),
                proved=(key in proved_all),
            )
        )
    return blockers


def write_markdown(out_path: Path, blockers: Iterable[Blocker]) -> None:
    rows = list(blockers)
    now = datetime.now(timezone.utc).astimezone()
    lines: list[str] = []
    lines.append("# Proof Blocker Snapshot")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append(f"- allowlisted_unproved_targets: {len(rows)}")
    lines.append("")
    lines.append("| Theorem | Location | Status |")
    lines.append("|---|---|---|")
    if not rows:
        lines.append("| (none) | - | fully-closed |")
    else:
        for b in rows:
            loc = f"`{b.module}:{b.line}`" if b.line > 0 else f"`{b.module}`"
            if not b.present:
                status = "missing (allowlist stale)"
            elif b.proved:
                status = "proved (allowlist stale)"
            else:
                status = "open (allowlisted)"
            lines.append(f"| `{b.theorem}` | {loc} | {status} |")
    lines.append("")
    lines.append("Notes:")
    lines.append("")
    lines.append("- `open (allowlisted)` entries are the current blockers for theorem-coverage closure.")
    lines.append("- `missing/proved` entries indicate allowlist drift and should fail `make check-theorem-coverage`.")
    lines.append("")
    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    blockers = collect_blockers(root)
    write_markdown(args.out.resolve(), blockers)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
