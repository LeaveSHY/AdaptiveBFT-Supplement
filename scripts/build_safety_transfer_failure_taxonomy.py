#!/usr/bin/env python3
"""Build a compact taxonomy of safety-transfer closure failures.

Input:
- docs/results/safety_transfer_closure_attempt_latest.md
- per-strategy logs referenced in that report

Output:
- docs/results/safety_transfer_failure_taxonomy_<stamp>.md
- docs/results/safety_transfer_failure_taxonomy_latest.md
"""

from __future__ import annotations

import argparse
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


@dataclass(frozen=True)
class ObligationFailure:
    file: str
    line: int
    goal: str


@dataclass(frozen=True)
class StrategySummary:
    strategy: str
    status: str
    log_rel: str
    failures: tuple[ObligationFailure, ...]


ROW_RE = re.compile(
    r"^\|\s*`(?P<strategy>[^`]+)`\s*\|\s*(?P<status>PASS|FAIL)\s*\|[^|]*\|[^|]*\|[^|]*\|\s*`(?P<log>[^`]+)`\s*\|$",
    re.MULTILINE,
)

FILE_LINE_RE = re.compile(r'^File\s+"(?P<file>[^"]+)",\s+line\s+(?P<line>\d+),')
ERROR_START_RE = re.compile(r"^\[ERROR\]: Could not prove or check:")
PROVE_RE = re.compile(r"^\s*PROVE\s+(?P<goal>.+)$")


def parse_closure_rows(text: str) -> list[tuple[str, str, str]]:
    rows: list[tuple[str, str, str]] = []
    for m in ROW_RE.finditer(text):
        rows.append((m.group("strategy"), m.group("status"), m.group("log")))
    return rows


def normalize_goal(goal: str) -> str:
    goal = " ".join(goal.split())
    goal = goal.replace("  ", " ")
    return goal.strip()


def parse_obligation_failures(log_text: str) -> list[ObligationFailure]:
    lines = log_text.splitlines()
    out: list[ObligationFailure] = []
    i = 0
    while i < len(lines):
        fm = FILE_LINE_RE.match(lines[i])
        if not fm:
            i += 1
            continue
        file_name = fm.group("file")
        line_no = int(fm.group("line"))

        j = i + 1
        if j >= len(lines) or not ERROR_START_RE.match(lines[j]):
            i += 1
            continue

        j += 1
        body: list[str] = []
        while j < len(lines):
            if FILE_LINE_RE.match(lines[j]) or ERROR_START_RE.match(lines[j]):
                break
            body.append(lines[j])
            j += 1

        goal = ""
        for raw in body:
            pm = PROVE_RE.match(raw)
            if pm:
                goal = normalize_goal(pm.group("goal"))
                break
        if goal:
            out.append(ObligationFailure(file=file_name, line=line_no, goal=goal))
        i = j
    return out


def write_report(out_path: Path, strategies: list[StrategySummary]) -> None:
    now = datetime.now(timezone.utc).astimezone()
    lines: list[str] = []
    lines.append("# Safety Transfer Failure Taxonomy")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append("")

    lines.append("## Per-Strategy Summary")
    lines.append("")
    lines.append("| Strategy | Status | Failed Obligations | Primary Location | Primary Goal |")
    lines.append("|---|---|---:|---|---|")
    for row in strategies:
        if row.failures:
            primary = row.failures[0]
            loc = f"`{primary.file}:{primary.line}`"
            goal = primary.goal.replace("|", "\\|")
        else:
            loc = "-"
            goal = "-"
        lines.append(
            f"| `{row.strategy}` | {row.status} | {len(row.failures)} | {loc} | {goal} |"
        )
    lines.append("")

    goal_counter: Counter[str] = Counter()
    goal_to_strategies: dict[str, set[str]] = defaultdict(set)
    for row in strategies:
        seen: set[str] = set()
        for failure in row.failures:
            sig = f"{failure.file}:{failure.line}: {failure.goal}"
            if sig not in seen:
                goal_counter[sig] += 1
                goal_to_strategies[sig].add(row.strategy)
                seen.add(sig)

    lines.append("## Grouped Goal Signatures")
    lines.append("")
    lines.append("| Goal Signature | Strategies | Hits |")
    lines.append("|---|---|---:|")
    if not goal_counter:
        lines.append("| (none) | - | 0 |")
    else:
        for sig, hits in goal_counter.most_common():
            strat = ", ".join(f"`{s}`" for s in sorted(goal_to_strategies[sig]))
            escaped_sig = sig.replace("|", "\\|")
            lines.append(f"| {escaped_sig} | {strat} | {hits} |")
    lines.append("")
    lines.append("## Notes")
    lines.append("")
    lines.append("- This artifact is diagnostic only; it does not change theorem status.")
    lines.append("- Use together with `docs/results/safety_transfer_closure_attempt_latest.md`.")
    lines.append("")

    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--closure", type=Path, default=Path("docs/results/safety_transfer_closure_attempt_latest.md"))
    parser.add_argument("--out", type=Path, default=Path("docs/results/safety_transfer_failure_taxonomy_latest.md"))
    args = parser.parse_args()

    root = args.root.resolve()
    closure_path = (root / args.closure).resolve() if not args.closure.is_absolute() else args.closure.resolve()
    out_path = (root / args.out).resolve() if not args.out.is_absolute() else args.out.resolve()

    if not closure_path.exists():
        raise SystemExit(f"missing closure report: {closure_path}")

    text = closure_path.read_text(encoding="utf-8", errors="replace")
    rows = parse_closure_rows(text)
    if not rows:
        summaries: list[StrategySummary] = []
        write_report(out_path, summaries)
        print(f"Safety-transfer failure taxonomy written to: {out_path.relative_to(root)}")
        return 0

    summaries: list[StrategySummary] = []
    for strategy, status, log_rel in rows:
        log_path = (root / log_rel).resolve()
        failures: list[ObligationFailure] = []
        if status == "FAIL" and log_path.exists():
            failures = parse_obligation_failures(log_path.read_text(encoding="utf-8", errors="replace"))
        summaries.append(
            StrategySummary(
                strategy=strategy,
                status=status,
                log_rel=log_rel,
                failures=tuple(failures),
            )
        )

    write_report(out_path, summaries)
    print(f"Safety-transfer failure taxonomy written to: {out_path.relative_to(root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
