#!/usr/bin/env python3
"""Build a historical trend report for safety-transfer closure attempts."""

from __future__ import annotations

import argparse
import re
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


CAMPAIGN_RE = re.compile(r"- campaign_id:\s*`([^`]+)`")
ROW_RE = re.compile(
    r"^\|\s*`(?P<strategy>[^`]+)`\s*\|\s*(?P<status>PASS|FAIL)\s*\|\s*(?P<exit>\d+)\s*\|\s*(?P<dur>[^|]+)\|\s*(?P<sig>[^|]+)\|",
    re.MULTILINE,
)


@dataclass(frozen=True)
class Row:
    campaign_id: str
    strategy: str
    status: str
    exit_code: int
    duration: str
    signature: str


def parse_attempt_report(path: Path) -> tuple[str, list[Row]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    m = CAMPAIGN_RE.search(text)
    campaign_id = m.group(1) if m else path.stem
    rows: list[Row] = []
    for rm in ROW_RE.finditer(text):
        rows.append(
            Row(
                campaign_id=campaign_id,
                strategy=rm.group("strategy"),
                status=rm.group("status"),
                exit_code=int(rm.group("exit")),
                duration=rm.group("dur").strip(),
                signature=rm.group("sig").strip(),
            )
        )
    return campaign_id, rows


def render(out: Path, all_rows: list[Row], campaigns: list[str], window: int) -> None:
    by_strategy: dict[str, list[Row]] = defaultdict(list)
    for row in all_rows:
        by_strategy[row.strategy].append(row)

    lines: list[str] = []
    lines.append("# Safety-Transfer Closure Trend")
    lines.append("")
    lines.append(f"- campaigns_seen: `{len(campaigns)}`")
    lines.append(f"- attempts_window: `{window}`")
    lines.append("")

    lines.append("## Strategy Aggregates")
    lines.append("")
    lines.append("| Strategy | Runs | Pass | Fail | Last Status | Last Signature |")
    lines.append("|---|---:|---:|---:|---|---|")
    for strategy in sorted(by_strategy):
        runs = by_strategy[strategy]
        pass_cnt = sum(1 for r in runs if r.status == "PASS")
        fail_cnt = sum(1 for r in runs if r.status != "PASS")
        last = runs[-1]
        sig = last.signature.replace("|", "\\|")
        lines.append(
            f"| `{strategy}` | {len(runs)} | {pass_cnt} | {fail_cnt} | {last.status} | {sig} |"
        )
    if not by_strategy:
        lines.append("| (none) | 0 | 0 | 0 | - | - |")
    lines.append("")

    lines.append("## Recent Campaigns")
    lines.append("")
    lines.append("| Campaign | Strategies | Pass | Fail |")
    lines.append("|---|---:|---:|---:|")
    grouped: dict[str, list[Row]] = defaultdict(list)
    for row in all_rows:
        grouped[row.campaign_id].append(row)
    for cid in campaigns:
        rows = grouped.get(cid, [])
        pass_cnt = sum(1 for r in rows if r.status == "PASS")
        fail_cnt = sum(1 for r in rows if r.status != "PASS")
        lines.append(f"| `{cid}` | {len(rows)} | {pass_cnt} | {fail_cnt} |")
    if not campaigns:
        lines.append("| (none) | 0 | 0 | 0 |")
    lines.append("")

    out.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--window", type=int, default=20)
    args = parser.parse_args()

    root = args.root.resolve()
    results = root / "docs" / "results"
    files = sorted(
        p
        for p in results.glob("safety_transfer_closure_attempt_*.md")
        if p.name not in {"safety_transfer_closure_attempt_latest.md"}
    )
    files = files[-args.window :] if args.window > 0 else files

    campaigns: list[str] = []
    rows: list[Row] = []
    for f in files:
        cid, parsed = parse_attempt_report(f)
        campaigns.append(cid)
        rows.extend(parsed)

    out = results / "safety_transfer_closure_trend_latest.md"
    render(out, rows, campaigns, args.window)
    print(f"Safety-transfer closure trend written to: {out.relative_to(root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

