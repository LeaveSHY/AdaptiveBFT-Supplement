#!/usr/bin/env python3
"""Synchronize README/LaTeX n7/n7lite + transfer rows from latest snapshot artifacts."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Dict

ROOT = Path(__file__).resolve().parents[1]
README = ROOT / "README.md"
TEX = ROOT / "docs" / "verification_tables.tex"
N7_MD = ROOT / "docs" / "results" / "scale_n7_attack_latest.md"
N7LITE_MD = ROOT / "docs" / "results" / "scale_n7lite_suite_latest.md"
TRANSFER_MD = ROOT / "docs" / "results" / "transfer_snapshot_latest.md"
MV5_MD = ROOT / "docs" / "results" / "mv5_suite_latest.md"


def parse_int(text: str) -> int:
    return int(text.replace(",", "").strip())


def fmt_int(n: int) -> str:
    return f"{n:,}"


def parse_iso_date(md_path: Path) -> str:
    text = md_path.read_text(encoding="utf-8")
    m = re.search(r"^- date:\s*([0-9]{4}-[0-9]{2}-[0-9]{2})\b", text, re.MULTILINE)
    if not m:
        raise RuntimeError(f"missing ISO date line in {md_path}")
    return m.group(1)


def parse_stamp_date(md_path: Path) -> str:
    text = md_path.read_text(encoding="utf-8")
    m = re.search(r"^# .*?\(([0-9]{8})-[0-9]{6}\)\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError(f"missing stamped heading date in {md_path}")
    raw = m.group(1)
    return f"{raw[0:4]}-{raw[4:6]}-{raw[6:8]}"


def parse_n7_snapshot() -> Dict[str, str]:
    text = N7_MD.read_text(encoding="utf-8")

    def pick(pattern: str, name: str) -> str:
        m = re.search(pattern, text, re.MULTILINE)
        if not m:
            raise RuntimeError(f"missing {name} in {N7_MD}")
        return m.group(1).strip()

    return {
        "states": fmt_int(parse_int(pick(r"^- states generated:\s*([0-9,]+)\s*$", "states"))),
        "distinct": fmt_int(parse_int(pick(r"^- distinct states:\s*([0-9,]+)\s*$", "distinct"))),
        "diameter": pick(r"^- diameter:\s*([0-9]+)\s*$", "diameter"),
        "wall": pick(r"^- wall-clock:\s*(.+)\s*$", "wall-clock"),
    }


def parse_n7lite_snapshot() -> Dict[str, str]:
    text = N7LITE_MD.read_text(encoding="utf-8")
    row_re = re.compile(
        r"^\|\s*`MC_AdaptiveAttack`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|$",
        re.MULTILINE,
    )
    m = row_re.search(text)
    if not m:
        raise RuntimeError(f"missing MC_AdaptiveAttack row in {N7LITE_MD}")
    if m.group("result") != "PASS":
        raise RuntimeError(f"n7lite snapshot row is not PASS in {N7LITE_MD}")
    return {
        "states": fmt_int(parse_int(m.group("states"))),
        "distinct": fmt_int(parse_int(m.group("distinct"))),
        "diameter": m.group("diam").strip(),
        "wall": m.group("wall").strip(),
    }


def parse_transfer_snapshot() -> Dict[str, Dict[str, str]]:
    text = TRANSFER_MD.read_text(encoding="utf-8")
    row_re = re.compile(
        r"^\|\s*(?P<profile>baseline\s*\(`MaxView=2`\)|`MaxView=3`|`MaxView=4`)\s*\|\s*"
        r"(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>Pass|FAIL|Pass)\s*\|$",
        re.MULTILINE,
    )
    out: Dict[str, Dict[str, str]] = {}
    for m in row_re.finditer(text):
        raw_profile = m.group("profile").strip()
        if raw_profile.startswith("baseline"):
            profile = "baseline"
        elif raw_profile == "`MaxView=3`":
            profile = "mv3"
        else:
            profile = "mv4"
        out[profile] = {
            "states": fmt_int(parse_int(m.group("states"))),
            "distinct": fmt_int(parse_int(m.group("distinct"))),
            "diameter": m.group("diam").strip(),
            "wall": m.group("wall").strip(),
            "result": m.group("result").strip(),
        }

    required = {"baseline", "mv3", "mv4"}
    missing = required - set(out)
    if missing:
        raise RuntimeError(f"transfer snapshot missing rows: {sorted(missing)}")
    return out


def parse_mv5_snapshot() -> Dict[str, Dict[str, str]]:
    text = MV5_MD.read_text(encoding="utf-8")
    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|$",
        re.MULTILINE,
    )
    out: Dict[str, Dict[str, str]] = {}
    for m in row_re.finditer(text):
        model = m.group("model")
        out[model] = {
            "states": fmt_int(parse_int(m.group("states"))),
            "distinct": fmt_int(parse_int(m.group("distinct"))),
            "diameter": m.group("diam").strip(),
            "wall": m.group("wall").strip(),
            "result": m.group("result").strip(),
        }

    required = {"MC_AdaptiveAttack", "MC_LivenessAPS", "MC_LivenessAPSAttack", "MC_RefinementTransfer"}
    missing = required - set(out)
    if missing:
        raise RuntimeError(f"mv5 snapshot missing rows: {sorted(missing)}")
    for model in required:
        if out[model]["result"] != "PASS":
            raise RuntimeError(f"mv5 snapshot row is not PASS for {model}")
    return out


def replace_one(text: str, pattern: str, repl: str, desc: str) -> str:
    out, n = re.subn(pattern, lambda _m: repl, text, flags=re.MULTILINE)
    if n != 1:
        raise RuntimeError(f"expected exactly one match for {desc}, got {n}")
    return out


def sync_readme(
    n7: Dict[str, str],
    n7lite: Dict[str, str],
    tr: Dict[str, Dict[str, str]],
    mv5: Dict[str, Dict[str, str]],
) -> None:
    text = README.read_text(encoding="utf-8")

    n7_line = (
        "| `MC_AdaptiveAttack` (`n7`) | bounded scale sanity under adaptive corruption | "
        f"{n7['states']} | {n7['distinct']} | {n7['diameter']} | {n7['wall']} |"
    )
    text = replace_one(
        text,
        r"^\| `MC_AdaptiveAttack` \(`n7`\) \| bounded scale sanity under adaptive corruption \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
        n7_line,
        "README n7 row",
    )

    n7lite_line = (
        "| `MC_AdaptiveAttack` (`n7lite`) | quick bounded scale sanity under adaptive corruption | "
        f"{n7lite['states']} | {n7lite['distinct']} | {n7lite['diameter']} | {n7lite['wall']} |"
    )
    text = replace_one(
        text,
        r"^\| `MC_AdaptiveAttack` \(`n7lite`\) \| quick bounded scale sanity under adaptive corruption \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
        n7lite_line,
        "README n7lite row",
    )

    baseline_line = (
        "| `MC_RefinementTransfer` (baseline) | concrete `Next` projects to abstract `NextA` or stutter | "
        f"{tr['baseline']['states']} | {tr['baseline']['distinct']} | {tr['baseline']['diameter']} | {tr['baseline']['wall']} |"
    )
    mv3_line = (
        "| `MC_RefinementTransfer` (`MaxView=3`) | same transfer check, deeper bound | "
        f"{tr['mv3']['states']} | {tr['mv3']['distinct']} | {tr['mv3']['diameter']} | {tr['mv3']['wall']} |"
    )
    mv4_line = (
        "| `MC_RefinementTransfer` (`MaxView=4`) | same transfer check, strengthened bound | "
        f"{tr['mv4']['states']} | {tr['mv4']['distinct']} | {tr['mv4']['diameter']} | {tr['mv4']['wall']} |"
    )
    text = replace_one(
        text,
        r"^\| `MC_RefinementTransfer` \(baseline\) \| concrete `Next` projects to abstract `NextA` or stutter \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
        baseline_line,
        "README transfer baseline row",
    )
    text = replace_one(
        text,
        r"^\| `MC_RefinementTransfer` \(`MaxView=3`\) \| same transfer check, deeper bound \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
        mv3_line,
        "README transfer mv3 row",
    )
    text = replace_one(
        text,
        r"^\| `MC_RefinementTransfer` \(`MaxView=4`\) \| same transfer check, strengthened bound \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
        mv4_line,
        "README transfer mv4 row",
    )

    mv5_rows = {
        "MC_AdaptiveAttack": (
            "| `MC_AdaptiveAttack` (`MaxView=5`) | deeper bounded safety exploration | "
            f"{mv5['MC_AdaptiveAttack']['states']} | {mv5['MC_AdaptiveAttack']['distinct']} | {mv5['MC_AdaptiveAttack']['diameter']} | {mv5['MC_AdaptiveAttack']['wall']} |",
            r"^\| `MC_AdaptiveAttack` \(`MaxView=5`\) \| deeper bounded safety exploration \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
            "README mv5 attack row",
        ),
        "MC_LivenessAPS": (
            "| `MC_LivenessAPS` (`MaxView=5`) | deeper bounded APS liveness wrapper | "
            f"{mv5['MC_LivenessAPS']['states']} | {mv5['MC_LivenessAPS']['distinct']} | {mv5['MC_LivenessAPS']['diameter']} | {mv5['MC_LivenessAPS']['wall']} |",
            r"^\| `MC_LivenessAPS` \(`MaxView=5`\) \| deeper bounded APS liveness wrapper \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
            "README mv5 aps row",
        ),
        "MC_LivenessAPSAttack": (
            "| `MC_LivenessAPSAttack` (`MaxView=5`) | deeper bounded joint liveness wrapper | "
            f"{mv5['MC_LivenessAPSAttack']['states']} | {mv5['MC_LivenessAPSAttack']['distinct']} | {mv5['MC_LivenessAPSAttack']['diameter']} | {mv5['MC_LivenessAPSAttack']['wall']} |",
            r"^\| `MC_LivenessAPSAttack` \(`MaxView=5`\) \| deeper bounded joint liveness wrapper \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
            "README mv5 joint row",
        ),
        "MC_RefinementTransfer": (
            "| `MC_RefinementTransfer` (`MaxView=5`) | deeper bounded transfer diagnostics | "
            f"{mv5['MC_RefinementTransfer']['states']} | {mv5['MC_RefinementTransfer']['distinct']} | {mv5['MC_RefinementTransfer']['diameter']} | {mv5['MC_RefinementTransfer']['wall']} |",
            r"^\| `MC_RefinementTransfer` \(`MaxView=5`\) \| deeper bounded transfer diagnostics \| [0-9,]+ \| [0-9,]+ \| [0-9]+ \| [^|]+ \|$",
            "README mv5 transfer row",
        ),
    }
    for row, pattern, desc in mv5_rows.values():
        text = replace_one(text, pattern, row, desc)

    README.write_text(text, encoding="utf-8")


def sync_tex(
    n7: Dict[str, str],
    n7lite: Dict[str, str],
    tr: Dict[str, Dict[str, str]],
    mv5: Dict[str, Dict[str, str]],
) -> None:
    text = TEX.read_text(encoding="utf-8")

    n7_line = (
        r"MC\_AdaptiveAttack (\texttt{n7}) & "
        f"{n7['states']} & {n7['distinct']} & {n7['diameter']} & {n7['wall']} & Pass & "
        r"Safety + W-A0/W-A1/W-A2/W-A3/W-A4 \\"
    )
    text = replace_one(
        text,
        r"^MC\\_AdaptiveAttack\s+\(\\texttt\{n7\}\)\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*Safety \+ W-A0/W-A1/W-A2/W-A3/W-A4\s*\\\\$",
        n7_line,
        "LaTeX n7 row",
    )

    n7lite_line = (
        r"MC\_AdaptiveAttack (\texttt{n7lite}) & "
        f"{n7lite['states']} & {n7lite['distinct']} & {n7lite['diameter']} & {n7lite['wall']} & Pass & "
        r"Safety + W-A0/W-A1/W-A2/W-A3/W-A4 \\"
    )
    text = replace_one(
        text,
        r"^MC\\_AdaptiveAttack\s+\(\\texttt\{n7lite\}\)\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*Safety \+ W-A0/W-A1/W-A2/W-A3/W-A4\s*\\\\$",
        n7lite_line,
        "LaTeX n7lite row",
    )

    baseline_line = (
        r"baseline (\texttt{MaxView=2}) & "
        f"{tr['baseline']['states']} & {tr['baseline']['distinct']} & {tr['baseline']['diameter']} & {tr['baseline']['wall']} & Pass & T0 + T1 + T2 + T3 + T4 \\\\"
    )
    mv3_line = (
        r"\texttt{MaxView=3} & "
        f"{tr['mv3']['states']} & {tr['mv3']['distinct']} & {tr['mv3']['diameter']} & {tr['mv3']['wall']} & Pass & T0 + T1 + T2 + T3 + T4 \\\\"
    )
    mv4_line = (
        r"\texttt{MaxView=4} & "
        f"{tr['mv4']['states']} & {tr['mv4']['distinct']} & {tr['mv4']['diameter']} & {tr['mv4']['wall']} & Pass & T0 + T1 + T2 + T3 + T4 \\\\"
    )
    text = replace_one(
        text,
        r"^baseline\s+\(\\texttt\{MaxView=2\}\)\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*T0 \+ T1 \+ T2 \+ T3 \+ T4\s*\\\\$",
        baseline_line,
        "LaTeX transfer baseline row",
    )
    text = replace_one(
        text,
        r"^\\texttt\{MaxView=3\}\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*T0 \+ T1 \+ T2 \+ T3 \+ T4\s*\\\\$",
        mv3_line,
        "LaTeX transfer mv3 row",
    )
    text = replace_one(
        text,
        r"^\\texttt\{MaxView=4\}\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*T0 \+ T1 \+ T2 \+ T3 \+ T4\s*\\\\$",
        mv4_line,
        "LaTeX transfer mv4 row",
    )

    mv5_attack = (
        r"MC\_AdaptiveAttack & "
        f"{mv5['MC_AdaptiveAttack']['states']} & {mv5['MC_AdaptiveAttack']['distinct']} & {mv5['MC_AdaptiveAttack']['diameter']} & {mv5['MC_AdaptiveAttack']['wall']} & Pass & "
        r"Safety + W-A0/W-A1/W-A2/W-A3/W-A4 \\"
    )
    mv5_aps = (
        r"MC\_LivenessAPS & "
        f"{mv5['MC_LivenessAPS']['states']} & {mv5['MC_LivenessAPS']['distinct']} & {mv5['MC_LivenessAPS']['diameter']} & {mv5['MC_LivenessAPS']['wall']} & Pass & "
        r"Safety + L1 + W-P0/W-P1/W-P2/W-P3/W-P4 \\"
    )
    mv5_joint = (
        r"MC\_LivenessAPSAttack & "
        f"{mv5['MC_LivenessAPSAttack']['states']} & {mv5['MC_LivenessAPSAttack']['distinct']} & {mv5['MC_LivenessAPSAttack']['diameter']} & {mv5['MC_LivenessAPSAttack']['wall']} & Pass & "
        r"Safety + L2 + W-J0/W-J1/W-J2/W-J3/W-J4 \\"
    )
    mv5_transfer = (
        r"MC\_RefinementTransfer & "
        f"{mv5['MC_RefinementTransfer']['states']} & {mv5['MC_RefinementTransfer']['distinct']} & {mv5['MC_RefinementTransfer']['diameter']} & {mv5['MC_RefinementTransfer']['wall']} & Pass & "
        r"T0 + T1 + T2 + T3 + T4 \\"
    )
    text = replace_one(
        text,
        r"^MC\\_AdaptiveAttack\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*Safety \+ W-A0/W-A1/W-A2/W-A3/W-A4\s*\\\\$",
        mv5_attack,
        "LaTeX mv5 attack row",
    )
    text = replace_one(
        text,
        r"^MC\\_LivenessAPS\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*Safety \+ L1 \+ W-P0/W-P1/W-P2/W-P3/W-P4\s*\\\\$",
        mv5_aps,
        "LaTeX mv5 aps row",
    )
    text = replace_one(
        text,
        r"^MC\\_LivenessAPSAttack\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*Safety \+ L2 \+ W-J0/W-J1/W-J2/W-J3/W-J4\s*\\\\$",
        mv5_joint,
        "LaTeX mv5 joint row",
    )
    text = replace_one(
        text,
        r"^MC\\_RefinementTransfer\s*&\s*[0-9,]+\s*&\s*[0-9,]+\s*&\s*[0-9]+\s*&\s*[^&]+\s*&\s*Pass\s*&\s*T0 \+ T1 \+ T2 \+ T3 \+ T4\s*\\\\$",
        mv5_transfer,
        "LaTeX mv5 transfer row",
    )

    mv5_date = parse_iso_date(MV5_MD)
    n7_date = parse_iso_date(N7_MD)
    n7lite_date = parse_iso_date(N7LITE_MD)
    transfer_date = parse_stamp_date(TRANSFER_MD)

    text = replace_one(
        text,
        r"\\+item Snapshot source: \\+texttt\{make suite-mv5\} \(artifact: \\+texttt\{docs/results/mv5\\_suite\\_latest\.md\}, executed on [0-9]{4}-[0-9]{2}-[0-9]{2}\)\.",
        rf"\item Snapshot source: \texttt{{make suite-mv5}} (artifact: \texttt{{docs/results/mv5\_suite\_latest.md}}, executed on {mv5_date}).",
        "LaTeX mv5 snapshot date note",
    )
    text = replace_one(
        text,
        r"\\+item Snapshot source: \\+texttt\{make scale-n7lite\} \(artifact: \\+texttt\{docs/results/scale\\_n7lite\\_suite\\_latest\.md\}, executed on [0-9]{4}-[0-9]{2}-[0-9]{2}\)\.",
        rf"\item Snapshot source: \texttt{{make scale-n7lite}} (artifact: \texttt{{docs/results/scale\_n7lite\_suite\_latest.md}}, executed on {n7lite_date}).",
        "LaTeX n7lite snapshot date note",
    )
    text = replace_one(
        text,
        r"\\+item Snapshot source: \\+texttt\{make scale-n7\} \(artifact: \\+texttt\{docs/results/scale\\_n7\\_attack\\_latest\.md\}, executed on [0-9]{4}-[0-9]{2}-[0-9]{2}\)\.",
        rf"\item Snapshot source: \texttt{{make scale-n7}} (artifact: \texttt{{docs/results/scale\_n7\_attack\_latest.md}}, executed on {n7_date}).",
        "LaTeX n7 snapshot date note",
    )
    text = replace_one(
        text,
        r"\\+item Commands: \\+texttt\{make test-transfer\}, \\+texttt\{make test-transfer-mv3\}, \\+texttt\{make test-transfer-mv4\} \(executed on [0-9]{4}-[0-9]{2}-[0-9]{2}\)\.",
        rf"\item Commands: \texttt{{make test-transfer}}, \texttt{{make test-transfer-mv3}}, \texttt{{make test-transfer-mv4}} (executed on {transfer_date}).",
        "LaTeX transfer snapshot date note",
    )

    TEX.write_text(text, encoding="utf-8")


def main() -> int:
    try:
        n7 = parse_n7_snapshot()
        n7lite = parse_n7lite_snapshot()
        tr = parse_transfer_snapshot()
        mv5 = parse_mv5_snapshot()
        sync_readme(n7, n7lite, tr, mv5)
        sync_tex(n7, n7lite, tr, mv5)
    except Exception as exc:  # pylint: disable=broad-except
        print(f"[ERROR] {exc}")
        return 1

    print("OK: synchronized README and verification_tables rows from latest n7/n7lite/transfer snapshots.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
