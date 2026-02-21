#!/usr/bin/env python3
"""Check wrapper/scale (n7+n7lite) artifacts against paper-facing docs."""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Tuple

ROOT = Path(__file__).resolve().parents[1]
WRAPPER_MD = ROOT / "docs" / "results" / "wrapper_projection_latest.md"
SCALE_MD = ROOT / "docs" / "results" / "scale_n7_attack_latest.md"
SCALE_N7LITE_MD = ROOT / "docs" / "results" / "scale_n7lite_suite_latest.md"
TRANSFER_MD = ROOT / "docs" / "results" / "transfer_snapshot_latest.md"
MV5_MD = ROOT / "docs" / "results" / "mv5_suite_latest.md"
README = ROOT / "README.md"
TEX = ROOT / "docs" / "verification_tables.tex"


@dataclass(frozen=True)
class Metrics:
    states: int
    distinct: int
    diameter: int
    wall_seconds: int


def parse_int(text: str) -> int:
    return int(text.replace(",", "").strip())


def parse_duration_seconds(text: str) -> int:
    s = text.strip().lower()
    s = s.replace("\\", "")
    s = s.replace("$", "")
    s = s.replace(" ", "")
    s = s.replace("<1s", "0s")

    patterns = [
        (r"^(\d+)h(\d+)min$", lambda m: int(m.group(1)) * 3600 + int(m.group(2)) * 60),
        (r"^(\d+)h(\d+)m$", lambda m: int(m.group(1)) * 3600 + int(m.group(2)) * 60),
        (r"^(\d+)min(\d+)s$", lambda m: int(m.group(1)) * 60 + int(m.group(2))),
        (r"^(\d+)m(\d+)s$", lambda m: int(m.group(1)) * 60 + int(m.group(2))),
        (r"^(\d+)s$", lambda m: int(m.group(1))),
    ]
    for pat, fn in patterns:
        m = re.match(pat, s)
        if m:
            return fn(m)
    raise RuntimeError(f"unrecognized duration format: {text!r}")


def parse_wrapper_snapshot() -> Dict[Tuple[str, str], Metrics]:
    if not WRAPPER_MD.exists():
        raise FileNotFoundError(f"missing wrapper snapshot: {WRAPPER_MD}")

    section = ""
    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|"
    )
    out: Dict[Tuple[str, str], Metrics] = {}

    for raw in WRAPPER_MD.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("## baseline"):
            section = "baseline"
            continue
        if line.startswith("## mv4"):
            section = "mv4"
            continue

        m = row_re.match(line)
        if not m or not section:
            continue
        if m.group("result") != "PASS":
            raise RuntimeError(f"wrapper snapshot has non-PASS row: {line}")

        key = (section, m.group("model"))
        out[key] = Metrics(
            states=parse_int(m.group("states")),
            distinct=parse_int(m.group("distinct")),
            diameter=parse_int(m.group("diam")),
            wall_seconds=parse_duration_seconds(m.group("wall")),
        )

    required = {
        ("baseline", "MC_AdaptiveAttack"),
        ("baseline", "MC_LivenessAPS"),
        ("baseline", "MC_LivenessAPSAttack"),
        ("mv4", "MC_AdaptiveAttack"),
        ("mv4", "MC_LivenessAPS"),
        ("mv4", "MC_LivenessAPSAttack"),
    }
    missing = sorted(required - set(out))
    if missing:
        raise RuntimeError(f"wrapper snapshot is missing rows: {missing}")
    return out


def parse_tex_wrapper_table() -> Dict[Tuple[str, str], Metrics]:
    text = TEX.read_text(encoding="utf-8")
    anchor = r"\label{tab:adaptivebft-wrapper-projection}"
    start = text.find(anchor)
    if start < 0:
        raise RuntimeError("wrapper table label not found in verification_tables.tex")
    end = text.find(r"\end{table*}", start)
    if end < 0:
        raise RuntimeError("wrapper table end not found in verification_tables.tex")
    block = text[start:end]

    row_re = re.compile(
        r"^(?P<profile>baseline|\\texttt\{MaxView=4\})\s*&\s*"
        r"(?P<model>MC\\_[A-Za-z0-9]+)\s*&\s*"
        r"(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*(?P<diam>[0-9]+)\s*&\s*"
        r"(?P<wall>[^&]+?)\s*&\s*Pass\s*&\s*(?P<props>[^\\]+)\\\\\s*$",
        re.MULTILINE,
    )

    out: Dict[Tuple[str, str], Metrics] = {}
    for m in row_re.finditer(block):
        profile = "baseline" if m.group("profile") == "baseline" else "mv4"
        model = m.group("model").replace("\\_", "_")
        key = (profile, model)
        out[key] = Metrics(
            states=parse_int(m.group("states")),
            distinct=parse_int(m.group("distinct")),
            diameter=parse_int(m.group("diam")),
            wall_seconds=parse_duration_seconds(m.group("wall")),
        )
    return out


def parse_tex_n7_table_row() -> Metrics:
    text = TEX.read_text(encoding="utf-8")
    anchor = r"\label{tab:adaptivebft-verif-results-n7}"
    start = text.find(anchor)
    if start < 0:
        raise RuntimeError("n7 table label not found in verification_tables.tex")
    end = text.find(r"\end{table*}", start)
    if end < 0:
        raise RuntimeError("n7 table end not found in verification_tables.tex")
    block = text[start:end]

    row_re = re.compile(
        r"^MC\\_AdaptiveAttack\s*\(\\texttt\{n7\}\)\s*&\s*"
        r"(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*"
        r"(?P<diam>[0-9]+)\s*&\s*(?P<wall>[^&]+)&\s*Pass\s*&",
        re.MULTILINE,
    )
    m = row_re.search(block)
    if not m:
        raise RuntimeError("n7 row (MC_AdaptiveAttack n7) not found in n7 table")

    return Metrics(
        states=parse_int(m.group("states")),
        distinct=parse_int(m.group("distinct")),
        diameter=parse_int(m.group("diam")),
        wall_seconds=parse_duration_seconds(m.group("wall")),
    )


def parse_tex_n7lite_table_row() -> Metrics:
    text = TEX.read_text(encoding="utf-8")
    anchor = r"\label{tab:adaptivebft-verif-results-n7lite}"
    start = text.find(anchor)
    if start < 0:
        raise RuntimeError("n7lite table label not found in verification_tables.tex")
    end = text.find(r"\end{table*}", start)
    if end < 0:
        raise RuntimeError("n7lite table end not found in verification_tables.tex")
    block = text[start:end]

    row_re = re.compile(
        r"^MC\\_AdaptiveAttack\s*\(\\texttt\{n7lite\}\)\s*&\s*"
        r"(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*"
        r"(?P<diam>[0-9]+)\s*&\s*(?P<wall>[^&]+)&\s*Pass\s*&",
        re.MULTILINE,
    )
    m = row_re.search(block)
    if not m:
        raise RuntimeError("n7lite row (MC_AdaptiveAttack n7lite) not found in n7lite table")

    return Metrics(
        states=parse_int(m.group("states")),
        distinct=parse_int(m.group("distinct")),
        diameter=parse_int(m.group("diam")),
        wall_seconds=parse_duration_seconds(m.group("wall")),
    )


def parse_transfer_snapshot() -> Dict[str, Metrics]:
    if not TRANSFER_MD.exists():
        raise FileNotFoundError(f"missing transfer snapshot: {TRANSFER_MD}")

    row_re = re.compile(
        r"^\|\s*(?P<profile>baseline\s*\(`MaxView=2`\)|`MaxView=3`|`MaxView=4`)\s*\|\s*"
        r"(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>Pass|FAIL)\s*\|$"
    )

    out: Dict[str, Metrics] = {}
    for raw in TRANSFER_MD.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if not m:
            continue
        if m.group("result").lower() != "pass":
            raise RuntimeError(f"transfer snapshot has non-PASS row: {line}")
        raw_profile = m.group("profile")
        profile = "baseline" if raw_profile.startswith("baseline") else ("mv3" if "3" in raw_profile else "mv4")
        out[profile] = Metrics(
            states=parse_int(m.group("states")),
            distinct=parse_int(m.group("distinct")),
            diameter=parse_int(m.group("diam")),
            wall_seconds=parse_duration_seconds(m.group("wall")),
        )

    required = {"baseline", "mv3", "mv4"}
    missing = sorted(required - set(out))
    if missing:
        raise RuntimeError(f"transfer snapshot is missing rows: {missing}")
    return out


def parse_mv5_snapshot() -> Dict[str, Metrics]:
    if not MV5_MD.exists():
        raise FileNotFoundError(f"missing mv5 snapshot: {MV5_MD}")

    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|$"
    )
    out: Dict[str, Metrics] = {}
    for raw in MV5_MD.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if not m:
            continue
        if m.group("result") != "PASS":
            raise RuntimeError(f"mv5 snapshot has non-PASS row: {line}")
        model = m.group("model")
        out[model] = Metrics(
            states=parse_int(m.group("states")),
            distinct=parse_int(m.group("distinct")),
            diameter=parse_int(m.group("diam")),
            wall_seconds=parse_duration_seconds(m.group("wall")),
        )

    required = {"MC_AdaptiveAttack", "MC_LivenessAPS", "MC_LivenessAPSAttack", "MC_RefinementTransfer"}
    missing = sorted(required - set(out))
    if missing:
        raise RuntimeError(f"mv5 snapshot is missing rows: {missing}")
    return out


def parse_readme_transfer_rows() -> Dict[str, Metrics]:
    rows = {
        "baseline": re.compile(
            r"^\| `MC_RefinementTransfer` \(baseline\) \| .* \| (?P<states>[0-9,]+) \| (?P<distinct>[0-9,]+) \| (?P<diam>[0-9]+) \| (?P<wall>[^|]+) \|$"
        ),
        "mv3": re.compile(
            r"^\| `MC_RefinementTransfer` \(`MaxView=3`\) \| .* \| (?P<states>[0-9,]+) \| (?P<distinct>[0-9,]+) \| (?P<diam>[0-9]+) \| (?P<wall>[^|]+) \|$"
        ),
        "mv4": re.compile(
            r"^\| `MC_RefinementTransfer` \(`MaxView=4`\) \| .* \| (?P<states>[0-9,]+) \| (?P<distinct>[0-9,]+) \| (?P<diam>[0-9]+) \| (?P<wall>[^|]+) \|$"
        ),
    }
    out: Dict[str, Metrics] = {}
    lines = [l.strip() for l in README.read_text(encoding="utf-8").splitlines()]
    for profile, pat in rows.items():
        for line in lines:
            m = pat.match(line)
            if m:
                out[profile] = Metrics(
                    states=parse_int(m.group("states")),
                    distinct=parse_int(m.group("distinct")),
                    diameter=parse_int(m.group("diam")),
                    wall_seconds=parse_duration_seconds(m.group("wall")),
                )
                break
        if profile not in out:
            raise RuntimeError(f"README transfer row not found for {profile}")
    return out


def parse_tex_transfer_rows() -> Dict[str, Metrics]:
    text = TEX.read_text(encoding="utf-8")
    anchor = r"\label{tab:adaptivebft-transfer-results}"
    start = text.find(anchor)
    if start < 0:
        raise RuntimeError("transfer table label not found in verification_tables.tex")
    end = text.find(r"\end{table*}", start)
    if end < 0:
        raise RuntimeError("transfer table end not found in verification_tables.tex")
    block = text[start:end]

    patterns = {
        "baseline": re.compile(
            r"^baseline\s+\(\\texttt\{MaxView=2\}\)\s*&\s*(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*(?P<diam>[0-9]+)\s*&\s*(?P<wall>[^&]+)&\s*Pass\s*&",
            re.MULTILINE,
        ),
        "mv3": re.compile(
            r"^\\texttt\{MaxView=3\}\s*&\s*(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*(?P<diam>[0-9]+)\s*&\s*(?P<wall>[^&]+)&\s*Pass\s*&",
            re.MULTILINE,
        ),
        "mv4": re.compile(
            r"^\\texttt\{MaxView=4\}\s*&\s*(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*(?P<diam>[0-9]+)\s*&\s*(?P<wall>[^&]+)&\s*Pass\s*&",
            re.MULTILINE,
        ),
    }
    out: Dict[str, Metrics] = {}
    for profile, pat in patterns.items():
        m = pat.search(block)
        if not m:
            raise RuntimeError(f"transfer table row not found for {profile}")
        out[profile] = Metrics(
            states=parse_int(m.group("states")),
            distinct=parse_int(m.group("distinct")),
            diameter=parse_int(m.group("diam")),
            wall_seconds=parse_duration_seconds(m.group("wall")),
        )
    return out


def parse_scale_snapshot() -> Metrics:
    if not SCALE_MD.exists():
        raise FileNotFoundError(f"missing n7 scale snapshot: {SCALE_MD}")
    text = SCALE_MD.read_text(encoding="utf-8")

    def pick(pattern: str, name: str) -> str:
        m = re.search(pattern, text, re.MULTILINE)
        if not m:
            raise RuntimeError(f"missing {name} in {SCALE_MD}")
        return m.group(1).strip()

    states = parse_int(pick(r"^- states generated:\s*([0-9,]+)\s*$", "states"))
    distinct = parse_int(pick(r"^- distinct states:\s*([0-9,]+)\s*$", "distinct"))
    diameter = int(pick(r"^- diameter:\s*([0-9]+)\s*$", "diameter"))
    wall_seconds = parse_duration_seconds(
        pick(r"^- wall-clock:\s*(.+)\s*$", "wall-clock")
    )
    return Metrics(
        states=states, distinct=distinct, diameter=diameter, wall_seconds=wall_seconds
    )


def parse_scale_n7lite_snapshot() -> Metrics:
    if not SCALE_N7LITE_MD.exists():
        raise FileNotFoundError(f"missing n7lite scale snapshot: {SCALE_N7LITE_MD}")
    text = SCALE_N7LITE_MD.read_text(encoding="utf-8")
    row_re = re.compile(
        r"^\|\s*`MC_AdaptiveAttack`\s*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|\s*(?P<result>PASS|FAIL)\s*\|$",
        re.MULTILINE,
    )
    m = row_re.search(text)
    if not m:
        raise RuntimeError(f"MC_AdaptiveAttack row not found in {SCALE_N7LITE_MD}")
    if m.group("result") != "PASS":
        raise RuntimeError(f"n7lite snapshot has non-PASS result in {SCALE_N7LITE_MD}")
    return Metrics(
        states=parse_int(m.group("states")),
        distinct=parse_int(m.group("distinct")),
        diameter=int(m.group("diam")),
        wall_seconds=parse_duration_seconds(m.group("wall")),
    )


def parse_readme_n7_row() -> Metrics:
    row_re = re.compile(
        r"^\|\s*`MC_AdaptiveAttack`\s*\(`n7`\)\s*\|[^|]*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|$"
    )
    for raw in README.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if m:
            return Metrics(
                states=parse_int(m.group("states")),
                distinct=parse_int(m.group("distinct")),
                diameter=parse_int(m.group("diam")),
                wall_seconds=parse_duration_seconds(m.group("wall")),
            )
    raise RuntimeError("README n7 row not found")


def parse_readme_n7lite_row() -> Metrics:
    row_re = re.compile(
        r"^\|\s*`MC_AdaptiveAttack`\s*\(`n7lite`\)\s*\|[^|]*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|$"
    )
    for raw in README.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if m:
            return Metrics(
                states=parse_int(m.group("states")),
                distinct=parse_int(m.group("distinct")),
                diameter=parse_int(m.group("diam")),
                wall_seconds=parse_duration_seconds(m.group("wall")),
            )
    raise RuntimeError("README n7lite row not found")


def parse_readme_mv5_rows() -> Dict[str, Metrics]:
    row_re = re.compile(
        r"^\|\s*`(?P<model>MC_[^`]+)`\s*\(`MaxView=5`\)\s*\|[^|]*\|\s*(?P<states>[0-9,]+)\s*\|\s*(?P<distinct>[0-9,]+)\s*\|\s*(?P<diam>[0-9]+)\s*\|\s*(?P<wall>[^|]+)\|$"
    )
    out: Dict[str, Metrics] = {}
    for raw in README.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        m = row_re.match(line)
        if not m:
            continue
        model = m.group("model")
        out[model] = Metrics(
            states=parse_int(m.group("states")),
            distinct=parse_int(m.group("distinct")),
            diameter=parse_int(m.group("diam")),
            wall_seconds=parse_duration_seconds(m.group("wall")),
        )

    required = {"MC_AdaptiveAttack", "MC_LivenessAPS", "MC_LivenessAPSAttack", "MC_RefinementTransfer"}
    missing = sorted(required - set(out))
    if missing:
        raise RuntimeError(f"README mv5 rows missing models: {missing}")
    return out


def parse_tex_mv5_rows() -> Dict[str, Metrics]:
    text = TEX.read_text(encoding="utf-8")
    anchor = r"\label{tab:adaptivebft-verif-results-mv5}"
    start = text.find(anchor)
    if start < 0:
        raise RuntimeError("mv5 table label not found in verification_tables.tex")
    end = text.find(r"\end{table*}", start)
    if end < 0:
        raise RuntimeError("mv5 table end not found in verification_tables.tex")
    block = text[start:end]

    row_re = re.compile(
        r"^(?P<model>MC\\_[A-Za-z0-9]+)\s*&\s*(?P<states>[0-9,]+)\s*&\s*(?P<distinct>[0-9,]+)\s*&\s*(?P<diam>[0-9]+)\s*&\s*(?P<wall>[^&]+)&\s*Pass\s*&",
        re.MULTILINE,
    )
    out: Dict[str, Metrics] = {}
    for m in row_re.finditer(block):
        model = m.group("model").replace("\\_", "_")
        out[model] = Metrics(
            states=parse_int(m.group("states")),
            distinct=parse_int(m.group("distinct")),
            diameter=parse_int(m.group("diam")),
            wall_seconds=parse_duration_seconds(m.group("wall")),
        )

    required = {"MC_AdaptiveAttack", "MC_LivenessAPS", "MC_LivenessAPSAttack", "MC_RefinementTransfer"}
    missing = sorted(required - set(out))
    if missing:
        raise RuntimeError(f"verification_tables.tex mv5 rows missing models: {missing}")
    return out


def main() -> int:
    wrapper_md = parse_wrapper_snapshot()
    wrapper_tex = parse_tex_wrapper_table()

    errors = 0
    for key, m_md in wrapper_md.items():
        if key not in wrapper_tex:
            print(f"[ERROR] wrapper table missing row: {key}")
            errors += 1
            continue
        m_tex = wrapper_tex[key]
        if (m_md.states, m_md.distinct, m_md.diameter, m_md.wall_seconds) != (
            m_tex.states,
            m_tex.distinct,
            m_tex.diameter,
            m_tex.wall_seconds,
        ):
            print(
                "[ERROR] wrapper row mismatch for"
                f" {key}: md=({m_md.states},{m_md.distinct},{m_md.diameter},{m_md.wall_seconds}s)"
                f" tex=({m_tex.states},{m_tex.distinct},{m_tex.diameter},{m_tex.wall_seconds}s)"
            )
            errors += 1

    n7_scale = parse_scale_snapshot()
    n7_readme = parse_readme_n7_row()
    if (n7_scale.states, n7_scale.distinct) != (n7_readme.states, n7_readme.distinct):
        print(
            "[ERROR] README n7 row mismatches scale snapshot (state-space size):"
            f" scale=({n7_scale.states},{n7_scale.distinct})"
            f" readme=({n7_readme.states},{n7_readme.distinct})"
        )
        errors += 1
    if n7_scale.diameter != n7_readme.diameter:
        print(
            "[WARN] README n7 diameter differs from latest snapshot:"
            f" snapshot={n7_scale.diameter}, readme={n7_readme.diameter}"
        )
    if n7_scale.wall_seconds != n7_readme.wall_seconds:
        print(
            "[WARN] README n7 wall-clock differs from latest snapshot:"
            f" snapshot={n7_scale.wall_seconds}s, readme={n7_readme.wall_seconds}s"
        )

    n7_tex = parse_tex_n7_table_row()
    if (n7_scale.states, n7_scale.distinct) != (n7_tex.states, n7_tex.distinct):
        print(
            "[ERROR] verification_tables.tex n7 row mismatches scale snapshot (state-space size):"
            f" scale=({n7_scale.states},{n7_scale.distinct})"
            f" tex=({n7_tex.states},{n7_tex.distinct})"
        )
        errors += 1
    if n7_scale.diameter != n7_tex.diameter:
        print(
            "[WARN] verification_tables.tex n7 diameter differs from latest snapshot:"
            f" snapshot={n7_scale.diameter}, tex={n7_tex.diameter}"
        )
    if n7_scale.wall_seconds != n7_tex.wall_seconds:
        print(
            "[WARN] verification_tables.tex n7 wall-clock differs from latest snapshot:"
            f" snapshot={n7_scale.wall_seconds}s, tex={n7_tex.wall_seconds}s"
        )

    n7lite_scale = parse_scale_n7lite_snapshot()
    n7lite_readme = parse_readme_n7lite_row()
    if (n7lite_scale.states, n7lite_scale.distinct) != (n7lite_readme.states, n7lite_readme.distinct):
        print(
            "[ERROR] README n7lite row mismatches n7lite snapshot (state-space size):"
            f" snapshot=({n7lite_scale.states},{n7lite_scale.distinct})"
            f" readme=({n7lite_readme.states},{n7lite_readme.distinct})"
        )
        errors += 1
    if n7lite_scale.diameter != n7lite_readme.diameter:
        print(
            "[WARN] README n7lite diameter differs from latest snapshot:"
            f" snapshot={n7lite_scale.diameter}, readme={n7lite_readme.diameter}"
        )
    if n7lite_scale.wall_seconds != n7lite_readme.wall_seconds:
        print(
            "[WARN] README n7lite wall-clock differs from latest snapshot:"
            f" snapshot={n7lite_scale.wall_seconds}s, readme={n7lite_readme.wall_seconds}s"
        )

    n7lite_tex = parse_tex_n7lite_table_row()
    if (n7lite_scale.states, n7lite_scale.distinct) != (n7lite_tex.states, n7lite_tex.distinct):
        print(
            "[ERROR] verification_tables.tex n7lite row mismatches latest snapshot (state-space size):"
            f" snapshot=({n7lite_scale.states},{n7lite_scale.distinct})"
            f" tex=({n7lite_tex.states},{n7lite_tex.distinct})"
        )
        errors += 1
    if n7lite_scale.diameter != n7lite_tex.diameter:
        print(
            "[WARN] verification_tables.tex n7lite diameter differs from latest snapshot:"
            f" snapshot={n7lite_scale.diameter}, tex={n7lite_tex.diameter}"
        )
    if n7lite_scale.wall_seconds != n7lite_tex.wall_seconds:
        print(
            "[WARN] verification_tables.tex n7lite wall-clock differs from latest snapshot:"
            f" snapshot={n7lite_scale.wall_seconds}s, tex={n7lite_tex.wall_seconds}s"
        )

    transfer_snap = parse_transfer_snapshot()
    transfer_readme = parse_readme_transfer_rows()
    transfer_tex = parse_tex_transfer_rows()
    for profile in ("baseline", "mv3", "mv4"):
        s = transfer_snap[profile]
        r = transfer_readme[profile]
        t = transfer_tex[profile]
        if (s.states, s.distinct, s.diameter) != (r.states, r.distinct, r.diameter):
            print(
                "[ERROR] README transfer row mismatches latest transfer snapshot:"
                f" profile={profile}, snapshot=({s.states},{s.distinct},{s.diameter})"
                f", readme=({r.states},{r.distinct},{r.diameter})"
            )
            errors += 1
        if (s.states, s.distinct, s.diameter) != (t.states, t.distinct, t.diameter):
            print(
                "[ERROR] verification_tables.tex transfer row mismatches latest transfer snapshot:"
                f" profile={profile}, snapshot=({s.states},{s.distinct},{s.diameter})"
                f", tex=({t.states},{t.distinct},{t.diameter})"
            )
            errors += 1
        if s.wall_seconds != r.wall_seconds:
            print(
                "[WARN] README transfer wall-clock differs from latest snapshot:"
                f" profile={profile}, snapshot={s.wall_seconds}s, readme={r.wall_seconds}s"
            )
        if s.wall_seconds != t.wall_seconds:
            print(
                "[WARN] verification_tables.tex transfer wall-clock differs from latest snapshot:"
                f" profile={profile}, snapshot={s.wall_seconds}s, tex={t.wall_seconds}s"
            )

    mv5_snap = parse_mv5_snapshot()
    mv5_readme = parse_readme_mv5_rows()
    mv5_tex = parse_tex_mv5_rows()
    for model in ("MC_AdaptiveAttack", "MC_LivenessAPS", "MC_LivenessAPSAttack", "MC_RefinementTransfer"):
        s = mv5_snap[model]
        r = mv5_readme[model]
        t = mv5_tex[model]
        if (s.states, s.distinct, s.diameter) != (r.states, r.distinct, r.diameter):
            print(
                "[ERROR] README mv5 row mismatches latest mv5 snapshot:"
                f" model={model}, snapshot=({s.states},{s.distinct},{s.diameter})"
                f", readme=({r.states},{r.distinct},{r.diameter})"
            )
            errors += 1
        if (s.states, s.distinct, s.diameter) != (t.states, t.distinct, t.diameter):
            print(
                "[ERROR] verification_tables.tex mv5 row mismatches latest mv5 snapshot:"
                f" model={model}, snapshot=({s.states},{s.distinct},{s.diameter})"
                f", tex=({t.states},{t.distinct},{t.diameter})"
            )
            errors += 1
        if s.wall_seconds != r.wall_seconds:
            print(
                "[WARN] README mv5 wall-clock differs from latest snapshot:"
                f" model={model}, snapshot={s.wall_seconds}s, readme={r.wall_seconds}s"
            )
        if s.wall_seconds != t.wall_seconds:
            print(
                "[WARN] verification_tables.tex mv5 wall-clock differs from latest snapshot:"
                f" model={model}, snapshot={s.wall_seconds}s, tex={t.wall_seconds}s"
            )

    if errors:
        print(f"\nFAILED: {errors} artifact-sync mismatch(es).")
        return 1

    print("OK: wrapper table + n7/n7lite rows + transfer rows + mv5 rows are synchronized with latest artifacts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
