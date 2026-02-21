#!/usr/bin/env python3
"""Run automated closure attempts for AbstractSafetyTransferTemplate.

This script temporarily patches AdaptiveBFT_Refinement_Theorems.tla with
candidate proofs for `AbstractSafetyTransferTemplate`, executes `make proofs`,
captures outcomes, and restores the original file.
"""

from __future__ import annotations

import argparse
import re
import hashlib
import subprocess
import textwrap
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


@dataclass
class AttemptResult:
    name: str
    status: str
    rc: int
    duration_s: float
    log_rel: str
    signature: str
    goals: list[tuple[int, str]]


ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "specifications" / "AdaptiveBFT_Refinement_Theorems.tla"
RESULTS = ROOT / "docs" / "results"


ATTEMPTS: dict[str, str] = {
    "instance_theorem_direct": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            BY ABSTRACT_THEOREMS!AbstractSafetyTheorem

        """
    ),
    "split_invariants_direct": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1>1. ABSTRACT!SpecA => []ABSTRACT!NoForkA
                BY ABSTRACT_THEOREMS!AbstractNoForkByInduction
            <1>2. ABSTRACT!SpecA => []ABSTRACT!LockMonotonicityA
                BY ABSTRACT_THEOREMS!AbstractLockSafetyByInduction
            <1>3. ABSTRACT!SpecA => []ABSTRACT!SafetyA
                BY <1>1, <1>2, PTL DEF ABSTRACT!SafetyA
            <1> QED
                BY <1>3

        """
    ),
    "instance_with_def_bridge": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1>1. ABSTRACT_THEOREMS!SpecA => []ABSTRACT_THEOREMS!SafetyA
                BY ABSTRACT_THEOREMS!AbstractSafetyTheorem
            <1>2. ABSTRACT!SpecA => ABSTRACT_THEOREMS!SpecA
                BY DEF ABSTRACT!SpecA, ABSTRACT_THEOREMS!SpecA
            <1>3. []ABSTRACT_THEOREMS!SafetyA => []ABSTRACT!SafetyA
                BY PTL DEF ABSTRACT!SafetyA, ABSTRACT_THEOREMS!SafetyA
            <1>4. ABSTRACT!SpecA => []ABSTRACT_THEOREMS!SafetyA
                BY <1>1, <1>2
            <1>5. ABSTRACT!SpecA => []ABSTRACT!SafetyA
                BY <1>3, <1>4
            <1> QED
                BY <1>5

        """
    ),
    "suffices_with_expanded_instances": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1> SUFFICES ASSUME ABSTRACT!SpecA
                         PROVE []ABSTRACT!SafetyA
              OBVIOUS
            <1>1. ABSTRACT_THEOREMS!SpecA
                BY DEF ABSTRACT!SpecA, ABSTRACT_THEOREMS!SpecA
            <1>2. []ABSTRACT_THEOREMS!SafetyA
                BY ABSTRACT_THEOREMS!AbstractSafetyTheorem, <1>1
            <1>3. []ABSTRACT!SafetyA
                BY <1>2 DEF ABSTRACT!SafetyA, ABSTRACT_THEOREMS!SafetyA
            <1> QED
                BY <1>3

        """
    ),
    "instance_use_obvious": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1> USE ABSTRACT_THEOREMS!AbstractSafetyTheorem
            <1> QED
                OBVIOUS

        """
    ),
    "instance_theorem_def": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            BY DEF ABSTRACT_THEOREMS!AbstractSafetyTheorem

        """
    ),
    "instance_use_then_def": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1> USE ABSTRACT_THEOREMS!AbstractSafetyTheorem
            <1> QED
                BY DEF ABSTRACT_THEOREMS!AbstractSafetyTheorem

        """
    ),
    "instance_theorem_ptl_lift": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1>1. ABSTRACT_THEOREMS!SpecA => []ABSTRACT_THEOREMS!SafetyA
                BY ABSTRACT_THEOREMS!AbstractSafetyTheorem
            <1>2. ABSTRACT!SpecA => ABSTRACT_THEOREMS!SpecA
                BY DEF ABSTRACT!SpecA, ABSTRACT_THEOREMS!SpecA
            <1>3. ABSTRACT!SafetyA <=> ABSTRACT_THEOREMS!SafetyA
                BY DEF ABSTRACT!SafetyA, ABSTRACT_THEOREMS!SafetyA
            <1>4. []ABSTRACT_THEOREMS!SafetyA => []ABSTRACT!SafetyA
                BY <1>3, PTL
            <1>5. ABSTRACT!SpecA => []ABSTRACT!SafetyA
                BY <1>1, <1>2, <1>4
            <1> QED
                BY <1>5

        """
    ),
    "instance_via_suffices_spec": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1> SUFFICES ASSUME ABSTRACT!SpecA
                         PROVE []ABSTRACT!SafetyA
              OBVIOUS
            <1>1. ABSTRACT_THEOREMS!SpecA => []ABSTRACT_THEOREMS!SafetyA
                BY ABSTRACT_THEOREMS!AbstractSafetyTheorem
            <1>2. ABSTRACT_THEOREMS!SpecA
                BY <1> DEF ABSTRACT!SpecA, ABSTRACT_THEOREMS!SpecA
            <1>3. []ABSTRACT_THEOREMS!SafetyA
                BY <1>1, <1>2
            <1>4. []ABSTRACT!SafetyA
                BY <1>3 DEF ABSTRACT!SafetyA, ABSTRACT_THEOREMS!SafetyA
            <1> QED
                BY <1>4

        """
    ),
    "split_and_lift_ptl": textwrap.dedent(
        """\
        THEOREM AbstractSafetyTransferTemplate ==
            (ABSTRACT!SpecA => []ABSTRACT!SafetyA)
        PROOF
            <1>1. ABSTRACT_THEOREMS!SpecA => []ABSTRACT_THEOREMS!NoForkA
                BY ABSTRACT_THEOREMS!AbstractNoForkByInduction
            <1>2. ABSTRACT_THEOREMS!SpecA => []ABSTRACT_THEOREMS!LockMonotonicityA
                BY ABSTRACT_THEOREMS!AbstractLockSafetyByInduction
            <1>3. ABSTRACT!SpecA => ABSTRACT_THEOREMS!SpecA
                BY DEF ABSTRACT!SpecA, ABSTRACT_THEOREMS!SpecA
            <1>4. ABSTRACT!SpecA => []ABSTRACT_THEOREMS!NoForkA
                BY <1>1, <1>3
            <1>5. ABSTRACT!SpecA => []ABSTRACT_THEOREMS!LockMonotonicityA
                BY <1>2, <1>3
            <1>6. ABSTRACT!SpecA => []ABSTRACT!NoForkA
                BY <1>4, PTL DEF ABSTRACT!NoForkA, ABSTRACT_THEOREMS!NoForkA
            <1>7. ABSTRACT!SpecA => []ABSTRACT!LockMonotonicityA
                BY <1>5, PTL DEF ABSTRACT!LockMonotonicityA, ABSTRACT_THEOREMS!LockMonotonicityA
            <1>8. ABSTRACT!SpecA => []ABSTRACT!SafetyA
                BY <1>6, <1>7, PTL DEF ABSTRACT!SafetyA
            <1> QED
                BY <1>8

        """
    ),
}


def splice_safety_block(source: str, replacement: str) -> str:
    marker_start = "THEOREM AbstractSafetyTransferTemplate =="
    marker_end = "THEOREM AbstractLivenessTransferTemplate =="
    i = source.find(marker_start)
    j = source.find(marker_end)
    if i < 0 or j < 0 or j <= i:
        raise RuntimeError("unable to locate safety-transfer theorem block boundaries")
    return source[:i] + replacement + source[j:]


def first_error_signature(text: str) -> str:
    for line in text.splitlines():
        if "[ERROR]:" in line:
            return line.strip()
    for line in text.splitlines():
        if "Could not prove or check" in line:
            return line.strip()
    for line in text.splitlines():
        if "Semantic errors" in line or "Level error" in line:
            return line.strip()
    return "no explicit error signature found"


def parse_failed_goals(text: str) -> list[tuple[int, str]]:
    pattern = re.compile(
        r'File "\./AdaptiveBFT_Refinement_Theorems\.tla", line (\d+),[^\n]*\n'
        r'\[ERROR\]: Could not prove or check:\n'
        r'((?:\s+.*\n)+)'
    )
    goals: list[tuple[int, str]] = []
    for match in pattern.finditer(text):
        line_no = int(match.group(1))
        block = match.group(2).splitlines()
        goal = ""
        for idx, raw in enumerate(block):
            s = raw.strip()
            if s.startswith("PROVE"):
                parts = [s[len("PROVE") :].strip()]
                for nxt in block[idx + 1 :]:
                    nxts = nxt.strip()
                    if not nxts:
                        continue
                    if nxts.startswith("ASSUME"):
                        continue
                    if nxts.startswith("PROVE"):
                        break
                    parts.append(nxts)
                goal = " ".join(p for p in parts if p)
                break
        if goal:
            goal = " ".join(goal.split())
            goals.append((line_no, goal))
    return goals


def run_make_proofs(log_path: Path, timeout_s: int, tlaps_retry: int) -> tuple[int, float, str]:
    t0 = time.time()
    proc = subprocess.run(
        [
            "make",
            f"TLAPS_RETRY={tlaps_retry}",
            "TLAPS_INVARIANT=0",
            "proofs",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=timeout_s,
        encoding="utf-8",
        errors="replace",
    )
    dt = time.time() - t0
    log_path.write_text(proc.stdout, encoding="utf-8")
    sig = first_error_signature(proc.stdout)
    return proc.returncode, dt, sig


def digest_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def write_report(
    out: Path,
    stamp: str,
    baseline: AttemptResult,
    attempts: list[AttemptResult],
    skip_candidates: bool,
    skip_reason: str,
    restore_ok: bool,
    restore_proofs_ok: bool,
    original_sha256: str,
    restored_sha256: str,
) -> None:
    now = datetime.now(timezone.utc).astimezone()
    lines: list[str] = []
    lines.append("# Safety Transfer Closure Attempts")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append(f"- campaign_id: `{stamp}`")
    lines.append("- target: `AbstractSafetyTransferTemplate`")
    lines.append(f"- attempts_total: `{len(attempts)}`")
    lines.append(f"- candidate_mode: `{'skip' if skip_candidates else 'full'}`")
    if skip_reason:
        lines.append(f"- skip_reason: {skip_reason}")
    lines.append("")
    lines.append("## Baseline")
    lines.append("")
    lines.append("| Case | Status | Exit | Duration | Log |")
    lines.append("|---|---|---:|---:|---|")
    lines.append(
        f"| `open_allowlisted` | {baseline.status} | {baseline.rc} | {baseline.duration_s:.1f}s | `{baseline.log_rel}` |"
    )
    lines.append("")
    lines.append("## Candidate Proof Attempts")
    lines.append("")
    lines.append("| Strategy | Status | Exit | Duration | Signature | Log |")
    lines.append("|---|---|---:|---:|---|---|")
    for r in attempts:
        sig = r.signature.replace("|", "\\|")
        lines.append(
            f"| `{r.name}` | {r.status} | {r.rc} | {r.duration_s:.1f}s | {sig} | `{r.log_rel}` |"
        )
    lines.append("")
    lines.append("## Failed Goal Snapshot (Latest Campaign)")
    lines.append("")
    lines.append("| Strategy | Goal line | Goal formula |")
    lines.append("|---|---:|---|")
    any_goal = False
    for r in attempts:
        for line_no, goal in r.goals[:1]:
            any_goal = True
            g = goal.replace("|", "\\|")
            lines.append(f"| `{r.name}` | {line_no} | {g} |")
    if not any_goal:
        lines.append("| (none) | - | no parsed `PROVE` goals found in logs |")

    agg: Counter[tuple[int, str]] = Counter()
    strat_for_goal: defaultdict[tuple[int, str], set[str]] = defaultdict(set)
    for r in attempts:
        for g in r.goals:
            agg[g] += 1
            strat_for_goal[g].add(r.name)
    lines.append("")
    lines.append("## Goal Aggregates")
    lines.append("")
    lines.append("| Goal line | Hits | Strategies | Goal formula |")
    lines.append("|---:|---:|---|---|")
    if agg:
        for (line_no, goal), hits in agg.most_common():
            ss = ", ".join(f"`{s}`" for s in sorted(strat_for_goal[(line_no, goal)]))
            g = goal.replace("|", "\\|")
            lines.append(f"| {line_no} | {hits} | {ss} | {g} |")
    else:
        lines.append("| - | 0 | - | no aggregate goals parsed |")
    lines.append("")
    lines.append("## Restore Check")
    lines.append("")
    lines.append(f"- restore_status: {'PASS' if restore_ok else 'FAIL'}")
    lines.append(f"- restore_proofs_status: {'PASS' if restore_proofs_ok else 'FAIL'}")
    lines.append(f"- source_sha256_before: `{original_sha256}`")
    lines.append(f"- source_sha256_after: `{restored_sha256}`")
    lines.append("- note: source file is restored to original content after all attempts.")
    lines.append("")
    out.write_text("\n".join(lines), encoding="utf-8")


def write_goalpack(out: Path, stamp: str, attempts: list[AttemptResult]) -> None:
    now = datetime.now(timezone.utc).astimezone()
    agg: Counter[tuple[int, str]] = Counter()
    strat_for_goal: defaultdict[tuple[int, str], set[str]] = defaultdict(set)
    for r in attempts:
        for g in r.goals:
            agg[g] += 1
            strat_for_goal[g].add(r.name)

    lines: list[str] = []
    lines.append("# Safety-Transfer Goalpack")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append(f"- campaign_id: `{stamp}`")
    lines.append(f"- strategies: `{len(attempts)}`")
    lines.append("")
    lines.append("## Ranked Unproved Goals")
    lines.append("")
    lines.append("| Rank | Goal line | Hits | Strategies | Goal formula |")
    lines.append("|---:|---:|---:|---|---|")
    if agg:
        for idx, ((line_no, goal), hits) in enumerate(agg.most_common(), start=1):
            ss = ", ".join(f"`{s}`" for s in sorted(strat_for_goal[(line_no, goal)]))
            g = goal.replace("|", "\\|")
            lines.append(f"| {idx} | {line_no} | {hits} | {ss} | {g} |")
    else:
        lines.append("| 1 | - | 0 | - | no parsed goals |")
    lines.append("")
    lines.append("## Tactic Worklist")
    lines.append("")
    lines.append("1. Split `SpecA` proof into `InitA` and `[NextA]_varsA` components before temporal lifting.")
    lines.append("2. Prove extensional equality lemmas for `ABSTRACT` vs `ABSTRACT_THEOREMS` operators (`InitA`, `NextA`, `varsA`, `SafetyA`).")
    lines.append("3. Add explicit PTL bridge lemma: `[](P) /\\ [](P => Q) => [](Q)` and instantiate for safety predicates.")
    lines.append("4. Keep closure attempts in module-only mode (`TLAPS_INVARIANT=0`) to avoid unrelated invariant-module flakiness.")
    lines.append("")
    out.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=1200, help="timeout per make proofs run (seconds)")
    parser.add_argument(
        "--tlaps-retry",
        type=int,
        default=4,
        help="TLAPS retry count passed to make proofs (mitigates backend flakiness)",
    )
    parser.add_argument(
        "--force-attempts",
        action="store_true",
        help="run all candidate attempts even when baseline indicates theorem is already closed",
    )
    args = parser.parse_args()

    RESULTS.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    base_name = f"safety_transfer_closure_attempt_{stamp}"

    original = SPEC.read_text(encoding="utf-8")
    original_sha256 = digest_text(original)
    restore_ok = False
    restore_proofs_ok = False

    baseline_log = RESULTS / f"{base_name}_baseline.log"
    rc, dt, sig = run_make_proofs(baseline_log, args.timeout, args.tlaps_retry)
    baseline_text = baseline_log.read_text(encoding="utf-8")
    baseline = AttemptResult(
        name="open_allowlisted",
        status="PASS" if rc == 0 else "FAIL",
        rc=rc,
        duration_s=dt,
        log_rel=str(baseline_log.relative_to(ROOT)).replace("\\", "/"),
        signature=sig,
        goals=parse_failed_goals(baseline_text),
    )

    attempt_results: list[AttemptResult] = []
    restored_sha256 = original_sha256
    skip_candidates = False
    skip_reason = ""
    baseline_closed = baseline.status == "PASS" and len(baseline.goals) == 0
    if baseline_closed and not args.force_attempts:
        skip_candidates = True
        skip_reason = "baseline proof pass with no parsed failed goals; skip expensive candidate rewrites"
        attempt_results.append(
            AttemptResult(
                name="already_closed_skip",
                status="PASS",
                rc=0,
                duration_s=0.0,
                log_rel=baseline.log_rel,
                signature="skipped: baseline theorem already closed",
                goals=[],
            )
        )
    try:
        if not skip_candidates:
            for name, block in ATTEMPTS.items():
                patched = splice_safety_block(original, block)
                SPEC.write_text(patched, encoding="utf-8")
                log_path = RESULTS / f"{base_name}_{name}.log"
                rc, dt, sig = run_make_proofs(log_path, args.timeout, args.tlaps_retry)
                log_text = log_path.read_text(encoding="utf-8")
                attempt_results.append(
                    AttemptResult(
                        name=name,
                        status="PASS" if rc == 0 else "FAIL",
                        rc=rc,
                        duration_s=dt,
                        log_rel=str(log_path.relative_to(ROOT)).replace("\\", "/"),
                        signature=sig,
                        goals=parse_failed_goals(log_text),
                    )
                )
    finally:
        SPEC.write_text(original, encoding="utf-8")
        restore_log = RESULTS / f"{base_name}_restore.log"
        rc2, dt2, sig2 = run_make_proofs(restore_log, args.timeout, args.tlaps_retry)
        restore_text = restore_log.read_text(encoding="utf-8")
        restored_sha256 = digest_text(SPEC.read_text(encoding="utf-8"))
        restore_proofs_ok = (rc2 == 0)
        restore_ok = (restored_sha256 == original_sha256)
        attempt_results.append(
            AttemptResult(
                name="restore_check",
                status="PASS" if restore_ok else "FAIL",
                rc=rc2,
                duration_s=dt2,
                log_rel=str(restore_log.relative_to(ROOT)).replace("\\", "/"),
                signature=sig2,
                goals=parse_failed_goals(restore_text),
            )
        )

    report = RESULTS / f"{base_name}.md"
    write_report(
        report,
        stamp,
        baseline,
        attempt_results[:-1],
        skip_candidates,
        skip_reason,
        restore_ok,
        restore_proofs_ok,
        original_sha256,
        restored_sha256,
    )
    latest = RESULTS / "safety_transfer_closure_attempt_latest.md"
    latest.write_text(report.read_text(encoding="utf-8"), encoding="utf-8")

    goalpack = RESULTS / f"safety_transfer_goalpack_{stamp}.md"
    write_goalpack(goalpack, stamp, attempt_results[:-1])
    goalpack_latest = RESULTS / "safety_transfer_goalpack_latest.md"
    goalpack_latest.write_text(goalpack.read_text(encoding="utf-8"), encoding="utf-8")

    print(f"Safety-transfer closure report: {report.relative_to(ROOT)}")
    print(f"Latest safety-transfer closure report: {latest.relative_to(ROOT)}")
    print(f"Safety-transfer goalpack: {goalpack.relative_to(ROOT)}")
    print(f"Latest safety-transfer goalpack: {goalpack_latest.relative_to(ROOT)}")
    return 0 if restore_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
