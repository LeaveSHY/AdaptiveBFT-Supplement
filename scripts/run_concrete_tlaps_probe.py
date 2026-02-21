#!/usr/bin/env python3
"""Run a concrete-track TLAPS probe and emit reviewer-facing diagnostics.

This probe is non-blocking by default: it records PASS/FAIL/TIMEOUT per
concrete theorem module and returns success so the campaign can continue.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


MODULES = [
    "AdaptiveBFT_ConcreteBridge_Theorems.tla",
    "AdaptiveBFT_ConcreteBinding_Theorems.tla",
    "AdaptiveBFT_ConcreteTransfer_Theorems.tla",
]


@dataclass(frozen=True)
class ProbeRow:
    module: str
    status: str
    timeout_s: int
    duration_s: float
    rc: int
    proved_max: str
    failed_obligations: str
    signature: str
    log_rel: str


def parse_proved_max(text: str) -> str:
    vals = [int(m.group(1)) for m in re.finditer(r"All\s+([0-9]+)\s+obligations?\s+proved", text)]
    if not vals:
        return "-"
    return str(max(vals))


def parse_failed_count(text: str) -> str:
    m = re.search(r"\[ERROR\]:\s*([0-9]+)/([0-9]+)\s+obligations\s+failed", text)
    if not m:
        return "0"
    return m.group(1)


def parse_signature(text: str) -> str:
    for line in text.splitlines():
        line = line.strip()
        if "[ERROR]: Could not prove or check:" in line:
            return "Could not prove/check (see log context)"
        if "Recursive operator definitions are not supported" in line:
            return "recursive-operator backend limitation"
        if "backend errors: there are unproved obligations" in line:
            return "backend errors: unproved obligations"
        if "No such file or directory" in line:
            return "path setup failure"
        if "Semantic errors" in line:
            return "semantic error"
        if "timed out" in line.lower():
            return "timeout"
    return "-"


def _to_text(data: object) -> str:
    if data is None:
        return ""
    if isinstance(data, bytes):
        return data.decode("utf-8", errors="replace")
    return str(data)


def wsl_resolve_spec_path(spec_dir: Path) -> str:
    raw = str(spec_dir).replace("\\", "/")
    if raw.startswith("/mnt/") or raw.startswith("/home/") or raw.startswith("/tmp/"):
        return raw
    proc = subprocess.run(
        ["wsl.exe", "-e", "wslpath", "-a", str(spec_dir)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return proc.stdout.strip().splitlines()[-1].strip()


def run_wsl_tlapm(module: str, spec_dir: Path, timeout_s: int) -> tuple[int, float, str]:
    wsl_spec = wsl_resolve_spec_path(spec_dir)
    cmd = [
        "wsl.exe",
        "-e",
        "bash",
        "-lc",
        f"cd '{wsl_spec}' && /root/.local/tlaps/bin/tlapm -I . -I ./modules '{module}'",
    ]
    t0 = time.time()
    try:
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout_s,
        )
        dt = time.time() - t0
        return proc.returncode, dt, proc.stdout
    except subprocess.TimeoutExpired as e:
        dt = time.time() - t0
        out = _to_text(e.stdout) + "\n[ERROR] timed out\n"
        return 124, dt, out


def run_local_tlapm(module: str, spec_dir: Path, timeout_s: int) -> tuple[int, float, str]:
    tlapm = shutil.which("tlapm")
    if not tlapm:
        return 127, 0.0, "[ERROR] tlapm not found on PATH\n"
    t0 = time.time()
    try:
        proc = subprocess.run(
            [tlapm, "-I", ".", "-I", "./modules", module],
            cwd=spec_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout_s,
        )
        dt = time.time() - t0
        return proc.returncode, dt, proc.stdout
    except subprocess.TimeoutExpired as e:
        dt = time.time() - t0
        out = _to_text(e.stdout) + "\n[ERROR] timed out\n"
        return 124, dt, out


def write_report(
    out: Path,
    rows: list[ProbeRow],
    timeout_s: int,
    timeout_transfer_s: int | None,
    backend: str,
) -> None:
    now = datetime.now(timezone.utc).astimezone()
    lines: list[str] = []
    lines.append("# Concrete TLAPS Probe")
    lines.append("")
    lines.append(f"- generated: {now.strftime('%Y-%m-%d %H:%M:%S %z')}")
    lines.append(f"- backend: `{backend}`")
    lines.append(f"- timeout_default: `{timeout_s}s`")
    if timeout_transfer_s is not None:
        lines.append(f"- timeout_transfer_override: `{timeout_transfer_s}s`")
    lines.append("- interpretation: concrete theorem track diagnostics (non-blocking probe).")
    lines.append("")
    lines.append("| Module | Status | Timeout | Duration | Exit | Obligations Proved (max) | Failed Obligations | Signature | Log |")
    lines.append("|---|---|---:|---:|---:|---:|---:|---|---|")
    for r in rows:
        sig = r.signature.replace("|", "\\|")
        lines.append(
            f"| `{r.module}` | {r.status} | {r.timeout_s}s | {r.duration_s:.1f}s | {r.rc} | {r.proved_max} | {r.failed_obligations} | {sig} | `{r.log_rel}` |"
        )
    lines.append("")
    lines.append("Notes:")
    lines.append("")
    lines.append("- `PASS`: all obligations proved for that module.")
    lines.append("- `FAIL`: parser/backend/unproved-obligation failure in current concrete proof skeleton.")
    lines.append("- `TIMEOUT`: timeout hit before completion.")
    lines.append("")
    out.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument(
        "--timeout-transfer",
        type=int,
        default=None,
        help="optional timeout override (seconds) for AdaptiveBFT_ConcreteTransfer_Theorems.tla",
    )
    parser.add_argument(
        "--fail-on-fail",
        action="store_true",
        help="exit non-zero when any module status is not PASS",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    spec_dir = root / "specifications"
    results = root / "docs" / "results"
    results.mkdir(parents=True, exist_ok=True)

    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    out = results / f"concrete_tlaps_probe_{stamp}.md"
    latest = results / "concrete_tlaps_probe_latest.md"

    backend = "none"
    runner = None
    if shutil.which("wsl.exe"):
        proc = subprocess.run(
            ["wsl.exe", "-e", "/root/.local/tlaps/bin/tlapm", "--version"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        if proc.returncode == 0:
            backend = "wsl:/root/.local/tlaps/bin/tlapm"
            runner = run_wsl_tlapm
    if runner is None and shutil.which("tlapm"):
        backend = shutil.which("tlapm") or "tlapm"
        runner = run_local_tlapm

    rows: list[ProbeRow] = []
    for module in MODULES:
        timeout_for_module = args.timeout
        if module == "AdaptiveBFT_ConcreteTransfer_Theorems.tla" and args.timeout_transfer is not None:
            timeout_for_module = args.timeout_transfer
        log_name = f"concrete_tlaps_probe_{stamp}_{module.replace('.tla', '')}.log"
        log_path = results / log_name
        log_rel = str(log_path.relative_to(root)).replace("\\", "/")
        if runner is None:
            text = "[ERROR] no tlapm backend available\n"
            rc = 127
            dt = 0.0
            status = "SKIP"
        else:
            rc, dt, text = runner(module, spec_dir, timeout_for_module)
            if rc == 124:
                status = "TIMEOUT"
            elif rc == 0:
                status = "PASS"
            else:
                status = "FAIL"
        log_path.write_text(text, encoding="utf-8")
        rows.append(
            ProbeRow(
                module=module,
                status=status,
                timeout_s=timeout_for_module,
                duration_s=dt,
                rc=rc,
                proved_max=parse_proved_max(text),
                failed_obligations=parse_failed_count(text),
                signature=parse_signature(text),
                log_rel=log_rel,
            )
        )

    write_report(out, rows, args.timeout, args.timeout_transfer, backend)
    latest.write_text(out.read_text(encoding="utf-8"), encoding="utf-8")
    print(f"Concrete TLAPS probe written to: {out.relative_to(root)}")
    print(f"Latest concrete TLAPS probe: {latest.relative_to(root)}")

    if args.fail_on_fail:
        bad = [r for r in rows if r.status not in {"PASS"}]
        return 1 if bad else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
