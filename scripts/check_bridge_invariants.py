#!/usr/bin/env python3
"""Gate check: wrapper-level refinement-bridge invariants are wired in all cfg profiles."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODELS_DIR = ROOT / "models"


MODEL_OPERATOR_REQUIREMENTS = {
    "MC_AdaptiveAttack.tla": [
        "RefinementInvariantCoreAttack ==",
        "SafetyBridgeFiniteAttack ==",
        "CommitProjectionShapeAttack ==",
        "SpecToAbstractSpecCheckedAttack ==",
    ],
    "MC_LivenessAPS.tla": [
        "RefinementInvariantCoreAPS ==",
        "SafetyBridgeFiniteAPS ==",
        "CommitProjectionShapeAPS ==",
        "SpecToAbstractSpecCheckedAPS ==",
    ],
    "MC_LivenessAPSAttack.tla": [
        "RefinementInvariantCoreJoint ==",
        "SafetyBridgeFiniteJoint ==",
        "CommitProjectionShapeJoint ==",
        "SpecToAbstractSpecCheckedJoint ==",
    ],
    "MC_RefinementTransfer.tla": [
        "RefinementInvariantCoreTransfer ==",
        "SafetyBridgeFiniteTransfer ==",
        "CommitProjectionShapeTransfer ==",
        "SpecToAbstractSpecChecked ==",
    ],
}


CFG_REQUIREMENTS = [
    (
        re.compile(r"^MC_AdaptiveAttack(?:_.*)?\.cfg$"),
        [
            "INVARIANT RefinementInvariantCoreAttack",
            "INVARIANT SafetyBridgeFiniteAttack",
            "INVARIANT CommitProjectionShapeAttack",
            "PROPERTY SpecToAbstractSpecCheckedAttack",
        ],
    ),
    (
        re.compile(r"^MC_LivenessAPS(?:_.*)?\.cfg$"),
        [
            "INVARIANT RefinementInvariantCoreAPS",
            "INVARIANT SafetyBridgeFiniteAPS",
            "INVARIANT CommitProjectionShapeAPS",
            "PROPERTY SpecToAbstractSpecCheckedAPS",
        ],
    ),
    (
        re.compile(r"^MC_LivenessAPSAttack(?:_.*)?\.cfg$"),
        [
            "INVARIANT RefinementInvariantCoreJoint",
            "INVARIANT SafetyBridgeFiniteJoint",
            "INVARIANT CommitProjectionShapeJoint",
            "PROPERTY SpecToAbstractSpecCheckedJoint",
        ],
    ),
    (
        re.compile(r"^MC_RefinementTransfer(?:_.*)?\.cfg$"),
        [
            "INVARIANT RefinementInvariantCoreTransfer",
            "INVARIANT SafetyBridgeFiniteTransfer",
            "INVARIANT CommitProjectionShapeTransfer",
            "PROPERTY SpecToAbstractSpecChecked",
        ],
    ),
]


def main() -> int:
    errors: list[str] = []

    for filename, required in MODEL_OPERATOR_REQUIREMENTS.items():
        path = MODELS_DIR / filename
        if not path.exists():
            errors.append(f"missing model file: {path}")
            continue
        text = path.read_text(encoding="utf-8")
        for token in required:
            if token not in text:
                errors.append(f"{filename}: missing operator token `{token}`")

    cfg_files = sorted(MODELS_DIR.glob("*.cfg"))
    for cfg_path in cfg_files:
        cfg_name = cfg_path.name
        text = cfg_path.read_text(encoding="utf-8")
        matched = False
        for pattern, required_lines in CFG_REQUIREMENTS:
            if not pattern.match(cfg_name):
                continue
            matched = True
            for line in required_lines:
                if line not in text:
                    errors.append(f"{cfg_name}: missing `{line}`")
            break
        if not matched:
            errors.append(f"{cfg_name}: no bridge requirement rule matched")

    if errors:
        print("Bridge-invariant wiring check: FAIL")
        for err in errors:
            print(f"- {err}")
        return 1

    print("Bridge-invariant wiring check: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
