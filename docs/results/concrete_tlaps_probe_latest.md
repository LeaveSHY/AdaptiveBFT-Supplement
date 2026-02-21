# Concrete TLAPS Probe

- generated: 2026-02-21 00:55:03 +0800
- backend: `wsl:/root/.local/tlaps/bin/tlapm`
- timeout_default: `300s`
- timeout_transfer_override: `1200s`
- interpretation: concrete theorem track diagnostics (non-blocking probe).

| Module | Status | Timeout | Duration | Exit | Obligations Proved (max) | Failed Obligations | Signature | Log |
|---|---|---:|---:|---:|---:|---:|---|---|
| `AdaptiveBFT_ConcreteBridge_Theorems.tla` | PASS | 300s | 7.5s | 0 | 6 | 0 | - | `docs/results/concrete_tlaps_probe_20260221-004026_AdaptiveBFT_ConcreteBridge_Theorems.log` |
| `AdaptiveBFT_ConcreteBinding_Theorems.tla` | PASS | 300s | 123.6s | 0 | 14 | 0 | - | `docs/results/concrete_tlaps_probe_20260221-004026_AdaptiveBFT_ConcreteBinding_Theorems.log` |
| `AdaptiveBFT_ConcreteTransfer_Theorems.tla` | PASS | 1200s | 744.9s | 0 | 10 | 0 | - | `docs/results/concrete_tlaps_probe_20260221-004026_AdaptiveBFT_ConcreteTransfer_Theorems.log` |

Notes:

- `PASS`: all obligations proved for that module.
- `FAIL`: parser/backend/unproved-obligation failure in current concrete proof skeleton.
- `TIMEOUT`: timeout hit before completion.
