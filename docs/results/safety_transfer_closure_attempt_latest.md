# Safety Transfer Closure Attempts

- generated: 2026-02-21 01:04:31 +0800
- campaign_id: `20260221-005503`
- target: `AbstractSafetyTransferTemplate`
- attempts_total: `1`
- candidate_mode: `skip`
- skip_reason: baseline proof pass with no parsed failed goals; skip expensive candidate rewrites

## Baseline

| Case | Status | Exit | Duration | Log |
|---|---|---:|---:|---|
| `open_allowlisted` | PASS | 0 | 282.5s | `docs/results/safety_transfer_closure_attempt_20260221-005503_baseline.log` |

## Candidate Proof Attempts

| Strategy | Status | Exit | Duration | Signature | Log |
|---|---|---:|---:|---|---|
| `already_closed_skip` | PASS | 0 | 0.0s | skipped: baseline theorem already closed | `docs/results/safety_transfer_closure_attempt_20260221-005503_baseline.log` |

## Failed Goal Snapshot (Latest Campaign)

| Strategy | Goal line | Goal formula |
|---|---:|---|
| (none) | - | no parsed `PROVE` goals found in logs |

## Goal Aggregates

| Goal line | Hits | Strategies | Goal formula |
|---:|---:|---|---|
| - | 0 | - | no aggregate goals parsed |

## Restore Check

- restore_status: PASS
- restore_proofs_status: PASS
- source_sha256_before: `6776097c852b75610bae65a559da37f38a142977e2d04f447f96be2d7701f9af`
- source_sha256_after: `6776097c852b75610bae65a559da37f38a142977e2d04f447f96be2d7701f9af`
- note: source file is restored to original content after all attempts.
