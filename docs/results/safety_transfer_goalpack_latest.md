# Safety-Transfer Goalpack

- generated: 2026-02-21 01:04:31 +0800
- campaign_id: `20260221-005503`
- strategies: `1`

## Ranked Unproved Goals

| Rank | Goal line | Hits | Strategies | Goal formula |
|---:|---:|---:|---|---|
| 1 | - | 0 | - | no parsed goals |

## Tactic Worklist

1. Split `SpecA` proof into `InitA` and `[NextA]_varsA` components before temporal lifting.
2. Prove extensional equality lemmas for `ABSTRACT` vs `ABSTRACT_THEOREMS` operators (`InitA`, `NextA`, `varsA`, `SafetyA`).
3. Add explicit PTL bridge lemma: `[](P) /\ [](P => Q) => [](Q)` and instantiate for safety predicates.
4. Keep closure attempts in module-only mode (`TLAPS_INVARIANT=0`) to avoid unrelated invariant-module flakiness.
