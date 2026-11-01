# L2-B persisted C7 shard harness interface

## Required A contract (published before implementation)

A shard identity needs `m`, `mode`, contiguous outer-boundary `start,count` (stride 1), and the actual `enumerateBoundaryCubes m mode start count` semantics. B will materialize its entire CountMap, including zero entries if present, as canonical sorted `(key, Array Nat)` literals; this must preserve every coefficient and shape/support, not totals alone.

B needs a computable Boolean checker for a materialized pure CountMap against that actual shard function, with a standard-axiom soundness theorem giving the per-shard exact relation used by A's disjoint partition/merge theorem. The checker must compare complete maps extensionally (all stored keys plus missing-key zero semantics) and validate shape. The concrete `by native_decide` theorem lives once per shard in a separately compiled module; consumers import its theorem and pure data without rerunning C7.

Consumed published A contract: `regionalShardPass m mode shards index stored = true`, with `boundaryShardStart` / `boundaryShardCount`, complete HashMap extensional BEq, and `ShardFamily` / `ShardReceipts`. Concrete per-piece modules contain only literal `Std.HashMap.ofList` data plus an independently compiled `checked` native theorem. B never edits A-owned source. Executable CLI, C phase/log map, restart and distributed merge commands are in `checker/sharded/USAGE.md`.

## Distribution / restart design

- Immutable source/pin manifest includes Lean and Mathlib identity, transitive safe source hashes, generator/checker source hashes, and A contract hashes.
- Independent worker directories own disjoint region IDs. No shared mutable producer database is needed.
- Each verified shard record binds region identity, data JSON, literal Lean source, theorem name/type digest, compiler/axiom receipt, and every persisted build artifact SHA256.
- Restart verifies all hashes and import receipts, then skips completed shard evaluation and compilation. Incomplete or changed records are rejected, not implicitly trusted.
- Merge validates source/pin agreement and disjoint exact coverage, stages saved compiled imports, and uses A's standard-axiom merge theorem. Missing/duplicate/overlapping pieces cannot become a full witness.
- Concrete native theorem trust is explicit and separate from A's standard-three-axiom generic proofs. Hash checks are integrity bindings, not mathematical proofs or a substitute for the native theorem.

