# Restartable C7 shard CLI

All commands run from the Lean project root. Python standard library only.
The current generator is `checker/sharded/shards.py`; the runtime contract is
`INTERFACE_L2_A.md`. The commands below leave the safe Lean source unchanged.
`--shards` is arbitrary (A uses `max 1 shards`), not fixed to the examples.

## C: native producer kit and phase-separated per-piece profile

```sh
ROOT="$(pwd)"  # run from the Lean project root
cd "$ROOT"
OUT=/absolute/isolated/worker
mkdir -p "$OUT"
python3 checker/sharded/shards.py snapshot --out "$OUT/snapshot.json" > "$OUT/snapshot.stdout.json"
python3 checker/sharded/shards.py prepare --snapshot "$OUT/snapshot.json" --out "$OUT" --timeout 120 > "$OUT/prepare.stdout.json"
python3 checker/sharded/shards.py produce --snapshot "$OUT/snapshot.json" --out "$OUT" --m 6 --shards 8192 --mode 0 --index 0 --timeout 600 > "$OUT/piece.stdout.json"
```

Change `--mode` and `--index` for each actual representative boundary region.
Do not change the source/harness during a snapshot's run. The producer is a
native executable at `$OUT/kit/producer`; `KIT.json` binds compiler, binary,
C output and all actual runtime object hashes. Its CLI is:

```sh
"$OUT/kit/producer" 6 0 8192 0 /absolute/profile/raw.json
```

That direct invocation only produces data and does NOT certify a shard.
The `produce` command independently calls `regionalShardPass` on pure stored
literals with `by native_decide`; only its complete `manifest.json` is reusable.
A fresh piece computes actual C7 twice overall: once in production, once in the
independent native checker. Both costs must appear in a whole-campaign estimate.

For a complete piece `$OUT/pieces/m6_s8192_mode0_i0/`:
- `logs/producer.log`: actual C7 evaluation BEGIN/END nanosecond interval,
  serialization interval and row count. Producer phase includes file IO.
- `logs/data_compile.log.json`: pure literal elaboration/artifact generation.
- `logs/check_compile.log.json`: independent native evaluation/proof compilation.
- `logs/check_compile.log`: exact native axiom audit.
- Each phase records argv, rc, wall/user/sys times. The current rusage RSS field
  is explicitly a cumulative child high-water, NOT an isolated phase peak;
  C's own process/cgroup/GNU-time measurement is needed for phase RSS.
- `build/` contains saved data and checked `.olean`/`.ilean`/C and any companion
  artifacts produced by the pinned compiler. `manifest.json` hashes all of them.
- Initial native producer compile and link are separate in `$OUT/kit/`.

The generator is deliberately one core per job. Distributed workers run separate
output directories; no mutable shared queue or producer database is required.
A campaign coordinator may assign several disjoint region IDs to one worker.

## Restart: validate and import, never recompute completed pieces

Run the identical `produce` command again. A complete piece first passes all
source/pin/data/theorem/artifact hashes and a fresh theorem import/type/axiom
audit, then returns `REUSED` with producer=0, native-checker=0, shard-compilations=0.
The import audit is a tiny new module containing no `native_decide` or enumerator.
Missing or altered files reject rather than silently triggering recertification.
An interrupted, not-yet-verified job can be regenerated; only complete manifests
are candidate inputs to merge.

Driver-only repairs can explicitly adopt an earlier snapshot without recomputing
its verified pieces:

```sh
python3 checker/sharded/shards.py snapshot --out /absolute/new-snapshot.json --adopt /absolute/old-snapshot.json
```

Adoption requires an IDENTICAL runtime source/pin ID. It binds the old snapshot
file hash and its original generator hashes in the new snapshot; it never
admits a different runtime pin, edits an old manifest, or silently disables the
hash gate. Existing pieces still pass their original exact data/theorem/artifact
bindings and a fresh import. Source/data expressions for small completed pieces
remain byte-identical. Newly compiled large literals use bounded 128-row blocks
and a pure flatten, with no C7 function in the stored definition. Compilation
sets maxHeartbeats=0/maxRecDepth=20000 under the independent wall cap/one-core
constraint; unbounded compiler heartbeats are not an unbounded execution permit.

Explicit validation with a fresh import audit:

```sh
python3 checker/sharded/shards.py validate --snapshot "$OUT/snapshot.json" --piece "$OUT/pieces/m6_s8192_mode0_i0" --import-audit "$OUT/audit0"
```

## Distributed merge

Copy the SAME snapshot and source/harness to each worker. Each worker may build
its own native kit; semantic source/pin/snapshot IDs agree, while per-worker
compiler/binary/artifact hashes stay individually recorded. Transfer completed
piece directories losslessly; preserve directory structure under each `pieces/`.

```sh
python3 checker/sharded/shards.py merge --snapshot /absolute/snapshot.json --m 6 --shards 8192 --pieces /absolute/workerA/pieces /absolute/workerB/pieces --out /absolute/merge --timeout 600
```

Full merge requires all `3 * max(1, shards)` IDs exactly once. Missing pieces,
duplicate IDs, overlap, mixed partition counts or mixed snapshots are errors.
It imports the stored checked constants, proves `ShardReceipts`, then consumes
A's `shardedRegionalLaws_exact`. It does not call C7, native_decide, or a producer.
A's finalized `ShardedSoundness.lean` must already be built in the project.
Its entire SitePerc source closure is bound separately in `MERGE.json` so that
proof-only changes do not invalidate completed runtime pieces.

`--receipts-only` is an explicit interim mode: it produces RECEIPTS_ONLY, not an
ExactRegionalLaws/full-campaign witness. Never present that mode as a full proof.
A separate final flow native witness must consume the merged stored data and the
actual four pure ByteArrays. The full6 witness is not supplied by small tests.

## Trust and integrity boundary

The source/pin ID binds exact runtime Lean sources, toolchain/git identity,
Lake lock/config and exact external package revisions/local edits. The snapshot
also binds the generator/producer files. Each piece binds its literal data,
region, theorem name/type, audit and every build output. Hashes detect loss and
mutation against the selected snapshot/manifest; they are not signatures and do
not authenticate an adversary who can replace the trusted snapshot and every
receipt together. Keep the snapshot/manifest digest in the coordinator's ledger.
Native concrete proofs retain one disclosed native axiom per piece. A's generic
partition/semantic proofs are audited separately for standard-three axioms only;
the imported concrete exact-laws theorem inherits its pieces' native axioms.
