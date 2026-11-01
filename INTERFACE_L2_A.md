# L2-A persisted C7 shard interface

Namespace `SitePerc.Checker`. New pure runtime module `SitePerc.Checker.ShardedDefs`; standard-three-axiom proof module `SitePerc.Checker.ShardedSoundness`. The generic source build and all seven standard-three-axiom audits have passed. This is not a claim that the full 6x6 computation has succeeded.

## Frozen partition and independent native obligations

- `boundaryShardTotal m := 2^(squareBoundary m).size`.
- `boundaryShardWorkers shards := max 1 shards`.
- `boundaryShardWidth m shards := (boundaryShardTotal m + boundaryShardWorkers shards - 1) / boundaryShardWorkers shards`.
- Shard `i < boundaryShardWorkers shards` owns exactly the boundary assignments `i*width + j` for `j < min width (boundaryShardTotal m - i*width)`. Empty trailing shards are allowed and remain explicit obligations. Stride is exactly one.
- `regionalShard (m mode shards i : Nat) : CountMap := (enumerateBoundaryCubes m mode (i*width) (min width (boundaryShardTotal m-i*width))).1`.
- `regionalShardPass (m mode shards i : Nat) (stored : CountMap) : Bool := decide (mode < 3 ∧ i < boundaryShardWorkers shards) && (stored == regionalShard m mode shards i)`.

`==` here is Std HashMap's extensional BEq. Its standard-axiom soundness gives `stored ~m actual`, including equal lookup Options and therefore exact stored-key support, every row and its length, and every key/open-count coefficient. It is not an aggregate-total test and not an unchecked producer assertion.

Each shard module must contain a PURE stored `CountMap` (for example `Std.HashMap.ofList [(key, #[...]), ...]`) and export a theorem of the exact form:

```lean
theorem checked : regionalShardPass m mode shards i stored = true := by native_decide
```

A module must bind the exact m/mode/shards/i/source/pin/data identity in its manifest. Native compilation is disclosed separately: it is NOT a standard-three proof and is not a kernel-only proof. Resumption imports the already compiled data/checked module; it does not re-run `regionalShardPass` or `regionalShard` on completed pieces. Checking a fresh shard evaluates its actual Lean producer once. No axiom/opaque declaration or external table PASS may replace `checked`.

## Final import/merge API

```lean
abbrev ShardFamily (shards : Nat) :=
  Fin 3 → Fin (boundaryShardWorkers shards) → CountMap

def ShardReceipts (m shards : Nat) (data : ShardFamily shards) : Prop :=
  ∀ (mode : Fin 3) (i : Fin (boundaryShardWorkers shards)),
    regionalShardPass m mode.val shards i.val (data mode i) = true

shardedRegionalLaws (m shards : Nat) (data : ShardFamily shards) : LawData
shardedRegionalCheck (m shards : Nat) (data : ShardFamily shards)
  (stageOne stageTwo : StageParams)
  (nodesOne edgesOne nodesTwo edgesTwo : ByteArray) :
  Except String (FlowReceipt × FlowReceipt)
shardedRegionalPass -- same inputs, Bool success observation
```

The family can be assembled from imported arrays by `fun mode i => storedColumns[mode.val]![i.val]!`. Its receipt proof dispatches to independently imported `checked` constants. `shardedRegionalLaws` only adds stored rows; it never invokes `regionalShard` or any C7 enumerator. The two final checks invoke only the existing `checkRegionalFlow` on this merged stored data. The proof type may mention actual enumeration, but proof import does not evaluate it.

## Standard-three theorem contracts

- `boundaryShard_partition`: each boundary assignment below `boundaryShardTotal m` has a UNIQUE `(shard, local-offset)` representation in the specified clipped intervals. In particular intervals are pairwise disjoint and cover exactly the boundary domain.
- `regionalShardPass_sound`: a successful native obligation gives exact HashMap equivalence to that actual shard.
- `regionalShard_shape` and `regionalShard_coefficient`: actual shard shape and each key/k equals its explicit boundary/interior Boolean cube sum.
- `shardedRegionalLaws_exact (m : Nat) (hm : RegionalSize m) (shards : Nat) (data : ShardFamily shards) (checked : ShardReceipts m shards data) : ExactRegionalLaws m (shardedRegionalLaws m shards data)`.
- `shardedRegionalPass_boundary_stages (shards : Nat) (data : ShardFamily shards) (checked : ShardReceipts 6 shards data) (nodesOne edgesOne nodesTwo edgesTwo : ByteArray) (h : shardedRegionalPass 6 shards data verifiedStageOneParams verifiedStageTwoParams nodesOne edgesOne nodesTwo edgesTwo = true) : boundaryDominates 6 (0,0) lineLattice intermediate q0 p1 ∧ boundaryDominates 6 (3,3) intermediate square p1 p2`.

`ExactRegionalLaws` is the unchanged consumer contract: exactly three columns, shape n+1 at EVERY lookup, and exact full-mask coefficient at EVERY key and k<=m*m. Its existing support/fiber/flow semantics and both Base boundary dominations are reused, not replaced by totals or a custom notion of domination.

## Public audit evidence

The public source theorems named above are complete under the standard axioms; see `data/AXIOM_AUDIT.json` and `data/L2_SHARDED_SUPPORT.json`. The raw per-shard coefficient theorem keeps the actual runtime modulo in its formula; the unique-cover theorem restricts valid shards/offsets, where assignments lie below the boundary total and no wraparound occurs. The full coefficient-partition theorem is over every actual full mask, key and open count.
