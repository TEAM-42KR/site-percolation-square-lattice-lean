import SitePerc.Checker.DirectDefs

/-! Restartable, disjoint actual C7 work.  Only the per-shard checker calls
`enumerateBoundaryCubes`; merge and final flow checking consume saved data.
Native receipt proofs are supplied by independently compiled data modules,
not by producer assertions or an external PASS flag. -/
namespace SitePerc.Checker

def boundaryShardTotal (m : Nat) : Nat := 2^(squareBoundary m).size

def boundaryShardWorkers (shards : Nat) : Nat := max 1 shards

def boundaryShardWidth (m shards : Nat) : Nat :=
  (boundaryShardTotal m + boundaryShardWorkers shards - 1) / boundaryShardWorkers shards

def boundaryShardStart (m shards i : Nat) : Nat := i * boundaryShardWidth m shards

def boundaryShardCount (m shards i : Nat) : Nat :=
  min (boundaryShardWidth m shards) (boundaryShardTotal m - boundaryShardStart m shards i)

/-- A single actual memoized/pruned, contiguous stride-one boundary job. -/
def regionalShard (m mode shards i : Nat) : CountMap :=
  (enumerateBoundaryCubes m mode (boundaryShardStart m shards i)
    (boundaryShardCount m shards i)).1

/-- Complete map equivalence, not a comparison of totals or listed rows only.
HashMap BEq compares its entire finite support and each complete stored array. -/
def regionalShardPass (m mode shards i : Nat) (stored : CountMap) : Bool :=
  decide (mode < 3 ∧ i < boundaryShardWorkers shards) &&
    (stored == regionalShard m mode shards i)

abbrev ShardFamily (shards : Nat) :=
  Fin 3 → Fin (boundaryShardWorkers shards) → CountMap

/-- Each obligation is discharged in its own native-checked saved module. -/
def ShardReceipts (m shards : Nat) (data : ShardFamily shards) : Prop :=
  ∀ (mode : Fin 3) (i : Fin (boundaryShardWorkers shards)),
    regionalShardPass m mode.val shards i.val (data mode i) = true

/-- No enumeration occurs in this consumer. -/
def shardedRegionalColumn (m shards : Nat) (data : ShardFamily shards)
    (mode : Fin 3) : CountMap :=
  mergeCountMaps (m*m) (Array.ofFn fun i : Fin (boundaryShardWorkers shards) => data mode i)

def shardedRegionalLaws (m shards : Nat) (data : ShardFamily shards) : LawData :=
  ⟨m*m,(squareBoundary m).size,3,0,
    Array.ofFn fun mode : Fin 3 => shardedRegionalColumn m shards data mode⟩

def shardedRegionalCheck (m shards : Nat) (data : ShardFamily shards)
    (stageOne stageTwo : StageParams)
    (nodesOne edgesOne nodesTwo edgesTwo : ByteArray) :
    Except String (FlowReceipt × FlowReceipt) := do
  let laws := shardedRegionalLaws m shards data
  let one ← checkRegionalFlow m laws stageOne nodesOne edgesOne
  let two ← checkRegionalFlow m laws stageTwo nodesTwo edgesTwo
  return (one,two)

def shardedRegionalPass (m shards : Nat) (data : ShardFamily shards)
    (stageOne stageTwo : StageParams)
    (nodesOne edgesOne nodesTwo edgesTwo : ByteArray) : Bool :=
  match shardedRegionalCheck m shards data stageOne stageTwo nodesOne edgesOne nodesTwo edgesTwo with
  | .ok _ => true
  | .error _ => false

end SitePerc.Checker
