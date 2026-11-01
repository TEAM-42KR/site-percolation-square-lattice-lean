import SitePerc.Checker.ShardedDefs
import Init.System.IO

/-! IO transport only. Each fresh job evaluates the actual pure Lean shard.
The output is not trusted: a separate literal-data module is native-checked. -/
open SitePerc.Checker

def main (args : List String) : IO UInt32 := do
  unless args.length == 5 do
    IO.eprintln "usage: Producer m mode shards index output.json"
    return 2
  let some m := args[0]!.toNat? | throw (IO.userError "bad m")
  let some mode := args[1]!.toNat? | throw (IO.userError "bad mode")
  let some shards := args[2]!.toNat? | throw (IO.userError "bad shards")
  let some index := args[3]!.toNat? | throw (IO.userError "bad index")
  unless (m == 2 || m == 4 || m == 6) && mode < 3 && index < boundaryShardWorkers shards do
    throw (IO.userError "unsupported or out-of-range shard")
  IO.eprintln "C7_PRODUCER_EVAL_BEGIN"
  let before ← IO.monoNanosNow
  let law := regionalShard m mode shards index
  let size := law.size
  let after ← IO.monoNanosNow
  IO.eprintln s!"C7_PRODUCER_EVAL_END rows={size} elapsed_ns={after-before}"
  let rows := law.toArray.qsort (fun a b => a.1 < b.1)
  let serialized ← IO.monoNanosNow
  let h ← IO.FS.Handle.mk (System.FilePath.mk args[4]!) .write
  h.putStr ("{\"schema\":1,\"m\":" ++ toString m ++ ",\"mode\":" ++ toString mode ++
    ",\"shards\":" ++ toString shards ++ ",\"index\":" ++ toString index ++
    ",\"start\":" ++ toString (boundaryShardStart m shards index) ++
    ",\"count\":" ++ toString (boundaryShardCount m shards index) ++ ",\"rows\":[")
  for j in [:rows.size] do
    if j > 0 then h.putStr ","
    let (key,cs) := rows[j]!
    h.putStr s!"[{key},{cs.toList}]"
  h.putStrLn "]}"
  h.flush
  let done ← IO.monoNanosNow
  IO.eprintln s!"C7_PRODUCER_SERIALIZE_END elapsed_ns={done-serialized}"
  return 0
