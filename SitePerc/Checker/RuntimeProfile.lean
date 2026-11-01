import SitePerc.Checker.DirectDefs

/-! Bounded synthetic cost observations, not certificate acceptance.
The driver uses the actual n=36/b=20/group=8 functions and full loops.
It deliberately avoids all C7 enumeration and all original input changes. -/
namespace SitePerc.Checker.RuntimeProfile

private def line (label : String) (count start checksum : Nat) : IO Unit := do
  let finish ← IO.monoMsNow
  IO.println s!"COST_PROFILE phase={label} count={count} elapsed_ms={finish-start} checksum={checksum}"
  (← IO.getStdout).flush

def run (args : List String) : IO UInt32 := do
  let count := ((args[0]?).bind String.toNat?).getD 16384
  if count == 0 then throw (IO.userError "profile count must be positive")
  let n := 36
  let b := 20
  let perms := regionalPerms 6
  let cs := Array.replicate (n+1) (2^n)
  let stressKey := packR10 ((List.range b).map (·+1))
  let p : StageParams := ⟨1,5001,10000,0,117,200,2^100⟩
  let ws := regionalMassWeights n p
  let nu := numerator cs ws.qw
  let mu := numerator cs ws.pw
  let row : RegionalNode := ⟨stressKey,(p.scale*nu+ws.qD-1)/ws.qD,p.scale*mu/ws.pD,0⟩
  let table : CountMap := ({} : CountMap).insert stressKey cs
  let rows := Array.replicate count row
  let keys := Array.replicate count stressKey
  let arcs := Array.ofFn fun i : Fin count =>
    (⟨i.val,(i.val+1)%count,i.val%perms.size,0,2^126⟩ : RegionalArc)
  let nodeBytes : ByteArray := ⟨Array.ofFn fun i : Fin (32+64*count) => UInt8.ofNat (i.val%251)⟩
  let arcBytes : ByteArray := ⟨Array.ofFn fun i : Fin (16+32*count) => UInt8.ofNat (i.val%251)⟩
  let uniqueKeys := (List.range count).map (fun i => 2^90+i)
  let fixture := (List.range count).foldl (fun m i => m.insert (2^90+i) cs) ({} : CountMap)
  let maps := Array.replicate 4 fixture

  let t ← IO.monoMsNow
  let parsedNodes := Array.ofFn fun i : Fin count => regionalNodeAt nodeBytes i.val
  let checksum := parsedNodes.foldl (fun z r => z+r.key+r.supply+r.capacity+r.absorbed) 0
  line "parse_nodes" count t checksum

  let t ← IO.monoMsNow
  let parsedArcs := Array.ofFn fun i : Fin count => regionalArcAt arcBytes i.val
  let checksum := parsedArcs.foldl (fun z r => z+r.src+r.dst+r.perm+r.reserved+r.flow) 0
  line "parse_arcs" count t checksum

  let t ← IO.monoMsNow
  let checked := rows.map (regionalNodeGuardWithWeights n b perms p table table ws)
  let passed := checked.foldl (fun z yes => z+if yes then 1 else 0) 0
  line "node_guard_full" count t passed
  if passed != count then throw (IO.userError "synthetic node fixture failed its full actual guard")

  let t ← IO.monoMsNow
  let checked := arcs.map (regionalArcGuard count b perms keys)
  let passed := checked.foldl (fun z yes => z+if yes then 1 else 0) 0
  line "arc_guard_full" count t passed
  if passed != count then throw (IO.userError "synthetic arc fixture failed its full actual guard")

  let t ← IO.monoMsNow
  let scanned := regionalKeysScan uniqueKeys {}
  let scanSize := (scanned.map (·.size)).getD 0
  line "unique_key_scan" count t scanSize
  if scanSize != count then throw (IO.userError "synthetic unique-key scan failed")

  let t ← IO.monoMsNow
  let initial := Array.replicate count (0 : Int)
  let replayed := replayBalance initial (arcs.map RegionalArc.toSparse)
  let zeros := replayed.foldl (fun z value => z+if value == 0 then 1 else 0) 0
  line "sparse_replay" count t zeros
  if zeros != count then throw (IO.userError "synthetic cyclic replay failed")

  let t ← IO.monoMsNow
  let merged := mergeCountMaps n maps
  let checksum := merged.fold (fun z _ values => z+values.foldl (·+·) 0) 0
  line "merge_four_maps" (4*count) t checksum
  if merged.size != count then throw (IO.userError "synthetic merge size failed")
  IO.println s!"COST_PROFILE_DONE n={n} b={b} group={perms.size} count={count} enumerated_masks=0 synthetic=true"
  return 0

end SitePerc.Checker.RuntimeProfile
