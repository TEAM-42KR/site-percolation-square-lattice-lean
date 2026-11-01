import SitePerc.Checker.RuntimeProfile

open SitePerc.Checker

def argNat (args : List String) (i fallback : Nat) : Nat :=
  ((args[i]?).bind String.toNat?).getD fallback

def writeMap (path : System.FilePath) (law : CountMap) : IO Unit :=
  IO.FS.withFile path .write fun h => do
    let rows := law.toList.mergeSort (fun a b => a.1 ≤ b.1)
    for (key,cs) in rows do
      h.putStrLn (String.intercalate "," ((toString key)::cs.toList.map toString))

def ordinaryEnum (args : List String) : IO UInt32 := do
  let m := argNat args 0 4
  let mode := argNat args 1 0
  let count := argNat args 2 (2^(m*m))
  let startMask := argNat args 4 0
  let workers := argNat args 5 1
  let b := squareBoundary m
  let ps := regionalPerms m
  let es := gridEdges m mode
  let start ← IO.monoMsNow
  let maps := boundedParallelIntervals (m*m) es b ps workers count startMask 1000000
  let total := maps.foldl (fun z law => z + law.fold (fun a _ cs => a + cs.foldl (·+·) 0) 0) 0
  let states := maps.foldl (fun z law => z+law.size) 0
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"ENUM m={m} mode={mode} boundary={b.size} edges={es.length} mask_start={startMask} configurations={count} workers={workers} state_rows={states} total={total} elapsed_ms={elapsed}"
  if let some (out : String) := args[3]? then
    if out != "-" then
      for i in [:maps.size] do
        writeMap (System.FilePath.mk (if workers == 1 then out else s!"{out}.{i}.csv")) maps[i]!
  return if total == count then 0 else 1

def regressionStageParams (m : Nat) (wierman : Bool) : Array StageParams :=
  if wierman then
  #[⟨1,5000000001,10000000000,0,11733349,20000000,2^100⟩,
    ⟨2,11733349,20000000,0,169873,250000,2^100⟩]
  else if m == 6 then
  #[⟨1,5001,10000,0,117,200,2^100⟩,⟨2,117,200,0,79,125,2^100⟩]
  else if m == 4 then
  #[⟨1,1,2,0,5823347,10000000,2^100⟩,⟨2,5823347,10000000,0,65185,100000,2^100⟩]
  else #[⟨1,1,2,0,586668,1000000,2^100⟩,⟨2,586668,1000000,0,679493,1000000,2^100⟩]

def certify (args : List String) (doEnum : Bool := true) (pruned : Bool := false) : IO UInt32 := do
  let m := argNat args 0 4
  let workers := argNat args 1 4
  let some path := args[2]? | throw (IO.userError "certify m workers law-file [node1 edge1 node2 edge2]")
  if !geometryChecks m then throw (IO.userError "C8 geometry failure")
  IO.println s!"C8_PASS m={m} group={(regionalPerms m).size}"
  let data ← IO.FS.readBinFile (System.FilePath.mk path)
  let t0 ← IO.monoMsNow
  let laws ← match parseRegionalLaws m data with
    | .error e => throw (IO.userError e)
    | .ok d => pure d
  IO.println s!"PARSE_PASS m={m} rows={laws.rows} bytes={data.size} elapsed_ms={(← IO.monoMsNow)-t0}"
  if doEnum then
    for mode in [0:3] do
      IO.println s!"C7_START m={m} mode={mode} workers={workers} masks={2^(m*m)}"
      (← IO.getStdout).flush
      let t ← IO.monoMsNow
      let maps := if pruned then
        (prunedParallel m mode workers (2^(squareBoundary m).size) 0).map Prod.fst
        else boundedParallelIntervals (m*m) (gridEdges m mode) (squareBoundary m)
          (regionalPerms m) workers (2^(m*m)) 0 1000000
      let total := maps.foldl (fun z law => z + law.fold (fun a _ cs => a + cs.foldl (·+·) 0) 0) 0
      IO.println s!"C7_ENUM_DONE mode={mode} total={total} rows={maps.foldl (fun z law => z+law.size) 0} elapsed_ms={(← IO.monoMsNow)-t}"
      (← IO.getStdout).flush
      let pass := compareCounts (m*m) maps laws.columns[mode]!
      IO.println s!"C7_COLUMN_PASS m={m} mode={mode} pass={pass} total={total} expected={2^(m*m)} elapsed_ms={(← IO.monoMsNow)-t}"
      (← IO.getStdout).flush
      if !pass || total != 2^(m*m) then return 2
    IO.println s!"C7_ALL_PASS m={m}"
  else IO.println "C7_NOT_CHECKED_THIS_PHASE"
  if args.length ≥ 7 then
    let params := regressionStageParams m (args[7]? == some "wierman1995")
    for stage in [0:2] do
      let nodes ← IO.FS.readBinFile (System.FilePath.mk args[3+2*stage]!)
      let edges ← IO.FS.readBinFile (System.FilePath.mk args[4+2*stage]!)
      let t ← IO.monoMsNow
      match checkRegionalFlow m laws params[stage]! nodes edges with
      | .error e =>
        IO.println s!"FLOW_FAIL stage={stage+1} error={e}"
        return 3
      | .ok r =>
        IO.println s!"C1_C6_FLOW_PASS stage={stage+1} nodes={r.nodes} edges={r.edges} supply={r.supply} absorption={r.absorption} elapsed_ms={(← IO.monoMsNow)-t}"
  return 0

def directCertify (args : List String) : IO UInt32 := do
  let m := argNat args 0 4
  let workers := argNat args 1 4
  if args.length < 6 then throw (IO.userError "direct m workers node1 edge1 node2 edge2 [wierman1995]")
  let ns1 ← IO.FS.readBinFile (System.FilePath.mk args[2]!)
  let es1 ← IO.FS.readBinFile (System.FilePath.mk args[3]!)
  let ns2 ← IO.FS.readBinFile (System.FilePath.mk args[4]!)
  let es2 ← IO.FS.readBinFile (System.FilePath.mk args[5]!)
  let ps := regressionStageParams m (args[6]? == some "wierman1995")
  let t ← IO.monoMsNow
  match directRegionalCheck m workers ps[0]! ps[1]! ns1 es1 ns2 es2 with
  | .error e =>
    IO.println s!"DIRECT_FAIL m={m} error={e}"
    return 3
  | .ok (one,two) =>
    IO.println s!"DIRECT_C7_C1_C6_PASS m={m} workers={workers} stage1_nodes={one.nodes} stage1_edges={one.edges} stage1_supply={one.supply} stage1_absorption={one.absorption} stage2_nodes={two.nodes} stage2_edges={two.edges} stage2_supply={two.supply} stage2_absorption={two.absorption} elapsed_ms={(← IO.monoMsNow)-t}"
    return 0

def prunedPilot (args : List String) : IO UInt32 := do
  let m := argNat args 0 6
  let mode := argNat args 1 0
  let count := argNat args 2 192
  let workers := argNat args 3 192
  let start := argNat args 4 373313
  let stride := argNat args 5 65537
  let t ← IO.monoMsNow
  let jobs := prunedParallel m mode workers count start stride
  let visited := jobs.foldl (fun z x => z+x.2.visited) 0
  let collapsed := jobs.foldl (fun z x => z+x.2.collapsed) 0
  let represented := jobs.foldl (fun z x => z+x.2.represented) 0
  let maps := jobs.map Prod.fst
  let total := maps.foldl (fun z law => z + law.fold (fun a _ cs => a+cs.foldl (·+·) 0) 0) 0
  IO.println s!"PRUNED_PILOT m={m} mode={mode} boundary_assignments={count} workers={workers} start={start} stride={stride} visited={visited} collapsed={collapsed} represented={represented} total={total} state_rows={maps.foldl (fun z law => z+law.size) 0} elapsed_ms={(← IO.monoMsNow)-t}"
  return if total == count*2^(interiorVertices m).length && total == represented then 0 else 1

def main (args : List String) : IO UInt32 := do
  try
    if args.head? == some "profile-runtime" then SitePerc.Checker.RuntimeProfile.run args.tail!
    else if args.head? == some "direct" then directCertify args.tail!
    else if args.head? == some "prune-pilot" then prunedPilot args.tail!
    else if args.head? == some "pruned" then certify args.tail! true true
    else if args.head? == some "certify" then certify args.tail!
    else if args.head? == some "flow" then certify args.tail! false
    else ordinaryEnum args
  catch e =>
    IO.eprintln s!"CHECKER_ERROR {e}"
    return 10
