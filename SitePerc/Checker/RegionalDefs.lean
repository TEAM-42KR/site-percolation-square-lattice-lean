import SitePerc.Checker.NativeDefs
import SitePerc.Checker.SparseFlowDefs
import SitePerc.Checker.ParallelDefs

namespace SitePerc.Checker

/-- Memory-bounded cache; resetting a cache cannot change any law count. -/
def enumerateBoundedCached (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) (cacheCap : Nat) : Nat → Nat → CountMap → KeyCache → CountMap × KeyCache
  | 0, _, law, cache => (law,cache)
  | count+1, start, law, cache =>
    let cache := if cache.size > cacheCap then {} else cache
    let raw := rawRootKey n es boundary start
    let (key,cache) := cacheKey boundary.size ps raw cache
    enumerateBoundedCached n es boundary ps cacheCap count (start+1)
      (bump n key (openCount n start) 1 law) cache

def boundedParallelIntervals (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (workers count start cacheCap : Nat) : Array CountMap := Id.run do
  let w := max 1 workers
  let width := (count+w-1)/w
  let jobs := (List.range w).map fun i => Task.spawn (prio:=Task.Priority.dedicated) fun _ =>
    let lo := i*width
    let len := min width (count-lo)
    (enumerateBoundedCached n es b ps cacheCap len (start+lo) {} {}).1
  return (jobs.map Task.get).toArray

/-- Candidate order is part of the certificate format: swap, flip-x, flip-y. -/
def candidateVertexPerms (m : Nat) : Array (Array Nat) := Id.run do
  let mut out := #[]
  for t in [0:8] do
    let p := Array.ofFn fun v : Fin (m*m) => Id.run do
      let mut x := v.val % m
      let mut y := v.val / m
      if t/4 == 1 then
        let z := x
        x := y
        y := z
      if (t/2)%2 == 1 then x := m-1-x
      if t%2 == 1 then y := m-1-y
      return y*m+x
    out := out.push p
  return out

def edgeMember (es : List Edge) (u v : Nat) : Bool :=
  decide ((u,v) ∈ es ∨ (v,u) ∈ es)

def commonAutomorphism (m : Nat) (p : Array Nat) : Bool :=
  (p.toList.mergeSort (· ≤ ·) == List.range (m*m)) &&
    (List.range 3).all (fun mode => (gridEdges m mode).all fun (u,v) =>
      edgeMember (gridEdges m mode) p[u]! p[v]!)

def regionalVertexPerms (m : Nat) : Array (Array Nat) :=
  (candidateVertexPerms m).filter (commonAutomorphism m)

def regionalPerms (m : Nat) : Array (Array Nat) :=
  let boundary := squareBoundary m
  (regionalVertexPerms m).map fun p =>
    boundary.map fun v => boundary.toList.idxOf p[v]!

def geometryChecks (m : Nat) : Bool := Id.run do
  if !(m == 2 || m == 4 || m == 6) then return false
  let n := m*m
  let boundary := squareBoundary m
  let vp := regionalVertexPerms m
  let bp := regionalPerms m
  let perimeter := (List.range n).filter (fun v =>
    v%m == 0 || v%m == m-1 || v/m == 0 || v/m == m-1)
  if boundary.toList.mergeSort (· ≤ ·) != perimeter then return false
  if vp.isEmpty || bp.size != vp.size then return false
  if !vp.contains (List.range n).toArray then return false
  for i in [:vp.size] do
    let p := vp[i]!
    if !commonAutomorphism m p then return false
    for a in [:n] do
      for c in [:n] do
        for mode in [0:3] do
          if edgeMember (gridEdges m mode) a c !=
            edgeMember (gridEdges m mode) p[a]! p[c]! then return false
    if bp[i]!.size != boundary.size then return false
    for b in [:boundary.size] do
      if (bp[i]!)[b]! ≥ boundary.size || p[boundary[b]!]! != boundary[(bp[i]!)[b]!]! then return false
    let mut inverseFound := false
    for q in vp do
      let comp := (List.range n).toArray.map fun a => p[q[a]!]!
      if !vp.contains comp then return false
      if comp == (List.range n).toArray then inverseFound := true
    if !inverseFound then return false
  return true

def parseRegionalLaws (m : Nat) (data : ByteArray) : Except String LawData := Id.run do
  let n := m*m
  let b := (squareBoundary m).size
  let ps := regionalPerms m
  if data.size < 20 then return .error "law header truncated"
  if natLE data 0 4 != n || natLE data 4 4 != b || natLE data 8 4 != 3 then
    return .error "law header geometry mismatch"
  let rows := natLE data 12 8
  let rowBytes := 16+3*(n+1)*8
  if rows == 0 || data.size != 20+rows*rowBytes then return .error "law length mismatch"
  let mut cols : Array CountMap := #[{},{},{}]
  let mut previous := 0
  for r in [0:rows] do
    let off := 20+r*rowBytes
    let key := natLE data off 16
    if r > 0 && key ≤ previous then return .error s!"law key order at {r}"
    if !validCanonical b ps key then return .error s!"law invalid state at {r}"
    previous := key
    for g in [0:3] do
      let mut cs := Array.replicate (n+1) 0
      let mut nonzero := false
      for k in [0:n+1] do
        let c := natLE data (off+16+(g*(n+1)+k)*8) 8
        if c > 2^n then return .error s!"law coefficient bound at {r}/{g}/{k}"
        if c != 0 then nonzero := true
        cs := cs.set! k c
      if nonzero then cols := cols.modify g (fun c => c.insert key cs)
  return .ok ⟨n,b,3,rows,cols⟩

structure RegionalNode where
  key : Nat
  supply : Nat
  capacity : Nat
  absorbed : Nat
  deriving Inhabited

structure RegionalArc where
  src : Nat
  dst : Nat
  perm : Nat
  reserved : Nat
  flow : Nat
  deriving Inhabited

def regionalNodeAt (nodes : ByteArray) (i : Nat) : RegionalNode :=
  let off := 32+64*i
  ⟨natLE nodes off 16, natLE nodes (off+16) 16,
    natLE nodes (off+32) 16, natLE nodes (off+48) 16⟩

def regionalArcAt (edges : ByteArray) (j : Nat) : RegionalArc :=
  let off := 16+32*j
  ⟨natLE edges off 4, natLE edges (off+4) 4,
    natLE edges (off+8) 4, natLE edges (off+12) 4,
    natLE edges (off+16) 16⟩

def regionalKeysScan : List Nat → Std.HashMap Nat Unit → Option (Std.HashMap Nat Unit)
  | [], seen => some seen
  | key::keys, seen =>
    if seen.contains key then none
    else regionalKeysScan keys (seen.insert key ())

structure RegionalMassWeights where
  qw : Array Nat
  pw : Array Nat
  qD : Nat
  pD : Nat

def regionalMassWeights (n : Nat) (p : StageParams) : RegionalMassWeights :=
  ⟨weights n p.qnum p.qden, weights n p.pnum p.pden, p.qden^n, p.pden^n⟩

def regionalNodeGuardWithWeights (n b : Nat) (perms : Array (Array Nat))
    (p : StageParams) (ref tar : CountMap) (w : RegionalMassWeights)
    (row : RegionalNode) : Bool :=
  let nu := numerator (ref.getD row.key (Array.replicate (n+1) 0)) w.qw
  let mu := numerator (tar.getD row.key (Array.replicate (n+1) 0)) w.pw
  validCanonical b perms row.key &&
    decide (row.supply < 2^127) && decide (row.capacity < 2^127) &&
    decide (row.absorbed < 2^127) && decide (row.absorbed ≤ row.capacity) &&
    (row.supply == if row.key == 0 then 0 else (p.scale*nu+w.qD-1)/w.qD) &&
    (row.capacity == p.scale*mu/w.pD)

/-- Proof-facing row predicate, definitionally equal to the actual precomputed
weight predicate used by the executable. -/
def regionalNodeGuard (n b : Nat) (perms : Array (Array Nat))
    (p : StageParams) (ref tar : CountMap) (row : RegionalNode) : Bool :=
  regionalNodeGuardWithWeights n b perms p ref tar (regionalMassWeights n p) row

def regionalArcGuard (M b : Nat) (perms : Array (Array Nat))
    (keys : Array Nat) (arc : RegionalArc) : Bool :=
  decide (arc.src < M) && decide (arc.dst < M) &&
    decide (arc.perm < perms.size) && (arc.reserved == 0) &&
    decide (0 < arc.flow) && decide (arc.flow < 2^127) &&
    keyLE b keys[arc.src]! (moveKey b perms[arc.perm]! keys[arc.dst]!)

def RegionalArc.toSparse (arc : RegionalArc) : SparseArc :=
  (arc.src, arc.dst, (arc.flow : Int))

def checkRegionalFlow (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) : Except String FlowReceipt := Id.run do
  let n := m*m
  if !geometryChecks m || laws.n != n || laws.b != (squareBoundary m).size || laws.graphs != 3 || laws.columns.size != 3 then
    return .error "geometry or law metadata"
  let b := (squareBoundary m).size
  let perms := regionalPerms m
  if p.scale == 0 || p.qden == 0 || p.pden == 0 || p.qnum > p.qden || p.pnum > p.pden then
    return .error "invalid exact parameters"
  if p.refcol ≥ laws.columns.size || p.tarcol ≥ laws.columns.size then return .error "column bounds"
  if nodes.size < 32 || !binaryMagic nodes 0 "R10ANODE" || natLE nodes 8 4 != n || natLE nodes 12 4 != b then
    return .error "node header"
  let M := natLE nodes 16 8
  if M == 0 || nodes.size != 32+64*M || natLE nodes 24 4 != p.refcol || natLE nodes 28 4 != p.tarcol then
    return .error "node shape or columns"
  if edges.size < 16 || !binaryMagic edges 0 "R10AEDGE" then return .error "edge header"
  let E := natLE edges 8 8
  if edges.size != 16+32*E then return .error "edge length"
  let ref := laws.columns[p.refcol]!
  let tar := laws.columns[p.tarcol]!
  let rows := Array.ofFn fun i : Fin M => regionalNodeAt nodes i.val
  let keys := rows.map RegionalNode.key
  let w := regionalMassWeights n p
  if !reflectedArrayAll rows (regionalNodeGuardWithWeights n b perms p ref tar w) then
    return .error "C1/C4/C5 nodes"
  if keys[0]! != 0 then return .error "C1 bottom index"
  let some seen := regionalKeysScan keys.toList {} |
    return .error "C1 duplicate key"
  if !ref.toList.all (fun kv => seen.contains kv.1) then
    return .error "C6 missing source"
  let rawArcs := Array.ofFn fun j : Fin E => regionalArcAt edges j.val
  if !reflectedArrayAll rawArcs (regionalArcGuard M b perms keys) then
    return .error "C2 edges"
  let arcs := rawArcs.map RegionalArc.toSparse
  let initial := rows.map (fun row => (row.supply : Int) - (row.absorbed : Int))
  if !(replayBalance initial arcs).all (· == 0) then
    return .error "C3 conservation"
  return .ok ⟨M,E,
    (rows.toList.map RegionalNode.supply).sum,
    (rows.toList.map RegionalNode.absorbed).sum⟩

end SitePerc.Checker
