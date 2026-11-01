import SitePerc.Checker.LawDefs

/-! Pure executable data path. IO only loads bytes and prints receipts in Exec. -/
namespace SitePerc.Checker

def addCounts (n : Nat) (a b : Array Nat) : Array Nat :=
  Array.ofFn fun i : Fin (n+1) => a[i.val]! + b[i.val]!

def sumCounts (n : Nat) (maps : Array CountMap) (key : Nat) : Array Nat :=
  maps.foldl (fun a m => match m[key]? with
    | none => a
    | some cs => addCounts n a cs) (Array.replicate (n+1) 0)

def compareCounts (n : Nat) (maps : Array CountMap) (expected : CountMap) : Bool :=
  expected.toList.all (fun (key,cs) => cs == sumCounts n maps key) &&
  maps.all (fun m => m.toList.all (fun (key,_) => expected.contains key))

/-- Every mask appears in exactly one interval; the final interval is clipped. -/
def parallelIntervals (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (workers count start : Nat) : Array CountMap := Id.run do
  let w := max 1 workers
  let width := (count+w-1)/w
  let jobs := (List.range w).map fun i => Task.spawn (prio:=Task.Priority.dedicated) fun _ =>
    let lo := i*width
    let len := min width (count-lo)
    (enumerateCached n es b ps len (start+lo) {} {}).1
  return (jobs.map Task.get).toArray

/-- Total parser: integer fields are read only after a whole-record bound check. -/
def natLE (data : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldr (fun j acc => data[offset+j]!.toNat + 256*acc) 0

def binarySize (data : ByteArray) (offset width : Nat) : Bool :=
  decide (offset+width ≤ data.size)

structure LawData where
  n : Nat
  b : Nat
  graphs : Nat
  rows : Nat
  columns : Array CountMap
  deriving Inhabited

def validLabels (xs : List Nat) : Bool :=
  decide (xs.length ≤ 31) && (normalize xs == xs)

def validCanonical (b : Nat) (ps : Array (Array Nat)) (key : Nat) : Bool :=
  let xs := (unpack b key).reverse
  decide (key < 32^b) && validLabels xs && (canonicalKey xs ps == key)

/-- Strict key order forbids duplicate rows; zero rows are harmless and do not
    create artificial support in any column. -/
def parseLaws (m : Nat) (data : ByteArray) : Except String LawData := Id.run do
  let n := m*m
  let b := (squareBoundary m).size
  let ps := squarePerms m (squareBoundary m)
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

def keyLE (b src dst : Nat) : Bool := Id.run do
  let s := (unpack b src).reverse.toArray
  let t := (unpack b dst).reverse.toArray
  let mut blockMap := Array.replicate 32 0
  for i in [0:b] do
    let a := s[i]!
    let c := t[i]!
    if a != 0 then
      if c == 0 then return false
      let old := blockMap[a]!
      if old != 0 && old != c then return false
      blockMap := blockMap.set! a c
  return true

def moveKey (b : Nat) (p : Array Nat) (key : Nat) : Nat :=
  packR10 (normalize (permute (unpack b key).reverse p))

def binaryMagic (data : ByteArray) (offset : Nat) (text : String) : Bool :=
  (text.toUTF8.data.toList.zipIdx).all (fun (c,j) => data[offset+j]! == c)

def weights (n num den : Nat) : Array Nat :=
  Array.ofFn fun k : Fin (n+1) => num^k.val * (den-num)^(n-k.val)

def numerator (cs ws : Array Nat) : Nat :=
  (List.range cs.size).foldl (fun z k => z + cs[k]! * ws[k]!) 0

structure StageParams where
  refcol : Nat
  qnum : Nat
  qden : Nat
  tarcol : Nat
  pnum : Nat
  pden : Nat
  scale : Nat := 2^100
  deriving Inhabited

structure FlowReceipt where
  nodes : Nat
  edges : Nat
  supply : Nat
  absorption : Nat
  deriving Repr, Inhabited

/-- C1-C6/C8 finite replay, using arbitrary-precision Nat/Int throughout.
    C7 must have been independently proved by compareCounts and enumeration. -/
def checkFlow (m : Nat) (laws : LawData) (p : StageParams)
    (nodes edges : ByteArray) : Except String FlowReceipt := Id.run do
  let n := m*m
  let b := (squareBoundary m).size
  let perms := squarePerms m (squareBoundary m)
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
  let qw := weights n p.qnum p.qden
  let pw := weights n p.pnum p.pden
  let qD := p.qden^n
  let pD := p.pden^n
  let mut keys := Array.replicate M 0
  let mut balance : Array Int := Array.replicate M 0
  let mut seen : Std.HashMap Nat Nat := {}
  let mut sumA := 0
  let mut sumSink := 0
  for i in [0:M] do
    let off := 32+64*i
    let key := natLE nodes off 16
    if seen.contains key || !validCanonical b perms key then return .error s!"C1 node key {i}"
    let a := natLE nodes (off+16) 16
    let c := natLE nodes (off+32) 16
    let sink := natLE nodes (off+48) 16
    if a ≥ 2^127 || c ≥ 2^127 || sink ≥ 2^127 || sink > c then return .error s!"C4 node {i}"
    let nu := numerator (ref.getD key (Array.replicate (n+1) 0)) qw
    let mu := numerator (tar.getD key (Array.replicate (n+1) 0)) pw
    let expectedA := if key == 0 then 0 else (p.scale*nu+qD-1)/qD
    let expectedC := p.scale*mu/pD
    if a != expectedA || c != expectedC then return .error s!"C5 mass {i}"
    seen := seen.insert key i
    keys := keys.set! i key
    balance := balance.set! i ((a:Int)-(sink:Int))
    sumA := sumA+a
    sumSink := sumSink+sink
  for (key,_) in ref.toList do
    if !seen.contains key then return .error s!"C6 missing source {key}"
  for j in [0:E] do
    let off := 16+32*j
    let s := natLE edges off 4
    let t := natLE edges (off+4) 4
    let h := natLE edges (off+8) 4
    let reserved := natLE edges (off+12) 4
    let f := natLE edges (off+16) 16
    if s ≥ M || t ≥ M || h ≥ perms.size || reserved != 0 || f == 0 || f ≥ 2^127 then
      return .error s!"C2 edge header {j}"
    if !keyLE b keys[s]! (moveKey b perms[h]! keys[t]!) then return .error s!"C2 order {j}"
    balance := balance.modify s (fun z => z-(f:Int))
    balance := balance.modify t (fun z => z+(f:Int))
  if !balance.all (· == 0) then return .error "C3 conservation"
  return .ok ⟨M,E,sumA,sumSink⟩

end SitePerc.Checker
