import SitePerc.Checker.RegionalDefs

/-! A semantic refinement of full mask enumeration.

Boundary bits are fixed first. A remaining Boolean subcube may be collapsed
only when its lower and upper *unquotiented normalized* boundary partitions
are equal. Equality of canonical orbit keys alone is deliberately insufficient.
No foreign code or IO value is used by these pure definitions.
-/
namespace SitePerc.Checker

/-- Remaining bits are assumed distinct and absent from the base by the
proof-facing cube invariant. Their numeric sum is therefore bitwise union. -/
def freeBits : List Nat → Nat
  | [] => 0
  | v::vs => 2^v + freeBits vs

/-- Pascal's row in a pure array, computed once per free dimension. -/
def cubeBinomialRow : Nat → Array Nat
  | 0 => #[1]
  | r+1 =>
    let prev := cubeBinomialRow r
    Array.ofFn fun k : Fin (r+2) => (prev[k.val]?).getD 0 +
      if k.val = 0 then 0 else (prev[k.val-1]?).getD 0

def cubeBinomials (maxFree : Nat) : Array (Array Nat) :=
  Array.ofFn fun r : Fin (maxFree+1) => cubeBinomialRow r.val

/-- A shift of exact precomputed binomial coefficients, in one map update. -/
def bumpCube (rows : Array (Array Nat)) (n key baseOpen free : Nat) (law : CountMap) : CountMap :=
  let old := law.getD key (Array.replicate (n+1) 0)
  let next := Array.ofFn fun k : Fin (n+1) =>
    old[k.val]! + if baseOpen ≤ k.val then (rows[free]![k.val-baseOpen]?).getD 0 else 0
  law.insert key next

/-- Reference decision tree, with the exact supplied variable order. -/
def cubeReference (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) : List Nat → Nat → Nat → CountMap → CountMap
  | [], base, k, law => bump n (configurationKey n es boundary ps base) k 1 law
  | v::vs, base, k, law =>
      let law := cubeReference n es boundary ps vs base k law
      cubeReference n es boundary ps vs (base+2^v) (k+1) law

structure CubeStats where
  visited : Nat := 0
  collapsed : Nat := 0
  represented : Nat := 0

instance cubeStatsInhabited : Inhabited CubeStats := ⟨{}⟩

/-- Both endpoint observations are carried down the tree: a child reuses
one endpoint, computing only its newly constrained other endpoint. -/
def enumerateCube (rows : Array (Array Nat)) (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) : List Nat → Nat → Nat → List Nat → List Nat →
      CountMap → CubeStats → CountMap × CubeStats
  | vs, base, k, lo, hi, law, st =>
    if lo == hi then
      let key := configurationKey n es boundary ps base
      (bumpCube rows n key k vs.length law,
        ⟨st.visited+1,st.collapsed+1,st.represented+2^vs.length⟩)
    else
      match vs with
      | [] =>
          (bump n (configurationKey n es boundary ps base) k 1 law,
            ⟨st.visited+1,st.collapsed,st.represented+1⟩)
      | v::vs =>
          let closedHi := normalize (rootLabels n es boundary (base+freeBits vs))
          let openLo := normalize (rootLabels n es boundary (base+2^v))
          let (law,st) := enumerateCube rows n es boundary ps vs base k lo closedHi law
            ⟨st.visited+1,st.collapsed,st.represented⟩
          enumerateCube rows n es boundary ps vs (base+2^v) (k+1) openLo hi law st

/-- Memoized implementation of the same endpoint-pruning recursion.
`rawLo` is exactly the original radix-64 raw key at `base`; hence cache keys
have the original meaning, not an unproved hash-based partition meaning. -/
def enumerateCubeMemo (rows : Array (Array Nat)) (n : Nat) (es : List Edge)
    (boundary : Array Nat) (ps : Array (Array Nat)) (cacheCap : Nat) :
    List Nat → Nat → Nat → Nat → List Nat → List Nat →
    CountMap → KeyCache → CubeStats → CountMap × KeyCache × CubeStats
  | vs, base, k, rawLo, lo, hi, law, cache, st =>
    if lo == hi then
      let cache := if cache.size > cacheCap then {} else cache
      let (key,cache) := cacheKey boundary.size ps rawLo cache
      (bumpCube rows n key k vs.length law, cache,
        ⟨st.visited+1,st.collapsed+1,st.represented+2^vs.length⟩)
    else
      match vs with
      | [] =>
          (bump n (configurationKey n es boundary ps base) k 1 law, cache,
            ⟨st.visited+1,st.collapsed,st.represented+1⟩)
      | v::vs =>
          let closedHi := normalize (rootLabels n es boundary (base+freeBits vs))
          let openLabels := rootLabels n es boundary (base+2^v)
          let openRaw := packBase 64 openLabels
          let openLo := normalize openLabels
          let (law,cache,st) := enumerateCubeMemo rows n es boundary ps cacheCap
            vs base k rawLo lo closedHi law cache
            ⟨st.visited+1,st.collapsed,st.represented⟩
          enumerateCubeMemo rows n es boundary ps cacheCap
            vs (base+2^v) (k+1) openRaw openLo hi law cache st

/-- Actual interior indices, keeping row-major order. -/
def interiorVertices (m : Nat) : List Nat :=
  (List.range (m*m)).filter fun v => !(squareBoundary m).contains v

/-- Build a boundary configuration using the exact boundary order. -/
def embedBoundary (boundary : Array Nat) (mask : Nat) : Nat :=
  (List.range boundary.size).foldl
    (fun base i => if mask.testBit i then base+2^boundary[i]! else base) 0

/-- Explicit tail loop makes the cache/accumulator invariant visible to the
kernel while retaining the same exact closed/open cube traversal. -/
def boundaryCubesLoop (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) (vs : List Nat) (rows : Array (Array Nat)) (stride : Nat) :
    Nat → Nat → CountMap → KeyCache → CubeStats → CountMap × KeyCache × CubeStats
  | 0, _, law, cache, st => (law,cache,st)
  | count+1, start, law, cache, st =>
    let bm := start % (2^boundary.size)
    let base := embedBoundary boundary bm
    let k := openCount boundary.size bm
    let loLabels := rootLabels n es boundary base
    let lo := normalize loLabels
    let hi := normalize (rootLabels n es boundary (base+freeBits vs))
    let (law,cache,st) := enumerateCubeMemo rows n es boundary ps 1000000
      vs base k (packBase 64 loLabels) lo hi law cache st
    boundaryCubesLoop n es boundary ps vs rows stride count (start+stride) law cache st

def enumerateBoundaryCubes (m mode start count : Nat) (stride : Nat := 1) : CountMap × CubeStats :=
  let vs := interiorVertices m
  let res := boundaryCubesLoop (m*m) (gridEdges m mode) (squareBoundary m)
    (regionalPerms m) vs (cubeBinomials vs.length) stride count start {} {} {}
  (res.1,res.2.2)

/-- Disjoint outer-boundary task ranges; count is boundary assignments, not
configuration count. A nonunit stride is only used by measured pilots. -/
def prunedParallel (m mode workers count start : Nat) (stride : Nat := 1) :
    Array (CountMap × CubeStats) := Id.run do
  let w := max 1 workers
  let width := (count+w-1)/w
  let jobs := (List.range w).map fun i => Task.spawn (prio:=Task.Priority.dedicated) fun _ =>
    let lo := i*width
    let len := min width (count-lo)
    enumerateBoundaryCubes m mode (start+lo*stride) len stride
  return (jobs.map Task.get).toArray

end SitePerc.Checker
