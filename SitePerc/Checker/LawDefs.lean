import SitePerc.Checker.UnionFindDefs
import Std.Data.HashMap

namespace SitePerc.Checker

/-- First-occurrence normalization; zero is closed, never an open singleton. -/
def normalize (xs : List Nat) : List Nat :=
  let seen := (xs.filter (fun x => x != 0)).eraseDups
  xs.map fun x => if x = 0 then 0 else seen.idxOf x + 1

/-- Little-endian packing; binary R10 rows are reversed when imported. -/
def pack : List Nat → Nat
  | [] => 0
  | x::xs => x + 32 * pack xs

def unpack : Nat → Nat → List Nat
  | 0, _ => []
  | b+1, key => key % 32 :: unpack b (key / 32)

/-- R10's high-endian canonicalization; stored canonical keys have exactly
    the same numerical value as the published binary rows. -/
def packR10 (xs : List Nat) : Nat := pack xs.reverse

def permute (xs : List Nat) (p : Array Nat) : List Nat :=
  p.toList.map fun i => xs[i]!

def canonicalKey (xs : List Nat) (ps : Array (Array Nat)) : Nat :=
  ps.foldl (fun best p => min best (packR10 (normalize (permute xs p)))) (packR10 (normalize xs))

def rootLabels (n : Nat) (es : List Edge) (boundary : Array Nat) (mask : Nat) : List Nat :=
  let u := components n es mask.testBit
  boundary.toList.map fun v => if mask.testBit v then u.rootD v + 1 else 0

def packBase (base : Nat) : List Nat → Nat
  | [] => 0
  | x::xs => x + base * packBase base xs

def unpackBase (base : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | b+1, key => key % base :: unpackBase base b (key / base)

def rawRootKey (n : Nat) (es : List Edge) (boundary : Array Nat) (mask : Nat) : Nat :=
  packBase 64 (rootLabels n es boundary mask)

def keyOfRaw (b : Nat) (ps : Array (Array Nat)) (raw : Nat) : Nat :=
  canonicalKey (unpackBase 64 b raw) ps

def configurationKey (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) (mask : Nat) : Nat :=
  keyOfRaw boundary.size ps (rawRootKey n es boundary mask)

def openCount (n mask : Nat) : Nat :=
  (List.range n).foldl (fun k i => if mask.testBit i then k+1 else k) 0

abbrev CountMap := Std.HashMap Nat (Array Nat)

def bump (n key k weight : Nat) (m : CountMap) : CountMap :=
  let cs := m.getD key (Array.replicate (n+1) 0)
  m.insert key (cs.set! k (cs[k]! + weight))

/-- Tail-recursive interval enumeration. No large `List.range` is allocated. -/
def enumerateInterval (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) : Nat → Nat → CountMap → CountMap
  | 0, _, law => law
  | count+1, start, law =>
    let key := configurationKey n es boundary ps start
    enumerateInterval n es boundary ps count (start+1) (bump n key (openCount n start) 1 law)

abbrev KeyCache := Std.HashMap Nat Nat

def cacheKey (b : Nat) (ps : Array (Array Nat)) (raw : Nat) (cache : KeyCache) : Nat × KeyCache :=
  match cache[raw]? with
  | some key => (key,cache)
  | none =>
    let key := keyOfRaw b ps raw
    (key,cache.insert raw key)

def enumerateCached (n : Nat) (es : List Edge) (boundary : Array Nat)
    (ps : Array (Array Nat)) : Nat → Nat → CountMap → KeyCache → CountMap × KeyCache
  | 0, _, law, cache => (law,cache)
  | count+1, start, law, cache =>
    let raw := rawRootKey n es boundary start
    let (key,cache) := cacheKey boundary.size ps raw cache
    enumerateCached n es boundary ps count (start+1) (bump n key (openCount n start) 1 law) cache

def gridEdges (m mode : Nat) : List Edge := Id.run do
  let mut es := []
  for y in [0:m] do
    for x in [0:m] do
      let v := y*m+x
      if x+1 < m then es := (v,v+1)::es
      if y+1 < m then es := (v,v+m)::es
      if x+1 < m && y+1 < m && (x+y)%2 == 0 &&
        (mode == 1 || (mode == 2 && ((x+(if m==6 then 3 else 1))%m == m-1 ||
          (y+(if m==6 then 3 else 1))%m == m-1))) then
        es := (v,v+m+1)::es
        es := (v+1,v+m)::es
  return es

def squareBoundary (m : Nat) : Array Nat := Id.run do
  let mut b := #[]
  for x in [0:m] do b := b.push x
  for y in [1:m] do b := b.push (y*m+(m-1))
  for x in [0:m-1] do b := b.push ((m-1)*m+(m-2-x))
  for y in [0:m-2] do b := b.push ((m-2-y)*m)
  return b

def squarePerms (m : Nat) (boundary : Array Nat) : Array (Array Nat) := Id.run do
  let mut ps := #[]
  for t in [0:8] do
    let mut p := #[]
    for b in boundary do
      let mut x := b%m
      let mut y := b/m
      if t / 4 == 1 then x := m-1-x
      for _ in [0:t%4] do
        let z := x
        x := m-1-y
        y := z
      p := p.push (boundary.toList.idxOf (y*m+x))
    ps := ps.push p
  return ps

end SitePerc.Checker
