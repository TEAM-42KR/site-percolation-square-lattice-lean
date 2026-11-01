import Batteries.Data.UnionFind

namespace SitePerc.Checker
open Batteries
abbrev Edge := Nat × Nat

def initUF : Nat → UnionFind
  | 0 => .empty
  | n+1 => (initUF n).push

def merge (u : UnionFind) (a b : Nat) : UnionFind :=
  if h : a < u.size ∧ b < u.size then u.union ⟨a,h.1⟩ ⟨b,h.2⟩ else u

def components (n : Nat) (es : List Edge) (ω : Nat → Bool) : UnionFind :=
  match es with
  | [] => initUF n
  | (a,b)::rest =>
      let u := components n rest ω
      if ω a && ω b then merge u a b else u

def BoundedEdges (n : Nat) (es : List Edge) : Prop :=
  ∀ e ∈ es, e.1 < n ∧ e.2 < n


end SitePerc.Checker
