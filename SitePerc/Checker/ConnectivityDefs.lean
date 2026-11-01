import SitePerc.Checker.UnionFindDefs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SitePerc.Checker
def edgeGraph (n : Nat) (es : List Edge) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => (a.val,b.val) ∈ es)

def openGraph (n : Nat) (es : List Edge) (ω : Nat → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b => (a.val,b.val) ∈ es ∧ ω a.val = true ∧ ω b.val = true)

end SitePerc.Checker
