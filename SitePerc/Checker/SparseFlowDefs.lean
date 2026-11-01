import Init.Data.Array.Basic

/-!
# Pure sparse-flow replay execution

This module contains only the executable sparse arc type and replay updates.
The conservation proofs and semantic adapters live in the proof module.
-/

namespace SitePerc.Checker

/-- Source, destination, and exact integer flow. -/
abbrev SparseArc := Nat × Nat × Int

/-- Apply one arc: subtract at the source, then add at the destination.
The order includes self-loops without a special case. -/
def replayArc (balance : Array Int) (arc : SparseArc) : Array Int :=
  (balance.modify arc.1 (fun z => z - arc.2.2)).modify arc.2.1
    (fun z => z + arc.2.2)

/-- The executable sparse replay.  Only the balance array is mutated; the
arc array is traversed in its given order. -/
def replayBalance (initial : Array Int) (arcs : Array SparseArc) : Array Int :=
  arcs.foldl replayArc initial

end SitePerc.Checker
