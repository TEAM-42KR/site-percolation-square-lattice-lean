import Init.Data.Array.Basic

namespace SitePerc.Checker

/-- Allocation-free Boolean conjunction over an exact numeric interval. -/
def rangeAll (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | count+1, start => f start && rangeAll f count (start+1)

/-- Task partitioning changes only evaluation order. Outside the array every
padded slot is true, and each in-range slot is tested once. -/
def parallelArrayAll {α : Type} (workers : Nat) (xs : Array α)
    (predicate : α → Bool) : Bool := Id.run do
  let w := max 1 workers
  let width := (xs.size+w-1)/w
  let jobs := (List.range w).map fun i => Task.spawn (prio:=Task.Priority.dedicated) fun _ =>
    rangeAll (fun j => let idx := i*width+j
      if h : idx < xs.size then predicate xs[idx] else true) width 0
  return jobs.all Task.get

/-- Small inputs stay sequential; the predicate's exact value is unchanged. -/
def reflectedArrayAll {α : Type} (xs : Array α) (predicate : α → Bool) : Bool :=
  if xs.size < 100000 then xs.all predicate else parallelArrayAll 192 xs predicate

end SitePerc.Checker
