import SitePerc.Checker.PrunedDefs
import SitePercConcreteData.Wierman1995
import Lean.Elab.Tactic.Decide

/-!
# Concrete executable receipt for the Wierman two-by-two data

The optional data module is generated outside the public source tree by
`scripts/generate_concrete_data.py`, using the supplied five binary files.
The same Lake project consumes it through the `SitePercConcreteData` library.

This file asserts only an exact executable Bool result. It does not assert
semantic boundary domination or whole-checker soundness. Its native proof
uses Lean's native-decision trust boundary, made explicit by the axiom print.
No producer verdict is an input to this predicate.
-/

namespace SitePerc.Checker.ConcreteReceipt

open SitePercConcreteData.Wierman1995

/-- Exactly the first-stage rational parameters used by the checker driver. -/
def stageOneParams : StageParams :=
  ⟨1, 5000000001, 10000000000, 0, 11733349, 20000000, 2^100⟩

/-- Exactly the second-stage rational parameters used by the checker driver. -/
def stageTwoParams : StageParams :=
  ⟨2, 11733349, 20000000, 0, 169873, 250000, 2^100⟩

/-- Actual parser, all three actual pruned enumerations, and both actual flow
checks. A parser error returns false; it cannot produce a vacuous certificate.
The workers/count/start arguments are exactly 1, all boundary masks, and 0. -/
def wierman1995Check : Bool :=
  match parseRegionalLaws 2 lawsBytes with
  | .error _ => false
  | .ok laws =>
      (List.range 3).all (fun mode =>
        compareCounts 4
          ((prunedParallel 2 mode 1 (2^(squareBoundary 2).size) 0).map Prod.fst)
          laws.columns[mode]!) &&
      (checkRegionalFlow 2 laws stageOneParams stageOneNodes stageOneEdges).isOk &&
      (checkRegionalFlow 2 laws stageTwoParams stageTwoNodes stageTwoEdges).isOk

/-- The actual concrete Bool predicate is true. The generated native axiom is
reported explicitly below; no semantic domination conclusion is inferred. -/
theorem wierman1995_check_true : wierman1995Check = true := by
  native_decide

set_option pp.fullNames true in
#print axioms wierman1995_check_true
#eval wierman1995Check

end SitePerc.Checker.ConcreteReceipt
