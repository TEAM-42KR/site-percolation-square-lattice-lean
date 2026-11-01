import SitePerc.Checker.PrunedDefs

/-! Pure direct-law path. No serialized producer law or IO value participates.
Each Task's exact coefficient map is added into the single map consumed by
C1--C6. The merge traverses existing entries without materializing a list. -/
namespace SitePerc.Checker

def mergeCountMap (n : Nat) (acc incoming : CountMap) : CountMap :=
  incoming.fold (fun acc key cs =>
    acc.insert key (addCounts n (acc.getD key (Array.replicate (n+1) 0)) cs)) acc

def mergeCountMaps (n : Nat) (maps : Array CountMap) : CountMap :=
  maps.foldl (mergeCountMap n) {}

def directRegionalColumn (m mode workers : Nat) : CountMap :=
  mergeCountMaps (m*m)
    ((prunedParallel m mode workers (2^(squareBoundary m).size) 0).map Prod.fst)

def directRegionalLaws (m workers : Nat) : LawData :=
  let cols := Array.ofFn fun mode : Fin 3 => directRegionalColumn m mode.val workers
  ⟨m*m,(squareBoundary m).size,3,0,cols⟩

/-- A single invocation generates all three laws once and checks both flows.
The Bool observation is used only after the success-soundness theorem. -/
def directRegionalCheck (m workers : Nat) (stageOne stageTwo : StageParams)
    (nodesOne edgesOne nodesTwo edgesTwo : ByteArray) : Except String (FlowReceipt × FlowReceipt) := do
  let laws := directRegionalLaws m workers
  let one ← checkRegionalFlow m laws stageOne nodesOne edgesOne
  let two ← checkRegionalFlow m laws stageTwo nodesTwo edgesTwo
  return (one,two)

def directRegionalPass (m workers : Nat) (stageOne stageTwo : StageParams)
    (nodesOne edgesOne nodesTwo edgesTwo : ByteArray) : Bool :=
  match directRegionalCheck m workers stageOne stageTwo nodesOne edgesOne nodesTwo edgesTwo with
  | .ok _ => true
  | .error _ => false

end SitePerc.Checker
