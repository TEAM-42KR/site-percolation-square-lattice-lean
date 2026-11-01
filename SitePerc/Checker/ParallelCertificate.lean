import SitePerc.Checker.ParallelCertificateDefs
import Mathlib.Tactic

namespace SitePerc.Checker

/-- Semantic scheduling refinement, not a claim about eager runtime speed. -/
theorem parallelDecodeFiles_eq (files : Array (Array String)) :
    parallelDecodeFiles files = files.map CompactCertificateBytes.decodeChunks := by
  simp only [parallelDecodeFiles,Task.spawn,Task.get,List.map_map]
  change (files.toList.map CompactCertificateBytes.decodeChunks).toArray = _
  rw [←Array.toList_map]

#print axioms parallelDecodeFiles_eq
end SitePerc.Checker
