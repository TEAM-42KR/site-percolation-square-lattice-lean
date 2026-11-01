import SitePerc.Checker.DirectDefs
import SitePerc.Checker.PrunedSoundness
import SitePerc.Checker.VerifiedRegionalFlow
import Mathlib.Tactic

namespace SitePerc.Checker

 theorem mergeCountMap_shape (n : Nat) (acc incoming : CountMap)
    (hs : CountShape n acc) : CountShape n (mergeCountMap n acc incoming) := by
  unfold mergeCountMap
  rw [Std.HashMap.fold_eq_foldl_toList]
  have step (a : CountMap) (key : Nat) (cs : Array Nat) (ha : CountShape n a) :
      CountShape n (a.insert key (addCounts n (a.getD key (Array.replicate (n+1) 0)) cs)) := by
    intro query
    rw [Std.HashMap.getD_insert]
    by_cases hq : query = key
    · simp [hq,addCounts]
    · simpa [hq,Ne.symm hq] using ha query
  have aux (xs : List (Nat × Array Nat)) (a : CountMap) (ha : CountShape n a) :
      CountShape n (xs.foldl (fun a kv =>
        a.insert kv.1 (addCounts n (a.getD kv.1 (Array.replicate (n+1) 0)) kv.2)) a) := by
    induction xs generalizing a with
    | nil => exact ha
    | cons kv xs ih => exact ih _ (step _ _ _ ha)
  exact aux _ _ hs

 theorem mergeCountMap_coefficient (n : Nat) (acc incoming : CountMap)
    (query k : Nat) (hk : k ≤ n) :
    coefficient n (mergeCountMap n acc incoming) query k =
      coefficient n acc query k + coefficient n incoming query k := by
  have step (a : CountMap) (key : Nat) (cs : Array Nat) :
      coefficient n (a.insert key (addCounts n (a.getD key (Array.replicate (n+1) 0)) cs)) query k =
      coefficient n a query k + if query = key then cs[k]! else 0 := by
    unfold coefficient
    rw [Std.HashMap.getD_insert]
    by_cases hq : query = key
    · simp only [hq,BEq.rfl,↓reduceIte]
      exact addCounts_get n _ _ k hk
    · simp [hq,Ne.symm hq]
  have foldsum (xs : List (Nat × Array Nat)) (a : CountMap) :
      coefficient n (xs.foldl (fun a kv =>
        a.insert kv.1 (addCounts n (a.getD kv.1 (Array.replicate (n+1) 0)) kv.2)) a) query k =
      coefficient n a query k +
        (xs.map (fun kv => if query = kv.1 then kv.2[k]! else 0)).sum := by
    induction xs generalizing a with
    | nil => simp
    | cons kv xs ih =>
      rw [List.foldl_cons,ih,step]
      simp [Nat.add_assoc]
  have findsum (xs : List (Nat × Array Nat))
      (hd : xs.Pairwise (fun a b => (a.1 == b.1) = false)) :
      (xs.map (fun kv => if query = kv.1 then kv.2[k]! else 0)).sum =
        ((xs.find? (fun kv => kv.1 == query)).map (fun kv => kv.2[k]!)).getD 0 := by
    induction xs with
    | nil => rfl
    | cons kv xs ih =>
      have hh := List.pairwise_cons.mp hd
      by_cases hq : query = kv.1
      · have hz : (xs.map (fun kv => if query = kv.1 then kv.2[k]! else 0)).sum = 0 := by
          apply List.sum_eq_zero
          intro a ha
          rcases List.mem_map.mp ha with ⟨v,hv,rfl⟩
          have hne : query ≠ v.1 := by
            intro eq
            have he : kv.1 = v.1 := hq.symm.trans eq
            have hb := hh.1 v hv
            simp [he] at hb
          simp [hne]
        rw [List.map_cons,List.sum_cons,hz]
        simp [List.find?_cons,hq]
      · simpa [List.find?_cons,hq,Ne.symm hq] using ih hh.2
  have one :
      (incoming.toList.map (fun kv => if query = kv.1 then kv.2[k]! else 0)).sum =
        coefficient n incoming query k := by
    rw [findsum incoming.toList incoming.distinct_keys_toList]
    cases he : incoming[query]? with
    | none =>
      have hnone : incoming.toList.find? (fun kv => kv.1 == query) = none := by
        apply Std.HashMap.find?_toList_eq_none_iff_not_mem.mpr
        simp [Std.HashMap.mem_iff_isSome_getElem?,he]
      simp only [hnone,Option.map_none,Option.getD_none]
      symm
      simp only [coefficient,Std.HashMap.getD_eq_getD_getElem?,he,Option.getD_none]
      exact zeroCounts_get n k hk
    | some cs =>
      have hmem : query ∈ incoming := by
        simp [Std.HashMap.mem_iff_isSome_getElem?,he]
      have hf : incoming.toList.find? (fun kv => kv.1 == query) = some (query,cs) :=
        Std.HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some.mpr
          ⟨Std.HashMap.getKey?_eq_some hmem,he⟩
      simp [hf,coefficient,Std.HashMap.getD_eq_getD_getElem?,he]
  unfold mergeCountMap
  rw [Std.HashMap.fold_eq_foldl_toList,foldsum,one]

 theorem mergeCountMaps_shape (n : Nat) (maps : Array CountMap) :
    CountShape n (mergeCountMaps n maps) := by
  have aux (xs : List CountMap) (acc : CountMap) (hs : CountShape n acc) :
      CountShape n (xs.foldl (mergeCountMap n) acc) := by
    induction xs generalizing acc with
    | nil => exact hs
    | cons x xs ih => exact ih _ (mergeCountMap_shape n acc x hs)
  unfold mergeCountMaps
  rw [←Array.foldl_toList]
  exact aux _ _ (countShape_empty n)

 theorem mergeCountMaps_coefficient (n : Nat) (maps : Array CountMap)
    (query k : Nat) (hk : k ≤ n) :
    coefficient n (mergeCountMaps n maps) query k = (sumCounts n maps query)[k]! := by
  have aux (xs : List CountMap) (acc : CountMap) :
      coefficient n (xs.foldl (mergeCountMap n) acc) query k =
      coefficient n acc query k + (xs.map (fun law => coefficient n law query k)).sum := by
    induction xs generalizing acc with
    | nil => simp
    | cons x xs ih =>
      rw [List.foldl_cons,ih,mergeCountMap_coefficient n acc x query k hk]
      simp [Nat.add_assoc]
  rw [sumCounts_coefficient n maps query k hk]
  unfold mergeCountMaps
  rw [←Array.foldl_toList,aux]
  have hz : coefficient n ({} : CountMap) query k = 0 := by
    simp only [coefficient,Std.HashMap.getD_empty]
    exact zeroCounts_get n k hk
  simp [hz]

 theorem directRegionalLaws_exact (m : Nat) (hm : RegionalSize m) (workers : Nat) :
    ExactRegionalLaws m (directRegionalLaws m workers) := by
  constructor
  · simp [directRegionalLaws]
  · intro mode
    have hc : (directRegionalLaws m workers).columns[mode.val]! =
        directRegionalColumn m mode.val workers := by
      rw [getElem!_pos _ _ (by simp [directRegionalLaws])]
      simp [directRegionalLaws]
    rw [hc]
    exact mergeCountMaps_shape (m*m) _
  · intro mode query k hk
    have hc : (directRegionalLaws m workers).columns[mode.val]! =
        directRegionalColumn m mode.val workers := by
      rw [getElem!_pos _ _ (by simp [directRegionalLaws])]
      simp [directRegionalLaws]
    rw [hc,directRegionalColumn,mergeCountMaps_coefficient (m*m) _ query k hk]
    exact prunedParallel_coefficients_correct m hm mode workers query k hk

/-- Single actual native success supplies both Base stage dominations.
No second enumeration, support hypothesis, mass table or producer trust. -/
theorem directRegionalPass_boundary_stages (workers : Nat)
    (nodesOne edgesOne nodesTwo edgesTwo : ByteArray)
    (h : directRegionalPass 6 workers verifiedStageOneParams verifiedStageTwoParams
      nodesOne edgesOne nodesTwo edgesTwo = true) :
    boundaryDominates 6 (0,0) lineLattice intermediate q0 p1 ∧
      boundaryDominates 6 (3,3) intermediate square p1 p2 := by
  cases hone : checkRegionalFlow 6 (directRegionalLaws 6 workers)
      verifiedStageOneParams nodesOne edgesOne with
  | error e =>
    simp only [directRegionalPass,directRegionalCheck,hone] at h
    change false = true at h
    cases h
  | ok one =>
    cases htwo : checkRegionalFlow 6 (directRegionalLaws 6 workers)
        verifiedStageTwoParams nodesTwo edgesTwo with
    | error e =>
      simp only [directRegionalPass,directRegionalCheck,hone,htwo] at h
      change false = true at h
      cases h
    | ok two =>
      exact verified_boundary_stages (directRegionalLaws 6 workers)
        (directRegionalLaws_exact 6 (Or.inr (Or.inr rfl)) workers)
        nodesOne edgesOne nodesTwo edgesTwo one two hone htwo

end SitePerc.Checker
