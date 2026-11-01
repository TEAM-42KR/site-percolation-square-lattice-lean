import SitePerc.Checker.RegionalDefs
import SitePerc.Checker.LawSoundness
import Mathlib.Tactic

namespace SitePerc.Checker

/-- Cache-cap resets are semantically invisible, for every cap including zero. -/
theorem enumerateBoundedCached_eq (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (cap count start : Nat) (law : CountMap) (cache : KeyCache)
    (hv : CacheValid b.size ps cache) :
    (enumerateBoundedCached n es b ps cap count start law cache).1 =
      enumerateInterval n es b ps count start law := by
  induction count generalizing start law cache with
  | zero => rfl
  | succ count ih =>
    simp only [enumerateBoundedCached,enumerateInterval]
    have hc : CacheValid b.size ps (if cache.size > cap then {} else cache) := by
      split
      · exact cacheValid_empty _ _
      · exact hv
    have h := cacheKey_sound b.size ps (rawRootKey n es b start) _ hc
    rw [ih _ _ _ h.2,h.1]
    rfl

@[simp] theorem addCounts_get (n : Nat) (a b : Array Nat) (k : Nat) (hk : k ≤ n) :
    (addCounts n a b)[k]! = a[k]! + b[k]! := by
  rw [getElem!_pos (addCounts n a b) k (by simp [addCounts]; omega)]
  simp [addCounts]

@[simp] theorem zeroCounts_get (n k : Nat) (hk : k ≤ n) :
    (Array.replicate (n+1) (0:Nat))[k]! = 0 := by
  rw [getElem!_pos (Array.replicate (n+1) (0:Nat)) k (by simp; omega)]
  simp

theorem sumCounts_coefficient (n : Nat) (maps : Array CountMap) (key k : Nat) (hk : k ≤ n) :
    (sumCounts n maps key)[k]! = (maps.toList.map (fun m => coefficient n m key k)).sum := by
  have aux (ms : List CountMap) (acc : Array Nat) :
      (ms.foldl (fun a m => match m[key]? with
        | none => a | some cs => addCounts n a cs) acc)[k]! =
      acc[k]! + (ms.map (fun m => coefficient n m key k)).sum := by
    induction ms generalizing acc with
    | nil => simp
    | cons m ms ih =>
      simp only [List.foldl_cons,List.map_cons,List.sum_cons]
      cases h : m[key]? with
      | none =>
        simp only [h]
        rw [ih]
        have hc : coefficient n m key k = 0 := by
          simp only [coefficient,Std.HashMap.getD_eq_getD_getElem?,h,Option.getD_none]
          exact zeroCounts_get n k hk
        simp [hc]
      | some cs =>
        simp only [h]
        rw [ih,addCounts_get _ _ _ _ hk]
        have hc : coefficient n m key k = cs[k]! := by
          simp [coefficient,Std.HashMap.getD_eq_getD_getElem?,h]
        simp [hc,Nat.add_assoc]
  unfold sumCounts
  rw [← Array.foldl_toList]
  have hh := aux maps.toList (Array.replicate (n+1) 0)
  rw [zeroCounts_get _ _ hk,Nat.zero_add] at hh
  convert hh using 1 <;> rfl

theorem sumCounts_of_absent (n : Nat) (maps : Array CountMap) (key : Nat)
    (h : ∀ m ∈ maps.toList, m[key]? = none) :
    sumCounts n maps key = Array.replicate (n+1) 0 := by
  have aux (ms : List CountMap) (acc : Array Nat) (h : ∀ m ∈ ms, m[key]? = none) :
      ms.foldl (fun a m => match m[key]? with
        | none => a | some cs => addCounts n a cs) acc = acc := by
    induction ms generalizing acc with
    | nil => rfl
    | cons m ms ih =>
      simp only [List.foldl_cons,h m (by simp)]
      apply ih
      intro m hm
      exact h m (by simp [hm])
  unfold sumCounts
  rw [← Array.foldl_toList]
  exact aux _ _ h

/-- Both directions of support matter: an absent expected key cannot hide any
    generated row, even when all totals or binomial sums happen to match. -/
theorem compareCounts_sound (n : Nat) (maps : Array CountMap) (expected : CountMap)
    (h : compareCounts n maps expected = true) (key : Nat) :
    expected.getD key (Array.replicate (n+1) 0) = sumCounts n maps key := by
  have hp : expected.toList.all (fun (key,cs) => cs == sumCounts n maps key) = true ∧
      maps.all (fun m => m.toList.all (fun (key,_) => expected.contains key)) = true := by
    simpa only [compareCounts,Bool.and_eq_true] using h
  have hrows := List.all_eq_true.mp hp.1
  have hsupp : ∀ m ∈ maps.toList, ∀ pair ∈ m.toList, expected.contains pair.1 = true := by
    simpa only [← Array.all_toList,List.all_eq_true] using hp.2
  cases he : expected[key]? with
  | some cs =>
    have hm : (key,cs) ∈ expected.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr he
    have hh : cs = sumCounts n maps key := by simpa only [beq_iff_eq] using hrows (key,cs) hm
    simpa [Std.HashMap.getD_eq_getD_getElem?,he] using hh
  | none =>
    have hm : ∀ m ∈ maps.toList, m[key]? = none := by
      intro m hmem
      cases hx : m[key]? with
      | none => rfl
      | some cs =>
        have hc := hsupp m hmem (key,cs) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx)
        have := Std.HashMap.getElem?_eq_some_getD_of_contains (m:=expected) (a:=key)
          (fallback:=Array.replicate (n+1) 0) hc
        simp [he] at this
    rw [sumCounts_of_absent n maps key hm]
    simp [Std.HashMap.getD_eq_getD_getElem?,he]

/-- Clipped consecutive blocks partition an initial segment, including the
    zero-length blocks after its end. No divisibility hypothesis is needed. -/
theorem sum_clipped_blocks (f : Nat → Nat) (width count workers : Nat) :
    (∑ i ∈ Finset.range workers, ∑ j ∈ Finset.range (min width (count-i*width)), f (i*width+j)) =
    ∑ k ∈ Finset.range (min count (workers*width)), f k := by
  induction workers with
  | zero => simp
  | succ w ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases h : count ≤ w*width
    · have hh : count ≤ (w+1)*width := by
        rw [Nat.add_mul]; omega
      simp [Nat.sub_eq_zero_of_le h,min_eq_left h,min_eq_left hh]
    · have hle : w*width ≤ count := by omega
      have he : min count ((w+1)*width) = w*width + min width (count-w*width) := by
        rw [Nat.add_mul,Nat.one_mul]
        omega
      rw [min_eq_right hle,he,Finset.sum_range_add]

theorem ceil_partition_covers (count workers : Nat) (hw : 0 < workers) :
    count ≤ workers * ((count+workers-1)/workers) := by
  have hm := Nat.mod_lt (count+workers-1) hw
  have hd := Nat.mod_add_div (count+workers-1) workers
  omega

theorem sum_map_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,ih,Finset.sum_range_succ]

/-- Task concurrency is a runtime choice only; its pure value is the exact list
    of disjoint clipped-interval computations. -/
theorem boundedParallel_value (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (workers count start cap : Nat) :
    (boundedParallelIntervals n es b ps workers count start cap).toList =
    (List.range (max 1 workers)).map (fun i =>
      enumerateInterval n es b ps (min ((count+max 1 workers-1)/(max 1 workers))
        (count-i*((count+max 1 workers-1)/(max 1 workers))))
        (start+i*((count+max 1 workers-1)/(max 1 workers))) {}) := by
  simp only [boundedParallelIntervals,Task.spawn,Task.get,List.toList_toArray,List.map_map]
  apply List.map_congr_left
  intro i hi
  exact enumerateBoundedCached_eq n es b ps cap _ _ {} {} (cacheValid_empty _ _)

theorem parallel_C7_sound (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (workers count start cap : Nat) (expected : CountMap)
    (h : compareCounts n (boundedParallelIntervals n es b ps workers count start cap) expected = true)
    (key k : Nat) (hk : k ≤ n) :
    coefficient n expected key k =
      ∑ mask ∈ Finset.range count, if configurationKey n es b ps (start+mask) = key ∧
        openCount n (start+mask) = k then 1 else 0 := by
  unfold coefficient
  rw [compareCounts_sound _ _ _ h key,sumCounts_coefficient _ _ _ _ hk]
  rw [boundedParallel_value,List.map_map,sum_map_range]
  let w := max 1 workers
  let width := (count+w-1)/w
  have hw : 0 < w := by dsimp [w]; omega
  have hz : coefficient n ({} : CountMap) key k = 0 := by simp [coefficient,zeroCounts_get _ _ hk]
  calc
    _ = ∑ i ∈ Finset.range w, ∑ j ∈ Finset.range (min width (count-i*width)),
        if configurationKey n es b ps (start+(i*width+j)) = key ∧
          openCount n (start+(i*width+j)) = k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [hz,Nat.zero_add,Nat.add_assoc,Function.comp_def,w,width] using
        enumerateInterval_coefficient n es b ps (min width (count-i*width)) (start+i*width) {} (countShape_empty n) key k hk
    _ = _ := by
      have hh := sum_clipped_blocks (fun t => if configurationKey n es b ps (start+t) = key ∧ openCount n (start+t) = k then 1 else 0) width count w
      have hcover : count ≤ w*width := ceil_partition_covers count w hw
      rw [min_eq_left hcover] at hh
      exact hh

#print axioms parallel_C7_sound
end SitePerc.Checker
