import SitePerc.Checker.Connectivity
import SitePerc.Checker.LawDefs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace SitePerc.Checker
open Batteries

@[simp] theorem length_normalize (xs : List Nat) : (normalize xs).length = xs.length := by
  simp [normalize]

theorem normalize_get (xs : List Nat) (i : Fin xs.length) :
    (normalize xs)[i.val]'(by simpa using i.isLt) =
    if xs[i.val] = 0 then 0 else ((xs.filter (fun x => x != 0)).eraseDups).idxOf xs[i.val] + 1 := by
  simp [normalize]

@[simp] theorem normalize_zero_iff (xs : List Nat) (i : Fin xs.length) :
    (normalize xs)[i.val]'(by simpa using i.isLt) = 0 ↔ xs[i.val] = 0 := by
  rw [normalize_get]
  split <;> simp_all

theorem normalize_eq_iff (xs : List Nat) (i j : Fin xs.length)
    (hi : xs[i.val] ≠ 0) (hj : xs[j.val] ≠ 0) :
    (normalize xs)[i.val]'(by simpa using i.isLt) =
      (normalize xs)[j.val]'(by simpa using j.isLt) ↔ xs[i.val] = xs[j.val] := by
  rw [normalize_get,normalize_get,if_neg hi,if_neg hj,Nat.add_right_cancel_iff]
  apply List.idxOf_inj
  simp [hi]

theorem eraseDups_length_le (xs : List Nat) : xs.eraseDups.length ≤ xs.length := by
  have h (as bs : List Nat) :
      (List.eraseDupsBy.loop (· == ·) as bs).length ≤ as.length + bs.length := by
    induction as generalizing bs with
    | nil => simp [List.eraseDupsBy.loop]
    | cons a as ih =>
      simp only [List.eraseDupsBy.loop]
      split
      · have := ih bs; simp only [List.length_cons]; omega
      · have := ih (a::bs); simp only [List.length_cons] at *; omega
  simpa only [List.eraseDups,List.eraseDupsBy,List.length_nil,Nat.add_zero] using h xs []

theorem normalize_lt (xs : List Nat) (i : Fin xs.length) :
    (normalize xs)[i.val]'(by simpa using i.isLt) ≤ xs.length := by
  rw [normalize_get]
  split
  · omega
  · next hi =>
    have hx : xs[i.val] ∈ (xs.filter (fun x => x != 0)).eraseDups := by simp [hi]
    have h := List.idxOf_lt_length_of_mem hx
    have hlen := eraseDups_length_le (xs.filter (fun x => x != 0))
    have hf := List.length_filter_le (fun x : Nat => x != 0) xs
    omega

@[simp] theorem length_unpack (b key : Nat) : (unpack b key).length = b := by
  induction b generalizing key with
  | zero => rfl
  | succ b ih => simp [unpack,ih]

theorem pack_lt (xs : List Nat) (h : ∀ x ∈ xs, x < 32) : pack xs < 32 ^ xs.length := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun a ha => h a (by simp [ha]))
    simp only [pack,List.length_cons,pow_succ]
    omega

theorem unpack_pack (xs : List Nat) (h : ∀ x ∈ xs, x < 32) :
    unpack xs.length (pack xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr : ∀ a ∈ xs, a < 32 := fun a ha => h a (by simp [ha])
    simp only [List.length_cons,pack,unpack]
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx]
    have hd : (x + 32 * pack xs) / 32 = pack xs := by omega
    rw [hd,ih hr]

def coefficient (n : Nat) (law : CountMap) (key k : Nat) : Nat :=
  (law.getD key (Array.replicate (n+1) 0))[k]!

theorem coefficient_bump (n key k weight : Nat) (m : CountMap) (hk : k ≤ n)
    (hshape : ∀ a, (m.getD a (Array.replicate (n+1) 0)).size = n+1)
    (a j : Nat) (hj : j ≤ n) :
    coefficient n (bump n key k weight m) a j =
    coefficient n m a j + if a = key ∧ j = k then weight else 0 := by
  unfold coefficient bump
  rw [Std.HashMap.getD_insert]
  by_cases ha : a = key
  · subst a
    simp only [BEq.rfl,↓reduceIte,true_and]
    have hs := hshape key
    by_cases hjk : j = k
    · subst j
      rw [Array.getElem!_set!_self _ _ _ (by omega)]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hjk)]
      simp [hjk]
  · simp [ha,Ne.symm ha,beq_iff_eq]

/-- All arrays keep their declared coefficient width. -/
def CountShape (n : Nat) (m : CountMap) : Prop :=
  ∀ key, (m.getD key (Array.replicate (n+1) 0)).size = n+1

@[simp] theorem countShape_empty (n : Nat) : CountShape n ({} : CountMap) := by
  intro key
  simp

theorem countShape_bump (n key k w : Nat) (m : CountMap) (hm : CountShape n m) :
    CountShape n (bump n key k w m) := by
  intro a
  unfold bump
  rw [Std.HashMap.getD_insert]
  split
  · simp [Array.size_set!,hm key]
  · exact hm a

theorem openCount_le (n mask : Nat) : openCount n mask ≤ n := by
  have aux (xs : List Nat) (k : Nat) :
      xs.foldl (fun k i => if mask.testBit i then k+1 else k) k ≤ k+xs.length := by
    induction xs generalizing k with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons,List.length_cons]
      split
      · have := ih (k+1); omega
      · have := ih k; omega
  simpa [openCount] using aux (List.range n) 0

theorem enumerateInterval_shape (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (count start : Nat) (m : CountMap) (hm : CountShape n m) :
    CountShape n (enumerateInterval n es b ps count start m) := by
  induction count generalizing start m with
  | zero => exact hm
  | succ c ih =>
    exact ih (start+1) _ (countShape_bump _ _ _ _ _ hm)

/-- Every single state/k coefficient, not only the total binomial mass. -/
theorem enumerateInterval_coefficient (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (count start : Nat) (m : CountMap)
    (hm : CountShape n m) (key k : Nat) (hk : k ≤ n) :
    coefficient n (enumerateInterval n es b ps count start m) key k =
    coefficient n m key k +
      ∑ j ∈ Finset.range count, if configurationKey n es b ps (start+j) = key ∧
        openCount n (start+j) = k then 1 else 0 := by
  induction count generalizing start m with
  | zero => simp [enumerateInterval]
  | succ count ih =>
    simp only [enumerateInterval]
    rw [ih (start+1) _ (countShape_bump _ _ _ _ _ hm)]
    rw [coefficient_bump _ _ _ _ _ (openCount_le _ _) hm _ _ hk]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero,Nat.add_assoc]
    have hs : (∑ j ∈ Finset.range count, if configurationKey n es b ps (start + (j+1)) = key ∧ openCount n (start+(j+1)) = k then 1 else 0) =
        ∑ j ∈ Finset.range count, if configurationKey n es b ps (start+1+j) = key ∧ openCount n (start+1+j) = k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have h : start+(j+1) = start+1+j := by omega
      rw [h]
    rw [hs]
    by_cases h1 : configurationKey n es b ps start = key
    · by_cases h2 : openCount n start = k
      · simp [h1,h2,Nat.add_comm,Nat.add_left_comm]
      · simp [h1,h2,Ne.symm h2,Nat.add_comm,Nat.add_left_comm]
    · simp [h1,Ne.symm h1,Nat.add_comm,Nat.add_left_comm]

theorem enumeration_coefficients_correct (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (key k : Nat) (hk : k ≤ n) :
    coefficient n (enumerateInterval n es b ps (2^n) 0 {}) key k =
      ∑ mask ∈ Finset.range (2^n), if configurationKey n es b ps mask = key ∧
        openCount n mask = k then 1 else 0 := by
  have hz : coefficient n ({} : CountMap) key k = 0 := by
    simp only [coefficient,Std.HashMap.getD_empty]
    rw [getElem!_pos (Array.replicate (n+1) (0:Nat)) k (by simp; omega)]
    simp
  simpa only [hz,Nat.zero_add,Nat.zero_add] using enumerateInterval_coefficient n es b ps (2^n) 0 {} (countShape_empty n) key k hk

def CacheValid (b : Nat) (ps : Array (Array Nat)) (cache : KeyCache) : Prop :=
  ∀ raw key, cache[raw]? = some key → key = keyOfRaw b ps raw

@[simp] theorem cacheValid_empty (b : Nat) (ps : Array (Array Nat)) : CacheValid b ps {} := by
  intro raw key h
  simp at h

theorem cacheKey_sound (b : Nat) (ps : Array (Array Nat)) (raw : Nat) (cache : KeyCache)
    (hv : CacheValid b ps cache) :
    (cacheKey b ps raw cache).1 = keyOfRaw b ps raw ∧
      CacheValid b ps (cacheKey b ps raw cache).2 := by
  unfold cacheKey
  split
  · next key he => exact ⟨hv raw key he,hv⟩
  · refine ⟨rfl,?_⟩
    intro r k h
    by_cases hr : r = raw
    · subst r
      simpa only [Std.HashMap.getElem?_insert_self,Option.some.injEq] using h.symm
    · apply hv r k
      simpa [Std.HashMap.getElem?_insert,hr,Ne.symm hr,beq_iff_eq] using h

/-- The performance cache is proved observationally equal to the unfactored
    tail-recursive enumerator. Cached producer code is not a trusted premise. -/
theorem enumerateCached_eq (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (count start : Nat) (law : CountMap) (cache : KeyCache)
    (hv : CacheValid b.size ps cache) :
    (enumerateCached n es b ps count start law cache).1 =
      enumerateInterval n es b ps count start law := by
  induction count generalizing start law cache with
  | zero => rfl
  | succ count ih =>
    simp only [enumerateCached,enumerateInterval]
    have h := cacheKey_sound b.size ps (rawRootKey n es b start) cache hv
    rw [ih _ _ _ h.2,h.1]
    rfl

theorem unpackBase64_pack (xs : List Nat) (h : ∀ x ∈ xs, x < 64) :
    unpackBase 64 xs.length (packBase 64 xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr : ∀ a ∈ xs, a < 64 := fun a ha => h a (by simp [ha])
    simp only [List.length_cons,packBase,unpackBase]
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx]
    have hd : (x + 64 * packBase 64 xs) / 64 = packBase 64 xs := by omega
    rw [hd,ih hr]

theorem rootLabels_lt64 (n : Nat) (hn : n < 64) (es : List Edge)
    (b : Array Nat) (hb : ∀ v ∈ b.toList, v < n) (mask : Nat) :
    ∀ x ∈ rootLabels n es b mask, x < 64 := by
  intro x hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  split
  · have hroot : (components n es mask.testBit).rootD v < n := by
      simpa using (Batteries.UnionFind.rootD_lt (self:=components n es mask.testBit) (x:=v)).mpr (by simpa using hb v hv)
    omega
  · omega

theorem configurationKey_semantics (n : Nat) (hn : n < 64) (es : List Edge)
    (b : Array Nat) (hb : ∀ v ∈ b.toList, v < n)
    (ps : Array (Array Nat)) (mask : Nat) :
    configurationKey n es b ps mask = canonicalKey (rootLabels n es b mask) ps := by
  unfold configurationKey keyOfRaw rawRootKey
  have hl : (rootLabels n es b mask).length = b.size := by simp [rootLabels]
  rw [← hl,unpackBase64_pack _ (rootLabels_lt64 n hn es b hb mask)]

#print axioms enumeration_coefficients_correct
#print axioms enumerateCached_eq
#print axioms configurationKey_semantics
#print axioms normalize_eq_iff
#print axioms unpack_pack
end SitePerc.Checker
