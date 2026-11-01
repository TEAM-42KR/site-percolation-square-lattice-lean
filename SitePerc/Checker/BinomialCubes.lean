import SitePerc.Checker.PrunedDefs
import SitePerc.Checker.LawSoundness
import Mathlib.Tactic

/-!
# Exact coefficients of constant-key Boolean cubes

The pure Pascal arrays and shifted map update are the executable checker
operations. Every identity is per key and per open-count coefficient; a total
binomial mass alone is never used as a replacement. Graph-specific constant-key
facts, configuration-bit encodings and enumeration refinement are separate.
-/

namespace SitePerc.Checker

/-- Logical getter default equality; it makes no runtime no-panic claim. -/
theorem array_nat_getElem_default (xs : Array Nat) (j : Nat) :
    xs[j]! = (xs[j]?).getD 0 := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rfl

/-- The actual Pascal row has its declared coefficient width. -/
theorem cubeBinomialRow_size (r : Nat) : (cubeBinomialRow r).size = r+1 := by
  cases r <;> simp [cubeBinomialRow]

/-- Exact safe row coefficients, including fallback zero outside the row. -/
theorem cubeBinomialRow_getD (r j : Nat) :
    ((cubeBinomialRow r)[j]?).getD 0 = Nat.choose r j := by
  induction r generalizing j with
  | zero => cases j <;> simp [cubeBinomialRow]
  | succ r ih =>
    by_cases hj : j < r+2
    · simp only [cubeBinomialRow, Array.getElem?_ofFn, hj, ↓reduceDIte,
        Option.getD_some]
      cases j with
      | zero => simp [ih]
      | succ j =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
          ih, Nat.choose_succ_succ, Nat.succ_eq_add_one]
        omega
    · have hz : Nat.choose (r+1) j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [cubeBinomialRow, Array.getElem?_ofFn, hj, hz]

/-- The original logical getter has the same exact coefficients. -/
theorem cubeBinomialRow_getElem (r j : Nat) :
    (cubeBinomialRow r)[j]! = Nat.choose r j := by
  rw [array_nat_getElem_default, cubeBinomialRow_getD]

/-- Every coefficient in a declared precomputed row is exact. -/
theorem cubeBinomials_getD (maxFree r j : Nat) (hr : r ≤ maxFree) :
    (((cubeBinomials maxFree)[r]!)[j]?).getD 0 = Nat.choose r j := by
  have htable : (cubeBinomials maxFree)[r]! = cubeBinomialRow r := by
    simp [cubeBinomials, show r < maxFree+1 by omega]
  rw [htable, cubeBinomialRow_getD]

/-- Exact precomputed table coefficients with the logical total getter. -/
theorem cubeBinomials_getElem (maxFree r j : Nat) (hr : r ≤ maxFree) :
    ((cubeBinomials maxFree)[r]!)[j]! = Nat.choose r j := by
  rw [array_nat_getElem_default, cubeBinomials_getD maxFree r j hr]

/-- Actual bumpCube adds the shifted binomial coefficient at each key/k. -/
theorem coefficient_bumpCube (n maxFree key baseOpen free : Nat)
    (law : CountMap) (query k : Nat) (hfree : free ≤ maxFree) (hk : k ≤ n) :
    ((bumpCube (cubeBinomials maxFree) n key baseOpen free law).getD query
      (Array.replicate (n+1) 0))[k]! =
      (law.getD query (Array.replicate (n+1) 0))[k]! +
        if query = key ∧ baseOpen ≤ k then Nat.choose free (k-baseOpen) else 0 := by
  unfold bumpCube
  rw [Std.HashMap.getD_insert]
  by_cases hkey : query = key
  · subst query
    simp only [BEq.rfl, ↓reduceIte, true_and]
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
    rw [cubeBinomials_getD maxFree free (k-baseOpen) hfree]
  · simp [hkey, Ne.symm hkey, beq_iff_eq]

/-- Exact scalar sum over the closed/open branches of a Boolean cube. -/
def cubeBinarySum : Nat → (List Bool → Nat) → Nat
  | 0, leaf => leaf []
  | r+1, leaf => cubeBinarySum r (fun bs => leaf (false::bs)) +
      cubeBinarySum r (fun bs => leaf (true::bs))

/-- The scalar binary tree depends only on its leaves of the declared length. -/
theorem cubeBinarySum_congr (r : Nat) (f g : List Bool → Nat)
    (h : ∀ bs : List Bool, bs.length = r → f bs = g bs) :
    cubeBinarySum r f = cubeBinarySum r g := by
  induction r generalizing f g with
  | zero => exact h [] rfl
  | succ r ih =>
    simp only [cubeBinarySum]
    rw [ih (fun bs => f (false::bs)) (fun bs => g (false::bs))
      (fun bs hb => h (false::bs) (by simp [hb])),
      ih (fun bs => f (true::bs)) (fun bs => g (true::bs))
      (fun bs hb => h (true::bs) (by simp [hb]))]

/-- Closed and open branches give Pascal's rule at every shifted coefficient. -/
theorem cube_shifted_choose_succ (r baseOpen k : Nat) :
    (if baseOpen ≤ k then Nat.choose r (k-baseOpen) else 0) +
      (if baseOpen+1 ≤ k then Nat.choose r (k-(baseOpen+1)) else 0) =
      if baseOpen ≤ k then Nat.choose (r+1) (k-baseOpen) else 0 := by
  by_cases hb : baseOpen ≤ k
  · by_cases he : k = baseOpen
    · subst k
      simp
    · have hlt : baseOpen+1 ≤ k := by omega
      have hshift : k-baseOpen = (k-(baseOpen+1))+1 := by omega
      simp only [hb, hlt, ↓reduceIte, hshift, Nat.choose_succ_succ,
        Nat.succ_eq_add_one]
      omega
  · have hb' : ¬baseOpen+1 ≤ k := by omega
    simp [hb, hb']

/-- A constant-key Boolean decision tree contributes an exact shifted binomial
coefficient at every queried key and every open-count k. -/
theorem cubeBinarySum_coeff (r baseOpen key query k : Nat)
    (leafKey : List Bool → Nat)
    (sameKey : ∀ bs : List Bool, bs.length = r → leafKey bs = key) :
    cubeBinarySum r (fun bs =>
      if leafKey bs = query ∧ baseOpen + bs.count true = k then 1 else 0) =
      if query = key ∧ baseOpen ≤ k then Nat.choose r (k-baseOpen) else 0 := by
  induction r generalizing baseOpen leafKey with
  | zero =>
    simp only [cubeBinarySum, List.count_nil, Nat.add_zero, sameKey [] rfl]
    by_cases hkey : query = key
    · subst query
      simp only [true_and]
      by_cases hb : baseOpen ≤ k
      · simp only [hb, ↓reduceIte]
        by_cases he : baseOpen = k
        · subst k; simp
        · have hlt : 0 < k-baseOpen := by omega
          rw [Nat.choose_eq_zero_of_lt hlt]
          simp [he]
      · have he : baseOpen ≠ k := by omega
        simp [hb, he]
    · simp [hkey, Ne.symm hkey]
  | succ r ih =>
    have hclosed : ∀ bs : List Bool, bs.length = r → leafKey (false::bs) = key :=
      fun bs hb => sameKey _ (by simp [hb])
    have hopen : ∀ bs : List Bool, bs.length = r → leafKey (true::bs) = key :=
      fun bs hb => sameKey _ (by simp [hb])
    have hsplit : cubeBinarySum (r+1) (fun bs =>
        if leafKey bs = query ∧ baseOpen + bs.count true = k then 1 else 0) =
        cubeBinarySum r (fun bs =>
          if leafKey (false::bs) = query ∧ baseOpen + bs.count true = k then 1 else 0) +
        cubeBinarySum r (fun bs =>
          if leafKey (true::bs) = query ∧ (baseOpen+1) + bs.count true = k then 1 else 0) := by
      simp only [cubeBinarySum, List.count_cons, Bool.false_beq, Bool.true_beq,
        Bool.not_true, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
        Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    rw [hsplit, ih baseOpen (fun bs => leafKey (false::bs)) hclosed,
      ih (baseOpen+1) (fun bs => leafKey (true::bs)) hopen]
    by_cases hkey : query = key
    · simp only [hkey, true_and]
      exact cube_shifted_choose_succ r baseOpen k
    · simp [hkey]

/-- Every actual collapsed key/k coefficient is exactly its full binary-tree
leaf sum, not just a total binomial-mass equality. -/
theorem coefficient_bumpCube_eq_binarySum (n maxFree key baseOpen free : Nat)
    (law : CountMap) (query k : Nat) (hfree : free ≤ maxFree) (hk : k ≤ n)
    (leafKey : List Bool → Nat)
    (sameKey : ∀ bs : List Bool, bs.length = free → leafKey bs = key) :
    ((bumpCube (cubeBinomials maxFree) n key baseOpen free law).getD query
      (Array.replicate (n+1) 0))[k]! =
      (law.getD query (Array.replicate (n+1) 0))[k]! +
        cubeBinarySum free (fun bs =>
          if leafKey bs = query ∧ baseOpen + bs.count true = k then 1 else 0) := by
  rw [coefficient_bumpCube n maxFree key baseOpen free law query k hfree hk,
    cubeBinarySum_coeff free baseOpen key query k leafKey sameKey]

#print axioms array_nat_getElem_default
#print axioms cubeBinomialRow_size
#print axioms cubeBinomialRow_getD
#print axioms cubeBinomialRow_getElem
#print axioms cubeBinomials_getD
#print axioms cubeBinomials_getElem
#print axioms coefficient_bumpCube
#print axioms cubeBinarySum_congr
#print axioms cube_shifted_choose_succ
#print axioms cubeBinarySum_coeff
#print axioms coefficient_bumpCube_eq_binarySum

end SitePerc.Checker
