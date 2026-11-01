import SitePerc.Checker.CheckerSoundness
import SitePerc.Checker.MaskConfigurations

namespace SitePerc.Checker

/-- C7 identifies every actual Bernoulli fiber, not only total mass. The key
    injection and extraction equality are explicit codec interfaces. -/
theorem C7_finiteStateLaw_mass {S : Type} [Fintype S] [DecidableEq S]
    (n : Nat) (es : List Edge) (b : Array Nat) (ps : Array (Array Nat))
    (workers cap : Nat) (expected : CountMap) (p : Parameter)
    (key : S → Nat) (key_injective : Function.Injective key)
    (X : Configuration (Fin n) → S)
    (extract : ∀ mask : Fin (2^n), configurationKey n es b ps mask.val =
      key (X (maskConfiguration n mask)))
    (checked : compareCounts n
      (boundedParallelIntervals n es b ps workers (2^n) 0 cap) expected = true)
    (s : S) :
    (finiteStateLaw p X).mass s =
      ∑ k ∈ Finset.range (n+1), ((expected.getD (key s) (Array.replicate (n+1) 0))[k]! : ℝ) *
        p.val^k * (1-p.val)^(n-k) := by
  classical
  rw [finiteStateLaw_mass_eq_range]
  symm
  calc
    _ = ∑ k ∈ Finset.range (n+1), ∑ mask ∈ Finset.range (2^n),
        if configurationKey n es b ps mask = key s ∧ openCount n mask = k then
          p.val^k * (1-p.val)^(n-k) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      have hc := parallel_C7_sound n es b ps workers (2^n) 0 cap expected checked (key s) k hk'
      change coefficient n expected (key s) k * p.val^k * (1-p.val)^(n-k) = _
      rw [hc]
      push_cast
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro mask hmask
      split <;> simp_all
    _ = ∑ mask ∈ Finset.range (2^n), ∑ k ∈ Finset.range (n+1),
        if configurationKey n es b ps mask = key s ∧ openCount n mask = k then
          p.val^k * (1-p.val)^(n-k) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro mask hmask
      have hm : mask < 2^n := Finset.mem_range.mp hmask
      have he : configurationKey n es b ps mask = key s ↔
          X (fun v => mask.testBit v.val) = s := by
        rw [extract ⟨mask,hm⟩]
        exact key_injective.eq_iff
      simp only [he]
      have hk : openCount n mask ∈ Finset.range (n+1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (openCount_le n mask))
      by_cases hs : X (fun v => mask.testBit v.val) = s
      · simp only [hs,true_and,↓reduceIte]
        rw [Finset.sum_eq_single (openCount n mask)]
        · simp
        · intro k hk' hne
          simp [Ne.symm hne]
        · intro hnot
          exact (hnot hk).elim
      · simp [hs]

/-- Each individual configuration forces its canonical key into table support. -/
theorem C7_support_complete (n : Nat) (es : List Edge) (b : Array Nat)
    (ps : Array (Array Nat)) (workers cap : Nat) (expected : CountMap)
    (checked : compareCounts n (boundedParallelIntervals n es b ps workers (2^n) 0 cap) expected = true)
    (mask : Fin (2^n)) : expected.contains (configurationKey n es b ps mask.val) = true := by
  let key := configurationKey n es b ps mask.val
  let k := openCount n mask.val
  have hk : k ≤ n := openCount_le n mask.val
  have hc := parallel_C7_sound n es b ps workers (2^n) 0 cap expected checked key k hk
  have hpos : 0 < coefficient n expected key k := by
    rw [hc]
    apply lt_of_lt_of_le (Nat.zero_lt_one)
    have hsum := Finset.single_le_sum (fun i (_hi : i ∈ Finset.range (2^n)) =>
      Nat.zero_le (if configurationKey n es b ps (0+i) = key ∧ openCount n (0+i) = k then 1 else 0))
      (Finset.mem_range.mpr mask.isLt)
    simpa only [Nat.zero_add,key,k,ite_true,and_self] using hsum
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  cases he : expected[key]? with
  | none =>
    have hz : coefficient n expected key k = 0 := by
      simp only [coefficient,Std.HashMap.getD_eq_getD_getElem?,he,Option.getD_none]
      exact zeroCounts_get n k hk
    omega
  | some cs => rfl

#print axioms C7_finiteStateLaw_mass
#print axioms C7_support_complete
end SitePerc.Checker
