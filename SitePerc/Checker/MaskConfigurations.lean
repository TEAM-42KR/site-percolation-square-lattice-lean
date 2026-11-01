import SitePerc.Checker.LawDefs
import SitePerc.FiniteProbability
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact mask enumeration and finite iid configurations

The low-bit decoder is the producer's actual `Nat.testBit` decoder. This
module identifies its complete integer-mask enumeration with the actual
finite Bernoulli law, preserving an arbitrary extraction function pointwise.
No connectivity, packed state, group action, or certificate premise is used.
-/

open scoped BigOperators

namespace SitePerc.Checker

/-- The exact low-bit configuration used by the integer-mask enumerator. -/
def maskConfiguration (n : ℕ) (mask : Fin (2 ^ n)) : Configuration (Fin n) :=
  fun v => mask.val.testBit v.val

/-- Every n-bit configuration is represented once, with the exact forward
`testBit` convention. The inverse is chosen only after bijectivity is proved. -/
noncomputable def maskEquivConfiguration (n : ℕ) :
    Fin (2 ^ n) ≃ Configuration (Fin n) :=
  Equiv.ofBijective (maskConfiguration n)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro a b hab
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < n
      · exact congrFun hab ⟨i, hi⟩
      · have hni : n ≤ i := Nat.le_of_not_gt hi
        have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hni
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hp),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hp)], by
      simp [Configuration]⟩)

theorem maskEquivConfiguration_apply (n : ℕ) (mask : Fin (2 ^ n)) (v : Fin n) :
    maskEquivConfiguration n mask v = mask.val.testBit v.val := by
  rfl

/-- The actual producer fold, not a replacement population-count definition. -/
theorem openCount_eq_bit_sum (n mask : ℕ) : openCount n mask =
    ∑ i ∈ Finset.range n, if mask.testBit i then 1 else 0 := by
  induction n with
  | zero => simp [openCount]
  | succ n ih =>
    have hs : openCount (n + 1) mask =
        if mask.testBit n then openCount n mask + 1 else openCount n mask := by
      simp [openCount, List.range_succ, List.foldl_append]
    rw [hs, Finset.sum_range_succ, ih]
    split <;> simp_all

/-- The actual fold counts exactly the true coordinates of the decoded configuration. -/
theorem openCount_eq_configuration_count (n : ℕ) (mask : Fin (2 ^ n)) :
    openCount n mask.val = SitePerc.openCount (maskConfiguration n mask) := by
  rw [openCount_eq_bit_sum, ← Fin.sum_univ_eq_sum_range]
  simp [SitePerc.openCount, maskConfiguration]
  rfl

/-- Both endpoint Bernoulli parameters are covered without division. -/
theorem configuration_closedCount_eq_sub (n : ℕ) (ω : Configuration (Fin n)) :
    SitePerc.closedCount ω = n - SitePerc.openCount ω := by
  have hcount : SitePerc.openCount ω + SitePerc.closedCount ω = n := by
    simpa [SitePerc.openCount, SitePerc.closedCount, Bool.not_eq_true] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (fun v => ω v = true)
  omega

theorem configWeight_maskConfiguration (n : ℕ) (p : Parameter) (mask : Fin (2 ^ n)) :
    configWeight p (maskConfiguration n mask) =
      p.val ^ openCount n mask.val * (1 - p.val) ^ (n - openCount n mask.val) := by
  rw [configWeight, configuration_closedCount_eq_sub,
    ← openCount_eq_configuration_count]

theorem sum_configuration_eq_sum_masks {R : Type*} [AddCommMonoid R] (n : ℕ)
    (F : Configuration (Fin n) → R) :
    ∑ ω : Configuration (Fin n), F ω = ∑ mask : Fin (2 ^ n), F (maskConfiguration n mask) := by
  exact (Equiv.sum_comp (maskEquivConfiguration n) F).symm

/-- The original extraction function is preserved in every summand. -/
theorem finiteStateLaw_mass_eq_masks {S : Type} [Fintype S] [DecidableEq S]
    (n : ℕ) (p : Parameter) (f : Configuration (Fin n) → S) (s : S) :
    (finiteStateLaw p f).mass s =
      ∑ mask : Fin (2 ^ n), if f (maskConfiguration n mask) = s then
        p.val ^ openCount n mask.val * (1 - p.val) ^ (n - openCount n mask.val) else 0 := by
  rw [finiteStateLaw_mass, sum_configuration_eq_sum_masks n]
  apply Finset.sum_congr rfl
  intro mask _
  rw [configWeight_maskConfiguration]

/-- The actual iid state law equals the exact producer-style Nat range sum. -/
theorem finiteStateLaw_mass_eq_range {S : Type} [Fintype S] [DecidableEq S]
    (n : ℕ) (p : Parameter) (f : Configuration (Fin n) → S) (s : S) :
    (finiteStateLaw p f).mass s =
      ∑ mask ∈ Finset.range (2 ^ n), if f (fun v => mask.testBit v.val) = s then
        p.val ^ openCount n mask * (1 - p.val) ^ (n - openCount n mask) else 0 := by
  rw [finiteStateLaw_mass_eq_masks]
  exact Fin.sum_univ_eq_sum_range
    (fun mask => if f (fun v => mask.testBit v.val) = s then
      p.val ^ openCount n mask * (1 - p.val) ^ (n - openCount n mask) else 0) (2 ^ n)

end SitePerc.Checker

#print axioms SitePerc.Checker.maskConfiguration
#print axioms SitePerc.Checker.maskEquivConfiguration
#print axioms SitePerc.Checker.maskEquivConfiguration_apply
#print axioms SitePerc.Checker.openCount_eq_bit_sum
#print axioms SitePerc.Checker.openCount_eq_configuration_count
#print axioms SitePerc.Checker.configuration_closedCount_eq_sub
#print axioms SitePerc.Checker.configWeight_maskConfiguration
#print axioms SitePerc.Checker.sum_configuration_eq_sum_masks
#print axioms SitePerc.Checker.finiteStateLaw_mass_eq_masks
#print axioms SitePerc.Checker.finiteStateLaw_mass_eq_range
