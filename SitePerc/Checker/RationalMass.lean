import SitePerc.Checker.NativeDefs
import SitePerc.Flow
import SitePerc.FiniteProbability
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Exact rational arithmetic semantics for checker masses

The native numerator and weights are used unchanged. Natural-number subtraction,
division and arbitrary-precision arithmetic are preserved. This module does not
prove coefficient enumeration, support/parser completeness, packed state order
or sparse-flow replay.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SitePerc.Checker

/-- The actual tail-recursive numerator is its finite natural dot product. -/
theorem numerator_eq_sum (cs ws : Array Nat) :
    numerator cs ws = ∑ k ∈ Finset.range cs.size, cs[k]! * ws[k]! := by
  have hfold (t z : Nat) :
      (List.range t).foldl (fun z k => z + cs[k]! * ws[k]!) z =
        z + ∑ k ∈ Finset.range t, cs[k]! * ws[k]! := by
    induction t with
    | zero => simp
    | succ t ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ih, Finset.sum_range_succ]
      omega
  simpa only [numerator, Nat.zero_add] using hfold cs.size 0

/-- Rational Bernoulli weights, including both endpoint parameters. -/
theorem bernoulli_weight_rational (p : Parameter) (n k a d : Nat)
    (hd : 0 < d) (ha : a ≤ d) (hk : k ≤ n)
    (hp : p.val = (a : ℝ) / d) :
    (a^k * (d-a)^(n-k) : Nat) / (d : ℝ)^n =
      p.val^k * (1-p.val)^(n-k) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hsub : ((d-a : Nat) : ℝ) = (d : ℝ) - a := Nat.cast_sub ha
  have hcomp : 1-p.val = ((d-a : Nat) : ℝ) / d := by
    rw [hp, hsub]
    field_simp
    <;> ring
  rw [hcomp, hp]
  simp only [Nat.cast_mul, Nat.cast_pow, div_pow]
  rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hk]

/-- Exact semantic identity for the checker's actual coefficient arrays. -/
theorem rational_numerator_eq_sum (p : Parameter) (n a d : Nat)
    (hd : 0 < d) (ha : a ≤ d) (hp : p.val = (a : ℝ) / d)
    (cs : Array Nat) (hlen : cs.size = n+1) :
    (numerator cs (weights n a d) : ℝ) / (d : ℝ)^n =
      ∑ k ∈ Finset.range (n+1), (cs[k]! : ℝ) * p.val^k * (1-p.val)^(n-k) := by
  rw [numerator_eq_sum, hlen, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hw : (weights n a d)[k]! = a^k * (d-a)^(n-k) := by
    simp [weights, hkn]
  rw [Nat.cast_mul, hw, mul_div_assoc, bernoulli_weight_rational p n k a d hd ha hkn hp]
  ring

/-- The exact Nat upward formula bounds the scaled rational mass from above. -/
theorem nat_upward_rounds_up (scale num den : Nat) (hd : 0 < den) :
    (scale : ℝ) * ((num : ℝ) / den) ≤
      (((scale*num+den-1)/den : Nat) : ℝ) := by
  have hb : scale*num ≤ den * ((scale*num+den-1)/den) := by
    simpa only [Nat.ceilDiv_eq_add_pred_div, smul_eq_mul] using
      (le_smul_ceilDiv (α := Nat) (β := Nat) (b := scale*num) hd)
  have hdr : (0 : ℝ) < den := by exact_mod_cast hd
  rw [← mul_div_assoc, div_le_iff₀ hdr]
  exact_mod_cast (by simpa only [Nat.mul_comm den] using hb)

/-- The exact Nat floor formula bounds the scaled rational mass from below. -/
theorem nat_floor_rounds_down (scale num den : Nat) (hd : 0 < den) :
    (((scale*num/den : Nat)) : ℝ) ≤ (scale : ℝ) * ((num : ℝ) / den) := by
  have hb := Nat.div_mul_le_self (scale*num) den
  have hdr : (0 : ℝ) < den := by exact_mod_cast hd
  rw [← mul_div_assoc, le_div_iff₀ hdr]
  exact_mod_cast hb

/-- Positive exact mass cannot disappear under the actual upward formula. -/
theorem nat_upward_positive (scale num den : Nat)
    (hs : 0 < scale) (hn : 0 < num) (hd : 0 < den) :
    0 < (scale*num+den-1)/den := by
  have hround := nat_upward_rounds_up scale num den hd
  have hpos : (0 : ℝ) < (scale : ℝ) * ((num : ℝ) / den) :=
    mul_pos (by exact_mod_cast hs)
      (div_pos (by exact_mod_cast hn) (by exact_mod_cast hd))
  exact_mod_cast lt_of_lt_of_le hpos hround

/-- Only the explicit coefficient/full-configuration identification is needed
from C7; the right-hand side is the actual finite Bernoulli law. -/
theorem rational_numerator_eq_state_mass {S : Type} [Fintype S]
    (p : Parameter) (n a d : Nat) (hd : 0 < d) (ha : a ≤ d)
    (hp : p.val = (a : ℝ) / d) (X : Configuration (Fin n) → S) (s : S)
    (cs : Array Nat) (hlen : cs.size = n+1)
    (counts : (∑ k ∈ Finset.range (n+1),
      (cs[k]! : ℝ) * p.val^k * (1-p.val)^(n-k)) =
      ∑ ω : Configuration (Fin n), if X ω = s then configWeight p ω else 0) :
    (numerator cs (weights n a d) : ℝ) / (d : ℝ)^n =
      (finiteStateLaw p X).mass s := by
  rw [rational_numerator_eq_sum p n a d hd ha hp cs hlen, counts,
    finiteStateLaw_mass p X s]

/-- Feed the exact checker arithmetic into D's actual-law mass bounds.
The displayed coefficient identities remain explicit obligations; neither
coefficient enumeration nor parser/support completeness is claimed here. -/
theorem massBounds_of_rational_counts {S : Type} [Fintype S]
    (n : Nat) (data : IntegerFlowData S) (p q : Parameter)
    (a d b e : Nat) (hd : 0 < d) (ha : a ≤ d) (he : 0 < e) (hb : b ≤ e)
    (hp : p.val = (a : ℝ)/d) (hq : q.val = (b : ℝ)/e)
    (X Y : Configuration (Fin n) → S) (src dst : S → Array Nat)
    (hsrc : ∀ s, (src s).size = n+1) (hdst : ∀ s, (dst s).size = n+1)
    (src_counts : ∀ s, (∑ k ∈ Finset.range (n+1),
      ((src s)[k]! : ℝ) * p.val^k * (1-p.val)^(n-k)) =
      ∑ ω : Configuration (Fin n), if X ω = s then configWeight p ω else 0)
    (dst_counts : ∀ s, (∑ k ∈ Finset.range (n+1),
      ((dst s)[k]! : ℝ) * q.val^k * (1-q.val)^(n-k)) =
      ∑ ω : Configuration (Fin n), if Y ω = s then configWeight q ω else 0)
    (key : S → Nat) (key_zero : ∀ s, key s = 0 ↔ s = data.bottom)
    (source : ∀ s, data.supply s = ((if key s == 0 then 0 else
      (data.scale * numerator (src s) (weights n a d) + d^n - 1)/(d^n) : Nat) : ℤ))
    (sink : ∀ s, data.capacity s =
      ((data.scale * numerator (dst s) (weights n b e) / (e^n) : Nat) : ℤ)) :
    data.MassBounds (finiteStateLaw p X) (finiteStateLaw q Y) := by
  constructor
  · intro s hs
    have hk : key s ≠ 0 := fun hz => hs ((key_zero s).mp hz)
    have hmass := rational_numerator_eq_state_mass p n a d hd ha hp X s
      (src s) (hsrc s) (src_counts s)
    have hround := nat_upward_rounds_up data.scale
      (numerator (src s) (weights n a d)) (d^n) (pow_pos hd n)
    simp only [Nat.cast_pow] at hround
    rw [hmass] at hround
    rw [source s]
    simpa only [beq_iff_eq, hk, ↓reduceIte, Int.cast_natCast] using hround
  · intro s
    have hmass := rational_numerator_eq_state_mass q n b e he hb hq Y s
      (dst s) (hdst s) (dst_counts s)
    have hround := nat_floor_rounds_down data.scale
      (numerator (dst s) (weights n b e)) (e^n) (pow_pos he n)
    simp only [Nat.cast_pow] at hround
    rw [hmass] at hround
    rw [sink s]
    simpa only [Int.cast_natCast] using hround

/-- At positive actual scale, zero supply is impossible for any non-bottom
state of positive actual Bernoulli state mass, including sparse omissions. -/
theorem positive_nonbottom_mass_has_supply {S : Type} [Fintype S]
    (n : Nat) (data : IntegerFlowData S) (p q : Parameter)
    (X Y : Configuration (Fin n) → S)
    (bounds : data.MassBounds (finiteStateLaw p X) (finiteStateLaw q Y))
    (hscale : 0 < data.scale) (s : S) (hs : s ≠ data.bottom)
    (hmass : 0 < (finiteStateLaw p X).mass s) : 0 < data.supply s := by
  have hpos : (0 : ℝ) < data.supply s :=
    lt_of_lt_of_le (mul_pos (by exact_mod_cast hscale) hmass)
      (bounds.source_rounds_up s hs)
  exact_mod_cast hpos

#print axioms numerator_eq_sum
#print axioms bernoulli_weight_rational
#print axioms rational_numerator_eq_sum
#print axioms nat_upward_rounds_up
#print axioms nat_floor_rounds_down
#print axioms nat_upward_positive
#print axioms rational_numerator_eq_state_mass
#print axioms massBounds_of_rational_counts
#print axioms positive_nonbottom_mass_has_supply

end SitePerc.Checker
