import SitePerc.Base
import Mathlib.Tactic

/-!
# Rounded upward integer flows

This module proves soundness of a supplied finite flow certificate.  It does
not assume or prove optimality of the producer's max-flow computation.
-/

open scoped BigOperators

namespace SitePerc

/-- Positive scale, upward edges, exact conservation, and one-sided rounding
imply every upper-set inequality for the actual finite probability laws. -/
theorem flow_implies_domination {S : Type} [Fintype S] [Preorder S]
    (ν μ : FiniteLaw S) (f : RoundedFlow ν μ) : finiteDominates ν μ := by
  classical
  intro U hU
  by_cases hb : f.bottom ∈ U
  · have hfull : U = Finset.univ := Finset.eq_univ_iff_forall.mpr
      (fun s => hU f.bottom s hb (f.bottom_le s))
    rw [hfull, ν.total, μ.total]
  · have hout (x : S) (hx : x ∈ U) :
        ∑ y, f.edge x y = ∑ y ∈ U, f.edge x y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ U)
      intro y _ hy
      by_contra hne
      have hpos : 0 < f.edge x y :=
        lt_of_le_of_ne (f.edge_nonnegative x y) (Ne.symm hne)
      exact hy (hU x y hx (f.edge_increasing x y hpos))
    have hcut : (∑ x ∈ U, ∑ y, f.edge x y) ≤
        ∑ y ∈ U, ∑ x, f.edge x y := by
      calc
        (∑ x ∈ U, ∑ y, f.edge x y) =
            ∑ x ∈ U, ∑ y ∈ U, f.edge x y :=
          Finset.sum_congr rfl (fun x hx => hout x hx)
        _ = ∑ y ∈ U, ∑ x ∈ U, f.edge x y := Finset.sum_comm
        _ ≤ ∑ y ∈ U, ∑ x, f.edge x y := by
          apply Finset.sum_le_sum
          intro y _
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
            (fun x _ _ => f.edge_nonnegative x y)
    have hbalance : (∑ x ∈ U, f.supply x) + (∑ x ∈ U, ∑ y, f.edge y x) =
        (∑ x ∈ U, f.absorbed x) + (∑ x ∈ U, ∑ y, f.edge x y) := by
      simpa only [Finset.sum_add_distrib] using
        (Finset.sum_congr rfl (fun x (_ : x ∈ U) => f.conservation x))
    have hsupply : (∑ x ∈ U, f.supply x) ≤ ∑ x ∈ U, f.absorbed x := by
      linarith
    have hscaled : (f.scale : ℝ) * (∑ x ∈ U, ν.mass x) ≤
        (f.scale : ℝ) * (∑ x ∈ U, μ.mass x) := by
      calc
        (f.scale : ℝ) * (∑ x ∈ U, ν.mass x) ≤ ∑ x ∈ U, (f.supply x : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro x hx
          exact f.source_rounds_up x (fun heq => hb (heq ▸ hx))
        _ ≤ ∑ x ∈ U, (f.absorbed x : ℝ) := by exact_mod_cast hsupply
        _ ≤ ∑ x ∈ U, (f.capacity x : ℝ) := by
          apply Finset.sum_le_sum
          intro x _
          exact_mod_cast (f.absorbed_bounds x).2
        _ ≤ (f.scale : ℝ) * (∑ x ∈ U, μ.mass x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun x _ => f.sink_rounds_down x)
    exact le_of_mul_le_mul_left hscaled (by exact_mod_cast f.scale_positive)

/-- A proof-free, arbitrary-precision integer flow on the complete finite state
space.  A sparse implementation may extend omitted nodes and arcs by zero. -/
structure IntegerFlowData (S : Type) where
  scale : ℕ
  bottom : S
  supply : S → ℤ
  capacity : S → ℤ
  absorbed : S → ℤ
  edge : S → S → ℤ

namespace IntegerFlowData

/-- Integer-only obligations: these contain no probability law or domination
assumption.  In particular, all edges are checked in the actual state order. -/
structure Valid {S : Type} [Fintype S] [Preorder S]
    (d : IntegerFlowData S) : Prop where
  scale_positive : 0 < d.scale
  bottom_le : ∀ s, d.bottom ≤ s
  supply_nonnegative : ∀ s, 0 ≤ d.supply s
  capacity_nonnegative : ∀ s, 0 ≤ d.capacity s
  absorbed_bounds : ∀ s, 0 ≤ d.absorbed s ∧ d.absorbed s ≤ d.capacity s
  edge_nonnegative : ∀ x y, 0 ≤ d.edge x y
  edge_increasing : ∀ x y, 0 < d.edge x y → x ≤ y
  bottom_supply : d.supply d.bottom = 0
  conservation : ∀ s,
    d.supply s + ∑ x, d.edge x s = d.absorbed s + ∑ y, d.edge s y

/-- A pure finite reference check for the integer obligations only.  This is a
semantic specification, not a recommendation to materialize a dense matrix.
A streaming checker can instead prove `Valid` from its own sparse checks. -/
def check {S : Type} [Fintype S] [Preorder S] [DecidableLE S]
    (d : IntegerFlowData S) : Bool :=
  decide (
    0 < d.scale ∧
    (∀ s, d.bottom ≤ s) ∧
    (∀ s, 0 ≤ d.supply s) ∧
    (∀ s, 0 ≤ d.capacity s) ∧
    (∀ s, 0 ≤ d.absorbed s ∧ d.absorbed s ≤ d.capacity s) ∧
    (∀ x y, 0 ≤ d.edge x y) ∧
    (∀ x y, 0 < d.edge x y → x ≤ y) ∧
    d.supply d.bottom = 0 ∧
    (∀ s, d.supply s + ∑ x, d.edge x s = d.absorbed s + ∑ y, d.edge s y))

/-- The separate C5-C7 interface.  These bounds concern the actual finite laws,
not unverified tables.  In particular the source bound also covers every
non-bottom state omitted from a sparse node table. -/
structure MassBounds {S : Type} [Fintype S] (d : IntegerFlowData S)
    (ν μ : FiniteLaw S) : Prop where
  source_rounds_up : ∀ s, s ≠ d.bottom → (d.scale : ℝ) * ν.mass s ≤ d.supply s
  sink_rounds_down : ∀ s, (d.capacity s : ℝ) ≤ (d.scale : ℝ) * μ.mass s

/-- Assemble the shared `RoundedFlow` without changing either finite law. -/
def toRoundedFlow {S : Type} [Fintype S] [Preorder S]
    (d : IntegerFlowData S) {ν μ : FiniteLaw S}
    (valid : d.Valid) (bounds : d.MassBounds ν μ) : RoundedFlow ν μ where
  scale := d.scale
  scale_positive := valid.scale_positive
  bottom := d.bottom
  bottom_le := valid.bottom_le
  supply := d.supply
  capacity := d.capacity
  absorbed := d.absorbed
  edge := d.edge
  supply_nonnegative := valid.supply_nonnegative
  capacity_nonnegative := valid.capacity_nonnegative
  absorbed_bounds := valid.absorbed_bounds
  edge_nonnegative := valid.edge_nonnegative
  edge_increasing := valid.edge_increasing
  bottom_supply := valid.bottom_supply
  source_rounds_up := bounds.source_rounds_up
  sink_rounds_down := bounds.sink_rounds_down
  conservation := valid.conservation

/-- Reflection of the pure finite integer checks into their explicit
arithmetic specification. -/
theorem check_sound {S : Type} [Fintype S] [Preorder S] [DecidableLE S]
    (d : IntegerFlowData S) (h : d.check = true) : d.Valid := by
  unfold check at h
  have hspec := of_decide_eq_true h
  rcases hspec with ⟨hscale, hbottom, hsupply, hcapacity, habsorbed,
    hedge, hincreasing, hzero, hconservation⟩
  exact ⟨hscale, hbottom, hsupply, hcapacity, habsorbed,
    hedge, hincreasing, hzero, hconservation⟩

/-- Exact ceiling/floor data imply the semantic, one-sided rounding bounds. -/
theorem massBounds_of_rounding {S : Type} [Fintype S]
    (d : IntegerFlowData S) (ν μ : FiniteLaw S)
    (source : ∀ s, s ≠ d.bottom → d.supply s = ⌈(d.scale : ℝ) * ν.mass s⌉)
    (sink : ∀ s, d.capacity s = ⌊(d.scale : ℝ) * μ.mass s⌋) :
    d.MassBounds ν μ := by
  constructor
  · intro s hs
    rw [source s hs]
    exact Int.le_ceil _
  · intro s
    rw [sink s]
    exact Int.floor_le _

/-- Soundness endpoint for a pure integer checker plus its actual-law bridge.
Acceptance of the integer check alone is deliberately not sufficient. -/
theorem check_implies_domination {S : Type} [Fintype S] [Preorder S] [DecidableLE S]
    (d : IntegerFlowData S) (ν μ : FiniteLaw S)
    (checked : d.check = true) (bounds : d.MassBounds ν μ) :
    finiteDominates ν μ :=
  flow_implies_domination ν μ (d.toRoundedFlow (d.check_sound checked) bounds)

end IntegerFlowData

end SitePerc

#print axioms SitePerc.flow_implies_domination
#print axioms SitePerc.IntegerFlowData.toRoundedFlow
#print axioms SitePerc.IntegerFlowData.check_sound
#print axioms SitePerc.IntegerFlowData.massBounds_of_rounding
#print axioms SitePerc.IntegerFlowData.check_implies_domination
