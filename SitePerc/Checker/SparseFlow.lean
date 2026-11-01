import SitePerc.Checker.SparseFlowDefs
import SitePerc.Flow
import Mathlib.Tactic

/-!
# Exact sparse-flow balance replay

The executable replay performs the same two sequential integer updates as a
sparse certificate consumer.  Arc occurrences are never deduplicated.
-/

open scoped BigOperators

namespace SitePerc.Checker

/-- Exact outgoing total, with one summand for every arc occurrence. -/
def sparseOutgoing (arcs : Array SparseArc) (i : Nat) : Int :=
  (arcs.toList.map (fun a => if a.1 = i then a.2.2 else 0)).sum

/-- Exact incoming total, with one summand for every arc occurrence. -/
def sparseIncoming (arcs : Array SparseArc) (i : Nat) : Int :=
  (arcs.toList.map (fun a => if a.2.1 = i then a.2.2 else 0)).sum

/-- The dense semantic edge function of the sparse multiset of arc occurrences.
This is a specification, not an instruction to materialize a dense matrix. -/
def sparseEdge {M : Nat} (arcs : Array SparseArc) (s t : Fin M) : Int :=
  (arcs.toList.map
    (fun a => if a.1 = s.val ∧ a.2.1 = t.val then a.2.2 else 0)).sum

/-- Every endpoint belongs to the complete finite node index space. -/
def sparseEndpoints (M : Nat) (arcs : Array SparseArc) : Prop :=
  ∀ a ∈ arcs.toList, a.1 < M ∧ a.2.1 < M

/-- Initial balance array for exact supply minus absorbed mass. -/
def replayInitial {M : Nat} (supply absorbed : Fin M → Int) : Array Int :=
  Array.ofFn (fun i => supply i - absorbed i)

/-- Individual sparse updates preserve the size, even for a self-loop. -/
theorem replayArc_size (initial : Array Int) (a : SparseArc) :
    (replayArc initial a).size = initial.size := by
  simp only [replayArc, Array.size_modify]

/-- Both incident contributions apply when source equals destination. -/
theorem replayArc_getElem (initial : Array Int) (a : SparseArc)
    (i : Fin initial.size) (h : i.val < (replayArc initial a).size) :
    (replayArc initial a)[i.val] = initial[i.val] -
      (if a.1 = i.val then a.2.2 else 0) +
      (if a.2.1 = i.val then a.2.2 else 0) := by
  simp only [replayArc, Array.getElem_modify, Array.size_modify]
  split_ifs <;> omega

/-- Sparse replay preserves the node index space. -/
theorem replayBalance_size (initial : Array Int) (arcs : Array SparseArc) :
    (replayBalance initial arcs).size = initial.size := by
  unfold replayBalance
  rw [← Array.foldl_toList]
  generalize arcs.toList = as
  induction as generalizing initial with
  | nil => rfl
  | cons a as ih =>
    simpa only [List.foldl_cons, replayArc_size] using ih (replayArc initial a)

/-- Exact coordinate meaning of the executable array fold.  The statement is
stronger than the endpoint-bounded case: irrelevant out-of-range updates do
not change a valid coordinate. -/
theorem replayBalance_getElem (initial : Array Int) (arcs : Array SparseArc)
    (i : Fin initial.size) (h : i.val < (replayBalance initial arcs).size) :
    (replayBalance initial arcs)[i.val] = initial[i.val] -
      sparseOutgoing arcs i.val + sparseIncoming arcs i.val := by
  have haux : ∀ (as : List SparseArc) (b : Array Int) (n : Nat)
      (hn : n < b.size) (hf : n < (as.foldl replayArc b).size),
      (as.foldl replayArc b)[n] = b[n] -
        (as.map (fun a => if a.1 = n then a.2.2 else 0)).sum +
        (as.map (fun a => if a.2.1 = n then a.2.2 else 0)).sum := by
    intro as
    induction as with
    | nil => intro b n hn hf; simp
    | cons a as ih =>
      intro b n hn hf
      have hn' : n < (replayArc b a).size := by
        simpa only [replayArc_size] using hn
      have hrec := ih (replayArc b a) n hn' hf
      have hstep := replayArc_getElem b a ⟨n, hn⟩ hn'
      calc
        _ = (replayArc b a)[n] -
            (as.map (fun a => if a.1 = n then a.2.2 else 0)).sum +
            (as.map (fun a => if a.2.1 = n then a.2.2 else 0)).sum := hrec
        _ = _ := by
          rw [hstep]
          simp only [List.map_cons, List.sum_cons]
          omega
  have hf : i.val < (arcs.toList.foldl replayArc initial).size := by
    simpa only [Array.foldl_toList, replayBalance] using h
  simpa only [Array.foldl_toList, replayBalance, sparseOutgoing, sparseIncoming]
    using haux arcs.toList initial i.val i.isLt hf

/-- Summing destinations retains exactly every outgoing arc occurrence.
Endpoint bounds are essential here: no flow may disappear outside `Fin M`. -/
theorem sparseEdge_sum_outgoing {M : Nat} (arcs : Array SparseArc)
    (bounds : sparseEndpoints M arcs) (i : Fin M) :
    (∑ j : Fin M, sparseEdge arcs i j) = sparseOutgoing arcs i.val := by
  unfold sparseEdge sparseOutgoing sparseEndpoints at *
  generalize arcs.toList = as at *
  revert bounds
  induction as with
  | nil => intro bounds; simp
  | cons a as ih =>
    intro bounds
    have ha := bounds a (by simp)
    have htail : ∀ b ∈ as, b.1 < M ∧ b.2.1 < M :=
      fun b hb => bounds b (by simp [hb])
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih htail]
    congr 1
    by_cases hs : a.1 = i.val
    · simp only [hs, true_and, ite_true]
      have one : (∑ j : Fin M,
          if (⟨a.2.1, ha.2⟩ : Fin M) = j then a.2.2 else 0) = a.2.2 := by simp
      simpa only [Fin.ext_iff] using one
    · simp [hs]

/-- Summing sources retains exactly every incoming arc occurrence. -/
theorem sparseEdge_sum_incoming {M : Nat} (arcs : Array SparseArc)
    (bounds : sparseEndpoints M arcs) (i : Fin M) :
    (∑ j : Fin M, sparseEdge arcs j i) = sparseIncoming arcs i.val := by
  unfold sparseEdge sparseIncoming sparseEndpoints at *
  generalize arcs.toList = as at *
  revert bounds
  induction as with
  | nil => intro bounds; simp
  | cons a as ih =>
    intro bounds
    have ha := bounds a (by simp)
    have htail : ∀ b ∈ as, b.1 < M ∧ b.2.1 < M :=
      fun b hb => bounds b (by simp [hb])
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih htail]
    congr 1
    by_cases ht : a.2.1 = i.val
    · simp only [ht, and_true, ite_true]
      have one : (∑ j : Fin M,
          if (⟨a.1, ha.1⟩ : Fin M) = j then a.2.2 else 0) = a.2.2 := by simp
      simpa only [Fin.ext_iff] using one
    · simp [ht]

/-- Acceptance of the actual zero-balance replay yields exact conservation
on every finite node.  Duplicates and self-loops require no separate cases. -/
theorem replayBalance_all_zero_conservation {M : Nat}
    (supply absorbed : Fin M → Int) (arcs : Array SparseArc)
    (bounds : sparseEndpoints M arcs)
    (zero : (replayBalance (replayInitial supply absorbed) arcs).all (· == 0) = true) :
    ∀ i : Fin M,
      supply i + ∑ j : Fin M, sparseEdge arcs j i =
        absorbed i + ∑ j : Fin M, sparseEdge arcs i j := by
  intro i
  let initial := replayInitial supply absorbed
  have hi : i.val < initial.size := by simpa [initial, replayInitial] using i.isLt
  have hf : i.val < (replayBalance initial arcs).size := by
    simpa only [replayBalance_size] using hi
  have hz : (replayBalance initial arcs)[i.val] = 0 := by
    simpa using (Array.all_eq_true.mp zero) i.val hf
  have hinit : initial[i.val] = supply i - absorbed i := by
    simp [initial, replayInitial]
  have hvalue := replayBalance_getElem initial arcs ⟨i.val, hi⟩ hf
  simp only [Fin.val_mk] at hvalue
  rw [hz, hinit] at hvalue
  rw [sparseEdge_sum_incoming arcs bounds i, sparseEdge_sum_outgoing arcs bounds i]
  omega

/-- Narrow adapter to the existing `IntegerFlowData` conservation field.
No source/capacity, order, or probability obligation is assumed or discharged. -/
theorem integerFlow_conservation_of_replayBalance {M : Nat}
    (d : IntegerFlowData (Fin M)) (arcs : Array SparseArc)
    (bounds : sparseEndpoints M arcs)
    (edge : ∀ i j, d.edge i j = sparseEdge arcs i j)
    (zero : (replayBalance (replayInitial d.supply d.absorbed) arcs).all (· == 0) = true) :
    ∀ i : Fin M,
      d.supply i + ∑ j : Fin M, d.edge j i =
        d.absorbed i + ∑ j : Fin M, d.edge i j := by
  intro i
  simpa only [edge] using
    replayBalance_all_zero_conservation d.supply d.absorbed arcs bounds zero i

end SitePerc.Checker

#print axioms SitePerc.Checker.replayArc_size
#print axioms SitePerc.Checker.replayArc_getElem
#print axioms SitePerc.Checker.replayBalance_size
#print axioms SitePerc.Checker.replayBalance_getElem
#print axioms SitePerc.Checker.sparseEdge_sum_outgoing
#print axioms SitePerc.Checker.sparseEdge_sum_incoming
#print axioms SitePerc.Checker.replayBalance_all_zero_conservation
#print axioms SitePerc.Checker.integerFlow_conservation_of_replayBalance
