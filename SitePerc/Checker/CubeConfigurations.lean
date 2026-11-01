import SitePerc.Checker.PrunedDefs
import SitePerc.Checker.MaskConfigurations
import Mathlib.Data.List.Permutation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Boundary/interior cubes are exact configurations

This module concerns pointwise Boolean cubes in the actual supplied vertex
order. No numerical interval between endpoint masks is interpreted as a cube.
The pruning and coefficient-refinement arguments are deliberately separate.
-/

open scoped BigOperators

namespace SitePerc.Checker

/-- Scatter low mask bits into the exact supplied vertex order. -/
def placedMask (vs : List ℕ) (mask : ℕ) : ℕ :=
  ∑ i : Fin vs.length, if mask.testBit i.val then 2 ^ vs[i.val] else 0

/-- A checked vertex partition gives a genuine coordinate equivalence. -/
noncomputable def partitionVertexEquiv {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n)) :
    (Fin vs.length ⊕ Fin ws.length) ≃ Fin n := by
  have hbound : ∀ v ∈ vs ++ ws, v < n := by
    intro v hv
    exact List.mem_range.mp (hp.mem_iff.mp hv)
  let vertex : (Fin vs.length ⊕ Fin ws.length) → Fin n := fun j =>
    match j with
    | Sum.inl i => ⟨vs[i.val], hbound _ (List.mem_append_left _ (List.getElem_mem i.isLt))⟩
    | Sum.inr i => ⟨ws[i.val], hbound _ (List.mem_append_right _ (List.getElem_mem i.isLt))⟩
  have hnd : (vs ++ ws).Nodup := hp.nodup_iff.mpr List.nodup_range
  obtain ⟨hv, hw, hd⟩ := List.nodup_append.mp hnd
  have hinj : Function.Injective vertex := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        congr 1
        exact hv.injective_get (congrArg Fin.val hab)
      | inr b =>
        exact False.elim (hd _ (List.getElem_mem a.isLt) _
          (List.getElem_mem b.isLt) (congrArg Fin.val hab))
    | inr a =>
      cases b with
      | inl b =>
        exact False.elim (hd _ (List.getElem_mem b.isLt) _
          (List.getElem_mem a.isLt) (congrArg Fin.val hab).symm)
      | inr b =>
        congr 1
        exact hw.injective_get (congrArg Fin.val hab)
  exact Equiv.ofBijective vertex
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by
      simpa only [Fintype.card_sum, Fintype.card_fin, List.length_append, List.length_range]
        using hp.length_eq⟩)

/-- Product masks are joined through the checked partition and the proved
all-mask/configuration equivalence. Its numerical forward formula is proved
below, rather than assumed as a coverage witness. -/
noncomputable def partitionMaskEquiv {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n)) :
    (Fin (2 ^ vs.length) × Fin (2 ^ ws.length)) ≃ Fin (2 ^ n) :=
  (Equiv.prodCongr (maskEquivConfiguration vs.length) (maskEquivConfiguration ws.length)).trans
    (((Equiv.sumArrowEquivProdArrow (Fin vs.length) (Fin ws.length) Bool).symm).trans
      (((partitionVertexEquiv vs ws hp).arrowCongr (Equiv.refl Bool)).trans
        (maskEquivConfiguration n).symm))


/-- The exact mask and k updates along one reference-tree assignment. -/
def cubePath : List ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | [], base, k, _ => (base, k)
  | v :: vs, base, k, mask =>
    if mask.testBit 0 then cubePath vs (base + 2 ^ v) (k + 1) (mask / 2)
    else cubePath vs base k (mask / 2)

theorem bitSum_eq_mask (n mask : ℕ) (hm : mask < 2 ^ n) :
    (∑ i ∈ Finset.range n, if mask.testBit i then 2 ^ i else 0) = mask := by
  induction n generalizing mask with
  | zero =>
    have hz : mask = 0 := by simpa using hm
    simp [hz]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hl : mask < 2 ^ n
    · rw [Nat.testBit_lt_two_pow hl]
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih mask hl
    · have hge : 2 ^ n ≤ mask := Nat.le_of_not_gt hl
      have ht := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hge hm
      rw [ht]
      simp only [ite_true]
      have hlt : mask - 2 ^ n < 2 ^ n := by
        rw [pow_succ] at hm
        omega
      have hsum : (∑ i ∈ Finset.range n, if mask.testBit i then 2 ^ i else 0) =
          mask % 2 ^ n := by
        calc
          _ = ∑ i ∈ Finset.range n, if (mask % 2 ^ n).testBit i then 2 ^ i else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [Nat.testBit_mod_two_pow, Finset.mem_range.mp hi]
          _ = _ := ih (mask % 2 ^ n) (Nat.mod_lt mask (by positivity))
      have hlow : mask % 2 ^ n = mask - 2 ^ n := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
      rw [hsum, hlow]
      omega

theorem foldRange_selected_add (n mask : ℕ) (f : ℕ → ℕ) (base : ℕ) :
    (List.range n).foldl (fun a i => if mask.testBit i then a + f i else a) base =
      base + ∑ i ∈ Finset.range n, if mask.testBit i then f i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    rw [ih]
    split <;> simp_all [Nat.add_assoc]

theorem embedBoundary_eq_placedMask (boundary : Array ℕ) (mask : ℕ) :
    embedBoundary boundary mask = placedMask boundary.toList mask := by
  unfold embedBoundary placedMask
  rw [foldRange_selected_add, Nat.zero_add, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Array.length_toList]
  simp [getElem!_pos, i.isLt]

theorem placedMask_cons (v : ℕ) (vs : List ℕ) (mask : ℕ) :
    placedMask (v :: vs) mask = (if mask.testBit 0 then 2 ^ v else 0) + placedMask vs (mask / 2) := by
  unfold placedMask
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, List.getElem_cons_zero,
    Fin.val_succ, List.getElem_cons_succ, Nat.testBit_add_one]
  rfl

theorem openCount_shift_cons (r mask : ℕ) :
    openCount (r + 1) mask = (if mask.testBit 0 then 1 else 0) + openCount r (mask / 2) := by
  rw [openCount_eq_bit_sum, ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ,
    openCount_eq_bit_sum, ← Fin.sum_univ_eq_sum_range]
  simp only [Fin.val_zero, Fin.val_succ, Nat.testBit_add_one]
  rfl

theorem cubePath_eq (vs : List ℕ) (base k mask : ℕ) :
    cubePath vs base k mask = (base + placedMask vs mask, k + openCount vs.length mask) := by
  induction vs generalizing base k mask with
  | nil => simp [cubePath, placedMask, openCount]
  | cons v vs ih =>
    rw [cubePath, placedMask_cons, List.length_cons, openCount_shift_cons]
    split <;> simp_all [Nat.add_assoc]

theorem partitionVertexEquiv_inl {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n)) (i : Fin vs.length) :
    (partitionVertexEquiv vs ws hp (Sum.inl i)).val = vs[i.val] := by
  rfl

theorem partitionVertexEquiv_inr {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n)) (i : Fin ws.length) :
    (partitionVertexEquiv vs ws hp (Sum.inr i)).val = ws[i.val] := by
  rfl

theorem partitionMaskEquiv_bit_inl {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n))
    (bm : Fin (2 ^ vs.length)) (im : Fin (2 ^ ws.length)) (i : Fin vs.length) :
    (partitionMaskEquiv vs ws hp (bm, im)).val.testBit
      (partitionVertexEquiv vs ws hp (Sum.inl i)).val = bm.val.testBit i.val := by
  change (maskEquivConfiguration n) ((maskEquivConfiguration n).symm _)
    (partitionVertexEquiv vs ws hp (Sum.inl i)) = _
  rw [Equiv.apply_symm_apply]
  simp [Equiv.arrowCongr_apply, maskEquivConfiguration_apply]

theorem partitionMaskEquiv_bit_inr {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n))
    (bm : Fin (2 ^ vs.length)) (im : Fin (2 ^ ws.length)) (i : Fin ws.length) :
    (partitionMaskEquiv vs ws hp (bm, im)).val.testBit
      (partitionVertexEquiv vs ws hp (Sum.inr i)).val = im.val.testBit i.val := by
  change (maskEquivConfiguration n) ((maskEquivConfiguration n).symm _)
    (partitionVertexEquiv vs ws hp (Sum.inr i)) = _
  rw [Equiv.apply_symm_apply]
  simp [Equiv.arrowCongr_apply, maskEquivConfiguration_apply]

theorem partitionMaskEquiv_val {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n))
    (bm : Fin (2 ^ vs.length)) (im : Fin (2 ^ ws.length)) :
    (partitionMaskEquiv vs ws hp (bm, im)).val = placedMask vs bm.val + placedMask ws im.val := by
  let out := partitionMaskEquiv vs ws hp (bm, im)
  have hsum := bitSum_eq_mask n out.val out.isLt
  rw [← Fin.sum_univ_eq_sum_range] at hsum
  rw [← hsum]
  rw [← Equiv.sum_comp (partitionVertexEquiv vs ws hp)
    (fun v : Fin n => if out.val.testBit v.val then 2 ^ v.val else 0)]
  rw [Fintype.sum_sum_type]
  simp only [out]
  simp_rw [partitionMaskEquiv_bit_inl, partitionMaskEquiv_bit_inr]
  simp only [partitionVertexEquiv_inl, partitionVertexEquiv_inr, placedMask]

theorem partitionMaskEquiv_openCount {n : ℕ} (vs ws : List ℕ)
    (hp : (vs ++ ws).Perm (List.range n))
    (bm : Fin (2 ^ vs.length)) (im : Fin (2 ^ ws.length)) :
    openCount n (partitionMaskEquiv vs ws hp (bm, im)).val =
      openCount vs.length bm.val + openCount ws.length im.val := by
  rw [openCount_eq_bit_sum, ← Fin.sum_univ_eq_sum_range]
  rw [← Equiv.sum_comp (partitionVertexEquiv vs ws hp)
    (fun v : Fin n => if (partitionMaskEquiv vs ws hp (bm, im)).val.testBit v.val then 1 else 0)]
  rw [Fintype.sum_sum_type]
  simp only [partitionMaskEquiv_bit_inl, partitionMaskEquiv_bit_inr]
  simp only [openCount_eq_bit_sum, ← Fin.sum_univ_eq_sum_range]

/-- Distinct remaining coordinates are bounded and all unset in base. -/
def ValidCube (n : ℕ) (vs : List ℕ) (base : ℕ) : Prop :=
  vs.Nodup ∧ ∀ v ∈ vs, v < n ∧ base.testBit v = false


theorem testBit_add_pow_of_closed (base v : ℕ) (hv : base.testBit v = false) (i : ℕ) :
    (base + 2 ^ v).testBit i = (base.testBit i || decide (i = v)) := by
  induction v generalizing base i with
  | zero =>
    cases i with
    | zero =>
      have hm : base % 2 = 0 := by
        have hne : base % 2 ≠ 1 := by simpa [Nat.testBit_zero] using hv
        omega
      simp [Nat.testBit_zero, Nat.add_mod, hm]
    | succ i =>
      have hm : base % 2 = 0 := by
        have hne : base % 2 ≠ 1 := by simpa [Nat.testBit_zero] using hv
        omega
      have hd : (base + 1) / 2 = base / 2 := by omega
      simp [Nat.testBit_add_one, hd]
  | succ v ih =>
    cases i with
    | zero =>
      rw [Nat.add_comm, Nat.testBit_two_pow_add_gt (Nat.zero_lt_succ v)]
      simp
    | succ i =>
      have hv' : (base / 2).testBit v = false := by
        simpa only [Nat.testBit_add_one] using hv
      have hi := ih (base / 2) hv' i
      have hd : (base + 2 * 2 ^ v) / 2 = base / 2 + 2 ^ v :=
        Nat.add_mul_div_left base (2 ^ v) (by decide : 0 < 2)
      simpa only [Nat.testBit_add_one, pow_succ', hd, Nat.add_right_cancel_iff] using hi

theorem validCube_closed {n v base : ℕ} {vs : List ℕ}
    (h : ValidCube n (v :: vs) base) : ValidCube n vs base := by
  exact ⟨(List.nodup_cons.mp h.1).2,
    fun w hw => h.2 w (List.mem_cons_of_mem v hw)⟩

theorem validCube_open {n v base : ℕ} {vs : List ℕ}
    (h : ValidCube n (v :: vs) base) : ValidCube n vs (base + 2 ^ v) := by
  refine ⟨(List.nodup_cons.mp h.1).2, ?_⟩
  intro w hw
  refine ⟨(h.2 w (List.mem_cons_of_mem v hw)).1, ?_⟩
  rw [testBit_add_pow_of_closed base v (h.2 v (by simp)).2]
  have hwv : w ≠ v := by
    intro heq
    exact (List.nodup_cons.mp h.1).1 (heq ▸ hw)
  simp [(h.2 w (List.mem_cons_of_mem v hw)).2, hwv]

theorem validCube_upper_bits {n base : ℕ} {vs : List ℕ} (h : ValidCube n vs base) (i : ℕ) :
    (base + freeBits vs).testBit i = (base.testBit i || decide (i ∈ vs)) := by
  induction vs generalizing base with
  | nil => simp [freeBits]
  | cons v vs ih =>
    rw [freeBits, ← Nat.add_assoc, ih (validCube_open h),
      testBit_add_pow_of_closed base v (h.2 v (by simp)).2]
    simp [List.mem_cons, Bool.or_assoc]

theorem validCube_assignment_support {n base : ℕ} {vs : List ℕ} (h : ValidCube n vs base)
    (mask i : ℕ) :
    (base.testBit i = true → (base + placedMask vs mask).testBit i = true) ∧
    ((base + placedMask vs mask).testBit i = true → base.testBit i = true ∨ i ∈ vs) := by
  induction vs generalizing base mask with
  | nil => simp [placedMask]
  | cons v vs ih =>
    rw [placedMask_cons]
    by_cases hm : mask.testBit 0 = true
    · simp only [hm, ite_true, ← Nat.add_assoc]
      have hb := testBit_add_pow_of_closed base v (h.2 v (by simp)).2 i
      obtain ⟨hlo, hhi⟩ := ih (validCube_open h) (mask / 2)
      constructor
      · intro hi
        apply hlo
        rw [hb]
        simp [hi]
      · intro hi
        rcases hhi hi with hbase | hmem
        · rw [hb, Bool.or_eq_true] at hbase
          rcases hbase with hbase | hbit
          · exact Or.inl hbase
          · exact Or.inr (List.mem_cons.mpr (Or.inl (of_decide_eq_true hbit)))
        · exact Or.inr (List.mem_cons_of_mem v hmem)
    · simp only [hm, Bool.false_eq_true, ite_false, Nat.zero_add]
      obtain ⟨hlo, hhi⟩ := ih (validCube_closed h) (mask / 2)
      refine ⟨hlo, ?_⟩
      intro hi
      rcases hhi hi with hbase | hmem
      · exact Or.inl hbase
      · exact Or.inr (List.mem_cons_of_mem v hmem)

theorem validCube_assignment_bounds {n base : ℕ} {vs : List ℕ} (h : ValidCube n vs base)
    (mask i : ℕ) :
    (base.testBit i = true → (base + placedMask vs mask).testBit i = true) ∧
    ((base + placedMask vs mask).testBit i = true → (base + freeBits vs).testBit i = true) := by
  obtain ⟨hlo, hhi⟩ := validCube_assignment_support h mask i
  refine ⟨hlo, ?_⟩
  intro hi
  rw [validCube_upper_bits h, Bool.or_eq_true]
  rcases hhi hi with hbase | hmem
  · exact Or.inl hbase
  · exact Or.inr (by simpa using hmem)

/-- Only these small vertex lists are evaluated by the kernel. This does not
enumerate any of the exponentially many configurations. -/
theorem squareBoundary_interior_perm (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6) :
    ((squareBoundary m).toList ++ interiorVertices m).Perm (List.range (m * m)) := by
  rcases hm with rfl | rfl | rfl <;> decide +kernel

/-- Exact boundary/interior product-mask equivalence for the supported squares.
The actual additive embedding and exact reference-tree k are proved below. -/
noncomputable def boundaryCubeEquiv (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6) :
    (Fin (2 ^ (squareBoundary m).size) × Fin (2 ^ (interiorVertices m).length)) ≃
      Fin (2 ^ (m * m)) := by
  have hp : ((squareBoundary m).toList ++ interiorVertices m).Perm
      (List.range (m * m)) := by rcases hm with rfl | rfl | rfl <;> decide +kernel
  exact partitionMaskEquiv (squareBoundary m).toList (interiorVertices m) hp

theorem boundaryCubeEquiv_val (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size))
    (im : Fin (2 ^ (interiorVertices m).length)) :
    (boundaryCubeEquiv m hm (bm, im)).val =
      embedBoundary (squareBoundary m) bm.val + placedMask (interiorVertices m) im.val := by
  change (partitionMaskEquiv (squareBoundary m).toList (interiorVertices m) _ (bm, im)).val = _
  rw [partitionMaskEquiv_val, embedBoundary_eq_placedMask]

theorem boundaryCubeEquiv_bit_boundary (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size))
    (im : Fin (2 ^ (interiorVertices m).length)) (i : Fin (squareBoundary m).size) :
    (boundaryCubeEquiv m hm (bm, im)).val.testBit (squareBoundary m)[i.val] = bm.val.testBit i.val := by
  have hb := partitionMaskEquiv_bit_inl (squareBoundary m).toList (interiorVertices m)
    (squareBoundary_interior_perm m hm) bm im i
  rw [partitionVertexEquiv_inl] at hb
  exact hb

theorem boundaryCubeEquiv_bit_interior (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size))
    (im : Fin (2 ^ (interiorVertices m).length)) (i : Fin (interiorVertices m).length) :
    (boundaryCubeEquiv m hm (bm, im)).val.testBit (interiorVertices m)[i.val] = im.val.testBit i.val := by
  have hb := partitionMaskEquiv_bit_inr (squareBoundary m).toList (interiorVertices m)
    (squareBoundary_interior_perm m hm) bm im i
  rw [partitionVertexEquiv_inr] at hb
  exact hb

theorem boundaryCubeEquiv_openCount (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size))
    (im : Fin (2 ^ (interiorVertices m).length)) :
    openCount (m * m) (boundaryCubeEquiv m hm (bm, im)).val =
      openCount (squareBoundary m).size bm.val + openCount (interiorVertices m).length im.val := by
  exact partitionMaskEquiv_openCount (squareBoundary m).toList (interiorVertices m)
    (squareBoundary_interior_perm m hm) bm im

theorem embedBoundary_interior_false (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size)) (v : ℕ) (hv : v ∈ interiorVertices m) :
    (embedBoundary (squareBoundary m) bm.val).testBit v = false := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hb := boundaryCubeEquiv_bit_interior m hm bm 0 i
  rw [boundaryCubeEquiv_val] at hb
  simpa [placedMask, ← hi] using hb

theorem boundaryCube_valid (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size)) :
    ValidCube (m * m) (interiorVertices m) (embedBoundary (squareBoundary m) bm.val) := by
  have hp := squareBoundary_interior_perm m hm
  have hnd : ((squareBoundary m).toList ++ interiorVertices m).Nodup :=
    hp.nodup_iff.mpr List.nodup_range
  refine ⟨(List.nodup_append.mp hnd).2.1, ?_⟩
  intro v hv
  exact ⟨List.mem_range.mp (hp.mem_iff.mp (List.mem_append_right _ hv)),
    embedBoundary_interior_false m hm bm v hv⟩

theorem boundaryCube_disjoint_bits (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size))
    (im : Fin (2 ^ (interiorVertices m).length)) (i : ℕ) :
    (embedBoundary (squareBoundary m) bm.val).testBit i = true →
      (placedMask (interiorVertices m) im.val).testBit i = false := by
  intro hb
  have hv := boundaryCube_valid m hm bm
  have hz : ValidCube (m * m) (interiorVertices m) 0 :=
    ⟨hv.1, fun v hmem => ⟨(hv.2 v hmem).1, by simp⟩⟩
  cases hi : (placedMask (interiorVertices m) im.val).testBit i
  · rfl
  · have hmem : i ∈ interiorVertices m := by
      have hs := (validCube_assignment_support hz im.val i).2 (by simpa using hi)
      simpa using hs
    rw [embedBoundary_interior_false m hm bm i hmem] at hb
    contradiction

theorem cubePath_boundary_exact (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6)
    (bm : Fin (2 ^ (squareBoundary m).size))
    (im : Fin (2 ^ (interiorVertices m).length)) :
    cubePath (interiorVertices m) (embedBoundary (squareBoundary m) bm.val)
      (openCount (squareBoundary m).size bm.val) im.val =
      ((boundaryCubeEquiv m hm (bm, im)).val,
        openCount (m * m) (boundaryCubeEquiv m hm (bm, im)).val) := by
  rw [cubePath_eq, ← boundaryCubeEquiv_val, boundaryCubeEquiv_openCount]

theorem boundaryCube_unique_mask (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6) (mask : Fin (2 ^ (m * m))) :
    ∃! pair : Fin (2 ^ (squareBoundary m).size) × Fin (2 ^ (interiorVertices m).length),
      embedBoundary (squareBoundary m) pair.1.val + placedMask (interiorVertices m) pair.2.val = mask.val := by
  let e := boundaryCubeEquiv m hm
  refine ⟨e.symm mask, ?_, ?_⟩
  · change embedBoundary (squareBoundary m) (e.symm mask).1.val +
      placedMask (interiorVertices m) (e.symm mask).2.val = mask.val
    exact (boundaryCubeEquiv_val m hm (e.symm mask).1 (e.symm mask).2).symm.trans
      (congrArg Fin.val (e.apply_symm_apply mask))
  · rintro ⟨bm, im⟩ hpair
    apply e.injective
    calc
      e (bm, im) = mask := Fin.ext ((boundaryCubeEquiv_val m hm bm im).trans hpair)
      _ = e (e.symm mask) := (e.apply_symm_apply mask).symm

theorem sum_masks_eq_boundary_cubes {R : Type*} [AddCommMonoid R]
    (m : ℕ) (hm : m = 2 ∨ m = 4 ∨ m = 6) (F : ℕ → R) :
    ∑ mask : Fin (2 ^ (m * m)), F mask.val =
      ∑ bm : Fin (2 ^ (squareBoundary m).size),
        ∑ im : Fin (2 ^ (interiorVertices m).length),
          F (embedBoundary (squareBoundary m) bm.val + placedMask (interiorVertices m) im.val) := by
  calc
    _ = ∑ pair, F (boundaryCubeEquiv m hm pair).val :=
      (Equiv.sum_comp (boundaryCubeEquiv m hm) (fun mask => F mask.val)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [boundaryCubeEquiv_val]

end SitePerc.Checker

/- Full implemented dependency closure: only the standard classical axioms. -/
#print axioms SitePerc.Checker.placedMask
#print axioms SitePerc.Checker.partitionVertexEquiv
#print axioms SitePerc.Checker.partitionMaskEquiv
#print axioms SitePerc.Checker.cubePath
#print axioms SitePerc.Checker.ValidCube
#print axioms SitePerc.Checker.boundaryCubeEquiv
#print axioms SitePerc.Checker.bitSum_eq_mask
#print axioms SitePerc.Checker.foldRange_selected_add
#print axioms SitePerc.Checker.embedBoundary_eq_placedMask
#print axioms SitePerc.Checker.placedMask_cons
#print axioms SitePerc.Checker.openCount_shift_cons
#print axioms SitePerc.Checker.cubePath_eq
#print axioms SitePerc.Checker.partitionVertexEquiv_inl
#print axioms SitePerc.Checker.partitionVertexEquiv_inr
#print axioms SitePerc.Checker.partitionMaskEquiv_bit_inl
#print axioms SitePerc.Checker.partitionMaskEquiv_bit_inr
#print axioms SitePerc.Checker.partitionMaskEquiv_val
#print axioms SitePerc.Checker.partitionMaskEquiv_openCount
#print axioms SitePerc.Checker.testBit_add_pow_of_closed
#print axioms SitePerc.Checker.validCube_closed
#print axioms SitePerc.Checker.validCube_open
#print axioms SitePerc.Checker.validCube_upper_bits
#print axioms SitePerc.Checker.validCube_assignment_support
#print axioms SitePerc.Checker.validCube_assignment_bounds
#print axioms SitePerc.Checker.squareBoundary_interior_perm
#print axioms SitePerc.Checker.boundaryCubeEquiv_val
#print axioms SitePerc.Checker.boundaryCubeEquiv_bit_boundary
#print axioms SitePerc.Checker.boundaryCubeEquiv_bit_interior
#print axioms SitePerc.Checker.boundaryCubeEquiv_openCount
#print axioms SitePerc.Checker.embedBoundary_interior_false
#print axioms SitePerc.Checker.boundaryCube_valid
#print axioms SitePerc.Checker.boundaryCube_disjoint_bits
#print axioms SitePerc.Checker.cubePath_boundary_exact
#print axioms SitePerc.Checker.boundaryCube_unique_mask
#print axioms SitePerc.Checker.sum_masks_eq_boundary_cubes
