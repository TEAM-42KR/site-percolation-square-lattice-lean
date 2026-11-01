/-
Real-valued fractional Hall theorem.
Adapted from AGT.fractional_hall, prove2.me submission
02256869-9a18-4f56-8484-c4f992e3c32e (korbonits).
The mathematical proof is reused; local names are qualified for this library.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

/-!
# The supply–demand theorem (fractional Hall)

We prove the bipartite supply–demand theorem by strong induction on
`|J| + |S|`, using four elementary transfer steps.

* **drop a buyer** with zero demand, or **drop a good** with zero capacity;
* **split** at a *tight* set of buyers `J₀` (`m(J₀) = c(Γ(J₀) ∩ S)`): the
  instance decomposes into `J₀ × (Γ(J₀) ∩ S)` and `(J ∖ J₀) × (S ∖ Γ(J₀))`,
  both feasible and both smaller when `J₀` is nonempty and proper;
* the **ε-step**: for a buyer `j₀` with positive demand and an adjacent good
  `a₀` with positive capacity, transfer `ε` units along `(j₀, a₀)`, where `ε`
  is the largest amount keeping the instance feasible — the minimum of `m j₀`,
  `c a₀`, and the slacks of the Hall inequalities that `(j₀, a₀)` tightens.

After the ε-step either `j₀` has zero demand, or `a₀` has zero capacity, or
some nonempty proper set of buyers has become tight; each case reduces to
strictly smaller instances.
-/

open Finset

namespace SitePercC.HallAux

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- The conclusion of the theorem: an exact transport. -/
def IsTransport (J : Finset B) (S : Finset A) (adj : B → Finset A) (m : B → ℝ) (c : A → ℝ)
    (x : B → A → ℝ) : Prop :=
  (∀ j a, 0 ≤ x j a) ∧ (∀ j a, x j a ≠ 0 → j ∈ J ∧ a ∈ S ∧ a ∈ adj j) ∧
  (∀ j ∈ J, ∑ a ∈ S, x j a = m j) ∧ (∀ a ∈ S, ∑ j ∈ J, x j a = c a)

/-- The hypotheses of the theorem. -/
def Feasible (J : Finset B) (S : Finset A) (adj : B → Finset A) (m : B → ℝ) (c : A → ℝ) :
    Prop :=
  (∀ j ∈ J, 0 ≤ m j) ∧ (∀ a ∈ S, 0 ≤ c a) ∧
  (∀ J' ⊆ J, ∑ j ∈ J', m j ≤ ∑ a ∈ J'.biUnion adj ∩ S, c a) ∧
  ∑ j ∈ J, m j = ∑ a ∈ S, c a

/-! ### Sum bookkeeping -/

theorem sum_eq_of_support {ι : Type*} {s₀ s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i, f i ≠ 0 → i ∈ s₀) (h : s₀ ⊆ s) : ∑ i ∈ s, f i = ∑ i ∈ s₀, f i :=
  (Finset.sum_subset h (fun i _ hi => by by_contra hne; exact hi (hf i hne))).symm

theorem sum_update_sub {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (i₀ : ι) (ε : ℝ) :
    ∑ i ∈ s, Function.update f i₀ (f i₀ - ε) i = ∑ i ∈ s, f i - if i₀ ∈ s then ε else 0 := by
  have h : ∀ i, Function.update f i₀ (f i₀ - ε) i = f i - if i = i₀ then ε else 0 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [hi]
  simp only [h]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-! ### Dropping a buyer with zero demand -/

theorem feasible_erase_buyer {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} (hF : Feasible J S adj m c) {j₀ : B} (hm : m j₀ = 0) :
    Feasible (J.erase j₀) S adj m c := by
  obtain ⟨hm0, hc0, hHall, htot⟩ := hF
  refine ⟨fun j hj => hm0 j (mem_of_mem_erase hj), hc0,
    fun J' hJ' => hHall J' (hJ'.trans (erase_subset _ _)), ?_⟩
  rw [Finset.sum_erase _ hm]
  exact htot

theorem transport_erase_buyer {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} {x : B → A → ℝ} {j₀ : B} (hm : m j₀ = 0)
    (hx : IsTransport (J.erase j₀) S adj m c x) : IsTransport J S adj m c x := by
  obtain ⟨h0, hsupp, hrow, hcol⟩ := hx
  have hx0 : ∀ a, x j₀ a = 0 := fun a => by
    by_contra hne
    exact notMem_erase j₀ J (hsupp j₀ a hne).1
  refine ⟨h0, fun j a h => ⟨mem_of_mem_erase (hsupp j a h).1, (hsupp j a h).2.1,
    (hsupp j a h).2.2⟩, ?_, ?_⟩
  · intro j hj
    by_cases h : j = j₀
    · subst h
      rw [hm]
      exact Finset.sum_eq_zero (fun a _ => hx0 a)
    · exact hrow j (mem_erase.2 ⟨h, hj⟩)
  · intro a ha
    rw [← Finset.sum_erase J (f := fun j => x j a) (hx0 a)]
    exact hcol a ha

/-! ### Dropping a good with zero capacity -/

theorem feasible_erase_good {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} (hF : Feasible J S adj m c) {a₀ : A} (hc : c a₀ = 0) :
    Feasible J (S.erase a₀) adj m c := by
  obtain ⟨hm0, hc0, hHall, htot⟩ := hF
  refine ⟨hm0, fun a ha => hc0 a (mem_of_mem_erase ha), fun J' hJ' => ?_, ?_⟩
  · rw [inter_erase, Finset.sum_erase _ hc]
    exact hHall J' hJ'
  · rw [Finset.sum_erase _ hc]
    exact htot

theorem transport_erase_good {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} {x : B → A → ℝ} {a₀ : A} (hc : c a₀ = 0)
    (hx : IsTransport J (S.erase a₀) adj m c x) : IsTransport J S adj m c x := by
  obtain ⟨h0, hsupp, hrow, hcol⟩ := hx
  have hx0 : ∀ j, x j a₀ = 0 := fun j => by
    by_contra hne
    exact notMem_erase a₀ S (hsupp j a₀ hne).2.1
  refine ⟨h0, fun j a h => ⟨(hsupp j a h).1, mem_of_mem_erase (hsupp j a h).2.1,
    (hsupp j a h).2.2⟩, ?_, ?_⟩
  · intro j hj
    rw [← Finset.sum_erase S (f := fun a => x j a) (hx0 j)]
    exact hrow j hj
  · intro a ha
    by_cases h : a = a₀
    · subst h
      rw [hc]
      exact Finset.sum_eq_zero (fun j _ => hx0 j)
    · exact hcol a (mem_erase.2 ⟨h, ha⟩)

/-! ### Splitting at a tight set of buyers -/

theorem feasible_split_left {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} (hF : Feasible J S adj m c) {J₀ : Finset B} (hJ₀ : J₀ ⊆ J)
    (htight : ∑ j ∈ J₀, m j = ∑ a ∈ J₀.biUnion adj ∩ S, c a) :
    Feasible J₀ (J₀.biUnion adj ∩ S) adj m c := by
  obtain ⟨hm0, hc0, hHall, htot⟩ := hF
  refine ⟨fun j hj => hm0 j (hJ₀ hj), fun a ha => hc0 a (mem_of_mem_inter_right ha),
    fun J' hJ' => ?_, htight⟩
  have heq : J'.biUnion adj ∩ (J₀.biUnion adj ∩ S) = J'.biUnion adj ∩ S := by
    ext a
    simp only [mem_inter, mem_biUnion]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨⟨j, hj, hja⟩, h3⟩; exact ⟨⟨j, hj, hja⟩, ⟨j, hJ' hj, hja⟩, h3⟩
  rw [heq]
  exact hHall J' (hJ'.trans hJ₀)

theorem feasible_split_right {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} (hF : Feasible J S adj m c) {J₀ : Finset B} (hJ₀ : J₀ ⊆ J)
    (htight : ∑ j ∈ J₀, m j = ∑ a ∈ J₀.biUnion adj ∩ S, c a) :
    Feasible (J \ J₀) (S \ (J₀.biUnion adj ∩ S)) adj m c := by
  obtain ⟨hm0, hc0, hHall, htot⟩ := hF
  set S₀ := J₀.biUnion adj ∩ S with hS₀
  have hS₀S : S₀ ⊆ S := inter_subset_right
  refine ⟨fun j hj => hm0 j ((mem_sdiff.1 hj).1), fun a ha => hc0 a ((mem_sdiff.1 ha).1),
    fun J' hJ' => ?_, ?_⟩
  · have hdisj : Disjoint J' J₀ := by
      rw [Finset.disjoint_left]
      intro j hj hj₀
      exact (mem_sdiff.1 (hJ' hj)).2 hj₀
    have hunion : J' ∪ J₀ ⊆ J := union_subset (hJ'.trans sdiff_subset) hJ₀
    have h := hHall (J' ∪ J₀) hunion
    rw [Finset.sum_union hdisj, union_biUnion] at h
    -- the goods reachable from `J' ∪ J₀` inside `S` contain `S₀`
    have hsub : S₀ ⊆ (J'.biUnion adj ∪ J₀.biUnion adj) ∩ S := by
      intro a ha
      rw [mem_inter] at ha ⊢
      exact ⟨mem_union_right _ ha.1, ha.2⟩
    have hsplit := Finset.sum_sdiff (f := c) hsub
    have heq : ((J'.biUnion adj ∪ J₀.biUnion adj) ∩ S) \ S₀ = J'.biUnion adj ∩ (S \ S₀) := by
      ext a
      simp only [hS₀, mem_sdiff, mem_inter, mem_union]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨?_, h2, h3⟩
        rcases h1 with h1 | h1
        · exact h1
        · exact absurd ⟨h1, h2⟩ h3
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨Or.inl h1, h2⟩, h3⟩
    rw [heq] at hsplit
    linarith
  · have hsplitJ := Finset.sum_sdiff (f := m) hJ₀
    have hsplitS := Finset.sum_sdiff (f := c) hS₀S
    linarith

theorem transport_split {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} {J₀ : Finset B} (hJ₀ : J₀ ⊆ J) {x₁ x₂ : B → A → ℝ}
    (hx₁ : IsTransport J₀ (J₀.biUnion adj ∩ S) adj m c x₁)
    (hx₂ : IsTransport (J \ J₀) (S \ (J₀.biUnion adj ∩ S)) adj m c x₂) :
    IsTransport J S adj m c (fun j a => x₁ j a + x₂ j a) := by
  obtain ⟨h0₁, hsupp₁, hrow₁, hcol₁⟩ := hx₁
  obtain ⟨h0₂, hsupp₂, hrow₂, hcol₂⟩ := hx₂
  set S₀ := J₀.biUnion adj ∩ S with hS₀
  have hS₀S : S₀ ⊆ S := inter_subset_right
  refine ⟨fun j a => add_nonneg (h0₁ j a) (h0₂ j a), ?_, ?_, ?_⟩
  · intro j a h
    change x₁ j a + x₂ j a ≠ 0 at h
    by_cases h1 : x₁ j a = 0
    · rw [h1, zero_add] at h
      obtain ⟨hj, ha, hadj⟩ := hsupp₂ j a h
      exact ⟨(mem_sdiff.1 hj).1, (mem_sdiff.1 ha).1, hadj⟩
    · obtain ⟨hj, ha, hadj⟩ := hsupp₁ j a h1
      exact ⟨hJ₀ hj, hS₀S ha, hadj⟩
  · intro j hj
    dsimp only
    rw [Finset.sum_add_distrib]
    by_cases hj₀ : j ∈ J₀
    · have e1 : ∑ a ∈ S, x₁ j a = m j := by
        rw [sum_eq_of_support (fun a ha => (hsupp₁ j a ha).2.1) hS₀S]
        exact hrow₁ j hj₀
      have e2 : ∑ a ∈ S, x₂ j a = 0 :=
        Finset.sum_eq_zero fun a _ => by
          by_contra hne
          exact (mem_sdiff.1 (hsupp₂ j a hne).1).2 hj₀
      rw [e1, e2, add_zero]
    · have hj' : j ∈ J \ J₀ := mem_sdiff.2 ⟨hj, hj₀⟩
      have e1 : ∑ a ∈ S, x₁ j a = 0 :=
        Finset.sum_eq_zero fun a _ => by
          by_contra hne
          exact hj₀ (hsupp₁ j a hne).1
      have e2 : ∑ a ∈ S, x₂ j a = m j := by
        rw [sum_eq_of_support (fun a ha => (hsupp₂ j a ha).2.1) sdiff_subset]
        exact hrow₂ j hj'
      rw [e1, e2, zero_add]
  · intro a ha
    dsimp only
    rw [Finset.sum_add_distrib]
    by_cases ha₀ : a ∈ S₀
    · have e1 : ∑ j ∈ J, x₁ j a = c a := by
        rw [sum_eq_of_support (fun j hj => (hsupp₁ j a hj).1) hJ₀]
        exact hcol₁ a ha₀
      have e2 : ∑ j ∈ J, x₂ j a = 0 :=
        Finset.sum_eq_zero fun j _ => by
          by_contra hne
          exact (mem_sdiff.1 (hsupp₂ j a hne).2.1).2 ha₀
      rw [e1, e2, add_zero]
    · have ha' : a ∈ S \ S₀ := mem_sdiff.2 ⟨ha, ha₀⟩
      have e1 : ∑ j ∈ J, x₁ j a = 0 :=
        Finset.sum_eq_zero fun j _ => by
          by_contra hne
          exact ha₀ (hsupp₁ j a hne).2.1
      have e2 : ∑ j ∈ J, x₂ j a = c a := by
        rw [sum_eq_of_support (fun j hj => (hsupp₂ j a hj).1) sdiff_subset]
        exact hcol₂ a ha'
      rw [e1, e2, zero_add]

/-! ### The ε-step -/

theorem feasible_eps {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} (hF : Feasible J S adj m c) {j₀ : B} {a₀ : A} (hj₀ : j₀ ∈ J) (ha₀ : a₀ ∈ S)
    (hadj : a₀ ∈ adj j₀) {ε : ℝ} (hεm : ε ≤ m j₀) (hεc : ε ≤ c a₀)
    (hεs : ∀ J' ⊆ J, j₀ ∉ J' → a₀ ∈ J'.biUnion adj →
      ∑ j ∈ J', m j + ε ≤ ∑ a ∈ J'.biUnion adj ∩ S, c a) :
    Feasible J S adj (Function.update m j₀ (m j₀ - ε)) (Function.update c a₀ (c a₀ - ε)) := by
  obtain ⟨hm0, hc0, hHall, htot⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases h : j = j₀
    · subst h; simp; linarith
    · rw [Function.update_of_ne h]; exact hm0 j hj
  · intro a ha
    by_cases h : a = a₀
    · subst h; simp; linarith
    · rw [Function.update_of_ne h]; exact hc0 a ha
  · intro J' hJ'
    rw [sum_update_sub, sum_update_sub]
    have h := hHall J' hJ'
    by_cases hj : j₀ ∈ J'
    · have ha : a₀ ∈ J'.biUnion adj ∩ S := mem_inter.2 ⟨mem_biUnion.2 ⟨j₀, hj, hadj⟩, ha₀⟩
      simp only [hj, ha, ite_true]
      linarith
    · by_cases ha : a₀ ∈ J'.biUnion adj
      · have ha' : a₀ ∈ J'.biUnion adj ∩ S := mem_inter.2 ⟨ha, ha₀⟩
        simp only [hj, ha', ite_true, ite_false]
        linarith [hεs J' hJ' hj ha]
      · have ha' : a₀ ∉ J'.biUnion adj ∩ S := fun h' => ha (mem_inter.1 h').1
        simp only [hj, ha', ite_false]
        linarith
  · rw [sum_update_sub, sum_update_sub]
    simp only [hj₀, ha₀, ite_true]
    linarith

theorem transport_eps {J : Finset B} {S : Finset A} {adj : B → Finset A} {m : B → ℝ}
    {c : A → ℝ} {j₀ : B} {a₀ : A} (hj₀ : j₀ ∈ J) (ha₀ : a₀ ∈ S) (hadj : a₀ ∈ adj j₀) {ε : ℝ}
    (hε0 : 0 ≤ ε) {x : B → A → ℝ}
    (hx : IsTransport J S adj (Function.update m j₀ (m j₀ - ε))
      (Function.update c a₀ (c a₀ - ε)) x) :
    IsTransport J S adj m c (fun j a => x j a + if j = j₀ ∧ a = a₀ then ε else 0) := by
  obtain ⟨h0, hsupp, hrow, hcol⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j a
    have : (0 : ℝ) ≤ if j = j₀ ∧ a = a₀ then ε else 0 := by split_ifs <;> simp [hε0]
    exact add_nonneg (h0 j a) this
  · intro j a h
    change x j a + (if j = j₀ ∧ a = a₀ then ε else 0) ≠ 0 at h
    by_cases hx0 : x j a = 0
    · rw [hx0, zero_add] at h
      by_cases hja : j = j₀ ∧ a = a₀
      · obtain ⟨rfl, rfl⟩ := hja
        exact ⟨hj₀, ha₀, hadj⟩
      · simp [hja] at h
    · exact hsupp j a hx0
  · intro j hj
    dsimp only
    rw [Finset.sum_add_distrib, hrow j hj]
    have : ∑ a ∈ S, (if j = j₀ ∧ a = a₀ then ε else 0) = if j = j₀ then ε else 0 := by
      by_cases hjj : j = j₀
      · simp only [hjj, true_and]
        rw [Finset.sum_ite_eq' S a₀ (fun _ => ε)]
        simp [ha₀]
      · simp [hjj]
    rw [this]
    by_cases hjj : j = j₀
    · subst hjj; simp
    · simp [hjj]
  · intro a ha
    dsimp only
    rw [Finset.sum_add_distrib, hcol a ha]
    have : ∑ j ∈ J, (if j = j₀ ∧ a = a₀ then ε else 0) = if a = a₀ then ε else 0 := by
      by_cases haa : a = a₀
      · simp only [haa, and_true]
        rw [Finset.sum_ite_eq' J j₀ (fun _ => ε)]
        simp [hj₀]
      · simp [haa]
    rw [this]
    by_cases haa : a = a₀
    · subst haa; simp
    · simp [haa]

/-! ### The induction -/

theorem main (n : ℕ) : ∀ (J : Finset B) (S : Finset A) (adj : B → Finset A) (m : B → ℝ)
    (c : A → ℝ), J.card + S.card = n → Feasible J S adj m c →
    ∃ x, IsTransport J S adj m c x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro J S adj m c hn hF
  rcases J.eq_empty_or_nonempty with hJ | ⟨j₀, hj₀⟩
  · -- no buyers: all capacities vanish
    subst hJ
    obtain ⟨-, hc0, -, htot⟩ := hF
    rw [Finset.sum_empty] at htot
    have hc : ∀ a ∈ S, c a = 0 := (Finset.sum_eq_zero_iff_of_nonneg hc0).1 htot.symm
    refine ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ h => absurd rfl h, fun j hj => by simp at hj,
      fun a ha => ?_⟩
    rw [Finset.sum_empty, hc a ha]
  by_cases hm0 : m j₀ = 0
  · -- drop the buyer `j₀`
    have hcard : (J.erase j₀).card + S.card < n := by
      rw [card_erase_of_mem hj₀]
      have := card_pos.2 ⟨j₀, hj₀⟩
      omega
    obtain ⟨x, hx⟩ := ih _ hcard (J.erase j₀) S adj m c rfl (feasible_erase_buyer hF hm0)
    exact ⟨x, transport_erase_buyer hm0 hx⟩
  have hmpos : 0 < m j₀ := lt_of_le_of_ne (hF.1 j₀ hj₀) (Ne.symm hm0)
  -- a good adjacent to `j₀` with positive capacity
  obtain ⟨a₀, ha₀adj, ha₀S, hca₀⟩ : ∃ a₀, a₀ ∈ adj j₀ ∧ a₀ ∈ S ∧ 0 < c a₀ := by
    by_contra hcon
    push Not at hcon
    have h1 := hF.2.2.1 {j₀} (by simpa using hj₀)
    rw [singleton_biUnion, sum_singleton] at h1
    have h2 : ∑ a ∈ adj j₀ ∩ S, c a ≤ 0 :=
      Finset.sum_nonpos fun a ha => hcon a (mem_inter.1 ha).1 (mem_inter.1 ha).2
    linarith
  -- the largest admissible transfer along `(j₀, a₀)`
  set F : Finset (Finset B) :=
    J.powerset.filter (fun J' => j₀ ∉ J' ∧ a₀ ∈ J'.biUnion adj) with hF_def
  set slack : Finset B → ℝ := fun J' => ∑ a ∈ J'.biUnion adj ∩ S, c a - ∑ j ∈ J', m j
    with hslack_def
  set E : Finset ℝ := insert (m j₀) (insert (c a₀) (F.image slack)) with hE_def
  have hEne : E.Nonempty := insert_nonempty _ _
  set ε := E.min' hEne with hε_def
  have hε_le : ∀ e ∈ E, ε ≤ e := fun e he => min'_le _ _ he
  have hε_mem : ε ∈ E := min'_mem _ _
  have hε_m : ε ≤ m j₀ := hε_le _ (mem_insert_self _ _)
  have hε_c : ε ≤ c a₀ := hε_le _ (mem_insert_of_mem (mem_insert_self _ _))
  have hslack_mem : ∀ J' ⊆ J, j₀ ∉ J' → a₀ ∈ J'.biUnion adj → slack J' ∈ E := by
    intro J' hJ' hj hA
    refine mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ ?_))
    rw [hF_def, mem_filter, mem_powerset]
    exact ⟨hJ', hj, hA⟩
  have hε_s : ∀ J' ⊆ J, j₀ ∉ J' → a₀ ∈ J'.biUnion adj →
      ∑ j ∈ J', m j + ε ≤ ∑ a ∈ J'.biUnion adj ∩ S, c a := by
    intro J' hJ' hj hA
    have := hε_le _ (hslack_mem J' hJ' hj hA)
    simp only [hslack_def] at this
    linarith
  have hε0 : 0 ≤ ε := by
    rcases mem_insert.1 hε_mem with h | h
    · rw [h]; exact hmpos.le
    rcases mem_insert.1 h with h | h
    · rw [h]; exact hca₀.le
    · obtain ⟨J', hJ'F, hJ'ε⟩ := mem_image.1 h
      rw [hF_def, mem_filter, mem_powerset] at hJ'F
      rw [← hJ'ε]
      have := hF.2.2.1 J' hJ'F.1
      simp only [hslack_def]
      linarith
  have hF' := feasible_eps hF hj₀ ha₀S ha₀adj hε_m hε_c hε_s
  set m' := Function.update m j₀ (m j₀ - ε) with hm'_def
  set c' := Function.update c a₀ (c a₀ - ε) with hc'_def
  -- solve the transferred instance
  obtain ⟨x', hx'⟩ : ∃ x', IsTransport J S adj m' c' x' := by
    rcases mem_insert.1 hε_mem with h | h
    · -- `ε = m j₀`: the buyer `j₀` is exhausted
      have hm'0 : m' j₀ = 0 := by simp [hm'_def, h]
      have hcard : (J.erase j₀).card + S.card < n := by
        rw [card_erase_of_mem hj₀]
        have := card_pos.2 ⟨j₀, hj₀⟩
        omega
      obtain ⟨x, hx⟩ := ih _ hcard (J.erase j₀) S adj m' c' rfl (feasible_erase_buyer hF' hm'0)
      exact ⟨x, transport_erase_buyer hm'0 hx⟩
    rcases mem_insert.1 h with h | h
    · -- `ε = c a₀`: the good `a₀` is sold out
      have hc'0 : c' a₀ = 0 := by simp [hc'_def, h]
      have hcard : J.card + (S.erase a₀).card < n := by
        rw [card_erase_of_mem ha₀S]
        have := card_pos.2 ⟨a₀, ha₀S⟩
        omega
      obtain ⟨x, hx⟩ := ih _ hcard J (S.erase a₀) adj m' c' rfl (feasible_erase_good hF' hc'0)
      exact ⟨x, transport_erase_good hc'0 hx⟩
    · -- `ε` is the slack of some `J'`, which is now tight: split
      obtain ⟨J', hJ'F, hJ'ε⟩ := mem_image.1 h
      rw [hF_def, mem_filter, mem_powerset] at hJ'F
      obtain ⟨hJ'J, hj₀J', ha₀J'⟩ := hJ'F
      have htight : ∑ j ∈ J', m' j = ∑ a ∈ J'.biUnion adj ∩ S, c' a := by
        rw [hm'_def, hc'_def, sum_update_sub, sum_update_sub]
        have ha' : a₀ ∈ J'.biUnion adj ∩ S := mem_inter.2 ⟨ha₀J', ha₀S⟩
        simp only [hj₀J', ha', ite_true, ite_false]
        simp only [hslack_def] at hJ'ε
        linarith
      have hJ'ne : J'.Nonempty := by
        obtain ⟨j, hj, -⟩ := mem_biUnion.1 ha₀J'
        exact ⟨j, hj⟩
      have hJ'lt : J'.card < J.card :=
        card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hJ'J, fun h => hj₀J' (h ▸ hj₀)⟩)
      have hcard₁ : J'.card + (J'.biUnion adj ∩ S).card < n := by
        have := card_le_card (inter_subset_right : J'.biUnion adj ∩ S ⊆ S)
        omega
      have hcard₂ : (J \ J').card + (S \ (J'.biUnion adj ∩ S)).card < n := by
        rw [card_sdiff_of_subset hJ'J]
        have h1 := card_pos.2 hJ'ne
        have h2 := card_le_card (sdiff_subset : S \ (J'.biUnion adj ∩ S) ⊆ S)
        omega
      obtain ⟨x₁, hx₁⟩ := ih _ hcard₁ J' _ adj m' c' rfl (feasible_split_left hF' hJ'J htight)
      obtain ⟨x₂, hx₂⟩ := ih _ hcard₂ (J \ J') _ adj m' c' rfl
        (feasible_split_right hF' hJ'J htight)
      exact ⟨_, transport_split hJ'J hx₁ hx₂⟩
  exact ⟨_, transport_eps hj₀ ha₀S ha₀adj hε0 hx'⟩

end SitePercC.HallAux

theorem SitePercC.fractional_hall {A B : Type*} [DecidableEq A]
    (J : Finset B) (S : Finset A) (adj : B → Finset A) (m : B → ℝ) (c : A → ℝ)
    (hm : ∀ j ∈ J, 0 ≤ m j) (hc : ∀ a ∈ S, 0 ≤ c a)
    (hHall : ∀ J' ⊆ J, ∑ j ∈ J', m j ≤ ∑ a ∈ J'.biUnion adj ∩ S, c a)
    (htot : ∑ j ∈ J, m j = ∑ a ∈ S, c a) :
    ∃ x : B → A → ℝ, (∀ j a, 0 ≤ x j a) ∧
      (∀ j a, x j a ≠ 0 → j ∈ J ∧ a ∈ S ∧ a ∈ adj j) ∧
      (∀ j ∈ J, ∑ a ∈ S, x j a = m j) ∧
      (∀ a ∈ S, ∑ j ∈ J, x j a = c a) := by
  classical
  exact SitePercC.HallAux.main _ J S adj m c rfl ⟨hm, hc, hHall, htot⟩
