/-
Finite stochastic order and symmetry quotients.
All laws are the actual real-valued laws from SitePerc.Base.
No antisymmetry of a raw boundary-state encoding is assumed.
-/
import SitePerc.Base
import SitePerc.FractionalHall
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped BigOperators

namespace SitePerc

/-- Finite Strassen holds on preorders, including redundant state encodings. -/
theorem finite_strassen {S : Type} [Fintype S] [Preorder S]
    (ν μ : FiniteLaw S) (h : finiteDominates ν μ) : monotoneCoupling ν μ := by
  classical
  let adj : S → Finset S := fun x => Finset.univ.filter (fun y => x ≤ y)
  have hHall : ∀ J : Finset S, J ⊆ Finset.univ →
      ∑ x ∈ J, ν.mass x ≤ ∑ y ∈ J.biUnion adj ∩ Finset.univ, μ.mass y := by
    intro J _
    let U := J.biUnion adj
    have hJU : J ⊆ U := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨x, hx, by simp [adj]⟩
    have hU : ∀ x y, x ∈ U → x ≤ y → y ∈ U := by
      intro x y hx hxy
      obtain ⟨z, hz, hzx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨z, hz, by
        simp only [adj, Finset.mem_filter, Finset.mem_univ, true_and] at hzx ⊢
        exact le_trans hzx hxy⟩
    calc
      ∑ x ∈ J, ν.mass x ≤ ∑ x ∈ U, ν.mass x :=
        Finset.sum_le_sum_of_subset_of_nonneg hJU (fun x _ _ => ν.nonnegative x)
      _ ≤ ∑ y ∈ U, μ.mass y := h U hU
      _ = ∑ y ∈ J.biUnion adj ∩ Finset.univ, μ.mass y := by simp [U]
  obtain ⟨π, hn, hs, hr, hc⟩ := SitePercC.fractional_hall
    (Finset.univ : Finset S) Finset.univ adj ν.mass μ.mass
    (fun x _ => ν.nonnegative x) (fun y _ => μ.nonnegative y)
    hHall (ν.total.trans μ.total.symm)
  refine ⟨π, hn, (fun x => hr x (Finset.mem_univ x)),
    (fun y => hc y (Finset.mem_univ y)), ?_⟩
  intro x y hxy
  have hy := (hs x y (ne_of_gt hxy)).2.2
  simpa [adj] using hy

/-- The converse needs only reflexivity/transitivity of the order. -/
theorem monotoneCoupling_implies_domination {S : Type} [Fintype S] [Preorder S]
    (ν μ : FiniteLaw S) (h : monotoneCoupling ν μ) : finiteDominates ν μ := by
  classical
  obtain ⟨π, hn, hr, hc, ho⟩ := h
  intro U hU
  calc
    ∑ x ∈ U, ν.mass x = ∑ x ∈ U, ∑ y, π x y := by simp_rw [hr]
    _ = ∑ y, ∑ x ∈ U, π x y := Finset.sum_comm
    _ ≤ ∑ y ∈ U, μ.mass y := by
      have hsum : ∑ y ∈ U, μ.mass y =
          ∑ y : S, if y ∈ U then μ.mass y else 0 := by simp
      rw [hsum]
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ U
      · simp only [hy, ite_true]
        rw [← hc y]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
          (fun x _ _ => hn x y)
      · simp only [hy, ite_false]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro x hx
        by_contra hne
        exact hy (hU x y hx (ho x y (lt_of_le_of_ne (hn x y) (Ne.symm hne))))


/-- The exact finite pushforward law, including zero-mass absent labels. -/
noncomputable def finiteLawMap {S Q : Type} [Fintype S] [Fintype Q] [DecidableEq Q]
    (ν : FiniteLaw S) (quot : S → Q) : FiniteLaw Q where
  mass := orbitMass ν.mass quot
  nonnegative := by
    intro a
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact ν.nonnegative x
    · exact le_rfl
  total := by
    classical
    unfold orbitMass
    rw [Finset.sum_comm]
    simpa using ν.total

/-- Uniform averaging uses all group elements, not a uniform orbit-size guess. -/
noncomputable def orbitAverage (Γ : Type) {S : Type}
    [Group Γ] [Fintype Γ] [MulAction Γ S] (f : S → ℝ) (x : S) : ℝ :=
  (Fintype.card Γ : ℝ)⁻¹ * ∑ g : Γ, f (g • x)

theorem orbitAverage_smul {S Γ : Type} [Group Γ] [Fintype Γ] [MulAction Γ S]
    (f : S → ℝ) (g : Γ) (x : S) : orbitAverage Γ f (g • x) = orbitAverage Γ f x := by
  unfold orbitAverage
  congr 1
  simpa [Equiv.mulRight, mul_smul] using
    Equiv.sum_comp (Equiv.mulRight g) (fun k : Γ => f (k • x))

theorem sum_mul_orbitAverage {S Γ : Type} [Fintype S] [Group Γ] [Fintype Γ]
    [MulAction Γ S] (w f : S → ℝ) (hw : ∀ g : Γ, ∀ x, w (g • x) = w x) :
    ∑ x, w x * orbitAverage Γ f x = ∑ x, w x * f x := by
  have hsum (g : Γ) : ∑ x, w x * f (g • x) = ∑ x, w x * f x := by
    calc
      ∑ x, w x * f (g • x) = ∑ x, w (g • x) * f (g • x) := by simp_rw [hw]
      _ = ∑ x, w x * f x := Equiv.sum_comp (MulAction.toPerm g) (fun x => w x * f x)
  have hx (x : S) : w x * orbitAverage Γ f x =
      (Fintype.card Γ : ℝ)⁻¹ * ∑ g : Γ, w x * f (g • x) := by
    rw [orbitAverage, ← Finset.mul_sum]
    ring
  simp_rw [hx]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [hsum]
  have hc : (Fintype.card Γ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [nsmul_eq_mul, hc]

theorem orbitAverage_mono {S Γ : Type} [Preorder S] [Group Γ] [Fintype Γ]
    [MulAction Γ S]
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y → g • x ≤ g • y)
    (f : S → ℝ) (hf : Monotone f) : Monotone (orbitAverage Γ f) := by
  intro x y hxy
  unfold orbitAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum (fun g _ => hf (orderAction g x y hxy))

theorem orbitMass_sum_mul {S Q : Type} [Fintype S] [Fintype Q] [DecidableEq Q]
    (w : S → ℝ) (quot : S → Q) (F : Q → ℝ) :
    ∑ a, orbitMass w quot a * F a = ∑ x, w x * F (quot x) := by
  classical
  unfold orbitMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem fiber_factorization {S Q : Type} (quot : S → Q) (f : S → ℝ)
    (hf : ∀ x y, quot x = quot y → f x = f y) :
    ∃ F : Q → ℝ, ∀ x, F (quot x) = f x := by
  classical
  refine ⟨fun a => if h : ∃ x, quot x = a then f (Classical.choose h) else 0, ?_⟩
  intro x
  have hx : ∃ y, quot y = quot x := ⟨x, rfl⟩
  simp only [dite_eq_left hx]
  exact hf _ x (Classical.choose_spec hx)

theorem orbitMass_pos_fiber {S Q : Type} [Fintype S] [DecidableEq Q]
    (w : S → ℝ) (quot : S → Q) (a : Q) (ha : 0 < orbitMass w quot a) :
    ∃ x, quot x = a := by
  classical
  by_contra h
  push Not at h
  simp [orbitMass, h] at ha

theorem actionInvariant_iff_fiber_constant {S Q Γ : Type} [Group Γ] [MulAction Γ S]
    (quot : S → Q) (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (w : S → ℝ) :
    (∀ g : Γ, ∀ x, w (g • x) = w x) ↔ ∀ x y, quot x = quot y → w x = w y := by
  constructor
  · intro hw x y hxy
    obtain ⟨g, hg⟩ := (fibers x y).mp hxy
    rw [← hg, hw]
  · intro hw g x
    exact (hw x (g • x) ((fibers x (g • x)).mpr ⟨g, rfl⟩)).symm

theorem finiteLawMap_invariant {Ω S Γ : Type} [Fintype Ω] [Fintype S]
    [DecidableEq S] [Group Γ] [MulAction Γ Ω] [MulAction Γ S]
    (ν : FiniteLaw Ω) (f : Ω → S)
    (hν : ∀ g : Γ, ∀ x, ν.mass (g • x) = ν.mass x)
    (hf : ∀ g : Γ, ∀ x, f (g • x) = g • f x) (g : Γ) (s : S) :
    (finiteLawMap ν f).mass (g • s) = (finiteLawMap ν f).mass s := by
  classical
  change (∑ x, if f x = g • s then ν.mass x else 0) =
    ∑ x, if f x = s then ν.mass x else 0
  calc
    _ = ∑ x, if f (g • x) = g • s then ν.mass (g • x) else 0 :=
      (Equiv.sum_comp (MulAction.toPerm g)
        (fun x => if f x = g • s then ν.mass x else 0)).symm
    _ = _ := by simp_rw [hf, hν, smul_left_cancel_iff]


/-- An actual orbit coupling lifts to the original laws. The construction uses
Strassen after averaging upper-set tests; no existence-of-lift premise is used. -/
theorem orbit_coupling_lift {S Q Γ : Type} [Fintype S] [Fintype Q] [DecidableEq Q]
    [Preorder S] [Preorder Q] [Group Γ] [Fintype Γ] [MulAction Γ S]
    (ν μ : FiniteLaw S) (quot : S → Q)
    (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y)
    (quotientOrder : ∀ x y, quot x ≤ quot y ↔ ∃ g : Γ, x ≤ g • y)
    (refInvariant : ∀ g : Γ, ∀ x, ν.mass (g • x) = ν.mass x)
    (tarInvariant : ∀ g : Γ, ∀ x, μ.mass (g • x) = μ.mass x)
    (π : Q → Q → ℝ) (nonneg : ∀ a b, 0 ≤ π a b)
    (rows : ∀ a, ∑ b, π a b = orbitMass ν.mass quot a)
    (cols : ∀ b, ∑ a, π a b = orbitMass μ.mass quot b)
    (ordered : ∀ a b, 0 < π a b → a ≤ b) : monotoneCoupling ν μ := by
  classical
  apply finite_strassen ν μ
  intro U hU
  let f : S → ℝ := fun x => if x ∈ U then 1 else 0
  let fbar := orbitAverage Γ f
  have hf : Monotone f := by
    intro x y hxy
    by_cases hx : x ∈ U
    · have hy := hU x y hx hxy
      simp [f, hx, hy]
    · simp only [f, hx, ite_false]
      split_ifs <;> norm_num
  have hmono : Monotone fbar :=
    orbitAverage_mono (fun g x y hxy => (orderAction g x y).mp hxy) f hf
  have hconstant : ∀ x y, quot x = quot y → fbar x = fbar y :=
    (actionInvariant_iff_fiber_constant quot fibers fbar).mp
      (fun g x => orbitAverage_smul f g x)
  obtain ⟨F, hF⟩ := fiber_factorization quot fbar hconstant
  have hcompare : ∀ a b, 0 < π a b → F a ≤ F b := by
    intro a b hab
    have ha : 0 < orbitMass ν.mass quot a := by
      rw [← rows a]
      exact lt_of_lt_of_le hab
        (Finset.single_le_sum (fun c _ => nonneg a c) (Finset.mem_univ b))
    have hb : 0 < orbitMass μ.mass quot b := by
      rw [← cols b]
      exact lt_of_lt_of_le hab
        (Finset.single_le_sum (fun c _ => nonneg c b) (Finset.mem_univ a))
    obtain ⟨x, hx⟩ := orbitMass_pos_fiber ν.mass quot a ha
    obtain ⟨y, hy⟩ := orbitMass_pos_fiber μ.mass quot b hb
    have hxy : quot x ≤ quot y := by simpa [hx, hy] using ordered a b hab
    obtain ⟨g, hg⟩ := (quotientOrder x y).mp hxy
    calc
      F a = fbar x := by rw [← hx, hF]
      _ ≤ fbar (g • y) := hmono hg
      _ = fbar y := orbitAverage_smul f g y
      _ = F b := by rw [← hy, hF]
  calc
    ∑ x ∈ U, ν.mass x = ∑ x, ν.mass x * f x := by simp [f, mul_ite]
    _ = ∑ x, ν.mass x * fbar x := (sum_mul_orbitAverage ν.mass f refInvariant).symm
    _ = ∑ a, orbitMass ν.mass quot a * F a := by
      rw [orbitMass_sum_mul]
      simp_rw [hF]
    _ = ∑ a, ∑ b, π a b * F a := by simp_rw [← rows, Finset.sum_mul]
    _ ≤ ∑ a, ∑ b, π a b * F b := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      by_cases hz : π a b = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left
          (hcompare a b (lt_of_le_of_ne (nonneg a b) (Ne.symm hz))) (nonneg a b)
    _ = ∑ b, orbitMass μ.mass quot b * F b := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, cols]
    _ = ∑ x, μ.mass x * fbar x := by
      rw [orbitMass_sum_mul]
      simp_rw [hF]
    _ = ∑ x, μ.mass x * f x := sum_mul_orbitAverage μ.mass f tarInvariant
    _ = ∑ x ∈ U, μ.mass x := by simp [f, mul_ite]

/-- Orbit stochastic dominance uses precisely the actual pushforward law. -/
theorem orbit_domination_lift {S Q Γ : Type} [Fintype S] [Fintype Q] [DecidableEq Q]
    [Preorder S] [Preorder Q] [Group Γ] [Fintype Γ] [MulAction Γ S]
    (ν μ : FiniteLaw S) (quot : S → Q)
    (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y)
    (quotientOrder : ∀ x y, quot x ≤ quot y ↔ ∃ g : Γ, x ≤ g • y)
    (refInvariant : ∀ g : Γ, ∀ x, ν.mass (g • x) = ν.mass x)
    (tarInvariant : ∀ g : Γ, ∀ x, μ.mass (g • x) = μ.mass x)
    (h : finiteDominates (finiteLawMap ν quot) (finiteLawMap μ quot)) : monotoneCoupling ν μ := by
  obtain ⟨π, hn, hr, hc, ho⟩ := finite_strassen (finiteLawMap ν quot) (finiteLawMap μ quot) h
  exact orbit_coupling_lift ν μ quot fibers orderAction quotientOrder refInvariant tarInvariant
    π hn hr hc ho


/-- Representative comparison on an actual orbit labeling. Surjectivity is
explicit because unused labels must not acquire a fabricated reflexive order. -/
noncomputable def orbitPreorder {S Q Γ : Type} [Preorder S] [Group Γ] [MulAction Γ S]
    (quot : S → Q) (surj : Function.Surjective quot)
    (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y) : Preorder Q where
  le a b := ∃ x y, quot x = a ∧ quot y = b ∧ x ≤ y
  le_refl a := by
    obtain ⟨x, hx⟩ := surj a
    exact ⟨x, x, hx, hx, le_rfl⟩
  le_trans a b c hab hbc := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hab
    obtain ⟨u, v, hu, hv, huv⟩ := hbc
    obtain ⟨g, hg⟩ := (fibers u y).mp (hu.trans hy.symm)
    refine ⟨x, g • v, hx, ?_, le_trans hxy ?_⟩
    · exact ((fibers v (g • v)).mpr ⟨g, rfl⟩).symm.trans hv
    · simpa [hg] using (orderAction g u v).mp huv

theorem orbitPreorder_le_iff {S Q Γ : Type} [Preorder S] [Group Γ] [MulAction Γ S]
    (quot : S → Q) (surj : Function.Surjective quot)
    (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y) (x y : S) :
    letI := orbitPreorder quot surj fibers orderAction
    quot x ≤ quot y ↔ ∃ g : Γ, x ≤ g • y := by
  change (∃ u v, quot u = quot x ∧ quot v = quot y ∧ u ≤ v) ↔ _
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨g, hg⟩ := (fibers u x).mp hu
    obtain ⟨h, hh⟩ := (fibers y v).mp hv.symm
    refine ⟨g * h, ?_⟩
    simpa only [mul_smul, hh, hg] using (orderAction g u v).mp huv
  · rintro ⟨g, hg⟩
    exact ⟨x, g • y, rfl, ((fibers y (g • y)).mpr ⟨g, rfl⟩).symm, hg⟩

theorem finite_action_eq_of_le_smul {S Γ : Type} [PartialOrder S] [Group Γ] [Finite Γ] [MulAction Γ S]
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y)
    (g : Γ) (x : S) (hx : x ≤ g • x) : x = g • x := by
  have hpow : ∀ n : ℕ, x ≤ g ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [pow_succ', mul_smul] using
        le_trans hx ((orderAction g x (g ^ n • x)).mp ih)
  have hb := (orderAction g x (g ^ (orderOf g - 1) • x)).mp (hpow (orderOf g - 1))
  have hone : 1 ≤ orderOf g := orderOf_pos g
  rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel hone, pow_orderOf_eq_one, one_smul] at hb
  exact le_antisymm hx hb

theorem orbitPreorder_antisymm {S Q Γ : Type} [PartialOrder S] [Group Γ] [Finite Γ] [MulAction Γ S]
    (quot : S → Q) (surj : Function.Surjective quot)
    (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y) :
    letI := orbitPreorder quot surj fibers orderAction
    ∀ a b : Q, a ≤ b → b ≤ a → a = b := by
  letI := orbitPreorder quot surj fibers orderAction
  intro a b hab hba
  obtain ⟨x, hx⟩ := surj a
  obtain ⟨y, hy⟩ := surj b
  have hxy : quot x ≤ quot y := by simpa [hx, hy] using hab
  have hyx : quot y ≤ quot x := by simpa [hx, hy] using hba
  obtain ⟨g, hg⟩ := (orbitPreorder_le_iff quot surj fibers orderAction x y).mp hxy
  obtain ⟨h, hh⟩ := (orbitPreorder_le_iff quot surj fibers orderAction y x).mp hyx
  have hstep : g • y ≤ (g * h) • x := by
    simpa only [mul_smul] using (orderAction g y (h • x)).mp hh
  have heq := finite_action_eq_of_le_smul orderAction (g * h) x (hg.trans hstep)
  have hrep : x = g • y := le_antisymm hg (hstep.trans_eq heq.symm)
  calc
    a = quot x := hx.symm
    _ = quot (g • y) := congrArg quot hrep
    _ = quot y := ((fibers y (g • y)).mpr ⟨g, rfl⟩).symm
    _ = b := hy

theorem orbitQuotient_fibers {S Γ : Type} [Group Γ] [MulAction Γ S] (x y : S) :
    Quotient.mk (MulAction.orbitRel Γ S) x = Quotient.mk (MulAction.orbitRel Γ S) y ↔
    ∃ g : Γ, g • x = y := by
  rw [eq_comm, Quotient.eq]
  exact MulAction.mem_orbit_iff



/-- A finite action on a genuine poset has an antisymmetric orbit order.
No such claim is made for an arbitrary raw BoundaryState preorder. -/
@[instance_reducible]
noncomputable def orbitPartialOrder {S Q Γ : Type} [PartialOrder S] [Group Γ]
    [Finite Γ] [MulAction Γ S] (quot : S → Q) (surj : Function.Surjective quot)
    (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y) : PartialOrder Q :=
  { orbitPreorder quot surj fibers orderAction with
    le_antisymm := orbitPreorder_antisymm quot surj fibers orderAction }

/-- The actual orbit quotient, not a postulated family of orbit witnesses. -/
@[instance_reducible]
noncomputable def orbitQuotientPartialOrder {S Γ : Type} [PartialOrder S] [Group Γ]
    [Finite Γ] [MulAction Γ S]
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y) :
    PartialOrder (MulAction.orbitRel.Quotient Γ S) :=
  orbitPartialOrder (Quotient.mk (MulAction.orbitRel Γ S))
    (by intro a; exact Quotient.inductionOn a (fun x => ⟨x, rfl⟩))
    (by intro x y; rw [eq_comm, Quotient.eq]; exact MulAction.mem_orbit_iff)
    orderAction

theorem orbitQuotient_le_iff {S Γ : Type} [PartialOrder S] [Group Γ] [Finite Γ] [MulAction Γ S]
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y) (x y : S) :
    letI := orbitQuotientPartialOrder orderAction
    Quotient.mk (MulAction.orbitRel Γ S) x ≤ Quotient.mk (MulAction.orbitRel Γ S) y ↔
    ∃ g : Γ, x ≤ g • y := by
  exact orbitPreorder_le_iff (Quotient.mk (MulAction.orbitRel Γ S))
    (by intro a; exact Quotient.inductionOn a (fun z => ⟨z, rfl⟩))
    (orbitQuotient_fibers) orderAction x y

theorem orbitPreorder_domination_lift {S Q Γ : Type} [Fintype S] [Fintype Q] [DecidableEq Q]
    [Preorder S] [Group Γ] [Fintype Γ] [MulAction Γ S]
    (ν μ : FiniteLaw S) (quot : S → Q) (surj : Function.Surjective quot)
    (fibers : ∀ x y, quot x = quot y ↔ ∃ g : Γ, g • x = y)
    (orderAction : ∀ g : Γ, ∀ x y : S, x ≤ y ↔ g • x ≤ g • y)
    (refInvariant : ∀ g : Γ, ∀ x, ν.mass (g • x) = ν.mass x)
    (tarInvariant : ∀ g : Γ, ∀ x, μ.mass (g • x) = μ.mass x)
    (h : letI := orbitPreorder quot surj fibers orderAction
      finiteDominates (finiteLawMap ν quot) (finiteLawMap μ quot)) : monotoneCoupling ν μ := by
  letI := orbitPreorder quot surj fibers orderAction
  exact orbit_domination_lift ν μ quot fibers orderAction
    (orbitPreorder_le_iff quot surj fibers orderAction) refInvariant tarInvariant h


end SitePerc
