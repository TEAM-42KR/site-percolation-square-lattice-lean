import SitePerc.Flow

/-! Finite integer-flow soundness under an injective state-space embedding. -/

open scoped BigOperators

set_option autoImplicit false

namespace SitePerc

/-- Source coverage is required only on its support. Target states outside the
node image carry zero flow capacity and may retain arbitrary nonnegative mass. -/
theorem injected_flow_implies_domination {I Q : Type}
    [Fintype I] [Fintype Q] [Preorder Q]
    (d : IntegerFlowData I) (f : I → Q) (hf : Function.Injective f)
    (ν μ : FiniteLaw Q)
    (valid : letI : Preorder I := Preorder.lift f; d.Valid)
    (bottom_le : ∀ q : Q, f d.bottom ≤ q)
    (source : ∀ i : I, i ≠ d.bottom →
      (d.scale : ℝ) * ν.mass (f i) ≤ (d.supply i : ℝ))
    (sink : ∀ i : I, (d.capacity i : ℝ) ≤ (d.scale : ℝ) * μ.mass (f i))
    (outside : ∀ q : Q, q ∉ Set.range f → ν.mass q = 0) :
    finiteDominates ν μ := by
  classical
  letI : Preorder I := Preorder.lift f
  intro U hU
  by_cases hbottom : f d.bottom ∈ U
  · have hfull : U = Finset.univ := Finset.eq_univ_iff_forall.mpr
      (fun q => hU (f d.bottom) q hbottom (bottom_le q))
    rw [hfull,ν.total,μ.total]
  · let V : Finset I := Finset.univ.filter (fun i => f i ∈ U)
    have hV (i : I) : i ∈ V ↔ f i ∈ U := by simp only [V,Finset.mem_filter,Finset.mem_univ,true_and]
    have hVU : V.image f ⊆ U := by
      intro q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact (hV i).mp hi
    have hsum_image (w : Q → ℝ) :
        (∑ q ∈ V.image f, w q) = ∑ i ∈ V, w (f i) :=
      Finset.sum_image (fun i _ j _ hij => hf hij)
    have hsource_sum : (∑ q ∈ U,ν.mass q) = ∑ i ∈ V,ν.mass (f i) := by
      rw [←hsum_image]
      symm
      apply Finset.sum_subset hVU
      intro q hq hnot
      apply outside q
      rintro ⟨i,rfl⟩
      exact hnot (Finset.mem_image.mpr ⟨i,(hV i).mpr hq,rfl⟩)
    have hsink_sum : (∑ i ∈ V,μ.mass (f i)) ≤ ∑ q ∈ U,μ.mass q := by
      rw [←hsum_image]
      exact Finset.sum_le_sum_of_subset_of_nonneg hVU (fun q _ _ => μ.nonnegative q)
    have hout (i : I) (hi : i ∈ V) :
        ∑ j,d.edge i j = ∑ j ∈ V,d.edge i j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ V)
      intro j _ hj
      by_contra hne
      have hpos : 0 < d.edge i j :=
        lt_of_le_of_ne (valid.edge_nonnegative i j) (Ne.symm hne)
      have hij : f i ≤ f j := valid.edge_increasing i j hpos
      exact hj ((hV j).mpr (hU (f i) (f j) ((hV i).mp hi) hij))
    have hcut : (∑ i ∈ V,∑ j,d.edge i j) ≤ ∑ j ∈ V,∑ i,d.edge i j := by
      calc
        (∑ i ∈ V,∑ j,d.edge i j) = ∑ i ∈ V,∑ j ∈ V,d.edge i j :=
          Finset.sum_congr rfl (fun i hi => hout i hi)
        _ = ∑ j ∈ V,∑ i ∈ V,d.edge i j := Finset.sum_comm
        _ ≤ ∑ j ∈ V,∑ i,d.edge i j := by
          apply Finset.sum_le_sum
          intro j _
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ V)
            (fun i _ _ => valid.edge_nonnegative i j)
    have hbalance : (∑ i ∈ V,d.supply i) + (∑ i ∈ V,∑ j,d.edge j i) =
        (∑ i ∈ V,d.absorbed i) + (∑ i ∈ V,∑ j,d.edge i j) := by
      simpa only [Finset.sum_add_distrib] using
        (Finset.sum_congr rfl (fun i (_ : i ∈ V) => valid.conservation i))
    have hsupply : (∑ i ∈ V,d.supply i) ≤ ∑ i ∈ V,d.absorbed i := by linarith
    have hscaled : (d.scale : ℝ) * (∑ q ∈ U,ν.mass q) ≤
        (d.scale : ℝ) * (∑ q ∈ U,μ.mass q) := by
      calc
        (d.scale : ℝ) * (∑ q ∈ U,ν.mass q) =
            (d.scale : ℝ) * (∑ i ∈ V,ν.mass (f i)) := by rw [hsource_sum]
        _ ≤ ∑ i ∈ V,(d.supply i : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          apply source i
          intro he
          exact hbottom (he ▸ (hV i).mp hi)
        _ ≤ ∑ i ∈ V,(d.absorbed i : ℝ) := by exact_mod_cast hsupply
        _ ≤ ∑ i ∈ V,(d.capacity i : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact_mod_cast (valid.absorbed_bounds i).2
        _ ≤ (d.scale : ℝ) * (∑ i ∈ V,μ.mass (f i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun i _ => sink i)
        _ ≤ (d.scale : ℝ) * (∑ q ∈ U,μ.mass q) :=
          mul_le_mul_of_nonneg_left hsink_sum (by positivity)
    exact le_of_mul_le_mul_left hscaled (by exact_mod_cast valid.scale_positive)

#print axioms injected_flow_implies_domination

end SitePerc
